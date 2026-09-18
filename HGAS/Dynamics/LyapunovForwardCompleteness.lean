import HGAS.Dynamics.ForwardCompleteness
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# Forward completeness from a coercive Lyapunov function

A locally Lipschitz vector field need not be forward complete.  The standard
Lyapunov continuation argument is therefore a genuine part of a GAS proof,
not a definitional formality.

This file gives a reusable proof.  For each initial state we multiply the
field by a smooth compactly supported bump which is identically one on a
large ball.  The cut-off field is globally Lipschitz and bounded, so it has
a global integral curve.  Because the bump is nonnegative, the Lyapunov
derivative remains nonpositive.  Coercivity confines that curve to the
inner ball, where the bump equals one; hence the same curve solves the
original ODE for all forward times.
-/

namespace HGAS

open Filter Set
open scoped NNReal Topology

noncomputable section

set_option maxHeartbeats 800000 in
-- Smooth-bump and compact-support typeclass synthesis is unusually deep in
-- this generic finite-dimensional statement.
/-- A continuously differentiable vector field with a differentiable,
quadratically coercive, nonincreasing Lyapunov function is forward
complete.

The derivative condition is expressed using the Fréchet derivative, which
makes its preservation under multiplication of the field by a
nonnegative cutoff immediate by linearity. -/
theorem forwardComplete_of_coercive_lyapunov
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E → E) (V : E → ℝ)
    (hf : ContDiff ℝ 1 f)
    (hV : Differentiable ℝ V)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ x : E, c * ‖x‖ ^ 2 ≤ V x)
    (hdecrease : ∀ x : E, fderiv ℝ V x (f x) ≤ 0) :
    ForwardComplete f := by
  intro x₀
  have hVx₀ : 0 ≤ V x₀ :=
    (mul_nonneg hc.le (sq_nonneg ‖x₀‖)).trans (hlower x₀)
  let R : ℝ := Real.sqrt (V x₀ / c) + 1
  have hquot : 0 ≤ V x₀ / c := div_nonneg hVx₀ hc.le
  have hR : 0 < R := by
    dsimp [R]
    positivity
  let bump : ContDiffBump (0 : E) :=
    { rIn := R
      rOut := R + 1
      rIn_pos := hR
      rIn_lt_rOut := lt_add_one R }
  let g : E → E := fun x ↦ bump x • f x
  have hgContDiff : ContDiff ℝ 1 g := by
    dsimp [g]
    exact bump.contDiff.smul hf
  have hgCompact : HasCompactSupport g := by
    dsimp [g]
    exact bump.hasCompactSupport.smul_right
  obtain ⟨K, hK⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport
      hgCompact hgContDiff one_ne_zero
  obtain ⟨L, hL⟩ :
      ∃ L : ℝ, ∀ x, ‖g x‖ ≤ L :=
    HasCompactSupport.exists_bound_of_continuous
      hgCompact hgContDiff.continuous
  let L' : NNReal :=
    ⟨max L (0 : ℝ), le_max_right L 0⟩
  have hL' : ∀ x, ‖g x‖ ≤ L' := by
    intro x
    exact (hL x).trans (by
      change L ≤ max L 0
      exact le_max_left _ _)
  obtain ⟨γ, hγzero, hγ⟩ :=
    exists_global_integralCurve_of_lipschitz_bounded
      g hK hL' x₀
  have hVderiv :
      ∀ t : ℝ,
        HasDerivAt (fun s ↦ V (γ s))
          (bump (γ t) * fderiv ℝ V (γ t) (f (γ t))) t := by
    intro t
    have hcomp :=
      (hV (γ t)).hasFDerivAt.comp_hasDerivAt t (hγ t)
    convert hcomp using 1
    simp only [g, map_smul, smul_eq_mul]
  have hVanti :
      AntitoneOn (fun t ↦ V (γ t)) (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact hV.continuous.comp_continuousOn hγ.continuous.continuousOn
    · intro t ht
      exact (hVderiv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hVderiv t).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos
        bump.nonneg (hdecrease (γ t))
  have hinside : ∀ t : ℝ, 0 ≤ t → ‖γ t‖ < R := by
    intro t ht
    have hVle : V (γ t) ≤ V x₀ := by
      rw [← hγzero]
      exact hVanti (by simp) ht ht
    have hsquare : ‖γ t‖ ^ 2 ≤ V x₀ / c := by
      exact (le_div_iff₀ hc).2
        (by simpa [mul_comm] using (hlower (γ t)).trans hVle)
    have hsqrt :
        ‖γ t‖ ≤ Real.sqrt (V x₀ / c) := by
      have hsqrt_sq :
          (Real.sqrt (V x₀ / c)) ^ 2 = V x₀ / c :=
        Real.sq_sqrt hquot
      nlinarith [norm_nonneg (γ t),
        Real.sqrt_nonneg (V x₀ / c)]
    dsimp [R]
    linarith
  refine ⟨γ, hγzero, ?_⟩
  intro t ht
  have hbump : bump (γ t) = 1 := by
    apply bump.one_of_mem_closedBall
    simpa [Metric.mem_closedBall, dist_zero_right] using
      (hinside t ht).le
  have hgt : g (γ t) = f (γ t) := by
    simp [g, hbump]
  simpa [hgt] using (hγ t).hasDerivWithinAt

end

end HGAS
