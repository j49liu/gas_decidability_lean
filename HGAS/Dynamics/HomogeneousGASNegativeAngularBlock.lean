import HGAS.Dynamics.AngularPhysicalTimeChange
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Homogeneous GAS gives one uniform negative angular block

This file closes the dynamical half of the constructive homogeneous
converse theorem.

Let `F` be a `C¹` field homogeneous of degree `k+1`, and suppose that the
origin is globally asymptotically stable.  Homogeneous Lyapunov stability
first supplies a uniform bound `B` for every physical trajectory starting
on the unit sphere.  A compactly supported auxiliary physical flow agrees
with all those forward trajectories.  Compactness of the unit sphere and
stability then give a common physical time `T` after which every such
orbit has radius less than `1/2`.

The angular-to-physical calculation in
`AngularPhysicalTimeChange` shows that

```
dt/dτ = r(τ)^{-k}.
```

Since `r(τ) < B`, physical time grows at least as fast as `B^{-k}τ`.
Thus the common angular horizon

```
L = (T+1) B^k
```

corresponds to a physical time beyond `T` for every initial direction.
At that horizon

```
exp(A(L,u)) = r(L,u) < 1/2,
```

so every angular cocycle block is bounded by the same negative number
`log(1/2)`.
-/

namespace HGAS

open Metric Set
open scoped BoundedContinuousFunction RealInnerProductSpace Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A GAS degree-`k+1` homogeneous `C¹` field has one common strictly
negative radial-reward block along its Euclidean angular flow. -/
theorem GloballyAsymptoticallyStable.exists_uniformNegativeEuclideanAngularBlock
    {F : E → E} {k : ℕ}
    (hgas : GloballyAsymptoticallyStable F 0)
    (hFhom : ScalesAsDegree ℝ (k + 1) F)
    (hF : ContDiff ℝ 1 F) :
    ∃ L c : ℝ, 0 < L ∧ 0 < c ∧
      ∀ u : E, ‖u‖ = 1 →
        Dynamics.orbitIntegral
          (euclideanAngularFlow F hF)
          (boundedCutoffInnerRadialReward F hF) L u ≤ -c := by
  obtain ⟨B, hB, T, hT, hbound, hcontract⟩ :=
    hgas.exists_cutoffFlow_unit_contraction hFhom hF
  let Ψ : Flow ℝ E :=
    homogeneousGASCutoffFlow F hF B hB
  let L : ℝ := (T + 1) * B ^ k
  let c : ℝ := -Real.log (1 / 2 : ℝ)
  have hL : 0 < L := by
    dsimp only [L]
    exact mul_pos (by linarith) (pow_pos hB k)
  have hc : 0 < c := by
    dsimp only [c]
    exact neg_pos.mpr
      (Real.log_neg (by norm_num) (by norm_num))
  refine ⟨L, c, hL, hc, ?_⟩
  intro u hu
  have hΨ :
      ∀ t : ℝ, 0 ≤ t →
        HasDerivAt (fun s : ℝ ↦ Ψ s u)
          (F (Ψ t u)) t := by
    intro t ht
    have horbit :=
      homogeneousGASCutoffFlow_isIntegralCurve
        F hF B hB u t
    have hfield :
        homogeneousGASCutoffField F B hB (Ψ t u) =
          F (Ψ t u) := by
      apply homogeneousGASCutoffField_eq_of_norm_le
      exact (hbound u hu t ht).le
    simpa only [Ψ, hfield] using horbit
  have hclockLower :
      (B ^ k)⁻¹ * L ≤
        euclideanAngularPhysicalClock F hF k L u := by
    apply euclideanAngularPhysicalClock_ge_of_physical_bound
      F hF k hFhom Ψ u hu hΨ hB
    · intro t ht
      exact hbound u hu t ht
    · exact hL.le
  have hcancel : (B ^ k)⁻¹ * L = T + 1 := by
    dsimp only [L]
    field_simp [pow_ne_zero k hB.ne']
  have hclockAfter :
      T ≤ euclideanAngularPhysicalClock F hF k L u := by
    rw [hcancel] at hclockLower
    linarith
  have hrealize :=
    euclideanAngularReconstruction_eq_physicalFlow
      F hF k hFhom Ψ u hu hΨ hL.le
  have hradiusHalf :
      euclideanAngularRadius F hF L u < (1 / 2 : ℝ) := by
    rw [← norm_euclideanAngularReconstruction F hF u hu L,
      hrealize]
    exact hcontract u hu _ hclockAfter
  have hlog :
      euclideanAngularLogRadius F hF L u <
        Real.log (1 / 2 : ℝ) := by
    exact
      (Real.lt_log_iff_exp_lt (by norm_num)).2
        (by
          simpa only [euclideanAngularRadius] using hradiusHalf)
  change euclideanAngularLogRadius F hF L u ≤ -c
  dsimp only [c]
  linarith

end

end HGAS
