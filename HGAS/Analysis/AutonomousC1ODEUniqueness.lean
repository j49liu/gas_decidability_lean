import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Connected.Clopen

/-!
# Global uniqueness for autonomous finite-dimensional `C¹` ODEs

Mathlib's Grönwall theorem gives uniqueness when both trajectories remain
in a set on which the vector field has one Lipschitz constant.  A
polynomial vector field need not be globally Lipschitz, so that statement
cannot be applied with the whole space.

This module supplies the standard local-to-global bridge.  A `C¹` vector
field is Lipschitz on every compact closed ball.  Therefore two solutions
which agree at one time agree in a neighborhood of every agreement time.
Their agreement set is also closed by continuity.  Since the real line is
connected, the nonempty agreement set is all of `ℝ`.

The result is reusable for arbitrary finite-dimensional real normed
spaces, not just for the Jacobi system.
-/

namespace HGAS.Analysis

open Filter Metric Set Topology

/-- Local uniqueness in the form needed for continuation arguments.

The two curves only have to solve the autonomous equation in a
neighborhood of the comparison time.  Separate continuity-at hypotheses
make the statement useful when one of the curves is given by a formula
whose ODE identity is known only on an open regular chart. -/
theorem autonomousC1_ode_solution_eventuallyEq
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Y : E → E}
    (hY : ContDiff ℝ 1 Y)
    {f g : ℝ → E} {t : ℝ}
    (hf :
      ∀ᶠ s in 𝓝 t,
        HasDerivAt f (Y (f s)) s)
    (hg :
      ∀ᶠ s in 𝓝 t,
        HasDerivAt g (Y (g s)) s)
    (hfcont : ContinuousAt f t)
    (hgcont : ContinuousAt g t)
    (heq : f t = g t) :
    f =ᶠ[𝓝 t] g := by
  let B : Set E := closedBall (f t) 1
  obtain ⟨K, hK⟩ :=
    hY.contDiffOn.exists_lipschitzOnWith
      one_ne_zero
      (convex_closedBall (f t) 1)
      (isCompact_closedBall (f t) 1)
  have hfmem :
      ∀ᶠ s in 𝓝 t, f s ∈ B :=
    hfcont.eventually
      (closedBall_mem_nhds (f t) zero_lt_one)
  have hgmem :
      ∀ᶠ s in 𝓝 t, g s ∈ B := by
    apply hgcont.eventually
    rw [show g t = f t by exact heq.symm]
    exact closedBall_mem_nhds (f t) zero_lt_one
  apply ODE_solution_unique_of_eventually
    (v := fun _ : ℝ ↦ Y)
    (s := fun _ : ℝ ↦ B)
    (K := K)
  · exact Filter.Eventually.of_forall fun _ ↦ hK
  · filter_upwards [hf, hfmem] with s hfs hs
    exact ⟨hfs, hs⟩
  · filter_upwards [hg, hgmem] with s hgs hs
    exact ⟨hgs, hs⟩
  · exact heq

/-- Two global solutions of the same autonomous finite-dimensional `C¹`
ODE which agree once agree for every real time. -/
theorem autonomousC1_ode_solution_unique
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Y : E → E}
    (hY : ContDiff ℝ 1 Y)
    {f g : ℝ → E}
    (hf : ∀ t, HasDerivAt f (Y (f t)) t)
    (hg : ∀ t, HasDerivAt g (Y (g t)) t)
    {t₀ : ℝ}
    (heq : f t₀ = g t₀) :
    f = g := by
  have hfcont : Continuous f :=
    continuous_iff_continuousAt.mpr
      fun t ↦ (hf t).continuousAt
  have hgcont : Continuous g :=
    continuous_iff_continuousAt.mpr
      fun t ↦ (hg t).continuousAt
  let agreement : Set ℝ := {t | f t = g t}
  have hagreement_closed : IsClosed agreement := by
    exact isClosed_eq hfcont hgcont
  have hagreement_open : IsOpen agreement := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    let B : Set E := closedBall (f t) 1
    obtain ⟨K, hK⟩ :=
      hY.contDiffOn.exists_lipschitzOnWith
        one_ne_zero
        (convex_closedBall (f t) 1)
        (isCompact_closedBall (f t) 1)
    have hfmem :
        ∀ᶠ s in 𝓝 t, f s ∈ B :=
      hfcont.continuousAt.eventually
        (closedBall_mem_nhds (f t) zero_lt_one)
    have hgmem :
        ∀ᶠ s in 𝓝 t, g s ∈ B := by
      apply hgcont.continuousAt.eventually
      rw [show g t = f t by exact ht.symm]
      exact closedBall_mem_nhds (f t) zero_lt_one
    have hlocal : f =ᶠ[𝓝 t] g := by
      apply ODE_solution_unique_of_eventually
        (v := fun _ : ℝ ↦ Y)
        (s := fun _ : ℝ ↦ B)
        (K := K)
      · exact Filter.Eventually.of_forall fun _ ↦ hK
      · filter_upwards [hfmem] with s hs
        exact ⟨hf s, hs⟩
      · filter_upwards [hgmem] with s hs
        exact ⟨hg s, hs⟩
      · exact ht
    exact hlocal
  have hagreement_clopen : IsClopen agreement :=
    ⟨hagreement_closed, hagreement_open⟩
  have hagreement_nonempty : agreement.Nonempty :=
    ⟨t₀, heq⟩
  have hagreement_univ :
      agreement = Set.univ :=
    hagreement_clopen.eq_univ hagreement_nonempty
  funext t
  have ht : t ∈ agreement := by
    rw [hagreement_univ]
    exact Set.mem_univ t
  exact ht

end HGAS.Analysis
