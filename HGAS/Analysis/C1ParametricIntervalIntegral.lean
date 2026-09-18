import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# A `C¹` parameter-dependent interval integral

This file packages a standard differentiation-under-the-integral argument
in the form needed by the finite-cocycle Lyapunov construction.

Let `F(x,t)` be a scalar integrand, and let `F'(x,t)` be its Fréchet
derivative with respect to the state variable `x`.  If both are jointly
continuous and `F'` is indeed the derivative of `F` in `x`, then

```
x ↦ ∫ t in a..b, F x t
```

is continuously differentiable, with derivative

```
x ↦ ∫ t in a..b, F' x t.
```

The only compactness used in the proof is compactness of a closed ball in a
finite-dimensional space and of the finite time interval.  Joint continuity
therefore supplies the local uniform derivative bound required by Mathlib's
dominated parametric-integral theorem.

The result is deliberately independent of flows and cocycles.  It is useful
whenever a finite-time integral is used to construct a smooth function.
-/

namespace HGAS

open Filter MeasureTheory Metric Set
open scoped Interval Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A jointly continuous family on a finite interval is interval integrable
after fixing the state parameter. -/
theorem intervalIntegrable_of_continuous_uncurry
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [CompleteSpace Z]
    (F : E → ℝ → Z)
    (hF : Continuous (Function.uncurry F))
    (x : E) (a b : ℝ) :
    IntervalIntegrable (F x) volume a b := by
  have hslice : Continuous (F x) := by
    have hx : Continuous (fun t : ℝ ↦ (x, t)) :=
      continuous_const.prodMk continuous_id
    simpa [Function.comp_def, Function.uncurry_apply_pair] using
      hF.comp hx
  exact hslice.intervalIntegrable a b

/-- Differentiating a jointly `C¹` scalar integrand under a finite interval
integral produces a `C¹` function of the state parameter.

The derivative is stated using a supplied jointly continuous field `F'`.
This makes the theorem reusable even when identifying the literal `fderiv`
of the uncurried map would be inconvenient. -/
theorem contDiff_one_intervalIntegral_of_continuous_fderiv
    (F : E → ℝ → ℝ)
    (F' : E → ℝ → E →L[ℝ] ℝ)
    (hF : Continuous (Function.uncurry F))
    (hF' : Continuous (Function.uncurry F'))
    (hderiv :
      ∀ x : E, ∀ t : ℝ,
        HasFDerivAt (fun y : E ↦ F y t) (F' x t) x)
    (a b : ℝ) :
    ContDiff ℝ 1 (fun x : E ↦ ∫ t in a..b, F x t) := by
  let D : E → E →L[ℝ] ℝ :=
    fun x ↦ ∫ t in a..b, F' x t
  have hD_continuous : Continuous D := by
    rw [continuous_iff_continuousAt]
    intro x₀
    let C : Set (E × ℝ) :=
      closedBall x₀ 1 ×ˢ uIcc a b
    have hCcompact : IsCompact C := by
      exact (isCompact_closedBall x₀ 1).prod isCompact_uIcc
    obtain ⟨M, hM⟩ :=
      hCcompact.bddAbove_image hF'.norm.continuousOn
    let B : ℝ := max M 0 + 1
    have hB_nonneg : 0 ≤ B := by
      dsimp only [B]
      have hzero : 0 ≤ max M 0 := le_max_right M 0
      linarith
    have hbound :
        ∀ y ∈ closedBall x₀ 1, ∀ t ∈ uIcc a b,
          ‖F' y t‖ ≤ B := by
      intro y hy t ht
      have hleM : ‖F' y t‖ ≤ M := by
        apply hM
        exact ⟨(y, t), ⟨hy, ht⟩, rfl⟩
      exact hleM.trans
        ((le_max_left M 0).trans (le_add_of_nonneg_right zero_le_one))
    have hmeas :
        ∀ᶠ y in 𝓝 x₀,
          AEStronglyMeasurable (F' y)
            (volume.restrict (Ι a b)) := by
      filter_upwards [] with y
      have hslice : Continuous (F' y) := by
        have hy : Continuous (fun t : ℝ ↦ (y, t)) :=
          continuous_const.prodMk continuous_id
        simpa [Function.comp_def, Function.uncurry_apply_pair] using
          hF'.comp hy
      exact hslice.aestronglyMeasurable
    have hbound_ae :
        ∀ᶠ y in 𝓝 x₀,
          ∀ᵐ t ∂volume, t ∈ Ι a b → ‖F' y t‖ ≤ B := by
      filter_upwards [closedBall_mem_nhds x₀ zero_lt_one] with y hy
      filter_upwards [] with t ht
      exact hbound y hy t (uIoc_subset_uIcc ht)
    have hB_integrable :
        IntervalIntegrable (fun _ : ℝ ↦ B) volume a b :=
      intervalIntegrable_const
    have hpoint_cont :
        ∀ᵐ t ∂volume, t ∈ Ι a b →
          ContinuousAt (fun y : E ↦ F' y t) x₀ := by
      filter_upwards [] with t _ht
      have ht : Continuous (fun y : E ↦ (y, t)) :=
        continuous_id.prodMk continuous_const
      exact (hF'.comp ht).continuousAt
    simpa only [D] using
      intervalIntegral.continuousAt_of_dominated_interval
        hmeas hbound_ae hB_integrable hpoint_cont
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨D, hD_continuous, ?_⟩
  intro x₀
  let C : Set (E × ℝ) :=
    closedBall x₀ 1 ×ˢ uIcc a b
  have hCcompact : IsCompact C := by
    exact (isCompact_closedBall x₀ 1).prod isCompact_uIcc
  obtain ⟨M, hM⟩ :=
    hCcompact.bddAbove_image hF'.norm.continuousOn
  let B : ℝ := max M 0 + 1
  have hbound :
      ∀ y ∈ ball x₀ 1, ∀ t ∈ uIcc a b,
        ‖F' y t‖ ≤ B := by
    intro y hy t ht
    have hleM : ‖F' y t‖ ≤ M := by
      apply hM
      exact
        ⟨(y, t),
          ⟨Metric.ball_subset_closedBall hy, ht⟩, rfl⟩
    exact hleM.trans
      ((le_max_left M 0).trans (le_add_of_nonneg_right zero_le_one))
  have hF_meas :
      ∀ᶠ y in 𝓝 x₀,
        AEStronglyMeasurable (F y)
          (volume.restrict (Ι a b)) := by
    filter_upwards [] with y
    have hslice : Continuous (F y) := by
      have hy : Continuous (fun t : ℝ ↦ (y, t)) :=
        continuous_const.prodMk continuous_id
      simpa [Function.comp_def, Function.uncurry_apply_pair] using
        hF.comp hy
    exact hslice.aestronglyMeasurable
  have hF_integrable :
      IntervalIntegrable (F x₀) volume a b :=
    intervalIntegrable_of_continuous_uncurry F hF x₀ a b
  have hF'_meas :
      AEStronglyMeasurable (F' x₀)
        (volume.restrict (Ι a b)) := by
    have hslice : Continuous (F' x₀) := by
      have hx : Continuous (fun t : ℝ ↦ (x₀, t)) :=
        continuous_const.prodMk continuous_id
      simpa [Function.comp_def, Function.uncurry_apply_pair] using
        hF'.comp hx
    exact hslice.aestronglyMeasurable
  have hbound_ae :
      ∀ᵐ t ∂volume, t ∈ Ι a b →
        ∀ y ∈ ball x₀ 1, ‖F' y t‖ ≤ B := by
    filter_upwards [] with t ht
    intro y hy
    exact hbound y hy t (uIoc_subset_uIcc ht)
  have hB_integrable :
      IntervalIntegrable (fun _ : ℝ ↦ B) volume a b :=
    intervalIntegrable_const
  have hdiff_ae :
      ∀ᵐ t ∂volume, t ∈ Ι a b →
        ∀ y ∈ ball x₀ 1,
          HasFDerivAt (fun z : E ↦ F z t) (F' y t) y := by
    filter_upwards [] with t _ht
    intro y _hy
    exact hderiv y t
  simpa only [D] using
    intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (ball_mem_nhds x₀ zero_lt_one)
      hF_meas hF_integrable hF'_meas hbound_ae
      hB_integrable hdiff_ae

end

end HGAS
