import HGAS.Dynamics.InvariantProbability
import Mathlib.Tactic

/-!
# Invariant measures annihilate nontrivial flow eigenfunctions

Let `μ` be invariant under a continuous flow `ϕ`.  If a bounded continuous
complex observable satisfies

```
                        f(ϕₜ x) = c f(x)
```

for one time `t`, then invariance gives

```
                        ∫ f dμ = c ∫ f dμ.
```

Consequently the integral is zero whenever `c ≠ 1`.

This elementary observation is the measure-theoretic core of Fourier-mode
selection.  It is often preferable to invoking a pointwise ergodic theorem:
once a classified theta/Bloch mode is known to transform by a nontrivial
character, its invariant mean vanishes directly.  The proof works for an
arbitrary invariant probability and does not assume ergodicity.
-/

namespace HGAS.Dynamics

open Filter Function MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section

variable {K : Type*}
  [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]
  {ϕ : Flow ℝ K}

/-- Integration of a bounded continuous complex observable is invariant
under every time map. -/
theorem InvariantProbabilityMeasure.integral_comp_time_complex
    (μ : InvariantProbabilityMeasure ϕ)
    (t : ℝ) (f : K →ᵇ ℂ) :
    (∫ x, f (ϕ t x) ∂(μ.measure : Measure K)) =
      ∫ x, f x ∂(μ.measure : Measure K) := by
  calc
    (∫ x, f (ϕ t x) ∂(μ.measure : Measure K)) =
        ∫ y, f y
          ∂Measure.map (ϕ t) (μ.measure : Measure K) := by
      symm
      exact integral_map
        (ϕ.continuous_toFun t).measurable.aemeasurable
        f.continuous.measurable.aestronglyMeasurable
    _ = ∫ y, f y ∂(μ.measure : Measure K) := by
      rw [μ.map_time_toMeasure t]

/-- A bounded continuous eigenfunction with a nontrivial multiplier has
zero integral against every invariant probability. -/
theorem InvariantProbabilityMeasure.integral_eigenfunction_eq_zero
    (μ : InvariantProbabilityMeasure ϕ)
    (f : K →ᵇ ℂ) (t : ℝ) (c : ℂ)
    (hc : c ≠ 1)
    (heigen : ∀ x, f (ϕ t x) = c * f x) :
    (∫ x, f x ∂(μ.measure : Measure K)) = 0 := by
  let I : ℂ := ∫ x, f x ∂(μ.measure : Measure K)
  have hinvariant :
      (∫ x, f (ϕ t x) ∂(μ.measure : Measure K)) = I := by
    exact μ.integral_comp_time_complex t f
  have hscaled :
      (∫ x, f (ϕ t x) ∂(μ.measure : Measure K)) =
        c * I := by
    calc
      (∫ x, f (ϕ t x) ∂(μ.measure : Measure K)) =
          ∫ x, c * f x ∂(μ.measure : Measure K) :=
        integral_congr_ae (Eventually.of_forall heigen)
      _ = c * I := by
        simpa only [I, smul_eq_mul] using
          (integral_smul c
            (fun x ↦ f x) :
              (∫ x, c • f x
                ∂(μ.measure : Measure K)) =
                c • ∫ x, f x
                  ∂(μ.measure : Measure K))
  have hfixed : c * I = I := hscaled.symm.trans hinvariant
  have hproduct : (c - 1) * I = 0 := by
    calc
      (c - 1) * I = c * I - I := by ring
      _ = 0 := by rw [hfixed, sub_self]
  exact (mul_eq_zero.mp hproduct).resolve_left
    (sub_ne_zero.mpr hc)

/-- Equivalent formulation with the eigenfunction multiplier written on
the right. -/
theorem InvariantProbabilityMeasure.integral_rightEigenfunction_eq_zero
    (μ : InvariantProbabilityMeasure ϕ)
    (f : K →ᵇ ℂ) (t : ℝ) (c : ℂ)
    (hc : c ≠ 1)
    (heigen : ∀ x, f (ϕ t x) = f x * c) :
    (∫ x, f x ∂(μ.measure : Measure K)) = 0 := by
  apply μ.integral_eigenfunction_eq_zero f t c hc
  intro x
  rw [heigen x, mul_comm]

end

end HGAS.Dynamics
