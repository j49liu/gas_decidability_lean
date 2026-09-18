import HGAS.Dynamics.GenericUnboundedObservableDivergence
import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-!
# Compactly supported minorants of a continuous function with infinite integral

This file records the Radon-measure approximation lemma needed in the
modular-cusp argument.

Let `R : X → ℝ` be continuous and nonnegative on a locally compact,
second-countable Hausdorff space, and let `μ` be a finite Borel measure.
If

```text
                         ∫⁻ x, ofReal (R x) ∂μ = ∞,
```

then `R` admits nonnegative compactly supported continuous minorants with
arbitrarily large ordinary integral.

The proof is constructive at the level of classical analysis:

1. truncate `R` at an integer height `n`;
2. choose `n` for which the truncated integral is already large;
3. regard that truncation as the density of a finite Radon measure;
4. use inner regularity to retain a compact set carrying a large amount
   of the weighted mass;
5. use Urysohn's lemma to choose a compactly supported cutoff equal to
   one on that compact set.

Multiplying the cutoff by the truncation gives the desired minorant.
The statement is deliberately independent of modular geometry and is
therefore reusable in other noncompact equidistribution arguments.
-/

namespace HGAS.Dynamics

open Filter Function _root_.MeasureTheory Set Topology
open scoped ENNReal CompactlySupported

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- The nonnegative truncation of a real-valued observable at the
integer height `n`. -/
def continuousNonnegativeTruncation
    (R : C(X, ℝ)) (n : ℕ) : C(X, ℝ) :=
  ⟨fun x ↦ min (R x) (n : ℝ),
    R.continuous.min continuous_const⟩

@[simp]
theorem continuousNonnegativeTruncation_apply
    (R : C(X, ℝ)) (n : ℕ) (x : X) :
    continuousNonnegativeTruncation R n x =
      min (R x) (n : ℝ) :=
  rfl

/-- Nonnegative truncations increase pointwise with their integer
height. -/
theorem continuousNonnegativeTruncation_mono
    (R : C(X, ℝ)) :
    Monotone (fun n : ℕ ↦
      fun x : X ↦
        ENNReal.ofReal
          (continuousNonnegativeTruncation R n x)) := by
  intro m n hmn x
  exact ENNReal.ofReal_le_ofReal
    (min_le_min_left (R x) (by exact_mod_cast hmn))

/-- For a nonnegative observable, the supremum of its integer
truncations is the observable itself (after `ENNReal.ofReal`). -/
theorem iSup_continuousNonnegativeTruncation
    (R : C(X, ℝ)) (x : X) :
    (⨆ n : ℕ,
        ENNReal.ofReal
          (continuousNonnegativeTruncation R n x)) =
      ENNReal.ofReal (R x) := by
  apply le_antisymm
  · exact iSup_le fun n ↦
      ENNReal.ofReal_le_ofReal (min_le_left _ _)
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, R x ≤ n :=
      exists_nat_ge (R x)
    refine le_iSup_of_le n ?_
    rw [continuousNonnegativeTruncation_apply,
      min_eq_left hn]

/-- Every nonnegative integer truncation is integrable against a finite
measure. -/
theorem continuousNonnegativeTruncation_integrable
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (R : C(X, ℝ)) (hR : ∀ x, 0 ≤ R x) (n : ℕ) :
    Integrable (continuousNonnegativeTruncation R n) μ := by
  apply Integrable.of_bound
    ((continuousNonnegativeTruncation R n).continuous
      |>.aestronglyMeasurable)
    (n : ℝ)
  exact Filter.Eventually.of_forall fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact min_le_right _ _
    · exact le_min (hR x) (by positivity)

/-- Infinite lower integral is detected by one bounded integer
truncation. -/
theorem exists_truncation_lintegral_gt
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X)
    (R : C(X, ℝ))
    (hRtop :
      ∫⁻ x, ENNReal.ofReal (R x) ∂μ = ∞)
    (a : ℝ≥0∞) (ha : a < ∞) :
    ∃ n : ℕ,
      a <
        ∫⁻ x,
          ENNReal.ofReal
            (continuousNonnegativeTruncation R n x) ∂μ := by
  have hmeas (n : ℕ) :
      Measurable (fun x : X ↦
        ENNReal.ofReal
          (continuousNonnegativeTruncation R n x)) :=
    ENNReal.measurable_ofReal.comp
      (continuousNonnegativeTruncation R n).continuous.measurable
  have hsup :
      (⨆ n : ℕ,
          ∫⁻ x,
            ENNReal.ofReal
              (continuousNonnegativeTruncation R n x) ∂μ) = ∞ := by
    rw [← lintegral_iSup hmeas
      (continuousNonnegativeTruncation_mono R)]
    simp_rw [iSup_continuousNonnegativeTruncation R]
    exact hRtop
  have :
      a <
        ⨆ n : ℕ,
          ∫⁻ x,
            ENNReal.ofReal
              (continuousNonnegativeTruncation R n x) ∂μ := by
    rw [hsup]
    exact ha
  exact lt_iSup_iff.mp this

/-- **Radon--Urysohn compact-minorant lemma.**

A continuous nonnegative function with infinite lower integral against
a finite Borel measure has nonnegative compactly supported continuous
minorants of arbitrarily large ordinary integral. -/
theorem exists_compactlySupportedContinuous_minorant_integral_gt
    [MeasurableSpace X] [BorelSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (R : C(X, ℝ)) (hR : ∀ x, 0 ≤ R x)
    (hRtop :
      ∫⁻ x, ENNReal.ofReal (R x) ∂μ = ∞)
    (B : ℝ) :
    ∃ f : C_c(X, ℝ),
      (∀ x, 0 ≤ f x) ∧
      (∀ x, f x ≤ R x) ∧
      B < ∫ x, f x ∂μ := by
  by_cases hB : B < 0
  · refine ⟨0, ?_, ?_, ?_⟩
    · intro x
      simp
    · intro x
      simpa using hR x
    · simpa using hB
  · have hB0 : 0 ≤ B := le_of_not_gt hB
    let a : ℝ≥0∞ := ENNReal.ofReal (B + 1)
    have ha : a < ∞ := ENNReal.ofReal_lt_top
    obtain ⟨n, hn⟩ :=
      exists_truncation_lintegral_gt μ R hRtop a ha
    let g : C(X, ℝ) :=
      continuousNonnegativeTruncation R n
    have hg_nonneg : ∀ x, 0 ≤ g x := by
      intro x
      exact le_min (hR x) (by positivity)
    have hg_le : ∀ x, g x ≤ R x := by
      intro x
      exact min_le_left _ _
    have hg_int : Integrable g μ :=
      continuousNonnegativeTruncation_integrable μ R hR n
    let ν : Measure X :=
      μ.withDensity (fun x ↦ ENNReal.ofReal (g x))
    have hdensity_ne_top :
        (∫⁻ x, ENNReal.ofReal (g x) ∂μ) ≠ ∞ := by
      rw [← ofReal_integral_eq_lintegral_ofReal
        hg_int
        (Filter.Eventually.of_forall hg_nonneg)]
      exact ENNReal.ofReal_ne_top
    have hνfinite : IsFiniteMeasure ν :=
      isFiniteMeasure_withDensity
        hdensity_ne_top
    letI : IsFiniteMeasure ν := hνfinite
    letI : TopologicalSpace.PseudoMetrizableSpace X := inferInstance
    letI : SigmaCompactSpace X := inferInstance
    letI : Measure.Regular ν := inferInstance
    have hνuniv : a < ν Set.univ := by
      rw [withDensity_apply _ MeasurableSet.univ,
        Measure.restrict_univ]
      simpa only [ν, g] using hn
    obtain ⟨K, _hKuniv, hKcompact, hKmass⟩ :=
      MeasurableSet.univ.exists_lt_isCompact_of_ne_top
        (measure_ne_top ν Set.univ) hνuniv
    obtain ⟨χ, hχone, hχcompact, _hχsupport, hχrange⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen
        hKcompact isOpen_univ (subset_univ K)
    let f : C_c(X, ℝ) :=
      ⟨⟨fun x ↦ χ x * g x,
          χ.continuous.mul g.continuous⟩,
        (hasCompactSupport_def.mpr hχcompact).mul_right⟩
    have hf_nonneg : ∀ x, 0 ≤ f x := by
      intro x
      exact mul_nonneg (hχrange x).1 (hg_nonneg x)
    have hf_le : ∀ x, f x ≤ R x := by
      intro x
      exact
        (mul_le_of_le_one_left
          (hg_nonneg x) (hχrange x).2).trans
          (hg_le x)
    refine ⟨f, hf_nonneg, hf_le, ?_⟩
    have hνK :
        ν K =
          ∫⁻ x in K, ENNReal.ofReal (g x) ∂μ := by
      rw [withDensity_apply _ hKcompact.measurableSet]
    have hgK_int : IntegrableOn g K μ :=
      hg_int.integrableOn
    have hlintegralK :
        ENNReal.ofReal (∫ x in K, g x ∂μ) =
          ∫⁻ x in K, ENNReal.ofReal (g x) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal
        hgK_int
        (Filter.Eventually.of_forall fun x ↦ hg_nonneg x)
    have hBK :
        B + 1 < ∫ x in K, g x ∂μ := by
      apply
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
          (by linarith : 0 ≤ B + 1)).mp
      rw [hlintegralK]
      exact hνK ▸ hKmass
    have hfeqK :
        (∫ x in K, f x ∂μ) =
          ∫ x in K, g x ∂μ := by
      apply integral_congr_ae
      filter_upwards
        [ae_restrict_mem hKcompact.measurableSet] with x hx
      change χ x * g x = g x
      have hχx : χ x = 1 := by
        simpa only [Pi.one_apply] using hχone hx
      rw [hχx, one_mul]
    have hf_int : Integrable f μ :=
      f.integrable
    have hKle :
        (∫ x in K, f x ∂μ) ≤ ∫ x, f x ∂μ :=
      setIntegral_le_integral hf_int
        (Filter.Eventually.of_forall hf_nonneg)
    linarith [hBK, hfeqK, hKle]

end

end HGAS.Dynamics
