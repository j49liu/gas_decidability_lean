import Stability.Selection.OrdinaryTimeFourierAlgebra

/-!
# Linear operations in the actual weighted Fourier norm

Finite sums obey the weighted triangle inequality. Scalar multiplication
has the exact expected norm, including a zero scalar. All coefficients
are the normalized Haar integrals used by `mFourierCoeff`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Stability.Selection

local instance linear_circleMeasure : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance linear_circleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

/-- Actual Fourier coefficients add for continuous functions. -/
theorem fourierCoeff_add
    (f g : UnitAddTorus d → ℂ) (hfc : Continuous f) (hgc : Continuous g) (a : d → ℤ) :
    UnitAddTorus.mFourierCoeff (fun x ↦ f x + g x) a =
      UnitAddTorus.mFourierCoeff f a + UnitAddTorus.mFourierCoeff g a := by
  unfold UnitAddTorus.mFourierCoeff
  simp only [smul_eq_mul, mul_add]
  exact integral_add
    (((UnitAddTorus.mFourier (-a)).continuous.mul hfc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (((UnitAddTorus.mFourier (-a)).continuous.mul hgc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

/-- Addition satisfies the weighted triangle inequality. -/
theorem exponential_fourierCoeff_add
    (f g : UnitAddTorus d → ℂ) (hfc : Continuous f) (hgc : Continuous g)
    {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hf : Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff f a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|))
    (hg : Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff g a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) :
    Summable (fun a ↦ ‖UnitAddTorus.mFourierCoeff (fun x ↦ f x + g x) a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) ∧
    (∑' a, ‖UnitAddTorus.mFourierCoeff (fun x ↦ f x + g x) a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) ≤
        (∑' a, ‖UnitAddTorus.mFourierCoeff f a‖ * ρ ^ (∑ j, |(a j : ℝ)|)) +
          ∑' a, ‖UnitAddTorus.mFourierCoeff g a‖ * ρ ^ (∑ j, |(a j : ℝ)|) := by
  have hle (a : d → ℤ) :
      ‖UnitAddTorus.mFourierCoeff (fun x ↦ f x + g x) a‖ * ρ ^ (∑ j, |(a j : ℝ)|) ≤
        ‖UnitAddTorus.mFourierCoeff f a‖ * ρ ^ (∑ j, |(a j : ℝ)|) +
          ‖UnitAddTorus.mFourierCoeff g a‖ * ρ ^ (∑ j, |(a j : ℝ)|) := by
    rw [fourierCoeff_add f g hfc hgc, ← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
  have hs := (hf.add hg).of_nonneg_of_le (fun a ↦ by positivity) hle
  exact ⟨hs, (hs.tsum_le_tsum hle (hf.add hg)).trans_eq (hf.tsum_add hg)⟩

/-- Scalar multiplication acts literally on each Haar coefficient. -/
theorem fourierCoeff_const_mul (f : UnitAddTorus d → ℂ) (c : ℂ) (a : d → ℤ) :
    UnitAddTorus.mFourierCoeff (fun x ↦ c * f x) a =
      c * UnitAddTorus.mFourierCoeff f a := by
  simpa [UnitAddTorus.mFourier_zero] using fourierCoeff_scalar_character_mul f c 0 a

/-- Scalar multiplication has its exact weighted norm, with no
continuity or nonzero-scalar hypothesis. -/
theorem exponential_fourierCoeff_const_mul
    (f : UnitAddTorus d → ℂ) (c : ℂ) (ρ : ℝ)
    (hf : Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff f a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) :
    Summable (fun a ↦ ‖UnitAddTorus.mFourierCoeff (fun x ↦ c * f x) a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) ∧
    (∑' a, ‖UnitAddTorus.mFourierCoeff (fun x ↦ c * f x) a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) =
        ‖c‖ * ∑' a, ‖UnitAddTorus.mFourierCoeff f a‖ * ρ ^ (∑ j, |(a j : ℝ)|) := by
  simp only [fourierCoeff_const_mul, norm_mul, mul_assoc]
  exact ⟨hf.mul_left ‖c‖, tsum_mul_left⟩

/-- A finite family satisfies the weighted triangle inequality,
including an empty indexing set. -/
theorem exponential_fourierCoeff_finset_sum {ι : Type*}
    (s : Finset ι) (f : ι → UnitAddTorus d → ℂ) (hfc : ∀ i, Continuous (f i))
    {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hf : ∀ i, Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff (f i) a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) :
    Summable (fun a ↦ ‖UnitAddTorus.mFourierCoeff (fun x ↦ ∑ i ∈ s, f i x) a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) ∧
    (∑' a, ‖UnitAddTorus.mFourierCoeff (fun x ↦ ∑ i ∈ s, f i x) a‖ *
      ρ ^ (∑ j, |(a j : ℝ)|)) ≤
        ∑ i ∈ s, ∑' a, ‖UnitAddTorus.mFourierCoeff (f i) a‖ * ρ ^ (∑ j, |(a j : ℝ)|) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, norm_zero] using
      (exponential_fourierCoeff_const (d := d) 0 ρ).imp_right (fun h ↦ h.le)
  | @insert i s hi ih =>
    have hs : Continuous fun x ↦ ∑ j ∈ s, f j x := by
      fun_prop
    have ha := exponential_fourierCoeff_add (f i) (fun x ↦ ∑ j ∈ s, f j x)
      (hfc i) hs hρ (hf i) ih.1
    simp only [Finset.sum_insert hi]
    exact ⟨ha.1, ha.2.trans (add_le_add le_rfl ih.2)⟩

end Stability.Selection
