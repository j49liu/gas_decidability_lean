import HGAS.Analysis.LatticeSummability
import HGAS.Analysis.TorusCharacters
import HGAS.Arithmetic.PositiveConstantTerm
import Mathlib.Tactic

/-!
# Fourier expansion of the DQL detector

This module joins the combinatorial selector in
`PositiveConstantTerm.lean` to normalized Haar integration on a finite
torus.

An expanded detector term is indexed by a theta index `x ∈ ℤᴺ` and a
Poisson index `s ∈ ℤᴺ`.  Its coefficient is

```
λ ^ ∑ |xⱼ|² * η ^ ∑ |sⱼ|,
```

and its torus exponent vector consists of all private exponents
`xⱼ²-sⱼ` followed by the DQL equation exponents.  We prove:

* absolute summability for `0 ≤ λ,η < 1`;
* the exponent vector is zero exactly at a DQL witness with `s=x²`;
* normalized Haar integration of the absolutely convergent detector series
  is exactly the surviving witness series.

This is the analytic constant-term calculation behind equation (4.8).
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal

namespace HGAS

/-! Probability normalization on each unit additive circle. -/

local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs
    (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs
    (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {eqs vars : ℕ}

/-- Torus coordinates: one private phase per arithmetic variable and one
phase per DQL equation. -/
abbrev DetectorPhase (eqs vars : ℕ) :=
  Sum (Fin vars) (Fin eqs)

/-- Series indices: theta and Poisson integer vectors. -/
abbrev DetectorIndex (vars : ℕ) :=
  (Fin vars → ℤ) × (Fin vars → ℤ)

/-- The `ℓ¹` energy of a Poisson index. -/
def poissonEnergy (s : Fin vars → ℤ) : ℕ :=
  ∑ j, (s j).natAbs

/-- Fourier exponent vector of one expanded detector term. -/
def detectorExponent
    (I : DQLSystem eqs vars) (p : DetectorIndex vars) :
    DetectorPhase eqs vars → ℤ
  | Sum.inl j => privatePhaseExponent p.1 p.2 j
  | Sum.inr row => equationPhaseExponent I p.1 p.2 row

/-- All torus exponents of an expanded term vanish exactly when its theta
index is a DQL witness and its Poisson index is forced to the coordinatewise
square. -/
theorem detectorExponent_eq_zero_iff
    (I : DQLSystem eqs vars) (x s : Fin vars → ℤ) :
    detectorExponent I (x, s) = 0 ↔
      I.Satisfies x ∧ s = fun j ↦ x j ^ 2 := by
  rw [← allPhaseExponents_eq_zero_iff I x s]
  constructor
  · intro h
    constructor
    · intro j
      exact congrFun h (Sum.inl j)
    · intro row
      exact congrFun h (Sum.inr row)
  · rintro ⟨hprivate, hequation⟩
    funext phase
    cases phase with
    | inl j => exact hprivate j
    | inr row => exact hequation row

/-- Nonnegative real coefficient of one expanded detector term, regarded as
a complex scalar. -/
def detectorCoefficient
    (lambda eta : ℝ) (p : DetectorIndex vars) : ℂ :=
  ((lambda ^ integerVectorEnergy p.1 *
    eta ^ poissonEnergy p.2 : ℝ) : ℂ)

/-- Coordinatewise squaring preserves the energy used by the Poisson
factor. -/
theorem poissonEnergy_square
    (x : Fin vars → ℤ) :
    poissonEnergy (fun j ↦ x j ^ 2) = integerVectorEnergy x := by
  simp only [poissonEnergy, integerVectorEnergy, Int.natAbs_pow]

/-- The Gaussian factor is the finite product of its one-coordinate
weights. -/
theorem gaussianProduct_eq_energyPower
    (lambda : ℝ) (x : Fin vars → ℤ) :
    (∏ j, Analysis.gaussianIntWeight lambda (x j)) =
      lambda ^ integerVectorEnergy x := by
  rw [integerVectorEnergy,
    ← Finset.prod_pow_eq_pow_sum]
  rfl

/-- The geometric Poisson factor is likewise a finite product. -/
theorem geometricProduct_eq_poissonPower
    (eta : ℝ) (s : Fin vars → ℤ) :
    (∏ j, Analysis.geometricIntWeight eta (s j)) =
      eta ^ poissonEnergy s := by
  rw [poissonEnergy,
    ← Finset.prod_pow_eq_pow_sum]
  rfl

/-- The coefficient norms of the expanded detector are summable. -/
theorem summable_norm_detectorCoefficient
    {lambda eta : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) :
    Summable (fun p : DetectorIndex vars ↦
      ‖detectorCoefficient lambda eta p‖) := by
  have hx :
      Summable (fun x : Fin vars → ℤ ↦
        lambda ^ integerVectorEnergy x) := by
    apply
      (Analysis.summable_finGaussianWeight
        hlambda0 hlambda1 vars).congr
    intro x
    exact gaussianProduct_eq_energyPower lambda x
  have hs :
      Summable (fun s : Fin vars → ℤ ↦
        eta ^ poissonEnergy s) := by
    apply
      (Analysis.summable_finGeometricWeight
        heta0 heta1 vars).congr
    intro s
    exact geometricProduct_eq_poissonPower eta s
  have hproduct :
      Summable (fun p : DetectorIndex vars ↦
        lambda ^ integerVectorEnergy p.1 *
          eta ^ poissonEnergy p.2) :=
    Summable.mul_of_nonneg
      (f := fun x : Fin vars → ℤ ↦
        lambda ^ integerVectorEnergy x)
      (g := fun s : Fin vars → ℤ ↦
        eta ^ poissonEnergy s)
      hx hs
      (fun x ↦ pow_nonneg hlambda0 _)
      (fun s ↦ pow_nonneg heta0 _)
  apply hproduct.congr
  intro p
  simp only [detectorCoefficient, Complex.norm_real]
  exact
    (abs_of_nonneg
      (mul_nonneg
        (pow_nonneg hlambda0 _)
        (pow_nonneg heta0 _))).symm

/-- The absolutely convergent expanded detector. -/
def expandedDetector
    (lambda eta : ℝ) (I : DQLSystem eqs vars)
    (phase : UnitAddTorus (DetectorPhase eqs vars)) : ℂ :=
  ∑' p : DetectorIndex vars,
    Analysis.torusSeriesTerm
      (detectorCoefficient lambda eta)
      (detectorExponent I) p phase

/-- Absolute coefficient summability also gives uniform convergence and
continuity of the expanded detector on the compact phase torus. -/
theorem continuous_expandedDetector
    {lambda eta : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (I : DQLSystem eqs vars) :
    Continuous (expandedDetector lambda eta I) := by
  apply continuous_tsum
  · intro p
    exact Continuous.mul continuous_const
      (UnitAddTorus.mFourier
        (detectorExponent I p)).continuous
  · exact summable_norm_detectorCoefficient
      hlambda0 hlambda1 heta0 heta1
  · intro p phase
    exact le_of_eq
      (Analysis.norm_torusSeriesTerm
        (detectorCoefficient lambda eta)
        (detectorExponent I) p phase)

/-- Haar integration extracts the zero-exponent subseries. -/
theorem integral_expandedDetector_eq_zeroExponentSeries
    {lambda eta : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (I : DQLSystem eqs vars) :
    (∫ phase : UnitAddTorus (DetectorPhase eqs vars),
      expandedDetector lambda eta I phase) =
        ∑' p : DetectorIndex vars,
          if detectorExponent I p = 0 then
            detectorCoefficient lambda eta p else 0 := by
  exact
    Analysis.integral_tsum_torusSeriesTerm_eq_constantTerms
      (detectorCoefficient lambda eta) (detectorExponent I)
      (summable_norm_detectorCoefficient
        hlambda0 hlambda1 heta0 heta1)

/-- The constant-term series can be written directly using DQL
satisfaction and the forced equality `s=x²`. -/
theorem integral_expandedDetector_eq_selectedPairSeries
    {lambda eta : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (I : DQLSystem eqs vars) :
    (∫ phase : UnitAddTorus (DetectorPhase eqs vars),
      expandedDetector lambda eta I phase) =
        ∑' p : DetectorIndex vars,
          if I.Satisfies p.1 ∧
              p.2 = (fun j ↦ p.1 j ^ 2) then
            detectorCoefficient lambda eta p else 0 := by
  rw [integral_expandedDetector_eq_zeroExponentSeries
    hlambda0 hlambda1 heta0 heta1 I]
  apply tsum_congr
  intro p
  have hiff := detectorExponent_eq_zero_iff I p.1 p.2
  by_cases hzero : detectorExponent I p = 0
  · have hselected :
        I.Satisfies p.1 ∧ p.2 = (fun j ↦ p.1 j ^ 2) := by
      exact hiff.mp hzero
    simp [hzero, hselected]
  · have hnotSelected :
        ¬ (I.Satisfies p.1 ∧
          p.2 = (fun j ↦ p.1 j ^ 2)) := by
      intro hselected
      exact hzero (hiff.mpr hselected)
    simp [hzero, hnotSelected]

/-- The real summand obtained after constant-term selection.  It is useful
to expose this separately: the Haar integral is complex-valued, but every
surviving coefficient is in fact a nonnegative real number. -/
def selectedPairWeight
    (lambda eta : ℝ) (I : DQLSystem eqs vars)
    (p : DetectorIndex vars) : ℝ :=
  if I.Satisfies p.1 ∧
      p.2 = (fun j ↦ p.1 j ^ 2) then
    lambda ^ integerVectorEnergy p.1 *
      eta ^ poissonEnergy p.2
  else 0

/-- For parameters in `[0,1)`, the selected real series is absolutely
summable. -/
theorem summable_selectedPairWeight
    {lambda eta : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (I : DQLSystem eqs vars) :
    Summable (selectedPairWeight lambda eta I) := by
  have hmajor :
      Summable (fun p : DetectorIndex vars ↦
        lambda ^ integerVectorEnergy p.1 *
          eta ^ poissonEnergy p.2) := by
    apply
      (summable_norm_detectorCoefficient
        (vars := vars) hlambda0 hlambda1 heta0 heta1).congr
    intro p
    simp only [detectorCoefficient, Complex.norm_real]
    exact
      abs_of_nonneg
        (mul_nonneg
          (pow_nonneg hlambda0 _)
          (pow_nonneg heta0 _))
  exact Summable.of_nonneg_of_le
    (fun p ↦ by
      simp only [selectedPairWeight]
      split_ifs
      · exact mul_nonneg
          (pow_nonneg hlambda0 _)
          (pow_nonneg heta0 _)
      · exact le_rfl)
    (fun p ↦ by
      simp only [selectedPairWeight]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg
          (pow_nonneg hlambda0 _)
          (pow_nonneg heta0 _))
    hmajor

/-- The Haar integral is literally the complex embedding of the
nonnegative selected-pair sum. -/
theorem integral_expandedDetector_eq_ofReal_selectedPairSum
    {lambda eta : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (I : DQLSystem eqs vars) :
    (∫ phase : UnitAddTorus (DetectorPhase eqs vars),
      expandedDetector lambda eta I phase) =
        ((∑' p : DetectorIndex vars,
          selectedPairWeight lambda eta I p : ℝ) : ℂ) := by
  rw [integral_expandedDetector_eq_selectedPairSeries
    hlambda0 hlambda1 heta0 heta1 I]
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro p
  simp only [selectedPairWeight, detectorCoefficient]
  split_ifs <;> rfl

/-- The real part of the detector integral is strictly positive exactly
when the DQL instance has an integer solution.  This is the fully analytic,
no-cancellation form of the arithmetic detector theorem. -/
theorem integral_expandedDetector_re_pos_iff_solvable
    {lambda eta : ℝ}
    (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (I : DQLSystem eqs vars) :
    0 < (∫ phase : UnitAddTorus (DetectorPhase eqs vars),
      expandedDetector lambda eta I phase).re ↔
        I.Solvable := by
  rw [integral_expandedDetector_eq_ofReal_selectedPairSum
    hlambda0.le hlambda1 heta0.le heta1 I]
  simp only [Complex.ofReal_re]
  constructor
  · intro hpositive
    by_contra hnotsolvable
    have hzero :
        selectedPairWeight lambda eta I =
          (fun _ ↦ 0) := by
      funext p
      have hnotSelected :
          ¬ (I.Satisfies p.1 ∧
            p.2 = (fun j ↦ p.1 j ^ 2)) := by
        rintro ⟨hsatisfies, -⟩
        exact hnotsolvable ⟨p.1, hsatisfies⟩
      simp [selectedPairWeight, hnotSelected]
    rw [hzero] at hpositive
    simp at hpositive
  · rintro ⟨x, hx⟩
    let p : DetectorIndex vars :=
      (x, fun j ↦ x j ^ 2)
    have hp :
        0 < selectedPairWeight lambda eta I p := by
      simp only [selectedPairWeight, p, hx, true_and,
        ↓reduceIte, poissonEnergy_square]
      exact mul_pos
        (pow_pos hlambda0 _)
        (pow_pos heta0 _)
    exact
      (summable_selectedPairWeight
        hlambda0.le hlambda1 heta0.le heta1 I).tsum_pos
        (fun q ↦ by
          simp only [selectedPairWeight]
          split_ifs
          · exact mul_nonneg
              (pow_nonneg hlambda0.le _)
              (pow_nonneg heta0.le _)
          · exact le_rfl)
        p hp

end HGAS
