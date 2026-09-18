import HGAS.Analysis.CanonicalDetectorNoInstanceAggregatedFamily
import HGAS.Analysis.CanonicalSelectorMomentSupportedCrosswalk
import HGAS.Analysis.RealifiedTorusFourierFamily
import HGAS.Arithmetic.NormalizedCorrectedCanonicalFixedDetectorGraph
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorDriftCode
import Mathlib.Tactic

/-!
# Complete Fourier family for the normalized corrected canonical drift

This file assembles the complete real drift vector in the literal compiler
order

```text
  normalized validity | 14 selector coordinates | detector.re | detector.im.
```

There are three cases.

* The normalized validity coordinate is the zero Fourier family.  Its
  equality to the canonical polynomial coordinate is proved below using
  all three normalization facts: controller radius one, driven-phase
  radius one, and final right-hand-side oscillator radius one.
* Each adjacent selector pair is obtained by realifying one of the seven
  supported centered complex moment families.
* The last pair is the realification of the supported no-instance
  detector family.

The resulting dependent coefficient family has termwise zero mode and
both ordinary and prime-radical weighted summability.  These are exactly
the coefficient-side premises of
`RadicalTimeChangedTorusFourierComponent`.
-/

noncomputable section

open Function

namespace HGAS.Analysis.NormalizedCorrectedCanonicalDriftFourierFamily

open HGAS
open HGAS.Clocks
open HGAS.Analysis.CanonicalSelectorMomentAggregatedFamilies
open HGAS.Analysis.CanonicalSelectorMomentSupportedCrosswalk
open HGAS.Analysis.CanonicalDetectorNoInstanceAggregatedFamily

variable {eqs vars : ℕ}

abbrev driftCount (vars : ℕ) : ℕ :=
  NormalizedCorrectedFixedDetectorDriftCode.driftCount vars

/-- The nested sum label underlying the compiler's drift-coordinate
equivalence. -/
abbrev Label (vars : ℕ) :=
  Fin 1 ⊕
    (Fin (CorrectedFixedDetectorMomentCode.scalarMomentCount vars) ⊕
      Fin 2)

/-- The compiler's nested finite-sum label for one flattened coordinate. -/
def label (q : Fin (driftCount vars)) : Label vars :=
  match finSumFinEquiv.symm q with
  | Sum.inl a => Sum.inl a
  | Sum.inr r =>
      match finSumFinEquiv.symm r with
      | Sum.inl k => Sum.inr (Sum.inl k)
      | Sum.inr b => Sum.inr (Sum.inr b)

/-- Index type before transporting the nested sum label to a `Fin`
coordinate.  Separating this definition makes dependent reduction
transparent in all three cases. -/
def indexAtLabel
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable) :
    Label vars → Type
  | Sum.inl _ => Unit
  | Sum.inr (Sum.inl k) =>
      let kb := finProdFinEquiv.symm k
      (momentFamily I kb.1).SupportedIndex
  | Sum.inr (Sum.inr _) =>
      (detector I hnot).SupportedIndex

/-- The index type for each real drift coordinate. -/
def Index
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable)
    (q : Fin (driftCount vars)) : Type :=
  indexAtLabel I hnot (label q)

/-- Coefficients before transport from labels to finite coordinates. -/
def coefficientAtLabel
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable) :
    ∀ L : Label vars, indexAtLabel I hnot L → ℂ
  | Sum.inl _ => fun _ ↦ 0
  | Sum.inr (Sum.inl k) =>
      let kb := finProdFinEquiv.symm k
      realifiedCoefficient kb.2
        (momentFamily I kb.1).supportedCoefficient
  | Sum.inr (Sum.inr b) =>
      realifiedCoefficient b
        (detector I hnot).supportedCoefficient

/-- Complex coefficient family whose real parts give the complete real
drift. -/
def coefficient
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable)
    (q : Fin (driftCount vars)) :
    Index I hnot q → ℂ :=
  coefficientAtLabel I hnot (label q)

/-- Exponents before transport from labels to finite coordinates. -/
def exponentAtLabel
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable) :
    ∀ L : Label vars,
      indexAtLabel I hnot L → Fin (vars + eqs) → ℤ
  | Sum.inl _ => fun _ ↦ 0
  | Sum.inr (Sum.inl k) =>
      let kb := finProdFinEquiv.symm k
      (momentFamily I kb.1).supportedExponent
  | Sum.inr (Sum.inr _) =>
      (detector I hnot).supportedExponent

/-- Exponent family in the literal fundamental-clock coordinates
`Fin (vars + eqs)`. -/
def exponent
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable)
    (q : Fin (driftCount vars)) :
    Index I hnot q → Fin (vars + eqs) → ℤ :=
  exponentAtLabel I hnot (label q)

/-- Every supported label family has termwise zero mode. -/
theorem zeroModeAtLabel
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable) :
    ∀ L i, exponentAtLabel I hnot L i = 0 →
      coefficientAtLabel I hnot L i = 0 := by
  intro L
  rcases L with a | k | b
  · fin_cases a
    intro i hi
    rfl
  · let kb := finProdFinEquiv.symm k
    intro i hi
    exact
      realifiedCoefficient_zero_of_zero kb.2
        (momentFamily I kb.1).supportedCoefficient
        (momentFamily I kb.1).supportedExponent
        (momentFamily I kb.1).supported_zeroMode i hi
  · intro i hi
    exact
      realifiedCoefficient_zero_of_zero b
        (detector I hnot).supportedCoefficient
        (detector I hnot).supportedExponent
        (detector I hnot).supported_zeroMode i hi

/-- Every supported finite-coordinate family has termwise zero mode. -/
theorem zeroMode
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable) :
    ∀ q i, exponent I hnot q i = 0 →
      coefficient I hnot q i = 0 := by
  intro q
  exact zeroModeAtLabel I hnot (label q)

/-- Ordinary coefficient summability at every nested-sum label. -/
theorem coefficientAtLabel_summable
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable) :
    ∀ L, Summable fun i ↦
      ‖coefficientAtLabel I hnot L i‖ := by
  intro L
  rcases L with a | k | b
  · have ha : a = 0 := Subsingleton.elim _ _
    subst a
    simp only [indexAtLabel, coefficientAtLabel, norm_zero]
    change Summable (fun _ : Unit ↦ (0 : ℝ))
    exact summable_zero
  · let kb := finProdFinEquiv.symm k
    exact
      summable_norm_realifiedCoefficient kb.2
        (momentFamily I kb.1).supportedCoefficient
        ((momentFamily I kb.1).supportedCoefficient_summable
          (harmlessRadicand (eqs := eqs) (vars := vars)))
  · exact
      summable_norm_realifiedCoefficient b
        (detector I hnot).supportedCoefficient
        ((detector I hnot).supportedCoefficient_summable
          (harmlessRadicand (eqs := eqs) (vars := vars)))

/-- Ordinary coefficient summability for every real drift coordinate. -/
theorem coefficient_summable
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable) :
    ∀ q, Summable fun i ↦ ‖coefficient I hnot q i‖ := by
  intro q
  exact coefficientAtLabel_summable I hnot (label q)

/-- Prime-radical weighted summability at every nested-sum label. -/
theorem coefficientAtLabel_weighted_summable
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable)
    (radicand : Fin (vars + eqs) → ℕ)
    (heightPower : ℕ) :
    ∀ L,
      Summable fun i ↦
        ‖coefficientAtLabel I hnot L i‖ *
          RadicalSmallDivisor.radicalConjugateHeight
              radicand (exponentAtLabel I hnot L i) ^ heightPower := by
  intro L
  rcases L with a | k | b
  · have ha : a = 0 := Subsingleton.elim _ _
    subst a
    simp only [indexAtLabel, coefficientAtLabel, exponentAtLabel,
      norm_zero, zero_mul]
    change Summable (fun _ : Unit ↦ (0 : ℝ))
    exact summable_zero
  · let kb := finProdFinEquiv.symm k
    exact
      summable_norm_realifiedCoefficient_mul_weight kb.2
        (momentFamily I kb.1).supportedCoefficient
        (fun i ↦
          RadicalSmallDivisor.radicalConjugateHeight
              radicand
              ((momentFamily I kb.1).supportedExponent i) ^
            heightPower)
        ((momentFamily I kb.1).supportedCoefficient_weighted_summable
          radicand heightPower)
  · exact
      summable_norm_realifiedCoefficient_mul_weight b
        (detector I hnot).supportedCoefficient
        (fun i ↦
          RadicalSmallDivisor.radicalConjugateHeight
              radicand
              ((detector I hnot).supportedExponent i) ^
            heightPower)
        ((detector I hnot).supportedCoefficient_weighted_summable
          radicand heightPower)

/-- Prime-radical weighted summability for every real drift coordinate
and every requested height power. -/
theorem coefficient_weighted_summable
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable)
    (radicand : Fin (vars + eqs) → ℕ)
    (heightPower : ℕ) :
    ∀ q,
      Summable fun i ↦
        ‖coefficient I hnot q i‖ *
          RadicalSmallDivisor.radicalConjugateHeight
              radicand (exponent I hnot q i) ^ heightPower := by
  intro q
  exact
    coefficientAtLabel_weighted_summable
      I hnot radicand heightPower (label q)

end HGAS.Analysis.NormalizedCorrectedCanonicalDriftFourierFamily
