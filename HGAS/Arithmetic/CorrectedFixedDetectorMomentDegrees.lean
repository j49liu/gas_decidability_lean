import HGAS.Arithmetic.CorrectedFixedDetectorMomentCode
import HGAS.Arithmetic.FixedDetectorMomentDegrees
import Mathlib.Tactic

/-!
# Degree ledger for the corrected selector moments

The correction in `CorrectedFixedDetectorMomentCode` changes only a
rational constant:

```text
  1/256  ↦  if linearCharacter I j = 0 then 1/128 else 1/256.
```

A constant has degree zero, independently of how it was selected from
the finite input table.  Consequently the original common degree ledger
is still valid verbatim.  This module records that fact for the corrected
compiler, without altering the original files.
-/

namespace HGAS.CorrectedFixedDetectorMomentCode

open HGAS
open HGAS.Clocks.ControllerPhaseProductCharacterCode

variable {eqs vars : ℕ}

/-- The correction does not alter the character-energy ledger. -/
abbrev momentCharacterEnergySum
    (I : DQLSystem eqs vars) : ℕ :=
  FixedDetectorMomentCode.momentCharacterEnergySum I

/-- The correction does not alter the common selector degree bound. -/
abbrev momentDegree
    (I : DQLSystem eqs vars) : ℕ :=
  FixedDetectorMomentCode.momentDegree I

private theorem jacobiPlus_energy_le_sum
    (I : DQLSystem eqs vars) (j : Fin vars) :
    exponentEnergy (FixedDetectorMomentCode.jacobiPlusExponent I j) ≤
      momentCharacterEnergySum I := by
  unfold momentCharacterEnergySum
  unfold FixedDetectorMomentCode.momentCharacterEnergySum
  apply le_trans
    (show
      exponentEnergy (FixedDetectorMomentCode.jacobiPlusExponent I j) ≤
        exponentEnergy
            (FixedDetectorMomentCode.unaryFirstHarmonicExponent
              (eqs := eqs) j) +
          exponentEnergy
            (FixedDetectorMomentCode.rootHalfExponent
              (eqs := eqs) j) +
          exponentEnergy
            (FixedDetectorMomentCode.jacobiPlusExponent I j) +
          exponentEnergy
            (FixedDetectorMomentCode.jacobiMinusExponent I j) by
      omega)
  exact
    Finset.single_le_sum
      (fun i _ ↦ Nat.zero_le
        (exponentEnergy
            (FixedDetectorMomentCode.unaryFirstHarmonicExponent
              (eqs := eqs) i) +
          exponentEnergy
            (FixedDetectorMomentCode.rootHalfExponent
              (eqs := eqs) i) +
          exponentEnergy
            (FixedDetectorMomentCode.jacobiPlusExponent I i) +
          exponentEnergy
            (FixedDetectorMomentCode.jacobiMinusExponent I i)))
      (Finset.mem_univ j)

private theorem jacobiMinus_energy_le_sum
    (I : DQLSystem eqs vars) (j : Fin vars) :
    exponentEnergy (FixedDetectorMomentCode.jacobiMinusExponent I j) ≤
      momentCharacterEnergySum I := by
  unfold momentCharacterEnergySum
  unfold FixedDetectorMomentCode.momentCharacterEnergySum
  apply le_trans
    (show
      exponentEnergy (FixedDetectorMomentCode.jacobiMinusExponent I j) ≤
        exponentEnergy
            (FixedDetectorMomentCode.unaryFirstHarmonicExponent
              (eqs := eqs) j) +
          exponentEnergy
            (FixedDetectorMomentCode.rootHalfExponent
              (eqs := eqs) j) +
          exponentEnergy
            (FixedDetectorMomentCode.jacobiPlusExponent I j) +
          exponentEnergy
            (FixedDetectorMomentCode.jacobiMinusExponent I j) by
      omega)
  exact
    Finset.single_le_sum
      (fun i _ ↦ Nat.zero_le
        (exponentEnergy
            (FixedDetectorMomentCode.unaryFirstHarmonicExponent
              (eqs := eqs) i) +
          exponentEnergy
            (FixedDetectorMomentCode.rootHalfExponent
              (eqs := eqs) i) +
          exponentEnergy
            (FixedDetectorMomentCode.jacobiPlusExponent I i) +
          exponentEnergy
            (FixedDetectorMomentCode.jacobiMinusExponent I i)))
      (Finset.mem_univ j)

/-- The corrected positive Jacobi moment has the original degree bound.
The conditional center remains a degree-zero rational pair. -/
theorem jacobiPlusMeanCode_termsDegreeLE
    (I : DQLSystem eqs vars) (j : Fin vars) :
    TermsDegreeLE (momentDegree I)
      (jacobiPlusMeanCode I j) := by
  have hproduct :=
    termsDegreeLE_mul
      (FixedDetectorMomentCode.thetaOutputPair_termsDegreeLE
        (eqs := eqs) j)
      (FixedDetectorMomentCode.controllerCharacterPair_termsDegreeLE
        (FixedDetectorMomentCode.jacobiPlusExponent I j))
  have h :=
    FixedDetectorMomentCode.subPair_termsDegreeLE hproduct
      (FixedDetectorMomentCode.rationalPair_termsDegreeLE
        (eqs := eqs) (vars := vars)
        (2 + exponentEnergy
          (FixedDetectorMomentCode.jacobiPlusExponent I j))
        (CorrectedJacobiSelectorCentering.selectorCenter I j))
  exact FixedDetectorMomentCode.termsDegreeLE_promote h (by
    unfold momentDegree FixedDetectorMomentCode.momentDegree
    have := jacobiPlus_energy_le_sum I j
    dsimp only [momentCharacterEnergySum] at this
    omega)

/-- The corrected negative Jacobi moment has the original degree bound. -/
theorem jacobiMinusMeanCode_termsDegreeLE
    (I : DQLSystem eqs vars) (j : Fin vars) :
    TermsDegreeLE (momentDegree I)
      (jacobiMinusMeanCode I j) := by
  have hproduct :=
    termsDegreeLE_mul
      (FixedDetectorMomentCode.thetaOutputPair_termsDegreeLE
        (eqs := eqs) j)
      (FixedDetectorMomentCode.controllerCharacterPair_termsDegreeLE
        (FixedDetectorMomentCode.jacobiMinusExponent I j))
  have h :=
    FixedDetectorMomentCode.subPair_termsDegreeLE hproduct
      (FixedDetectorMomentCode.rationalPair_termsDegreeLE
        (eqs := eqs) (vars := vars)
        (2 + exponentEnergy
          (FixedDetectorMomentCode.jacobiMinusExponent I j))
        (CorrectedJacobiSelectorCentering.selectorCenter I j))
  exact FixedDetectorMomentCode.termsDegreeLE_promote h (by
    unfold momentDegree FixedDetectorMomentCode.momentDegree
    have := jacobiMinus_energy_le_sum I j
    dsimp only [momentCharacterEnergySum] at this
    omega)

/-- The common bound holds for all seven corrected moments. -/
theorem localMomentCode_termsDegreeLE
    (I : DQLSystem eqs vars) (j : Fin vars)
    (m : Fin localMomentCount) :
    TermsDegreeLE (momentDegree I)
      (localMomentCode I j m) := by
  fin_cases m
  · simpa [localMomentCode] using
      FixedDetectorMomentCode.unaryMeanCode_termsDegreeLE I j
  · simpa [localMomentCode] using
      FixedDetectorMomentCode.unaryFirstHarmonicCode_termsDegreeLE I j
  · simpa [localMomentCode] using
      FixedDetectorMomentCode.rootP4MeanCode_termsDegreeLE I j
  · simpa [localMomentCode] using
      FixedDetectorMomentCode.rootP2MeanCode_termsDegreeLE I j
  · simpa [localMomentCode] using
      FixedDetectorMomentCode.jacobiMeanCode_termsDegreeLE I j
  · simpa [localMomentCode] using
      jacobiPlusMeanCode_termsDegreeLE I j
  · simpa [localMomentCode] using
      jacobiMinusMeanCode_termsDegreeLE I j

/-- Uniform complex-pair bound after flattening by variable and moment. -/
theorem momentCode_termsDegreeLE
    (I : DQLSystem eqs vars)
    (k : Fin (momentCount vars)) :
    TermsDegreeLE (momentDegree I)
      (momentCode I k) := by
  exact
    localMomentCode_termsDegreeLE I
      (finProdFinEquiv.symm k).1
      (finProdFinEquiv.symm k).2

/-- Uniform degree bound for every corrected realified moment coordinate. -/
theorem scalarMomentCode_termsDegreeLE
    (I : DQLSystem eqs vars)
    (k : Fin (scalarMomentCount vars)) :
    PolynomialCode.TermsDegreeLE (momentDegree I)
      (scalarMomentCode I k) := by
  let mc := finProdFinEquiv.symm k
  have h := momentCode_termsDegreeLE I mc.1
  change
    PolynomialCode.TermsDegreeLE (momentDegree I)
      (![(momentCode I mc.1).1,
        (momentCode I mc.1).2] mc.2)
  have hk : mc.2 = 0 ∨ mc.2 = 1 := by omega
  rcases hk with hzero | hone
  · rw [hzero]
    exact h.1
  · rw [hone]
    exact h.2

end HGAS.CorrectedFixedDetectorMomentCode
