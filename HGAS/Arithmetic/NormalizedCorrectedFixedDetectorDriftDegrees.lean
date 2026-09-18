import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorDriftCode
import HGAS.Arithmetic.CorrectedFixedDetectorDriftDegrees
import Mathlib.Tactic

/-!
# Degree ledger for the radius-normalized corrected drift

The new radius penalties have degree four.  The previous validity bound
was already at least eight, so the complete drift retains exactly the old
common degree ledger.
-/

namespace HGAS.NormalizedCorrectedFixedDetectorDriftCode

open HGAS
open HGAS.NormalizedCorrectedFixedDetectorValidityCode

variable {eqs vars : ℕ}

abbrev driftDegree (I : DQLSystem eqs vars) : ℕ :=
  CorrectedFixedDetectorDriftCode.driftDegree I

theorem normalizedValidityDegree_le_driftDegree
    (I : DQLSystem eqs vars) :
    max (FixedDetectorValidityEnergyCode.validityDegree I) 4 ≤
      driftDegree I := by
  apply max_le
  · exact
      CorrectedFixedDetectorDriftCode.validityDegree_le_driftDegree I
  · have h4validity :
        4 ≤ FixedDetectorValidityEnergyCode.validityDegree I := by
      have h48 : 4 ≤ 8 := by omega
      exact h48.trans
        (Nat.le_max_left 8
          (max
            (FixedDetectorValidityEnergyCode.gaugeResidualEnergyDegree I)
            (FixedDetectorValidityEnergyCode.reciprocalResidualEnergyDegree I)))
    exact h4validity.trans
      (CorrectedFixedDetectorDriftCode.validityDegree_le_driftDegree I)

theorem momentDegree_le_driftDegree
    (I : DQLSystem eqs vars) :
    CorrectedFixedDetectorMomentCode.momentDegree I ≤ driftDegree I :=
  CorrectedFixedDetectorDriftCode.momentDegree_le_driftDegree I

theorem detectorDegree_le_driftDegree
    (I : DQLSystem eqs vars) :
    4 * vars + 1 ≤ driftDegree I :=
  CorrectedFixedDetectorDriftCode.detectorDegree_le_driftDegree I

theorem driftCode_validityIndex_termsDegreeLE
    (I : DQLSystem eqs vars) :
    PolynomialCode.TermsDegreeLE
      (max (FixedDetectorValidityEnergyCode.validityDegree I) 4)
      (driftCode I (validityIndex vars)) := by
  simpa [driftCode] using
    (totalNormalizedValidityEnergyCode_termsDegreeLE I)

theorem driftCode_momentIndex_termsDegreeLE
    (I : DQLSystem eqs vars)
    (k : Fin (CorrectedFixedDetectorMomentCode.scalarMomentCount vars)) :
    PolynomialCode.TermsDegreeLE
      (CorrectedFixedDetectorMomentCode.momentDegree I)
      (driftCode I (momentIndex k)) := by
  simpa [driftCode] using
    CorrectedFixedDetectorMomentCode.scalarMomentCode_termsDegreeLE I k

theorem driftCode_detectorIndex_termsDegreeLE
    (I : DQLSystem eqs vars) (b : Fin 2) :
    PolynomialCode.TermsDegreeLE (4 * vars + 1)
      (driftCode I (detectorIndex b)) := by
  have h :=
    FixedDetectorPolynomialCode.detectorCode_termsDegreeLE
      (eqs := eqs) (vars := vars)
  fin_cases b
  · simpa [driftCode] using h.1
  · simpa [driftCode] using h.2

theorem driftCode_termsDegreeLE
    (I : DQLSystem eqs vars)
    (q : Fin (driftCount vars)) :
    PolynomialCode.TermsDegreeLE (driftDegree I)
      (driftCode I q) := by
  obtain ⟨i | r, rfl⟩ := finSumFinEquiv.surjective q
  · fin_cases i
    exact
      (driftCode_validityIndex_termsDegreeLE I).promote
        (normalizedValidityDegree_le_driftDegree I)
  · obtain ⟨k | b, rfl⟩ := finSumFinEquiv.surjective r
    · exact
        (driftCode_momentIndex_termsDegreeLE I k).promote
          (momentDegree_le_driftDegree I)
    · exact
        (driftCode_detectorIndex_termsDegreeLE I b).promote
          (detectorDegree_le_driftDegree I)

end HGAS.NormalizedCorrectedFixedDetectorDriftCode
