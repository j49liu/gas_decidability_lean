import HGAS.Arithmetic.CorrectedFixedDetectorDriftCode
import HGAS.Arithmetic.CorrectedFixedDetectorMomentDegrees
import HGAS.Arithmetic.FixedDetectorDriftDegrees
import Mathlib.Tactic

/-!
# Degree ledger for the corrected complete drift

Conditional centering changes coefficients but no monomial exponent.
Therefore the corrected drift has exactly the same explicit common degree
bound as the original drift.
-/

namespace HGAS.CorrectedFixedDetectorDriftCode

open HGAS

variable {eqs vars : ℕ}

/-- The unchanged common degree ledger. -/
abbrev driftDegree (I : DQLSystem eqs vars) : ℕ :=
  FixedDetectorDriftCode.driftDegree I

theorem validityDegree_le_driftDegree
    (I : DQLSystem eqs vars) :
    FixedDetectorValidityEnergyCode.validityDegree I ≤
      driftDegree I :=
  FixedDetectorDriftCode.validityDegree_le_driftDegree I

theorem momentDegree_le_driftDegree
    (I : DQLSystem eqs vars) :
    CorrectedFixedDetectorMomentCode.momentDegree I ≤
      driftDegree I :=
  FixedDetectorDriftCode.momentDegree_le_driftDegree I

theorem detectorDegree_le_driftDegree
    (I : DQLSystem eqs vars) :
    4 * vars + 1 ≤ driftDegree I :=
  FixedDetectorDriftCode.detectorDegree_le_driftDegree I

theorem driftCode_validityIndex_termsDegreeLE
    (I : DQLSystem eqs vars) :
    PolynomialCode.TermsDegreeLE
      (FixedDetectorValidityEnergyCode.validityDegree I)
      (driftCode I (validityIndex vars)) := by
  simpa [driftCode] using
    FixedDetectorValidityEnergyCode.totalValidityEnergyCode_termsDegreeLE I

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

/-- Every corrected drift coordinate satisfies the unchanged common
bound. -/
theorem driftCode_termsDegreeLE
    (I : DQLSystem eqs vars)
    (q : Fin (driftCount vars)) :
    PolynomialCode.TermsDegreeLE (driftDegree I)
      (driftCode I q) := by
  obtain ⟨i | r, rfl⟩ := finSumFinEquiv.surjective q
  · fin_cases i
    exact
      (driftCode_validityIndex_termsDegreeLE I).promote
        (validityDegree_le_driftDegree I)
  · obtain ⟨k | b, rfl⟩ := finSumFinEquiv.surjective r
    · exact
        (driftCode_momentIndex_termsDegreeLE I k).promote
          (momentDegree_le_driftDegree I)
    · exact
        (driftCode_detectorIndex_termsDegreeLE I b).promote
          (detectorDegree_le_driftDegree I)

end HGAS.CorrectedFixedDetectorDriftCode
