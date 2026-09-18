import HGAS.Arithmetic.FixedDetectorDriftCode
import HGAS.Arithmetic.FixedDetectorMomentDegrees
import Mathlib.Tactic

/-!
# Degree ledger for the complete fixed-detector drift

The drift vector has three kinds of coordinates:

* the aggregate validity energy;
* the real and imaginary coordinates of the selector moments; and
* the real and imaginary coordinates of the arithmetic detector.

The first two bounds depend effectively on the finite DQL table.  The
detector itself has the coefficient-independent bound `4 * vars + 1`.
Taking the maximum of these three quantities gives one explicit degree
bound for every coordinate of the complete drift vector.
-/

namespace HGAS.FixedDetectorDriftCode

open HGAS

variable {eqs vars : ℕ}

/-- One executable total-degree bound for every coordinate of the complete
fixed-detector drift. -/
def driftDegree (I : DQLSystem eqs vars) : ℕ :=
  max (FixedDetectorValidityEnergyCode.validityDegree I)
    (max (FixedDetectorMomentCode.momentDegree I) (4 * vars + 1))

/-- The validity-coordinate bound is below the common drift bound. -/
theorem validityDegree_le_driftDegree
    (I : DQLSystem eqs vars) :
    FixedDetectorValidityEnergyCode.validityDegree I ≤
      driftDegree I :=
  Nat.le_max_left _ _

/-- The selector-moment bound is below the common drift bound. -/
theorem momentDegree_le_driftDegree
    (I : DQLSystem eqs vars) :
    FixedDetectorMomentCode.momentDegree I ≤ driftDegree I :=
  (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)

/-- The coefficient-independent detector bound is below the common drift
bound. -/
theorem detectorDegree_le_driftDegree
    (I : DQLSystem eqs vars) :
    4 * vars + 1 ≤ driftDegree I :=
  (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)

/-! ## Sharp bounds for the three coordinate blocks -/

/-- The first coordinate has exactly the previously established validity
energy bound. -/
theorem driftCode_validityIndex_termsDegreeLE
    (I : DQLSystem eqs vars) :
    PolynomialCode.TermsDegreeLE
      (FixedDetectorValidityEnergyCode.validityDegree I)
      (driftCode I (validityIndex vars)) := by
  simpa [driftCode] using
    FixedDetectorValidityEnergyCode.totalValidityEnergyCode_termsDegreeLE I

/-- Every realified selector-moment coordinate has the common moment
bound. -/
theorem driftCode_momentIndex_termsDegreeLE
    (I : DQLSystem eqs vars)
    (k : Fin (FixedDetectorMomentCode.scalarMomentCount vars)) :
    PolynomialCode.TermsDegreeLE
      (FixedDetectorMomentCode.momentDegree I)
      (driftCode I (momentIndex k)) := by
  simpa [driftCode] using
    FixedDetectorMomentCode.scalarMomentCode_termsDegreeLE I k

/-- Each of the two real detector coordinates has degree at most
`4 * vars + 1`. -/
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

/-! ## One bound for the whole vector -/

/-- Every emitted drift coordinate satisfies the single explicit bound
`driftDegree I`. -/
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

end HGAS.FixedDetectorDriftCode
