import HGAS.Clocks.ControllerPolynomialCode
import HGAS.Compiler.CompactAccumulatorPipelineDegrees
import Mathlib.Tactic

/-!
# Degree ledger for a controller--phase clock block

The controller equations contain the cubic terms `p s r²` and `p r³`.
The driven phase equations are quadratic.  Hence the uniform raw degree is
three, exactly as stated in the finite-resource ledger of the proof.
-/

namespace HGAS.Clocks.ControllerPolynomialCode

open HGAS

/-- Every component of the four-coordinate clock field has raw degree at
most three. -/
theorem fieldCode_termsDegreeLE
    (p : RationalCode) :
    ∀ i, PolynomialCode.TermsDegreeLE 3
      (fieldCode p i) := by
  have hp :
      PolynomialCode.TermsDegreeLE 0
        (PolynomialCode.constant p :
          PolynomialCode dimension) :=
    PolynomialCode.termsDegreeLE_constant p
  have hr := PolynomialCode.termsDegreeLE_varCode rIndex
  have hs := PolynomialCode.termsDegreeLE_varCode sIndex
  have hc := PolynomialCode.termsDegreeLE_varCode cIndex
  have hd := PolynomialCode.termsDegreeLE_varCode dIndex
  have hr2 :
      PolynomialCode.TermsDegreeLE 2
        (PolynomialCode.pow rCode 2) := by
    simpa [rCode] using
      PolynomialCode.termsDegreeLE_pow hr 2
  have hpr2 :
      PolynomialCode.TermsDegreeLE 2
        (PolynomialCode.mul
          (PolynomialCode.constant p) (PolynomialCode.pow rCode 2)) := by
    simpa using PolynomialCode.termsDegreeLE_mul hp hr2
  have hmismatch :
      PolynomialCode.TermsDegreeLE 2 (mismatchCode p) := by
    apply PolynomialCode.termsDegreeLE_sub hpr2
    exact PolynomialCode.termsDegreeLE_one.promote (by omega)
  have hrField :
      PolynomialCode.TermsDegreeLE 3 (rFieldCode p) := by
    apply PolynomialCode.termsDegreeLE_neg
    simpa [rFieldCode] using
      PolynomialCode.termsDegreeLE_mul hs hmismatch
  have hsField :
      PolynomialCode.TermsDegreeLE 3 (sFieldCode p) := by
    simpa [sFieldCode] using
      PolynomialCode.termsDegreeLE_mul hr hmismatch
  have hpr :
      PolynomialCode.TermsDegreeLE 1
        (PolynomialCode.mul
          (PolynomialCode.constant p) rCode) := by
    simpa [rCode] using
      PolynomialCode.termsDegreeLE_mul hp hr
  have hcField :
      PolynomialCode.TermsDegreeLE 3 (cFieldCode p) := by
    apply
      (PolynomialCode.termsDegreeLE_neg
        (PolynomialCode.termsDegreeLE_mul hpr hd)).promote
    omega
  have hdField :
      PolynomialCode.TermsDegreeLE 3 (dFieldCode p) := by
    exact
      (PolynomialCode.termsDegreeLE_mul hpr hc).promote
        (by omega)
  intro i
  fin_cases i
  · exact hrField
  · exact hsField
  · exact hcField
  · exact hdField

end HGAS.Clocks.ControllerPolynomialCode
