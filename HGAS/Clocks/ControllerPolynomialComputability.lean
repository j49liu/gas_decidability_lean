import HGAS.Accumulator.PolynomialComputability
import HGAS.Clocks.ControllerPolynomialCode
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Effectivity of the controller--phase clock compiler

The sole runtime input is the rational code for the prime controller
parameter.  Every sparse-polynomial constructor used in the four equations
is primitive recursive, so the complete clock field is a literal effective
compiler.
-/

namespace HGAS.Clocks.ControllerPolynomialCode

open HGAS

theorem mismatchCode_primrec :
    Primrec mismatchCode := by
  exact
    PolynomialCode.sub_primrec.comp
      (PolynomialCode.mul_primrec.comp
        PolynomialCode.constant_primrec
        (Primrec.const (PolynomialCode.pow rCode 2)))
      (Primrec.const PolynomialCode.one)

theorem rFieldCode_primrec :
    Primrec rFieldCode := by
  exact
    PolynomialCode.neg_primrec.comp
      (PolynomialCode.mul_primrec.comp
        (Primrec.const sCode) mismatchCode_primrec)

theorem sFieldCode_primrec :
    Primrec sFieldCode := by
  exact
    PolynomialCode.mul_primrec.comp
      (Primrec.const rCode) mismatchCode_primrec

theorem cFieldCode_primrec :
    Primrec cFieldCode := by
  exact
    PolynomialCode.neg_primrec.comp
      (PolynomialCode.mul_primrec.comp
        (PolynomialCode.mul_primrec.comp
          PolynomialCode.constant_primrec
          (Primrec.const rCode))
        (Primrec.const dCode))

theorem dFieldCode_primrec :
    Primrec dFieldCode := by
  exact
    PolynomialCode.mul_primrec.comp
      (PolynomialCode.mul_primrec.comp
        PolynomialCode.constant_primrec
        (Primrec.const rCode))
      (Primrec.const cCode)

/-- The four-component field compiler is primitive recursive in `p`. -/
theorem fieldCode_primrec :
    Primrec fieldCode := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro i
  fin_cases i
  · exact rFieldCode_primrec
  · exact sFieldCode_primrec
  · exact cFieldCode_primrec
  · exact dFieldCode_primrec

theorem fieldCode_computable :
    Computable fieldCode :=
  fieldCode_primrec.to_comp

end HGAS.Clocks.ControllerPolynomialCode
