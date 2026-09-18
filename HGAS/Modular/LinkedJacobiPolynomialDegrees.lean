import HGAS.Modular.JacobiPolynomialDegrees
import HGAS.Modular.LinkedJacobiPolynomialCode
import HGAS.Modular.UnaryPolynomialDegrees
import Mathlib.Tactic

/-!
# Degree bounds for the linked unary--Jacobi compiler

The unary modular field is quadratic and the reciprocal Jacobi field has
raw degree at most eight.  Injective variable transport preserves raw
degree exactly, so their block sum still has degree at most eight.

Among the ten validity residuals, the largest terms are `Y⁴` in the unary
Jacobi and third coefficient-link equations.  Consequently the complete
residual family has degree at most four.
-/

namespace HGAS.Modular

open HGAS

namespace LinkedJacobiPolynomialCode

/-- Uniform degree-eight bound for the fourteen-coordinate complex field. -/
theorem complexFieldCode_termsDegreeLE
    (κZ κPhi : GaussianRationalCode) :
    ComplexPolynomialFieldCode.TermsDegreeLE 8
      (complexFieldCode κZ κPhi) := by
  apply ComplexPolynomialBlockCode.field_termsDegreeLE
  · intro i
    exact
      (UnaryPolynomialCode.scaledModularFieldCode_termsDegreeLE
        κPhi i).promote (by omega)
  · exact
      JacobiPolynomialCode.combinedFieldCode_termsDegreeLE
        κZ κPhi

/-- The real linked compiler has the same degree-eight raw bound. -/
theorem compileFieldCode_termsDegreeLE
    (κZ κPhi : GaussianRationalCode) :
    ∀ i, PolynomialCode.TermsDegreeLE 8
      (compileFieldCode κZ κPhi i) :=
  ComplexPolynomialFieldCode.realify_termsDegreeLE
    (complexFieldCode_termsDegreeLE κZ κPhi)

/-- Every one of the ten linked residuals has raw degree at most four.
This fixed finite ledger is discharged by kernel reduction of the
constructive degree predicate. -/
theorem residualCode_termsDegreeLE
    (i : Fin 10) :
    ComplexPolynomialCode.TermsDegreeLE 4
      (residualCode i) := by
  fin_cases i <;> decide

/-- Splitting the ten complex residuals into twenty scalar real residuals
preserves the degree-four bound required by the accumulator compiler. -/
theorem realResidualCode_termsDegreeLE :
    ∀ q, PolynomialCode.TermsDegreeLE 4
      (realResidualCode q) :=
  ComplexPolynomialFamilyCode.realify_termsDegreeLE
    residualCode_termsDegreeLE

end LinkedJacobiPolynomialCode

end HGAS.Modular
