import HGAS.Algebra.ComplexPolynomialDegrees
import HGAS.Modular.JacobiPolynomialCode
import Mathlib.Tactic

/-!
# Raw degree bounds for the reciprocal Jacobi compiler

The ten-coordinate Jacobi chart has two polynomial derivations.  In the
literal sparse syntax:

* the elliptic derivation has degree at most five;
* the modular derivation has degree at most eight;
* every Gaussian-rational two-clock combination therefore has degree at
  most eight;
* realification preserves that bound; and
* the four intrinsic validity residuals have degree at most three.

The two fixed finite ledgers are discharged by evaluation of the
constructive raw-list degree decision procedure.  The parameterized clock
statement is then proved structurally, so no computation depends on the
clock coefficients.
-/

namespace HGAS.Modular

open HGAS

namespace JacobiPolynomialCode

/-- The raw elliptic chart field has degree at most five. -/
theorem ellipticFieldCode_termsDegreeLE :
    ComplexPolynomialFieldCode.TermsDegreeLE 5
      ellipticFieldCode := by
  decide

set_option maxRecDepth 10000 in
/-- The raw modular chart field has degree at most eight.  The degree-eight
term occurs in the `Delta` equation before any cancellation. -/
theorem modularFieldCode_termsDegreeLE :
    ComplexPolynomialFieldCode.TermsDegreeLE 8
      modularFieldCode := by
  decide

/-- Every Gaussian-rational two-clock combination has raw degree at most
eight. -/
theorem combinedFieldCode_termsDegreeLE
    (κZ κPhi : GaussianRationalCode) :
    ComplexPolynomialFieldCode.TermsDegreeLE 8
      (combinedFieldCode κZ κPhi) := by
  intro i
  apply ComplexPolynomialCode.termsDegreeLE_add
  · apply ComplexPolynomialCode.termsDegreeLE_mulGaussian
    exact
      (ellipticFieldCode_termsDegreeLE i).promote
        (by omega)
  · exact
      ComplexPolynomialCode.termsDegreeLE_mulGaussian κPhi
        (modularFieldCode_termsDegreeLE i)

/-- The real twenty-coordinate compiler retains the degree-eight raw
bound. -/
theorem compileFieldCode_termsDegreeLE
    (κZ κPhi : GaussianRationalCode) :
    ∀ i, PolynomialCode.TermsDegreeLE 8
      (compileFieldCode κZ κPhi i) :=
  ComplexPolynomialFieldCode.realify_termsDegreeLE
    (combinedFieldCode_termsDegreeLE κZ κPhi)

/-- Each intrinsic residual `(R₀,R₁,R₂,Rᵁ)` has raw degree at most
three. -/
theorem residualCode_termsDegreeLE
    (i : Fin 4) :
    ComplexPolynomialCode.TermsDegreeLE 3
      (residualCode i) := by
  fin_cases i <;> decide

end JacobiPolynomialCode

end HGAS.Modular
