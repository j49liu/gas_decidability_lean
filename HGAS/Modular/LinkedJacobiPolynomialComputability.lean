import HGAS.Modular.JacobiPolynomialComputability
import HGAS.Modular.LinkedJacobiPolynomialCode
import HGAS.Modular.UnaryPolynomialComputability
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Effectivity of the linked unary--Jacobi compiler

The linked field has only two runtime inputs: the Gaussian-rational
elliptic and modular clock coefficients.  Its fourteen-coordinate complex
code is assembled by the primitive-recursive block-field constructor; its
twenty-eight-coordinate real code is then obtained by the generic
primitive-recursive realification operation.

All ten validity residuals are fixed finite expressions, so their indexed
family is primitive recursive as well.
-/

namespace HGAS.Modular

open HGAS

namespace LinkedJacobiPolynomialCode

/-- The full linked complex source compiler is primitive recursive in its
two clock codes. -/
theorem complexFieldCode_primrec :
    Primrec₂ complexFieldCode := by
  change Primrec
    (fun q : GaussianRationalCode × GaussianRationalCode ↦
      complexFieldCode q.1 q.2)
  exact
    ComplexPolynomialBlockCode.field_primrec.comp
      (UnaryPolynomialCode.scaledModularFieldCode_primrec.comp
        Primrec.snd)
      JacobiPolynomialCode.combinedFieldCode_primrec

theorem complexFieldCode_computable :
    Computable₂ complexFieldCode :=
  complexFieldCode_primrec.to_comp

/-- Realification of the linked compiler is primitive recursive. -/
theorem compileFieldCode_primrec :
    Primrec₂ compileFieldCode := by
  change Primrec
    (fun q : GaussianRationalCode × GaussianRationalCode ↦
      compileFieldCode q.1 q.2)
  exact
    ComplexPolynomialFieldCode.realify_primrec.comp
      complexFieldCode_primrec

theorem compileFieldCode_computable :
    Computable₂ compileFieldCode :=
  compileFieldCode_primrec.to_comp

/-- The fixed family of ten linked validity residuals is primitive
recursive. -/
theorem residualCode_primrec :
    Primrec residualCode :=
  Primrec.dom_finite _

theorem residualCode_computable :
    Computable residualCode :=
  residualCode_primrec.to_comp

/-- Indexed access to the twenty scalar real residual codes is primitive
recursive. -/
theorem realResidualCode_primrec :
    Primrec realResidualCode :=
  Primrec.dom_finite _

theorem realResidualCode_computable :
    Computable realResidualCode :=
  realResidualCode_primrec.to_comp

end LinkedJacobiPolynomialCode

end HGAS.Modular
