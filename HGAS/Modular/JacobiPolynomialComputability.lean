import HGAS.Algebra.ComplexPolynomialComputability
import HGAS.Modular.JacobiPolynomialCode
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Effectivity of the reciprocal Jacobi compiler

The elliptic and modular chart fields are fixed finite expressions.  The
runtime inputs at this layer are only two Gaussian-rational clock
coefficients.  This file proves that forming their linear combination and
realifying it is primitive recursive (hence computable).
-/

namespace HGAS.Modular

open HGAS

namespace JacobiPolynomialCode

open ComplexPolynomialCode

/-- The fixed elliptic field is a primitive-recursive constant. -/
theorem ellipticFieldCode_primrec :
    Primrec (fun _ : Unit ↦ ellipticFieldCode) :=
  Primrec.const _

theorem ellipticFieldCode_computable :
    Computable (fun _ : Unit ↦ ellipticFieldCode) :=
  ellipticFieldCode_primrec.to_comp

/-- The fixed modular field is a primitive-recursive constant. -/
theorem modularFieldCode_primrec :
    Primrec (fun _ : Unit ↦ modularFieldCode) :=
  Primrec.const _

theorem modularFieldCode_computable :
    Computable (fun _ : Unit ↦ modularFieldCode) :=
  modularFieldCode_primrec.to_comp

/-- Assembly of the two-clock complex field is primitive recursive in both
Gaussian-rational coefficients. -/
theorem combinedFieldCode_primrec :
    Primrec₂ combinedFieldCode := by
  change Primrec
    (fun q : GaussianRationalCode × GaussianRationalCode ↦
      combinedFieldCode q.1 q.2)
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro i
  have hZ :
      Primrec
        (fun q : GaussianRationalCode × GaussianRationalCode ↦
          mulGaussian q.1 (ellipticFieldCode i)) :=
    ComplexPolynomialCode.mulGaussian_primrec.comp
      Primrec.fst (Primrec.const _)
  have hPhi :
      Primrec
        (fun q : GaussianRationalCode × GaussianRationalCode ↦
          mulGaussian q.2 (modularFieldCode i)) :=
    ComplexPolynomialCode.mulGaussian_primrec.comp
      Primrec.snd (Primrec.const _)
  exact
    (ComplexPolynomialCode.add_primrec.comp hZ hPhi).of_eq
      fun _ ↦ rfl

theorem combinedFieldCode_computable :
    Computable₂ combinedFieldCode :=
  combinedFieldCode_primrec.to_comp

/-- Complete realification of the two-clock field is primitive recursive. -/
theorem compileFieldCode_primrec :
    Primrec₂ compileFieldCode := by
  change Primrec
    (fun q : GaussianRationalCode × GaussianRationalCode ↦
      compileFieldCode q.1 q.2)
  exact
    ComplexPolynomialFieldCode.realify_primrec.comp
      combinedFieldCode_primrec

theorem compileFieldCode_computable :
    Computable₂ compileFieldCode :=
  compileFieldCode_primrec.to_comp

/-- The fixed four-residual family is primitive recursive. -/
theorem residualCode_primrec :
    Primrec residualCode :=
  Primrec.dom_finite _

theorem residualCode_computable :
    Computable residualCode :=
  residualCode_primrec.to_comp

end JacobiPolynomialCode

end HGAS.Modular
