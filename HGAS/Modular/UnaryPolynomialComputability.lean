import HGAS.Algebra.ComplexPolynomialComputability
import HGAS.Modular.UnaryPolynomialCode
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Effectivity of the unary modular polynomial compiler

The syntax in `UnaryPolynomialCode` is a genuine finite compiler.  This
file proves that attaching a Gaussian-rational clock rate, assembling the
finite vector, and splitting it into real and imaginary coordinates are
primitive-recursive operations.

The modular and root equations themselves are fixed finite expressions.
The only compiler input at this layer is the coded Gaussian-rational
clock rate.  Later compilers may obtain that rate from a clock block and
compose these theorems directly.
-/

namespace HGAS.Modular

open HGAS

namespace UnaryPolynomialCode

open ComplexPolynomialCode

/-- The fixed four-coordinate field is a primitive-recursive constant. -/
theorem modularFieldCode_primrec :
    Primrec (fun _ : Unit ↦ modularFieldCode) :=
  Primrec.const _

theorem modularFieldCode_computable :
    Computable (fun _ : Unit ↦ modularFieldCode) :=
  modularFieldCode_primrec.to_comp

/-- Scaling the unary field by a coded Gaussian-rational clock rate is
primitive recursive. -/
theorem scaledModularFieldCode_primrec :
    Primrec scaledModularFieldCode := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro i
  exact
    (ComplexPolynomialCode.mulGaussian_primrec.comp
      Primrec.id (Primrec.const (modularFieldCode i))).of_eq
      fun κ ↦ rfl

theorem scaledModularFieldCode_computable :
    Computable scaledModularFieldCode :=
  scaledModularFieldCode_primrec.to_comp

/-- Complete primitive-recursive realification of the unary field. -/
theorem compileModularFieldCode_primrec :
    Primrec compileModularFieldCode := by
  exact
    ComplexPolynomialFieldCode.realify_primrec.comp
      scaledModularFieldCode_primrec

theorem compileModularFieldCode_computable :
    Computable compileModularFieldCode :=
  compileModularFieldCode_primrec.to_comp

/-- The fixed Jacobi residual code is primitive recursive. -/
theorem jacobiResidualCode_primrec :
    Primrec (fun _ : Unit ↦ jacobiResidualCode) :=
  Primrec.const _

theorem jacobiResidualCode_computable :
    Computable (fun _ : Unit ↦ jacobiResidualCode) :=
  jacobiResidualCode_primrec.to_comp

/-! ## Root extension -/

theorem rootFieldCode_primrec :
    Primrec (fun _ : Unit ↦ rootFieldCode) :=
  Primrec.const _

theorem rootFieldCode_computable :
    Computable (fun _ : Unit ↦ rootFieldCode) :=
  rootFieldCode_primrec.to_comp

theorem scaledRootFieldCode_primrec :
    Primrec scaledRootFieldCode := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro i
  exact
    (ComplexPolynomialCode.mulGaussian_primrec.comp
      Primrec.id (Primrec.const (rootFieldCode i))).of_eq
      fun κ ↦ rfl

theorem scaledRootFieldCode_computable :
    Computable scaledRootFieldCode :=
  scaledRootFieldCode_primrec.to_comp

theorem compileRootFieldCode_primrec :
    Primrec compileRootFieldCode := by
  exact
    ComplexPolynomialFieldCode.realify_primrec.comp
      scaledRootFieldCode_primrec

theorem compileRootFieldCode_computable :
    Computable compileRootFieldCode :=
  compileRootFieldCode_primrec.to_comp

/-- The finite family `R_J,L₂,L₄,L_H,S₃` is primitive recursive. -/
theorem rootResidualCode_primrec :
    Primrec rootResidualCode :=
  Primrec.dom_finite _

theorem rootResidualCode_computable :
    Computable rootResidualCode :=
  rootResidualCode_primrec.to_comp

end UnaryPolynomialCode

namespace GaugePolynomialCode

open ComplexPolynomialCode

/-- Assembly of the two gauge equations from the coded logarithmic
coefficient is primitive recursive. -/
theorem fieldCode_primrec :
    Primrec fieldCode := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro i
  fin_cases i
  · exact
      (ComplexPolynomialCode.mulGaussian_primrec.comp
        Primrec.id
        (Primrec.const
          (ComplexPolynomialCode.var GIndex))).of_eq
        fun a ↦ rfl
  · have hclock :
        Primrec (fun a : GaussianRationalCode ↦
          ComplexPolynomialCode.mulGaussian a
            (ComplexPolynomialCode.var clockIndex)) :=
      ComplexPolynomialCode.mulGaussian_primrec.comp
        Primrec.id
        (Primrec.const
          (ComplexPolynomialCode.var clockIndex))
    exact
      (ComplexPolynomialCode.mul_primrec.comp
        (Primrec.const
          (UnaryPolynomialCode.rational 4 :
            ComplexPolynomialCode dimension))
        hclock).of_eq fun a ↦ rfl

theorem fieldCode_computable :
    Computable fieldCode :=
  fieldCode_primrec.to_comp

/-- Complete primitive-recursive real gauge compiler. -/
theorem realFieldCode_primrec :
    Primrec realFieldCode := by
  exact
    ComplexPolynomialFieldCode.realify_primrec.comp
      fieldCode_primrec

theorem realFieldCode_computable :
    Computable realFieldCode :=
  realFieldCode_primrec.to_comp

theorem residualCode_primrec :
    Primrec (fun _ : Unit ↦ residualCode) :=
  Primrec.const _

theorem residualCode_computable :
    Computable (fun _ : Unit ↦ residualCode) :=
  residualCode_primrec.to_comp

end GaugePolynomialCode

end HGAS.Modular
