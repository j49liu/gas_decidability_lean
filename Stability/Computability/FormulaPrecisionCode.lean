import Stability.Computability.FormulaTemplate
import Stability.Simulation.FormulaPrecision

/-!
# Primitive-recursive codes for the actual common precision

The coordinate map, finite family order, and rational accuracy are fixed
compiler parameters. Only explicitly primitive-recursive constant leaves
vary with the input. Zero accuracy and empty families are included in the
algebraic identities; positivity is a separate semantic theorem.
-/

namespace Stability.FormulaTemplate

open HGAS Simulation

variable {α σ ι : Type*} {n m : ℕ}

/-- A fixed order converts a finite template family to raw error-majorant codes. -/
def errorSumCode (order : ι ≃ Fin m) (r : σ → Fin n)
    (es : ι → FormulaTemplate α σ) (x : α) : PolynomialCode n :=
  PolynomialCode.sumCodes (List.ofFn fun i ↦ (majorantsCode r (es (order.symm i)) x).2)

theorem decode_errorSumCode [Fintype ι] (order : ι ≃ Fin m) (r : σ → Fin n)
    (es : ι → FormulaTemplate α σ) (x : α) :
    PolynomialCode.decode (errorSumCode order r es x) =
      MvPolynomial.rename r (∑ i, (AbsFormula.majorants ((es i).instantiate x)).2) := by
  simp only [errorSumCode, PolynomialCode.decode_sumCodes, List.map_ofFn,
    List.sum_ofFn, Function.comp_apply, map_sum]
  have hmajorants i := congrArg Prod.snd (decode_majorantsCode r (es i) x)
  dsimp only at hmajorants
  simp only [hmajorants]
  exact Equiv.sum_comp order.symm
    (fun i ↦ MvPolynomial.rename r (AbsFormula.majorants ((es i).instantiate x)).2)

def precisionCode (order : ι ≃ Fin m) (r : σ → Fin n)
    (es : ι → FormulaTemplate α σ) (clock : σ) (ε : ℚ) (x : α) : PolynomialCode n :=
  PolynomialCode.mul
    (PolynomialCode.mul (PolynomialCode.constant (RationalCode.encode ε⁻¹))
      (PolynomialCode.add PolynomialCode.one
        (PolynomialCode.pow (PolynomialCode.varCode (r clock)) 2)))
    (PolynomialCode.add PolynomialCode.one (errorSumCode order r es x))

/-- Decoding recovers the literal polynomial precision, not a substitute bound. -/
theorem decode_precisionCode [Fintype ι] (order : ι ≃ Fin m) (r : σ → Fin n)
    (es : ι → FormulaTemplate α σ) (clock : σ) (ε : ℚ) (x : α) :
    PolynomialCode.decode (precisionCode order r es clock ε x) =
      MvPolynomial.rename r
        (AbsFormula.precisionPolynomial (fun i ↦ (es i).instantiate x) clock ε) := by
  simp [precisionCode, decode_errorSumCode, AbsFormula.precisionPolynomial,
    AbsFormula.commonErrorMajorant]

theorem errorSumCode_primrec [Primcodable α] (order : ι ≃ Fin m) (r : σ → Fin n)
    (es : ι → FormulaTemplate α σ) (he : ∀ i, PrimitiveConstants (es i)) :
    Primrec (errorSumCode order r es) := by
  apply PolynomialCode.sumCodes_primrec.comp
  apply Primrec.list_ofFn
  intro i
  exact Primrec.snd.comp (majorantsCode_primrec r _ (he _))

theorem precisionCode_primrec [Primcodable α] (order : ι ≃ Fin m) (r : σ → Fin n)
    (es : ι → FormulaTemplate α σ) (clock : σ) (ε : ℚ)
    (he : ∀ i, PrimitiveConstants (es i)) :
    Primrec (precisionCode order r es clock ε) :=
  PolynomialCode.mul_primrec.comp (Primrec.const _)
    (PolynomialCode.add_primrec.comp (Primrec.const _)
      (errorSumCode_primrec order r es he))

end Stability.FormulaTemplate
