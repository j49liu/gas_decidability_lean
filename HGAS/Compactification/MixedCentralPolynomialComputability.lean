import HGAS.Compactification.MixedCentralPolynomialField
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Effectivity of the mixed central compiler

For a fixed finite mixed layout and clearing degree, every operation in
the paper-exact compiler is primitive recursive.  In particular, the
compiler does not decide semantic polynomial equality and does not
perform division or any real-number operation.  It only maps and combines
finite lists of natural exponents and rational coefficient codes.
-/

namespace HGAS

namespace MixedCentralPolynomialCode

variable {n k l : ℕ}

private theorem natListSum_primrec :
    Primrec (fun xs : List ℕ ↦ xs.sum) := by
  have hstep :
      Primrec₂ (fun (_ : List ℕ) (p : ℕ × ℕ) ↦ p.1 + p.2) :=
    Primrec.nat_add.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.list_foldr Primrec.id (Primrec.const 0) hstep).of_eq
      fun _ ↦ rfl

/-- Affine block degree is primitive recursive in the exponent vector
for every fixed mixed layout and affine block. -/
theorem affineBlockDegree_primrec
    (layout : Fin n → Fin k ⊕ Fin l) (b : Fin k) :
    Primrec (fun e : ExponentCode n ↦
      affineBlockDegree layout e b) := by
  have hlist :
      Primrec
        (fun e : ExponentCode n ↦
          List.ofFn fun j : Fin n ↦
            if layout j = Sum.inl b then e j else 0) :=
    Primrec.list_ofFn fun j ↦ by
      by_cases hj : layout j = Sum.inl b
      · exact
          (Primrec.fin_app.comp Primrec.id
            (Primrec.const j)).of_eq fun e ↦ by simp [hj]
      · exact
          (Primrec.const 0).of_eq fun e ↦ by simp [hj]
  exact
    (natListSum_primrec.comp hlist).of_eq fun e ↦ by
      simp [affineBlockDegree, List.sum_ofFn]

/-- The mixed lifted exponent is primitive recursive. -/
theorem liftExponent_primrec
    (layout : Fin n → Fin k ⊕ Fin l) (M : ℕ) :
    Primrec (liftExponent layout M :
      ExponentCode n → ExponentCode (n + k)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro q
  cases hq : finSumFinEquiv.symm q with
  | inl j =>
      exact
        (Primrec.fin_app.comp Primrec.id
          (Primrec.const j)).of_eq fun e ↦ by
            change e j = liftExponent layout M e q
            rw [liftExponent, hq]
  | inr b =>
      exact
        (Primrec.nat_sub.comp
          (Primrec.const M)
          (affineBlockDegree_primrec layout b)).of_eq fun e ↦ by
            rw [liftExponent, hq]

/-- One lifted mixed sparse term is primitive recursive. -/
theorem liftTerm_primrec
    (layout : Fin n → Fin k ⊕ Fin l) (M : ℕ) :
    Primrec (liftTerm layout M :
      (ExponentCode n × RationalCode) →
        ExponentCode (n + k) × RationalCode) := by
  exact
    (Primrec.pair
      ((liftExponent_primrec layout M).comp Primrec.fst)
      Primrec.snd).of_eq fun _ ↦ rfl

/-- Mixed denominator clearing is primitive recursive. -/
theorem homogenize_primrec
    (layout : Fin n → Fin k ⊕ Fin l) (M : ℕ) :
    Primrec (homogenize layout M :
      PolynomialCode n → PolynomialCode (n + k)) := by
  exact
    (Primrec.list_map Primrec.id
      ((liftTerm_primrec layout M).comp₂
        Primrec₂.right)).of_eq fun _ ↦ rfl

theorem homogenize_computable
    (layout : Fin n → Fin k ⊕ Fin l) (M : ℕ) :
    Computable (homogenize layout M :
      PolynomialCode n → PolynomialCode (n + k)) :=
  (homogenize_primrec layout M).to_comp

/-- The coded affine dot product is primitive recursive in the source
field code. -/
theorem affineBlockDotCode_primrec
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (b : Fin k) :
    Primrec (fun P : PolynomialFieldCode n ↦
      affineBlockDotCode layout M P b) := by
  apply PolynomialCode.sumCodes_primrec.comp
  apply Primrec.list_ofFn
  intro j
  by_cases hj : layout j = Sum.inl b
  · exact
      (PolynomialCode.mul_primrec.comp
        (Primrec.const
          (PolynomialCode.varCode (xIndex (k := k) j)))
        ((homogenize_primrec layout M).comp
          (Primrec.fin_app.comp Primrec.id
            (Primrec.const j)))).of_eq fun P ↦ by
              simp [hj]
  · exact
      (Primrec.const PolynomialCode.zero).of_eq fun P ↦ by
        simp [hj]

/-- One old-coordinate mixed equation is primitive recursive in the
source field code. -/
theorem xFieldCode_primrec
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (j : Fin n) :
    Primrec (fun P : PolynomialFieldCode n ↦
      xFieldCode layout M P j) := by
  cases hj : layout j with
  | inl b =>
      have hPj :
          Primrec (fun P : PolynomialFieldCode n ↦
            homogenize layout M (P j)) :=
        (homogenize_primrec layout M).comp
          (Primrec.fin_app.comp Primrec.id (Primrec.const j))
      have hdot :
          Primrec (fun P : PolynomialFieldCode n ↦
            affineBlockDotCode layout M P b) :=
        affineBlockDotCode_primrec layout M b
      exact
        (PolynomialCode.mul_primrec.comp
          (Primrec.const
            (PolynomialCode.varCode (wIndex (n := n) b)))
          (PolynomialCode.sub_primrec.comp
            hPj
            (PolynomialCode.mul_primrec.comp
              (Primrec.const
                (PolynomialCode.varCode (xIndex (k := k) j)))
              hdot))).of_eq fun P ↦ by
                rw [xFieldCode, hj]
  | inr c =>
      exact
        ((homogenize_primrec layout M).comp
          (Primrec.fin_app.comp Primrec.id
            (Primrec.const j))).of_eq fun P ↦ by
              simp [xFieldCode, hj]

/-- One new chart-coordinate equation is primitive recursive. -/
theorem wFieldCode_primrec
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (b : Fin k) :
    Primrec (fun P : PolynomialFieldCode n ↦
      wFieldCode layout M P b) := by
  exact
    (PolynomialCode.neg_primrec.comp
      (PolynomialCode.mul_primrec.comp
        (Primrec.const
          (PolynomialCode.pow
            (PolynomialCode.varCode (wIndex (n := n) b)) 2))
        (affineBlockDotCode_primrec layout M b))).of_eq
          fun _ ↦ rfl

/-- **Effective paper-exact mixed central field compiler.** -/
theorem fieldCode_primrec
    (layout : Fin n → Fin k ⊕ Fin l) (M : ℕ) :
    Primrec (fieldCode layout M :
      PolynomialFieldCode n →
        PolynomialFieldCode (n + k)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro q
  cases hq : finSumFinEquiv.symm q with
  | inl j =>
      exact
        (xFieldCode_primrec layout M j).of_eq fun P ↦ by
          rw [fieldCode, hq]
  | inr b =>
      exact
        (wFieldCode_primrec layout M b).of_eq fun P ↦ by
          rw [fieldCode, hq]

theorem fieldCode_computable
    (layout : Fin n → Fin k ⊕ Fin l) (M : ℕ) :
    Computable (fieldCode layout M :
      PolynomialFieldCode n →
        PolynomialFieldCode (n + k)) :=
  (fieldCode_primrec layout M).to_comp

end MixedCentralPolynomialCode

end HGAS
