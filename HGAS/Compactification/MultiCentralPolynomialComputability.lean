import HGAS.Compactification.MultiCentralPolynomialField
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Effectivity of multi-block central compactification

All maps in the central compactification compiler operate on finite raw
sparse syntax.  This module verifies the corresponding recursion-theoretic
claim: for every fixed finite block layout and clearing degree, both
termwise denominator clearing and assembly of the complete tangent field
are primitive recursive, hence computable.

The block layout is fixed at compile time, exactly as it is in the
fixed-resource reduction.  No semantic polynomial equality, root choice,
or real-number operation occurs in these programs.
-/

namespace HGAS

namespace MultiCentralPolynomialCode

variable {n k : ℕ}

private theorem natListSum_primrec :
    Primrec (fun l : List ℕ ↦ l.sum) := by
  have hstep :
      Primrec₂
        (fun (_ : List ℕ) (p : ℕ × ℕ) ↦ p.1 + p.2) :=
    Primrec.nat_add.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.list_foldr Primrec.id (Primrec.const 0) hstep).of_eq
      fun _ ↦ rfl

/-- Block degree is primitive recursive in the exponent vector for every
fixed block. -/
theorem blockDegree_primrec
    (sourceBlock : Fin n → Fin k) (b : Fin k) :
    Primrec (fun e : ExponentCode n ↦
      blockDegree sourceBlock e b) := by
  have hlist :
      Primrec
        (fun e : ExponentCode n ↦
          List.ofFn fun j : Fin n ↦
            if sourceBlock j = b then e j else 0) :=
    Primrec.list_ofFn fun j ↦ by
      by_cases hj : sourceBlock j = b
      · exact
          (Primrec.fin_app.comp Primrec.id
            (Primrec.const j)).of_eq fun e ↦ by simp [hj]
      · exact
          (Primrec.const 0).of_eq fun e ↦ by simp [hj]
  exact
    (natListSum_primrec.comp hlist).of_eq fun e ↦ by
      simp [blockDegree, List.sum_ofFn]

/-- The lifted exponent is primitive recursive for fixed layout and
clearing degree. -/
theorem liftExponent_primrec
    (sourceBlock : Fin n → Fin k) (M : ℕ) :
    Primrec (liftExponent sourceBlock M :
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
            change e j = liftExponent sourceBlock M e q
            rw [liftExponent, hq]
  | inr b =>
      exact
        (Primrec.nat_sub.comp
          (Primrec.const M)
          (blockDegree_primrec sourceBlock b)).of_eq fun e ↦ by
            rw [liftExponent, hq]

/-- One lifted sparse term is primitive recursive. -/
theorem liftTerm_primrec
    (sourceBlock : Fin n → Fin k) (M : ℕ) :
    Primrec (liftTerm sourceBlock M :
      (ExponentCode n × RationalCode) →
        ExponentCode (n + k) × RationalCode) := by
  exact
    (Primrec.pair
      ((liftExponent_primrec sourceBlock M).comp Primrec.fst)
      Primrec.snd).of_eq fun _ ↦ rfl

/-- Simultaneous multi-block denominator clearing is primitive recursive. -/
theorem homogenize_primrec
    (sourceBlock : Fin n → Fin k) (M : ℕ) :
    Primrec (homogenize sourceBlock M :
      PolynomialCode n → PolynomialCode (n + k)) := by
  exact
    (Primrec.list_map Primrec.id
      ((liftTerm_primrec sourceBlock M).comp₂
        Primrec₂.right)).of_eq fun _ ↦ rfl

theorem homogenize_computable
    (sourceBlock : Fin n → Fin k) (M : ℕ) :
    Computable (homogenize sourceBlock M :
      PolynomialCode n → PolynomialCode (n + k)) :=
  (homogenize_primrec sourceBlock M).to_comp

/-- The coded block dot product is primitive recursive in the source
field code. -/
theorem blockDotCode_primrec
    (sourceBlock : Fin n → Fin k) (M : ℕ) (b : Fin k) :
    Primrec (fun P : PolynomialFieldCode n ↦
      blockDotCode sourceBlock M P b) := by
  apply PolynomialCode.sumCodes_primrec.comp
  apply Primrec.list_ofFn
  intro j
  by_cases hj : sourceBlock j = b
  · exact
      (PolynomialCode.mul_primrec.comp
        (Primrec.const
          (PolynomialCode.varCode (xIndex (k := k) j)))
        ((homogenize_primrec sourceBlock M).comp
          (Primrec.fin_app.comp Primrec.id
            (Primrec.const j)))).of_eq fun P ↦ by
              simp [hj]
  · exact
      (Primrec.const PolynomialCode.zero).of_eq fun P ↦ by
        simp [hj]

/-- One old-coordinate compactification equation is primitive recursive in
the source field code. -/
theorem xFieldCode_primrec
    (sourceBlock : Fin n → Fin k) (M : ℕ) (j : Fin n) :
    Primrec (fun P : PolynomialFieldCode n ↦
      xFieldCode sourceBlock M P j) := by
  let b := sourceBlock j
  have hPj :
      Primrec (fun P : PolynomialFieldCode n ↦
        homogenize sourceBlock M (P j)) :=
    (homogenize_primrec sourceBlock M).comp
      (Primrec.fin_app.comp Primrec.id (Primrec.const j))
  have hdot :
      Primrec (fun P : PolynomialFieldCode n ↦
        blockDotCode sourceBlock M P b) :=
    blockDotCode_primrec sourceBlock M b
  exact
    (PolynomialCode.mul_primrec.comp
      (Primrec.const
        (PolynomialCode.varCode (wIndex (n := n) b)))
      (PolynomialCode.sub_primrec.comp
        hPj
        (PolynomialCode.mul_primrec.comp
          (Primrec.const
            (PolynomialCode.varCode (xIndex (k := k) j)))
          hdot))).of_eq fun _ ↦ rfl

/-- One chart-coordinate compactification equation is primitive recursive
in the source field code. -/
theorem wFieldCode_primrec
    (sourceBlock : Fin n → Fin k) (M : ℕ) (b : Fin k) :
    Primrec (fun P : PolynomialFieldCode n ↦
      wFieldCode sourceBlock M P b) := by
  exact
    (PolynomialCode.neg_primrec.comp
      (PolynomialCode.mul_primrec.comp
        (Primrec.const
          (PolynomialCode.pow
            (PolynomialCode.varCode (wIndex (n := n) b)) 2))
        (blockDotCode_primrec sourceBlock M b))).of_eq
          fun _ ↦ rfl

/-- **Effective multi-block central field compiler.** -/
theorem fieldCode_primrec
    (sourceBlock : Fin n → Fin k) (M : ℕ) :
    Primrec (fieldCode sourceBlock M :
      PolynomialFieldCode n →
        PolynomialFieldCode (n + k)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro q
  cases hq : finSumFinEquiv.symm q with
  | inl j =>
      exact
        (xFieldCode_primrec sourceBlock M j).of_eq fun P ↦ by
          rw [fieldCode, hq]
  | inr b =>
      exact
        (wFieldCode_primrec sourceBlock M b).of_eq fun P ↦ by
          rw [fieldCode, hq]

theorem fieldCode_computable
    (sourceBlock : Fin n → Fin k) (M : ℕ) :
    Computable (fieldCode sourceBlock M :
      PolynomialFieldCode n →
        PolynomialFieldCode (n + k)) :=
  (fieldCode_primrec sourceBlock M).to_comp

end MultiCentralPolynomialCode

end HGAS
