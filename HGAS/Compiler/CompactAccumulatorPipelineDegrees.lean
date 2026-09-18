import HGAS.Compiler.CompactAccumulatorPipelineComputability
import Mathlib.Tactic

/-!
# Raw degree ledger for the compactification--accumulator pipeline

The executable polynomial compiler keeps raw sparse lists: it does not
delete zero coefficients, merge duplicate monomials, or compute semantic
support.  Consequently, the degree statements needed by the final
homogeneous wrapper must also be proved on raw lists.

Let every source-field and drift-observable monomial have degree at most
`E`.  Mixed central denominator clearing adds at most `k*M` to a
monomial.  The tangent central field adds at most three further linear
factors.  The compact accumulator then fits in the same bound because
its drift coordinates have degree at most `E + k*M`, while the
stereographic formula adds at most two factors.  Thus the complete field
has the uniform raw bound

```
                         E + k*M + 3.
```

Independently, the reward has raw degree at most
`max 1 (2*k)`: its only nonconstant terms are the accumulator coordinate
`W` and `2 * ∏ᵦ wᵦ²`.
-/

namespace HGAS

open scoped BigOperators

namespace PolynomialCode

variable {n : ℕ}

/-- A coded rational constant has raw degree zero. -/
theorem termsDegreeLE_constant (q : RationalCode) :
    TermsDegreeLE 0 (constant q : PolynomialCode n) := by
  intro t ht
  exact (termsParityEligible_constant q t ht).1

/-- Raw degree bound for a syntactic power. -/
theorem termsDegreeLE_pow
    {E : ℕ} {p : PolynomialCode n}
    (hp : TermsDegreeLE E p) :
    ∀ r, TermsDegreeLE (E * r) (pow p r)
  | 0 => by
      simpa using (termsDegreeLE_one (n := n))
  | r + 1 => by
      rw [pow]
      have hmul :=
        termsDegreeLE_mul hp (termsDegreeLE_pow hp r)
      simpa [Nat.mul_succ, Nat.add_comm] using hmul

/-- Multiplication of a raw finite list of `E`-bounded codes has degree
at most `E` times the list length. -/
theorem termsDegreeLE_foldr_mul
    {E : ℕ} (ps : List (PolynomialCode n))
    (hp : ∀ p ∈ ps, TermsDegreeLE E p) :
    TermsDegreeLE (E * ps.length)
      (ps.foldr mul one) := by
  induction ps with
  | nil =>
      simpa using (termsDegreeLE_one (n := n))
  | cons p ps ih =>
      simp only [List.foldr_cons, List.length_cons]
      have hmul :=
        termsDegreeLE_mul
          (hp p (by simp))
          (ih (fun q hq ↦ hp q (by simp [hq])))
      simpa [Nat.mul_add, Nat.add_comm] using hmul

end PolynomialCode

namespace MixedCentralPolynomialCode

variable {n k l E : ℕ}

/-- Exact raw total degree of one mixed lifted exponent. -/
theorem totalDegree_liftExponent
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (e : ExponentCode n) :
    ExponentCode.totalDegree (liftExponent layout M e) =
      ExponentCode.totalDegree e +
        ∑ b, (M - affineBlockDegree layout e b) := by
  simp only [ExponentCode.totalDegree, List.sum_ofFn]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp [liftExponent]

/-- Mixed lifting adds at most `k*M` to the raw total degree.  This
syntactic estimate is total and therefore does not require the
denominator-clearing side condition. -/
theorem totalDegree_liftExponent_le
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (e : ExponentCode n)
    (he : ExponentCode.totalDegree e ≤ E) :
    ExponentCode.totalDegree (liftExponent layout M e) ≤
      E + k * M := by
  rw [totalDegree_liftExponent]
  have hsum :
      (∑ b : Fin k,
          (M - affineBlockDegree layout e b)) ≤
        k * M := by
    calc
      (∑ b : Fin k,
          (M - affineBlockDegree layout e b)) ≤
          ∑ _b : Fin k, M := by
            apply Finset.sum_le_sum
            intro b _
            exact Nat.sub_le M _
      _ = k * M := by simp
  exact Nat.add_le_add he hsum

/-- Raw degree bound for mixed denominator clearing. -/
theorem homogenize_termsDegreeLE
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) {p : PolynomialCode n}
    (hp : PolynomialCode.TermsDegreeLE E p) :
    PolynomialCode.TermsDegreeLE (E + k * M)
      (homogenize layout M p) := by
  intro t ht
  rw [homogenize, List.mem_map] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  exact totalDegree_liftExponent_le layout M u.1 (hp u hu)

/-- The affine block dot-product code adds one linear factor to a
cleared source equation. -/
theorem affineBlockDotCode_termsDegreeLE
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
    (b : Fin k) :
    PolynomialCode.TermsDegreeLE (E + k * M + 1)
      (affineBlockDotCode layout M P b) := by
  rw [affineBlockDotCode]
  apply PolynomialCode.termsDegreeLE_sumCodes
  intro p hp
  rw [List.mem_ofFn] at hp
  obtain ⟨j, rfl⟩ := hp
  by_cases hj : layout j = Sum.inl b
  · simp only [hj, ↓reduceIte]
    have hmul :=
      PolynomialCode.termsDegreeLE_mul
        (PolynomialCode.termsDegreeLE_varCode
          (xIndex (k := k) j))
        (homogenize_termsDegreeLE layout M (hP j))
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using hmul
  · simp only [hj, ↓reduceIte]
    exact PolynomialCode.termsDegreeLE_zero _

/-- Every old-coordinate equation emitted by mixed central
compactification has the uniform raw degree bound `E + k*M + 3`. -/
theorem xFieldCode_termsDegreeLE
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
    (j : Fin n) :
    PolynomialCode.TermsDegreeLE (E + k * M + 3)
      (xFieldCode layout M P j) := by
  cases hj : layout j with
  | inl b =>
      rw [xFieldCode, hj]
      have hhom :=
        homogenize_termsDegreeLE layout M (hP j)
      have hdot :=
        affineBlockDotCode_termsDegreeLE layout M P hP b
      have hxdot :=
        PolynomialCode.termsDegreeLE_mul
          (PolynomialCode.termsDegreeLE_varCode
            (xIndex (k := k) j))
          hdot
      have hsub :
          PolynomialCode.TermsDegreeLE
            (E + k * M + 2)
            (PolynomialCode.sub
              (homogenize layout M (P j))
              (PolynomialCode.mul
                (PolynomialCode.varCode
                  (xIndex (k := k) j))
                (affineBlockDotCode layout M P b))) :=
        PolynomialCode.termsDegreeLE_sub
          (hhom.promote (by omega))
          (hxdot.promote (by
            simp only [Nat.add_assoc]
            omega))
      have hout :=
        PolynomialCode.termsDegreeLE_mul
          (PolynomialCode.termsDegreeLE_varCode
            (wIndex (n := n) b))
          hsub
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using hout
  | inr c =>
      rw [xFieldCode, hj]
      exact
        (homogenize_termsDegreeLE
          layout M (hP j)).promote (by omega)

/-- Every new chart-coordinate equation has the same uniform bound. -/
theorem wFieldCode_termsDegreeLE
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
    (b : Fin k) :
    PolynomialCode.TermsDegreeLE (E + k * M + 3)
      (wFieldCode layout M P b) := by
  rw [wFieldCode]
  apply PolynomialCode.termsDegreeLE_neg
  have hpow :=
    PolynomialCode.termsDegreeLE_pow
      (PolynomialCode.termsDegreeLE_varCode
        (wIndex (n := n) b)) 2
  have hdot :=
    affineBlockDotCode_termsDegreeLE layout M P hP b
  have hmul := PolynomialCode.termsDegreeLE_mul hpow hdot
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using hmul

/-- Uniform raw degree ledger for the complete mixed central field. -/
theorem fieldCode_termsDegreeLE
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j)) :
    ∀ q,
      PolynomialCode.TermsDegreeLE (E + k * M + 3)
        (fieldCode layout M P q) := by
  intro q
  cases hq : finSumFinEquiv.symm q with
  | inl j =>
      rw [fieldCode, hq]
      exact xFieldCode_termsDegreeLE layout M P hP j
  | inr b =>
      rw [fieldCode, hq]
      exact wFieldCode_termsDegreeLE layout M P hP b

end MixedCentralPolynomialCode

namespace CompactAccumulatorPipelineCode

variable {n k l m E EP Eh D : ℕ}

/-- The slowed drift code has raw degree at most `E + k*M`.
Multiplication by the rational scale does not increase degree. -/
theorem slowedDriftCode_termsDegreeLE
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (κ : RationalCode)
    (h : Fin m → PolynomialCode n)
    (hh : ∀ i, PolynomialCode.TermsDegreeLE E (h i))
    (i : Fin m) :
    PolynomialCode.TermsDegreeLE (E + k * M)
      (slowedDriftCode layout M κ h i) := by
  rw [slowedDriftCode]
  have hmul :=
    PolynomialCode.termsDegreeLE_mul
      (PolynomialCode.termsDegreeLE_constant κ)
      (MixedCentralPolynomialCode.homogenize_termsDegreeLE
        layout M (hh i))
  simpa using hmul

/-- General composed field ledger.  This version separates the source
field degree `EP`, drift-observable degree `Eh`, and requested final
bound `D`, exposing precisely the three arithmetic side conditions
used by the accumulator stage. -/
theorem fieldCode_termsDegreeLE_of_bounds
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE EP (P j))
    (h : Fin m → PolynomialCode n)
    (hh : ∀ i, PolynomialCode.TermsDegreeLE Eh (h i))
    (hD : 2 ≤ D)
    (hbase : EP + k * M + 3 ≤ D)
    (hdrift : Eh + k * M ≤ D - 2) :
    ∀ q,
      PolynomialCode.TermsDegreeLE D
        (fieldCode layout M κ P h q) := by
  apply AccumulatorPolynomialCode.fieldCode_termsDegreeLE hD
  · intro q
    exact
      (MixedCentralPolynomialCode.fieldCode_termsDegreeLE
        layout M P hP q).promote hbase
  · intro i
    exact
      (slowedDriftCode_termsDegreeLE
        layout M κ h hh i).promote hdrift

/-- If the source field and all drift observables share the raw bound
`E`, the entire composed field has degree at most `E + k*M + 3`. -/
theorem fieldCode_termsDegreeLE
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
    (h : Fin m → PolynomialCode n)
    (hh : ∀ i, PolynomialCode.TermsDegreeLE E (h i)) :
    ∀ q,
      PolynomialCode.TermsDegreeLE (E + k * M + 3)
        (fieldCode layout M κ P h q) := by
  exact
    fieldCode_termsDegreeLE_of_bounds
      layout M κ P hP h hh
      (by omega) (by omega) (by omega)

/-- The raw central weight product has degree at most `2*k`. -/
theorem centralWeightProductCode_termsDegreeLE :
    PolynomialCode.TermsDegreeLE (2 * k)
      (centralWeightProductCode (n := n) (k := k)) := by
  rw [centralWeightProductCode]
  have hfold :=
    PolynomialCode.termsDegreeLE_foldr_mul
      (E := 2)
      (List.ofFn fun b : Fin k ↦
        PolynomialCode.pow
          (PolynomialCode.varCode
            (MixedCentralPolynomialCode.wIndex (n := n) b)) 2)
      (by
        intro p hp
        rw [List.mem_ofFn] at hp
        obtain ⟨b, rfl⟩ := hp
        simpa using
          (PolynomialCode.termsDegreeLE_pow
            (PolynomialCode.termsDegreeLE_varCode
              (MixedCentralPolynomialCode.wIndex
                (n := n) b)) 2))
  simpa using hfold

/-- Embedding past the accumulator variables preserves the weight
product's raw degree. -/
theorem liftedCentralWeightProductCode_termsDegreeLE :
    PolynomialCode.TermsDegreeLE (2 * k)
      (liftedCentralWeightProductCode
        (n := n) (k := k) (m := m)) := by
  exact
    AccumulatorPolynomialCode.liftBase_termsDegreeLE
      (centralWeightProductCode_termsDegreeLE
        (n := n) (k := k))

/-- Exact uniform raw bound for the emitted strict-sign reward. -/
theorem rewardCode_termsDegreeLE
    (ε : RationalCode) :
    PolynomialCode.TermsDegreeLE (max 1 (2 * k))
      (rewardCode (n := n) (k := k) (m := m) ε) := by
  rw [rewardCode]
  apply PolynomialCode.termsDegreeLE_sub
  · apply PolynomialCode.termsDegreeLE_add
    · exact
        (PolynomialCode.termsDegreeLE_varCode
          (AccumulatorPolynomialCode.wIndex (n + k) m)).promote
            (Nat.le_max_left _ _)
    · have hmul :=
        PolynomialCode.termsDegreeLE_mul
          (PolynomialCode.termsDegreeLE_constant
            (RationalCode.ofNat 2))
          (liftedCentralWeightProductCode_termsDegreeLE
            (n := n) (k := k) (m := m))
      exact hmul.promote (by
        simp)
  · apply PolynomialCode.termsDegreeLE_add
    · exact PolynomialCode.termsDegreeLE_one.promote (by omega)
    · exact
        (PolynomialCode.termsDegreeLE_constant ε).promote (by omega)

/-- A single bound for both components of the complete compiler output. -/
theorem compile_termsDegreeLE
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ)
    (input : CompilerInput n m)
    (hP :
      ∀ j,
        PolynomialCode.TermsDegreeLE E (input.1.1.2 j))
    (hh :
      ∀ i,
        PolynomialCode.TermsDegreeLE E (input.1.2 i)) :
    (∀ q,
      PolynomialCode.TermsDegreeLE
        (max (E + k * M + 3) (max 1 (2 * k)))
        ((compile layout M input).1 q)) ∧
      PolynomialCode.TermsDegreeLE
        (max (E + k * M + 3) (max 1 (2 * k)))
        (compile layout M input).2 := by
  constructor
  · intro q
    exact
      (fieldCode_termsDegreeLE
        layout M input.1.1.1 input.1.1.2 hP
          input.1.2 hh q).promote
        (Nat.le_max_left _ _)
  · exact
      (rewardCode_termsDegreeLE
        (n := n) (k := k) (m := m) input.2).promote
          (Nat.le_max_right _ _)

end CompactAccumulatorPipelineCode

end HGAS
