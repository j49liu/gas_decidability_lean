import HGAS.Algebra.PolynomialVariableEmbedding
import HGAS.Accumulator.PolynomialDegrees
import Mathlib.Tactic

/-!
# Separate raw degree bounds for two polynomial variable blocks

Ordinary total degree loses useful information when two polynomial systems
are coupled.  For example, a coefficient may be linear in controller
variables and multiply a degree-eight target field.  The resulting total
degree is nine, but its more informative bidegree is `(1,8)`.

For the canonical split `Fin (m+p)`, this module defines the raw left and
right degrees of an exponent and the predicate

```
  PolynomialBlockCode.TermsBidegreeLE DL DR q.
```

It means that every raw monomial of `q` has left degree at most `DL` and
right degree at most `DR`.  As elsewhere in the compiler, this is a
syntactic list predicate: duplicate monomials and zero coefficients are
retained.  The closure rules below cover constants, addition, negation,
multiplication, and the canonical left/right variable embeddings.
-/

namespace HGAS

open scoped BigOperators

namespace PolynomialBlockCode

variable {m p : ℕ}

/-- Degree contributed by variables in the left block. -/
def leftDegree (e : ExponentCode (m + p)) : ℕ :=
  ∑ i : Fin m, e (leftEmbedding (p := p) i)

/-- Degree contributed by variables in the right block. -/
def rightDegree (e : ExponentCode (m + p)) : ℕ :=
  ∑ j : Fin p, e (rightEmbedding (m := m) j)

/-- Every raw term has the indicated separate left and right degree
bounds. -/
def TermsBidegreeLE
    (DL DR : ℕ) (q : PolynomialCode (m + p)) : Prop :=
  ∀ t ∈ q, leftDegree t.1 ≤ DL ∧ rightDegree t.1 ≤ DR

instance termsBidegreeLEDecidable
    (DL DR : ℕ) (q : PolynomialCode (m + p)) :
    Decidable (TermsBidegreeLE DL DR q) := by
  unfold TermsBidegreeLE
  infer_instance

@[simp]
theorem leftDegree_zero :
    leftDegree (ExponentCode.zero : ExponentCode (m + p)) = 0 := by
  simp [leftDegree, ExponentCode.zero]

@[simp]
theorem rightDegree_zero :
    rightDegree (ExponentCode.zero : ExponentCode (m + p)) = 0 := by
  simp [rightDegree, ExponentCode.zero]

@[simp]
theorem leftDegree_add
    (a b : ExponentCode (m + p)) :
    leftDegree (ExponentCode.add a b) =
      leftDegree a + leftDegree b := by
  simp [leftDegree, ExponentCode.add, Finset.sum_add_distrib]

@[simp]
theorem rightDegree_add
    (a b : ExponentCode (m + p)) :
    rightDegree (ExponentCode.add a b) =
      rightDegree a + rightDegree b := by
  simp [rightDegree, ExponentCode.add, Finset.sum_add_distrib]

theorem leftEmbedding_ne_rightEmbedding
    (i : Fin m) (j : Fin p) :
    leftEmbedding (p := p) i ≠ rightEmbedding (m := m) j := by
  intro h
  have hh := congrArg finSumFinEquiv.symm h
  simp at hh

theorem rightEmbedding_ne_leftEmbedding
    (j : Fin p) (i : Fin m) :
    rightEmbedding (m := m) j ≠ leftEmbedding (p := p) i :=
  (leftEmbedding_ne_rightEmbedding i j).symm

@[simp]
theorem leftDegree_injectVariables_left
    (e : ExponentCode m) :
    leftDegree
        (ExponentCode.injectVariables
          (leftEmbedding (p := p)) e) =
      ExponentCode.totalDegree e := by
  simp [leftDegree, ExponentCode.totalDegree, List.sum_ofFn]

@[simp]
theorem rightDegree_injectVariables_left
    (e : ExponentCode m) :
    rightDegree
        (ExponentCode.injectVariables
          (leftEmbedding (p := p)) e) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply ExponentCode.injectVariables_eq_zero_of_not_mem_range
  rintro ⟨i, hi⟩
  exact leftEmbedding_ne_rightEmbedding i j hi

@[simp]
theorem leftDegree_injectVariables_right
    (e : ExponentCode p) :
    leftDegree
        (ExponentCode.injectVariables
          (rightEmbedding (m := m)) e) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  apply ExponentCode.injectVariables_eq_zero_of_not_mem_range
  rintro ⟨j, hj⟩
  exact rightEmbedding_ne_leftEmbedding j i hj

@[simp]
theorem rightDegree_injectVariables_right
    (e : ExponentCode p) :
    rightDegree
        (ExponentCode.injectVariables
          (rightEmbedding (m := m)) e) =
      ExponentCode.totalDegree e := by
  simp [rightDegree, ExponentCode.totalDegree, List.sum_ofFn]

theorem termsBidegreeLE_zero (DL DR : ℕ) :
    TermsBidegreeLE DL DR
      (PolynomialCode.zero : PolynomialCode (m + p)) := by
  simp [TermsBidegreeLE, PolynomialCode.zero]

theorem termsBidegreeLE_constant (q : RationalCode) :
  TermsBidegreeLE 0 0
      (PolynomialCode.constant q : PolynomialCode (m + p)) := by
  intro t ht
  change t ∈ [(ExponentCode.zero, q)] at ht
  rw [List.mem_singleton] at ht
  subst t
  simp

theorem termsBidegreeLE_one :
  TermsBidegreeLE 0 0
      (PolynomialCode.one : PolynomialCode (m + p)) := by
  intro t ht
  change t ∈ [(ExponentCode.zero, RationalCode.one)] at ht
  rw [List.mem_singleton] at ht
  subst t
  simp

theorem termsBidegreeLE_add
    {DL DR : ℕ} {q r : PolynomialCode (m + p)}
    (hq : TermsBidegreeLE DL DR q)
    (hr : TermsBidegreeLE DL DR r) :
    TermsBidegreeLE DL DR (PolynomialCode.add q r) := by
  intro t ht
  rw [PolynomialCode.add, List.mem_append] at ht
  exact ht.elim (hq t) (hr t)

theorem termsBidegreeLE_neg
    {DL DR : ℕ} {q : PolynomialCode (m + p)}
    (hq : TermsBidegreeLE DL DR q) :
    TermsBidegreeLE DL DR (PolynomialCode.neg q) := by
  intro t ht
  rw [PolynomialCode.neg, List.mem_map] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  exact hq u hu

theorem termsBidegreeLE_sub
    {DL DR : ℕ} {q r : PolynomialCode (m + p)}
    (hq : TermsBidegreeLE DL DR q)
    (hr : TermsBidegreeLE DL DR r) :
    TermsBidegreeLE DL DR (PolynomialCode.sub q r) :=
  termsBidegreeLE_add hq (termsBidegreeLE_neg hr)

theorem termsBidegreeLE_mulByTerm
    {DL₁ DR₁ DL₂ DR₂ : ℕ}
    {a : ExponentCode (m + p) × RationalCode}
    {q : PolynomialCode (m + p)}
    (ha :
      leftDegree a.1 ≤ DL₁ ∧ rightDegree a.1 ≤ DR₁)
    (hq : TermsBidegreeLE DL₂ DR₂ q) :
    TermsBidegreeLE (DL₁ + DL₂) (DR₁ + DR₂)
      (PolynomialCode.mulByTerm a q) := by
  intro t ht
  rw [PolynomialCode.mulByTerm, List.mem_map] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  simp only [PolynomialCode.mulTerm, leftDegree_add, rightDegree_add]
  exact
    ⟨Nat.add_le_add ha.1 (hq u hu).1,
      Nat.add_le_add ha.2 (hq u hu).2⟩

theorem termsBidegreeLE_mul
    {DL₁ DR₁ DL₂ DR₂ : ℕ}
    {q r : PolynomialCode (m + p)}
    (hq : TermsBidegreeLE DL₁ DR₁ q)
    (hr : TermsBidegreeLE DL₂ DR₂ r) :
    TermsBidegreeLE (DL₁ + DL₂) (DR₁ + DR₂)
      (PolynomialCode.mul q r) := by
  induction q with
  | nil =>
      exact termsBidegreeLE_zero _ _
  | cons t q ih =>
      have ht := hq t (by simp)
      have hq' : TermsBidegreeLE DL₁ DR₁ q :=
        fun u hu ↦ hq u (by simp [hu])
      change
        TermsBidegreeLE (DL₁ + DL₂) (DR₁ + DR₂)
          (PolynomialCode.mulByTerm t r ++ PolynomialCode.mul q r)
      exact termsBidegreeLE_add
        (termsBidegreeLE_mulByTerm ht hr) (ih hq')

theorem TermsBidegreeLE.promote
    {DL DR EL ER : ℕ}
    {q : PolynomialCode (m + p)}
    (hq : TermsBidegreeLE DL DR q)
    (hleft : DL ≤ EL) (hright : DR ≤ ER) :
    TermsBidegreeLE EL ER q :=
  fun t ht ↦
    ⟨(hq t ht).1.trans hleft, (hq t ht).2.trans hright⟩

/-- Putting a polynomial in the left block gives right degree zero and
preserves its ordinary raw degree as the left-degree bound. -/
theorem termsBidegreeLE_left
    {D : ℕ} {q : PolynomialCode m}
    (hq : PolynomialCode.TermsDegreeLE D q) :
    TermsBidegreeLE D 0 (left (p := p) q) := by
  intro t ht
  rw [left, PolynomialCode.injectVariables, List.mem_map] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  constructor
  · simpa [PolynomialCode.injectVariablesTerm] using hq u hu
  · simp [PolynomialCode.injectVariablesTerm]

/-- Putting a polynomial in the right block gives left degree zero and
preserves its ordinary raw degree as the right-degree bound. -/
theorem termsBidegreeLE_right
    {D : ℕ} {q : PolynomialCode p}
    (hq : PolynomialCode.TermsDegreeLE D q) :
    TermsBidegreeLE 0 D (right (m := m) q) := by
  intro t ht
  rw [right, PolynomialCode.injectVariables, List.mem_map] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  constructor
  · simp [PolynomialCode.injectVariablesTerm]
  · simpa [PolynomialCode.injectVariablesTerm] using hq u hu

end PolynomialBlockCode

end HGAS
