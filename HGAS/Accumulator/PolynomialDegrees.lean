import HGAS.Accumulator.PolynomialCode
import HGAS.Wrapper.SparseDegreeCalculus
import Mathlib.Tactic

/-!
# Raw degree bounds for the compact-accumulator compiler

The homogeneous wrapper requires an explicit degree bound on every source
coordinate.  This file first develops the small amount of raw-list degree
calculus needed for arbitrary (not parity-restricted) sparse codes, then
proves the accumulator ledger:

* if the base field has degree at most `D`;
* if every drift coordinate has degree at most `D-2`; and
* if `2 ≤ D`,

then every coordinate emitted by the compact-accumulator compiler has
degree at most `D`.
-/

namespace HGAS

namespace PolynomialCode

variable {n : ℕ}

/-- The raw-list degree predicate is constructively decidable.  Exposing
this instance lets fixed finite compilers discharge large degree ledgers
by kernel-checked computation, while the structural lemmas below remain
available for parameterized expressions. -/
instance termsDegreeLEDecidable
    (D : ℕ) (p : PolynomialCode n) :
    Decidable (TermsDegreeLE D p) := by
  unfold TermsDegreeLE
  infer_instance

theorem termsDegreeLE_zero (D : ℕ) :
    TermsDegreeLE D (zero : PolynomialCode n) := by
  simp [TermsDegreeLE, zero]

theorem termsDegreeLE_add
    {D : ℕ} {p q : PolynomialCode n}
    (hp : TermsDegreeLE D p)
    (hq : TermsDegreeLE D q) :
    TermsDegreeLE D (add p q) := by
  intro t ht
  rw [add, List.mem_append] at ht
  exact ht.elim (hp t) (hq t)

theorem termsDegreeLE_neg
    {D : ℕ} {p : PolynomialCode n}
    (hp : TermsDegreeLE D p) :
    TermsDegreeLE D (neg p) := by
  intro t ht
  rw [neg, List.mem_map] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  exact hp u hu

theorem termsDegreeLE_sub
    {D : ℕ} {p q : PolynomialCode n}
    (hp : TermsDegreeLE D p)
    (hq : TermsDegreeLE D q) :
    TermsDegreeLE D (sub p q) :=
  termsDegreeLE_add hp (termsDegreeLE_neg hq)

theorem termsDegreeLE_mulByTerm
    {D E : ℕ} {a : ExponentCode n × RationalCode}
    {p : PolynomialCode n}
    (ha : ExponentCode.totalDegree a.1 ≤ D)
    (hp : TermsDegreeLE E p) :
    TermsDegreeLE (D + E) (mulByTerm a p) := by
  intro t ht
  rw [mulByTerm, List.mem_map] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  simp only [mulTerm, totalDegree_exponent_add]
  exact Nat.add_le_add ha (hp u hu)

theorem termsDegreeLE_mul
    {D E : ℕ} {p q : PolynomialCode n}
    (hp : TermsDegreeLE D p)
    (hq : TermsDegreeLE E q) :
    TermsDegreeLE (D + E) (mul p q) := by
  induction p with
  | nil =>
      exact termsDegreeLE_zero (D + E)
  | cons t p ih =>
      rw [termsDegreeLE_cons_iff] at hp
      change
        TermsDegreeLE (D + E)
          (mulByTerm t q ++ mul p q)
      exact termsDegreeLE_add
        (termsDegreeLE_mulByTerm hp.1 hq)
        (ih hp.2)

theorem TermsDegreeLE.promote
    {D E : ℕ} {p : PolynomialCode n}
    (hp : TermsDegreeLE D p) (hDE : D ≤ E) :
    TermsDegreeLE E p :=
  fun t ht ↦ (hp t ht).trans hDE

theorem termsDegreeLE_sumCodes
    {D : ℕ} {ps : List (PolynomialCode n)}
    (hp : ∀ p ∈ ps, TermsDegreeLE D p) :
    TermsDegreeLE D (sumCodes ps) := by
  induction ps with
  | nil => exact termsDegreeLE_zero D
  | cons p ps ih =>
      change TermsDegreeLE D (add p (sumCodes ps))
      exact termsDegreeLE_add
        (hp p (by simp))
        (ih (fun q hq ↦ hp q (by simp [hq])))

theorem termsDegreeLE_one :
    TermsDegreeLE 0 (one : PolynomialCode n) := by
  intro t ht
  exact (termsParityEligible_one (n := n) t ht).1

theorem termsDegreeLE_varCode (i : Fin n) :
    TermsDegreeLE 1 (varCode i) := by
  intro t ht
  exact (termsParityEligible_varCode i t ht).1

end PolynomialCode

namespace ExponentCode

theorem totalDegree_dimensionEmbed
    {n p : ℕ} (e : ExponentCode n) :
    totalDegree (dimensionEmbed p e) = totalDegree e := by
  simp only [totalDegree, List.sum_ofFn]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp [dimensionEmbed]

end ExponentCode

namespace PolynomialCode

theorem termsDegreeLE_dimensionEmbed
    {n p D : ℕ} {q : PolynomialCode n}
    (hq : TermsDegreeLE D q) :
    TermsDegreeLE D (dimensionEmbed p q) := by
  intro t ht
  rw [dimensionEmbed, List.mem_map] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  simp only [dimensionEmbedTerm,
    ExponentCode.totalDegree_dimensionEmbed]
  exact hq u hu

end PolynomialCode

namespace AccumulatorPolynomialCode

variable {n m D : ℕ}

theorem liftBase_termsDegreeLE
    {p : PolynomialCode n}
    (hp : PolynomialCode.TermsDegreeLE D p) :
    PolynomialCode.TermsDegreeLE D
      (liftBase (m := m) p) :=
  PolynomialCode.termsDegreeLE_dimensionEmbed hp

theorem onePlusWCode_termsDegreeLE :
    PolynomialCode.TermsDegreeLE 1
      (onePlusWCode (n := n) (m := m)) := by
  apply PolynomialCode.termsDegreeLE_add
  · exact PolynomialCode.termsDegreeLE_one.promote (by omega)
  · exact PolynomialCode.termsDegreeLE_varCode _

theorem dotCode_termsDegreeLE
    (hD : 2 ≤ D)
    (g : Fin m → PolynomialCode n)
    (hg :
      ∀ i,
        PolynomialCode.TermsDegreeLE (D - 2) (g i)) :
    PolynomialCode.TermsDegreeLE (D - 1)
      (dotCode g) := by
  apply PolynomialCode.termsDegreeLE_sumCodes
  intro p hp
  rw [List.mem_ofFn] at hp
  obtain ⟨i, rfl⟩ := hp
  have hmul :=
    PolynomialCode.termsDegreeLE_mul
      (PolynomialCode.termsDegreeLE_varCode
        (uIndex (n := n) i))
      (liftBase_termsDegreeLE (m := m) (hg i))
  simpa only [driftCode] using
    hmul.promote (by omega)

theorem uFieldCode_termsDegreeLE
    (hD : 2 ≤ D)
    (g : Fin m → PolynomialCode n)
    (hg :
      ∀ i,
        PolynomialCode.TermsDegreeLE (D - 2) (g i))
    (i : Fin m) :
    PolynomialCode.TermsDegreeLE D
      (uFieldCode g i) := by
  apply PolynomialCode.termsDegreeLE_sub
  · exact
      (PolynomialCode.termsDegreeLE_mul
        (onePlusWCode_termsDegreeLE (n := n) (m := m))
        (liftBase_termsDegreeLE (m := m) (hg i))).promote
          (by omega)
  · exact
      (PolynomialCode.termsDegreeLE_mul
        (dotCode_termsDegreeLE hD g hg)
        (PolynomialCode.termsDegreeLE_varCode
          (uIndex (n := n) i))).promote
            (by omega)

theorem wFieldCode_termsDegreeLE
    (hD : 2 ≤ D)
    (g : Fin m → PolynomialCode n)
    (hg :
      ∀ i,
        PolynomialCode.TermsDegreeLE (D - 2) (g i)) :
    PolynomialCode.TermsDegreeLE D
      (wFieldCode g) := by
  apply PolynomialCode.termsDegreeLE_neg
  exact
    (PolynomialCode.termsDegreeLE_mul
      (onePlusWCode_termsDegreeLE (n := n) (m := m))
      (dotCode_termsDegreeLE hD g hg)).promote
        (by omega)

/-- Degree ledger for the complete compact-accumulator field. -/
theorem fieldCode_termsDegreeLE
    (hD : 2 ≤ D)
    (P : PolynomialFieldCode n)
    (hP :
      ∀ j, PolynomialCode.TermsDegreeLE D (P j))
    (g : Fin m → PolynomialCode n)
    (hg :
      ∀ i,
        PolynomialCode.TermsDegreeLE (D - 2) (g i)) :
    ∀ q,
      PolynomialCode.TermsDegreeLE D
        (fieldCode P g q) := by
  intro q
  cases houter : finSumFinEquiv.symm q with
  | inl j =>
      rw [fieldCode, houter]
      exact liftBase_termsDegreeLE (m := m) (hP j)
  | inr r =>
      cases hinner : finSumFinEquiv.symm r with
      | inl i =>
          simp only [fieldCode, houter, hinner]
          exact uFieldCode_termsDegreeLE hD g hg i
      | inr j =>
          simp only [fieldCode, houter, hinner]
          exact wFieldCode_termsDegreeLE hD g hg

end AccumulatorPolynomialCode

end HGAS
