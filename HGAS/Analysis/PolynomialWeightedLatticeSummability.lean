import HGAS.Analysis.LatticeSummability
import Mathlib.Tactic

/-!
# Polynomially weighted geometric decay on integer lattices

Small-divisor estimates cost a fixed polynomial power of the Fourier
exponent height.  Gaussian and geometric detector coefficients decay
exponentially, so this polynomial loss is harmless.

This module records that elementary fact in a reusable form.  For
`0 < q < 1`, every weight

```text
       (1 + |z|)^r q^|z|
```

is summable on `ℤ`.  Finite products then imply summability of

```text
       (1 + Σ_i |x_i|)^r q^(Σ_i |x_i|)
```

on every fixed integer lattice.  The final theorem permits an arbitrary
nonnegative height bounded by a fixed constant times a power of the
`ℓ¹` energy, exactly matching applications of the radical conjugate
height.
-/

noncomputable section

open scoped BigOperators

namespace HGAS.Analysis

/-- A polynomially weighted two-sided geometric sequence. -/
def polynomialGeometricIntWeight
    (q : ℝ) (r : ℕ) (z : ℤ) : ℝ :=
  (1 + (z.natAbs : ℝ)) ^ r * q ^ z.natAbs

theorem polynomialGeometricIntWeight_nonneg
    {q : ℝ} (hq : 0 ≤ q) (r : ℕ) (z : ℤ) :
    0 ≤ polynomialGeometricIntWeight q r z := by
  exact mul_nonneg (pow_nonneg (by positivity) _)
    (pow_nonneg hq _)

/-- Every fixed polynomial loss is absorbed by two-sided geometric
decay. -/
theorem summable_polynomialGeometricIntWeight
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (r : ℕ) :
    Summable (polynomialGeometricIntWeight q r) := by
  have hnorm : ‖q‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_pos hq0] using hq1
  have hbase :
      Summable fun n : ℕ ↦ (n : ℝ) ^ r * q ^ n := by
    have h :=
      summable_norm_pow_mul_geometric_of_norm_lt_one
        (R := ℝ) r hnorm
    have habs_nat (n : ℕ) :
        |(n : ℝ)| = (n : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg n)
    simpa only [Real.norm_eq_abs, abs_mul,
      abs_pow, habs_nat, abs_of_pos hq0] using h
  have hgeom :
      Summable fun n : ℕ ↦ q ^ n :=
    summable_geometric_of_lt_one hq0.le hq1
  have hnat :
      Summable fun n : ℕ ↦
        (1 + (n : ℝ)) ^ r * q ^ n := by
    have hmajor :
        Summable fun n : ℕ ↦
          (2 : ℝ) ^ (r - 1) *
            (q ^ n + (n : ℝ) ^ r * q ^ n) :=
      (hgeom.add hbase).mul_left ((2 : ℝ) ^ (r - 1))
    apply Summable.of_nonneg_of_le
    · intro n
      exact mul_nonneg (pow_nonneg (by positivity) _)
        (pow_nonneg hq0.le _)
    · intro n
      have hpow :
          (1 + (n : ℝ)) ^ r ≤
            (2 : ℝ) ^ (r - 1) *
              (1 ^ r + (n : ℝ) ^ r) :=
        add_pow_le (by positivity) (Nat.cast_nonneg n) r
      calc
        (1 + (n : ℝ)) ^ r * q ^ n ≤
            ((2 : ℝ) ^ (r - 1) *
              (1 ^ r + (n : ℝ) ^ r)) * q ^ n :=
          mul_le_mul_of_nonneg_right hpow
            (pow_nonneg hq0.le _)
        _ =
            (2 : ℝ) ^ (r - 1) *
              (q ^ n + (n : ℝ) ^ r * q ^ n) := by
          ring
    · exact hmajor
  apply Summable.of_nat_of_neg
  · simpa [polynomialGeometricIntWeight,
      add_comm] using hnat
  · simpa [polynomialGeometricIntWeight,
      add_comm] using hnat

/-- Elementary product majorant:
`1 + Σ fᵢ ≤ Π (1 + fᵢ)` for nonnegative `fᵢ`. -/
theorem one_add_sum_le_prod_one_add
    {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    1 + ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 + f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, 0 ≤ f i := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      have hsum : 0 ≤ ∑ i ∈ s, f i :=
        Finset.sum_nonneg hfs
      calc
        1 + (f a + ∑ i ∈ s, f i) ≤
            (1 + f a) * (1 + ∑ i ∈ s, f i) := by
          nlinarith [mul_nonneg hfa hsum]
        _ ≤ (1 + f a) * ∏ i ∈ s, (1 + f i) := by
          exact
            mul_le_mul_of_nonneg_left
              (ih hfs) (by positivity)

/-- The `ℓ¹` energy of an integer vector. -/
def integerL1Energy {n : ℕ} (x : Fin n → ℤ) : ℕ :=
  ∑ i, (x i).natAbs

/-- A polynomial in total `ℓ¹` energy times geometric decay is summable on
every fixed integer lattice. -/
theorem summable_polynomial_finGeometricEnergy
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (n r : ℕ) :
    Summable fun x : Fin n → ℤ ↦
      (1 + (integerL1Energy x : ℝ)) ^ r *
        q ^ integerL1Energy x := by
  let weight : ℤ → ℝ :=
    polynomialGeometricIntWeight q r
  have hweight : Summable weight :=
    summable_polynomialGeometricIntWeight hq0 hq1 r
  have hweight0 : ∀ z, 0 ≤ weight z :=
    fun z ↦ polynomialGeometricIntWeight_nonneg hq0.le r z
  have hproduct :
      Summable fun x : Fin n → ℤ ↦
        ∏ i, weight (x i) :=
    summable_finIntegerProduct weight hweight hweight0 n
  apply Summable.of_nonneg_of_le
  · intro x
    exact mul_nonneg (pow_nonneg (by positivity) _)
      (pow_nonneg hq0.le _)
  · intro x
    have hlinear :
        1 + (integerL1Energy x : ℝ) ≤
          ∏ i : Fin n, (1 + ((x i).natAbs : ℝ)) := by
      simpa only [integerL1Energy, Nat.cast_sum] using
        (one_add_sum_le_prod_one_add
          (Finset.univ : Finset (Fin n))
          (fun i ↦ ((x i).natAbs : ℝ))
          (by intro i hi; positivity))
    have hpow :
        (1 + (integerL1Energy x : ℝ)) ^ r ≤
          (∏ i : Fin n,
            (1 + ((x i).natAbs : ℝ))) ^ r := by
      gcongr
    calc
      (1 + (integerL1Energy x : ℝ)) ^ r *
          q ^ integerL1Energy x ≤
        (∏ i : Fin n,
            (1 + ((x i).natAbs : ℝ))) ^ r *
          q ^ integerL1Energy x :=
        mul_le_mul_of_nonneg_right hpow
          (pow_nonneg hq0.le _)
      _ = ∏ i : Fin n, weight (x i) := by
        simp only [weight, polynomialGeometricIntWeight,
          Finset.prod_mul_distrib, ← Finset.prod_pow,
          ← Finset.prod_pow_eq_pow_sum, integerL1Energy]
  · exact hproduct

/-- A nonnegative height with a fixed polynomial bound may be inserted to
any fixed power without destroying lattice summability. -/
theorem summable_geometric_mul_height_pow_of_polynomial_bound
    {q C : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (n heightPower growthPower : ℕ)
    (height : (Fin n → ℤ) → ℝ)
    (hheight0 : ∀ x, 0 ≤ height x)
    (hheight :
      ∀ x,
        height x ≤
          C * (1 + (integerL1Energy x : ℝ)) ^ growthPower) :
    Summable fun x : Fin n → ℤ ↦
      q ^ integerL1Energy x * height x ^ heightPower := by
  have hbase :=
    summable_polynomial_finGeometricEnergy
      hq0 hq1 n (growthPower * heightPower)
  have hconst :
      Summable fun x : Fin n → ℤ ↦
        C ^ heightPower *
          ((1 + (integerL1Energy x : ℝ)) ^
              (growthPower * heightPower) *
            q ^ integerL1Energy x) :=
    hbase.mul_left (C ^ heightPower)
  apply Summable.of_nonneg_of_le
  · intro x
    exact mul_nonneg (pow_nonneg hq0.le _)
      (pow_nonneg (hheight0 x) _)
  · intro x
    have hp :
        height x ^ heightPower ≤
          (C *
            (1 + (integerL1Energy x : ℝ)) ^ growthPower) ^
              heightPower := by
      exact pow_le_pow_left₀ (hheight0 x)
        (hheight x) heightPower
    calc
      q ^ integerL1Energy x * height x ^ heightPower ≤
          q ^ integerL1Energy x *
            (C *
              (1 + (integerL1Energy x : ℝ)) ^ growthPower) ^
                heightPower :=
        mul_le_mul_of_nonneg_left hp
          (pow_nonneg hq0.le _)
      _ =
          C ^ heightPower *
            ((1 + (integerL1Energy x : ℝ)) ^
                (growthPower * heightPower) *
              q ^ integerL1Energy x) := by
        rw [mul_pow, ← pow_mul]
        ring
  · exact hconst

/-! ## Two equal lattice blocks

The arithmetic detector is indexed by a pair `(x,s)` of integer vectors.
The following equivalence and its consequences expose that common shape
without forcing downstream files to flatten pairs by hand. -/

/-- Concatenate two integer vectors into a single vector. -/
def finIntegerPairEquiv (n : ℕ) :
    (Fin (n + n) → ℤ) ≃
      (Fin n → ℤ) × (Fin n → ℤ) :=
  (Equiv.arrowCongr
      (finSumFinEquiv :
        Fin n ⊕ Fin n ≃ Fin (n + n)).symm
      (Equiv.refl ℤ)).trans
    (Equiv.sumArrowEquivProdArrow (Fin n) (Fin n) ℤ)

/-- Total `ℓ¹` energy of a pair of integer vectors. -/
def integerPairL1Energy {n : ℕ}
    (x : (Fin n → ℤ) × (Fin n → ℤ)) : ℕ :=
  integerL1Energy x.1 + integerL1Energy x.2

theorem integerPairL1Energy_eq {n : ℕ}
    (x : (Fin n → ℤ) × (Fin n → ℤ)) :
    integerPairL1Energy x =
      integerL1Energy x.1 + integerL1Energy x.2 := by
  rfl

/-- Polynomially weighted geometric decay is summable on a pair of fixed
integer lattices. -/
theorem summable_polynomial_pairGeometricEnergy
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (n r : ℕ) :
    Summable fun x :
        (Fin n → ℤ) × (Fin n → ℤ) ↦
      (1 + (integerPairL1Energy x : ℝ)) ^ r *
        q ^ integerPairL1Energy x := by
  let e := finIntegerPairEquiv n
  let f :
      ((Fin n → ℤ) × (Fin n → ℤ)) → ℝ :=
    fun x ↦
      (1 + (integerPairL1Energy x : ℝ)) ^ r *
        q ^ integerPairL1Energy x
  apply (e.summable_iff (f := f)).mp
  have h :=
    summable_polynomial_finGeometricEnergy
      hq0 hq1 (n + n) r
  apply h.congr
  intro x
  have henergy :
      integerPairL1Energy (e x) =
        integerL1Energy x := by
    simp only [integerPairL1Energy_eq, integerL1Energy]
    change
      (∑ i : Fin n,
          (x (finSumFinEquiv (Sum.inl i))).natAbs) +
        (∑ i : Fin n,
          (x (finSumFinEquiv (Sum.inr i))).natAbs) =
        ∑ i : Fin (n + n), (x i).natAbs
    calc
      _ =
          ∑ i : Fin n ⊕ Fin n,
            (x (finSumFinEquiv i)).natAbs :=
        (Fintype.sum_sum_type
          (fun i : Fin n ⊕ Fin n ↦
            (x (finSumFinEquiv i)).natAbs)).symm
      _ = _ :=
        finSumFinEquiv.sum_comp
          (fun i : Fin (n + n) ↦ (x i).natAbs)
  simp [f, henergy]

/-- Pair-lattice form of
`summable_geometric_mul_height_pow_of_polynomial_bound`. -/
theorem summable_pair_geometric_mul_height_pow_of_polynomial_bound
    {q C : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (n heightPower growthPower : ℕ)
    (height :
      ((Fin n → ℤ) × (Fin n → ℤ)) → ℝ)
    (hheight0 : ∀ x, 0 ≤ height x)
    (hheight :
      ∀ x,
        height x ≤
          C *
            (1 + (integerPairL1Energy x : ℝ)) ^
              growthPower) :
    Summable fun x :
        (Fin n → ℤ) × (Fin n → ℤ) ↦
      q ^ integerPairL1Energy x *
        height x ^ heightPower := by
  have hbase :=
    summable_polynomial_pairGeometricEnergy
      hq0 hq1 n (growthPower * heightPower)
  have hconst :
      Summable fun x :
          (Fin n → ℤ) × (Fin n → ℤ) ↦
        C ^ heightPower *
          ((1 + (integerPairL1Energy x : ℝ)) ^
              (growthPower * heightPower) *
            q ^ integerPairL1Energy x) :=
    hbase.mul_left (C ^ heightPower)
  apply Summable.of_nonneg_of_le
  · intro x
    exact mul_nonneg (pow_nonneg hq0.le _)
      (pow_nonneg (hheight0 x) _)
  · intro x
    have hp :
        height x ^ heightPower ≤
          (C *
            (1 + (integerPairL1Energy x : ℝ)) ^
              growthPower) ^ heightPower :=
      pow_le_pow_left₀ (hheight0 x)
        (hheight x) heightPower
    calc
      q ^ integerPairL1Energy x *
          height x ^ heightPower ≤
        q ^ integerPairL1Energy x *
          (C *
            (1 + (integerPairL1Energy x : ℝ)) ^
              growthPower) ^ heightPower :=
        mul_le_mul_of_nonneg_left hp
          (pow_nonneg hq0.le _)
      _ =
          C ^ heightPower *
            ((1 + (integerPairL1Energy x : ℝ)) ^
                (growthPower * heightPower) *
              q ^ integerPairL1Energy x) := by
        rw [mul_pow, ← pow_mul]
        ring
  · exact hconst

end HGAS.Analysis
