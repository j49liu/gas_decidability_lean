import HGAS.Analysis.PolynomialWeightedLatticeSummability
import HGAS.Analysis.GaussianPolynomialWeightedSummability
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Explicit budgets for polynomially weighted integer lattices

Qualitative summability is insufficient for an effective accumulator
gain: the compiler needs a concrete number known to dominate the whole
Fourier primitive.  This module makes the standard geometric-series
argument quantitative.

For `r : ℕ`, put

```text
 A(r) = 2 · r! · 2^(r+1).
```

The elementary rising-factorial estimate

```text
 (1+n)^r ≤ r! * choose (n+r) r
```

and the negative-binomial series imply

```text
 Σ_{z:ℤ} (1+|z|)^r 2^(-|z|) ≤ A(r).
```

Taking products gives, for every finite integer lattice,

```text
 Σ_x (1+Σ_i |x_i|)^r 2^(-Σ_i |x_i|) ≤ A(r)^d.
```

All displayed budgets are natural numbers cast to `ℝ`; hence they can be
computed exactly from finite input data.
-/

noncomputable section

open scoped BigOperators

namespace HGAS.Analysis

/-- One-sided polynomial/geometric weight at ratio `1/2`. -/
def halfPolynomialNatWeight (r n : ℕ) : ℝ :=
  (1 + (n : ℝ)) ^ r * (1 / 2 : ℝ) ^ n

/-- Two-sided polynomial/geometric weight at ratio `1/2`. -/
def halfPolynomialIntWeight (r : ℕ) (z : ℤ) : ℝ :=
  (1 + (z.natAbs : ℝ)) ^ r * (1 / 2 : ℝ) ^ z.natAbs

/-- Explicit one-dimensional two-sided budget. -/
def halfPolynomialIntBudget (r : ℕ) : ℕ :=
  2 * r.factorial * 2 ^ (r + 1)

theorem halfPolynomialNatWeight_nonneg
    (r n : ℕ) :
    0 ≤ halfPolynomialNatWeight r n := by
  unfold halfPolynomialNatWeight
  positivity

theorem halfPolynomialIntWeight_nonneg
    (r : ℕ) (z : ℤ) :
    0 ≤ halfPolynomialIntWeight r z := by
  unfold halfPolynomialIntWeight
  positivity

/-- Rising factorials give a pointwise negative-binomial majorant. -/
theorem halfPolynomialNatWeight_le_chooseMajorant
    (r n : ℕ) :
    halfPolynomialNatWeight r n ≤
      (r.factorial : ℝ) * ((n + r).choose r : ℝ) *
        (1 / 2 : ℝ) ^ n := by
  have hpowNat :
      (n + 1) ^ r ≤
        r.factorial * (n + r).choose r := by
    calc
      (n + 1) ^ r ≤ (n + 1).ascFactorial r :=
        Nat.pow_succ_le_ascFactorial (n + 1) r
      _ = r.factorial * (n + r).choose r :=
        Nat.ascFactorial_eq_factorial_mul_choose n r
  have hpow :
      (1 + (n : ℝ)) ^ r ≤
        (r.factorial : ℝ) * ((n + r).choose r : ℝ) := by
    have hcast :
        (((n + 1) ^ r : ℕ) : ℝ) ≤
          ((r.factorial * (n + r).choose r : ℕ) : ℝ) := by
      exact_mod_cast hpowNat
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one,
      Nat.cast_mul, Nat.cast_choose, add_comm] using hcast
  unfold halfPolynomialNatWeight
  exact mul_le_mul_of_nonneg_right hpow (by positivity)

theorem summable_halfPolynomialNatWeight
    (r : ℕ) :
    Summable (halfPolynomialNatWeight r) := by
  let g : ℕ → ℝ :=
    fun n ↦
      (r.factorial : ℝ) * ((n + r).choose r : ℝ) *
        (1 / 2 : ℝ) ^ n
  have hchoose :
      Summable fun n : ℕ ↦
        ((n + r).choose r : ℝ) *
          (1 / 2 : ℝ) ^ n :=
    summable_choose_mul_geometric_of_norm_lt_one
      r (by norm_num)
  have hg : Summable g := by
    simpa only [g, mul_assoc] using
      hchoose.mul_left (r.factorial : ℝ)
  exact Summable.of_nonneg_of_le
    (halfPolynomialNatWeight_nonneg r)
    (halfPolynomialNatWeight_le_chooseMajorant r)
    hg

/-- Explicit one-sided sum bound. -/
theorem tsum_halfPolynomialNatWeight_le
    (r : ℕ) :
    (∑' n : ℕ, halfPolynomialNatWeight r n) ≤
      (r.factorial * 2 ^ (r + 1) : ℕ) := by
  let g : ℕ → ℝ :=
    fun n ↦
      (r.factorial : ℝ) * ((n + r).choose r : ℝ) *
        (1 / 2 : ℝ) ^ n
  have hg :
      Summable g := by
    have hchoose :
        Summable fun n : ℕ ↦
          ((n + r).choose r : ℝ) *
            (1 / 2 : ℝ) ^ n :=
      summable_choose_mul_geometric_of_norm_lt_one
        r (by norm_num)
    simpa only [g, mul_assoc] using
      hchoose.mul_left (r.factorial : ℝ)
  calc
    (∑' n : ℕ, halfPolynomialNatWeight r n) ≤
        ∑' n : ℕ, g n :=
      (summable_halfPolynomialNatWeight r).tsum_le_tsum
        (halfPolynomialNatWeight_le_chooseMajorant r)
        hg
    _ =
        (r.factorial : ℝ) *
          (1 / (1 - (1 / 2 : ℝ)) ^ (r + 1)) := by
      simp only [g, mul_assoc]
      rw [tsum_mul_left]
      rw [tsum_choose_mul_geometric_of_norm_lt_one
        r (by norm_num)]
    _ = (r.factorial * 2 ^ (r + 1) : ℕ) := by
      push_cast
      norm_num [div_pow]

/-- The two-sided weight is summable. -/
theorem summable_halfPolynomialIntWeight
    (r : ℕ) :
    Summable (halfPolynomialIntWeight r) := by
  change
    Summable
      (polynomialGeometricIntWeight (1 / 2 : ℝ) r)
  exact
    summable_polynomialGeometricIntWeight
      (q := (1 / 2 : ℝ)) (by norm_num) (by norm_num) r

/-- Explicit two-sided sum bound. -/
theorem tsum_halfPolynomialIntWeight_le
    (r : ℕ) :
    (∑' z : ℤ, halfPolynomialIntWeight r z) ≤
      (halfPolynomialIntBudget r : ℕ) := by
  let f : ℕ → ℝ := halfPolynomialNatWeight r
  have hf : Summable f :=
    summable_halfPolynomialNatWeight r
  have hshift : Summable fun n : ℕ ↦ f (n + 1) :=
    (summable_nat_add_iff 1).2 hf
  have hshiftLe :
      (∑' n : ℕ, f (n + 1)) ≤
        ∑' n : ℕ, f n := by
    have hsplit := hf.tsum_eq_zero_add
    have hfzero : 0 ≤ f 0 :=
      halfPolynomialNatWeight_nonneg r 0
    linarith
  have hpair :
      (∑' n : ℕ,
        (halfPolynomialIntWeight r (n : ℤ) +
          halfPolynomialIntWeight r (-(n : ℤ) - 1))) =
        (∑' n : ℕ, f n) +
          ∑' n : ℕ, f (n + 1) := by
    have hleft :
        (fun n : ℕ ↦ halfPolynomialIntWeight r (n : ℤ)) =
          f := by
      funext n
      simp [f, halfPolynomialIntWeight,
        halfPolynomialNatWeight]
    have hright :
        (fun n : ℕ ↦
          halfPolynomialIntWeight r (-(n : ℤ) - 1)) =
            fun n ↦ f (n + 1) := by
      funext n
      rw [show -(n : ℤ) - 1 = Int.negSucc n by
        rw [Int.negSucc_eq]
        ring]
      simp [f, halfPolynomialIntWeight,
        halfPolynomialNatWeight, Int.natAbs_negSucc]
    have hpairs :
        (fun n : ℕ ↦
          halfPolynomialIntWeight r (n : ℤ) +
            halfPolynomialIntWeight r (-(n : ℤ) - 1)) =
          fun n ↦ f n + f (n + 1) := by
      funext n
      rw [← congrFun hleft n, ← congrFun hright n]
    rw [hpairs]
    exact hf.tsum_add hshift
  have hint :
      (∑' z : ℤ, halfPolynomialIntWeight r z) =
        (∑' n : ℕ,
          (halfPolynomialIntWeight r (n : ℤ) +
            halfPolynomialIntWeight r (-(n : ℤ) - 1))) := by
    symm
    rw [←
      tsum_nat_add_neg_add_one
        (summable_halfPolynomialIntWeight r)]
    apply tsum_congr
    intro n
    congr 2
    ring
  rw [hint, hpair]
  calc
    (∑' n : ℕ, f n) + ∑' n : ℕ, f (n + 1) ≤
        2 * ∑' n : ℕ, f n := by linarith
    _ ≤
        2 * (r.factorial * 2 ^ (r + 1) : ℕ) := by
      exact mul_le_mul_of_nonneg_left
        (tsum_halfPolynomialNatWeight_le r) (by norm_num)
    _ = (halfPolynomialIntBudget r : ℕ) := by
      simp [halfPolynomialIntBudget]
      ring

/-- Exact factorization of a finite product `tsum`. -/
theorem tsum_finIntegerProduct_eq_pow
    (weight : ℤ → ℝ)
    (hweight : Summable weight)
    (hweight0 : ∀ z, 0 ≤ weight z)
    (n : ℕ) :
    (∑' x : Fin n → ℤ, ∏ i, weight (x i)) =
      (∑' z : ℤ, weight z) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      let e : ℤ × (Fin n → ℤ) ≃ (Fin (n + 1) → ℤ) :=
        Fin.consEquiv fun _ ↦ ℤ
      let tail : (Fin n → ℤ) → ℝ :=
        fun x ↦ ∏ i, weight (x i)
      have htail : Summable tail :=
        summable_finIntegerProduct weight hweight hweight0 n
      have hproduct :
          Summable fun p : ℤ × (Fin n → ℤ) ↦
            weight p.1 * tail p.2 :=
        Summable.mul_of_nonneg
          hweight htail hweight0
          (fun x ↦ Finset.prod_nonneg fun _ _ ↦ hweight0 _)
      have heq :
          (∑' x : Fin (n + 1) → ℤ,
              ∏ i, weight (x i)) =
            ∑' p : ℤ × (Fin n → ℤ),
              weight p.1 * tail p.2 := by
        rw [← e.tsum_eq]
        apply tsum_congr
        intro p
        simp [e, tail, Fin.prod_univ_succ]
      rw [heq, ← hweight.tsum_mul_tsum htail hproduct,
        ih]
      ring

/-- Total `ℓ¹` polynomial/geometric weight on a finite lattice. -/
def halfPolynomialFinWeight
    (n r : ℕ) (x : Fin n → ℤ) : ℝ :=
  (1 + (integerL1Energy x : ℝ)) ^ r *
    (1 / 2 : ℝ) ^ integerL1Energy x

theorem halfPolynomialFinWeight_nonneg
    (n r : ℕ) (x : Fin n → ℤ) :
    0 ≤ halfPolynomialFinWeight n r x := by
  unfold halfPolynomialFinWeight
  positivity

theorem summable_halfPolynomialFinWeight
    (n r : ℕ) :
    Summable (halfPolynomialFinWeight n r) := by
  change
    Summable fun x : Fin n → ℤ ↦
      (1 + (integerL1Energy x : ℝ)) ^ r *
        (1 / 2 : ℝ) ^ integerL1Energy x
  exact
    summable_polynomial_finGeometricEnergy
      (q := (1 / 2 : ℝ)) (by norm_num) (by norm_num) n r

/-- Explicit finite-lattice sum bound. -/
theorem tsum_halfPolynomialFinWeight_le
    (n r : ℕ) :
    (∑' x : Fin n → ℤ, halfPolynomialFinWeight n r x) ≤
      (halfPolynomialIntBudget r : ℝ) ^ n := by
  let weight : ℤ → ℝ := halfPolynomialIntWeight r
  let productWeight : (Fin n → ℤ) → ℝ :=
    fun x ↦ ∏ i, weight (x i)
  have hweight : Summable weight :=
    summable_halfPolynomialIntWeight r
  have hweight0 : ∀ z, 0 ≤ weight z :=
    halfPolynomialIntWeight_nonneg r
  have hproduct : Summable productWeight :=
    summable_finIntegerProduct weight hweight hweight0 n
  have hpoint :
      ∀ x : Fin n → ℤ,
        halfPolynomialFinWeight n r x ≤
          productWeight x := by
    intro x
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
    unfold halfPolynomialFinWeight productWeight weight
    calc
      (1 + (integerL1Energy x : ℝ)) ^ r *
          (1 / 2 : ℝ) ^ integerL1Energy x ≤
        (∏ i : Fin n,
            (1 + ((x i).natAbs : ℝ))) ^ r *
          (1 / 2 : ℝ) ^ integerL1Energy x :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ =
        ∏ i : Fin n, halfPolynomialIntWeight r (x i) := by
        simp only [halfPolynomialIntWeight,
          Finset.prod_mul_distrib, ← Finset.prod_pow,
          ← Finset.prod_pow_eq_pow_sum, integerL1Energy]
  calc
    (∑' x : Fin n → ℤ, halfPolynomialFinWeight n r x) ≤
        ∑' x : Fin n → ℤ, productWeight x :=
      (summable_halfPolynomialFinWeight n r).tsum_le_tsum
        hpoint hproduct
    _ = (∑' z : ℤ, weight z) ^ n :=
      tsum_finIntegerProduct_eq_pow weight hweight hweight0 n
    _ ≤ (halfPolynomialIntBudget r : ℝ) ^ n := by
      exact pow_le_pow_left₀
        (tsum_nonneg hweight0)
        (tsum_halfPolynomialIntWeight_le r) n

/-- Total polynomial/geometric weight on a pair of equal integer
lattices. -/
def halfPolynomialPairWeight
    (n r : ℕ)
    (x : (Fin n → ℤ) × (Fin n → ℤ)) : ℝ :=
  (1 + (integerPairL1Energy x : ℝ)) ^ r *
    (1 / 2 : ℝ) ^ integerPairL1Energy x

theorem summable_halfPolynomialPairWeight
    (n r : ℕ) :
    Summable (halfPolynomialPairWeight n r) := by
  change
    Summable fun x :
        (Fin n → ℤ) × (Fin n → ℤ) ↦
      (1 + (integerPairL1Energy x : ℝ)) ^ r *
        (1 / 2 : ℝ) ^ integerPairL1Energy x
  exact
    summable_polynomial_pairGeometricEnergy
      (q := (1 / 2 : ℝ)) (by norm_num) (by norm_num) n r

/-- Explicit paired-lattice sum bound. -/
theorem tsum_halfPolynomialPairWeight_le
    (n r : ℕ) :
    (∑' x : (Fin n → ℤ) × (Fin n → ℤ),
      halfPolynomialPairWeight n r x) ≤
        (halfPolynomialIntBudget r : ℝ) ^ (n + n) := by
  let e := finIntegerPairEquiv n
  have henergy :
      ∀ x : Fin (n + n) → ℤ,
        integerPairL1Energy (e x) =
          integerL1Energy x := by
    intro x
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
  have heq :
      (∑' x :
          (Fin n → ℤ) × (Fin n → ℤ),
          halfPolynomialPairWeight n r x) =
        ∑' x : Fin (n + n) → ℤ,
          halfPolynomialFinWeight (n + n) r x := by
    rw [← e.tsum_eq]
    apply tsum_congr
    intro x
    simp only [halfPolynomialPairWeight,
      halfPolynomialFinWeight, henergy]
  rw [heq]
  exact tsum_halfPolynomialFinWeight_le (n + n) r

/-- Two ordinary integer coordinates are the `n = 1` paired lattice,
stated without the `Fin 1` wrappers used by the general theorem. -/
theorem tsum_halfPolynomialIntPairWeight_le
    (r : ℕ) :
    (∑' x : ℤ × ℤ,
      (1 + (integerPairAbsEnergy x : ℝ)) ^ r *
        (1 / 2 : ℝ) ^ integerPairAbsEnergy x) ≤
      (halfPolynomialIntBudget r : ℝ) ^ 2 := by
  let weight : ℤ → ℝ := halfPolynomialIntWeight r
  let productWeight : ℤ × ℤ → ℝ :=
    fun x ↦ weight x.1 * weight x.2
  have hweight : Summable weight :=
    summable_halfPolynomialIntWeight r
  have hweight0 : ∀ z, 0 ≤ weight z :=
    halfPolynomialIntWeight_nonneg r
  have hproduct : Summable productWeight :=
    Summable.mul_of_nonneg hweight hweight
      hweight0 hweight0
  have hbase :
      Summable fun x : ℤ × ℤ ↦
        (1 + (integerPairAbsEnergy x : ℝ)) ^ r *
          (1 / 2 : ℝ) ^ integerPairAbsEnergy x :=
    summable_polynomialGeometricIntPairWeight
      (q := (1 / 2 : ℝ)) (by norm_num) (by norm_num) r
  have hpoint :
      ∀ x : ℤ × ℤ,
        (1 + (integerPairAbsEnergy x : ℝ)) ^ r *
            (1 / 2 : ℝ) ^ integerPairAbsEnergy x ≤
          productWeight x := by
    intro x
    have hlinear :
        1 + (integerPairAbsEnergy x : ℝ) ≤
          (1 + (x.1.natAbs : ℝ)) *
            (1 + (x.2.natAbs : ℝ)) := by
      unfold integerPairAbsEnergy
      push_cast
      have h1 : 0 ≤ (x.1.natAbs : ℝ) :=
        Nat.cast_nonneg _
      have h2 : 0 ≤ (x.2.natAbs : ℝ) :=
        Nat.cast_nonneg _
      nlinarith [mul_nonneg h1 h2]
    have hpow :
        (1 + (integerPairAbsEnergy x : ℝ)) ^ r ≤
          ((1 + (x.1.natAbs : ℝ)) *
            (1 + (x.2.natAbs : ℝ))) ^ r := by
      gcongr
    unfold productWeight weight
    calc
      (1 + (integerPairAbsEnergy x : ℝ)) ^ r *
          (1 / 2 : ℝ) ^ integerPairAbsEnergy x ≤
        ((1 + (x.1.natAbs : ℝ)) *
            (1 + (x.2.natAbs : ℝ))) ^ r *
          (1 / 2 : ℝ) ^ integerPairAbsEnergy x :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ =
        halfPolynomialIntWeight r x.1 *
          halfPolynomialIntWeight r x.2 := by
        simp only [halfPolynomialIntWeight,
          integerPairAbsEnergy, pow_add, mul_pow]
        ring
  calc
    (∑' x : ℤ × ℤ,
      (1 + (integerPairAbsEnergy x : ℝ)) ^ r *
        (1 / 2 : ℝ) ^ integerPairAbsEnergy x) ≤
      ∑' x : ℤ × ℤ, productWeight x :=
        hbase.tsum_le_tsum hpoint hproduct
    _ =
      (∑' z : ℤ, weight z) *
        ∑' z : ℤ, weight z := by
      symm
      exact hweight.tsum_mul_tsum hweight hproduct
    _ ≤
      (halfPolynomialIntBudget r : ℝ) *
        halfPolynomialIntBudget r := by
      exact mul_le_mul
        (tsum_halfPolynomialIntWeight_le r)
        (tsum_halfPolynomialIntWeight_le r)
        (tsum_nonneg hweight0)
        (by positivity)
    _ = (halfPolynomialIntBudget r : ℝ) ^ 2 := by
      ring

end HGAS.Analysis
