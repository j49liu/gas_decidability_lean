import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Tactic

/-!
# The unscaled Veronese map

For `x : Fin n → R` and a multiindex `a : Fin n → ℕ` of total degree
`k`, the unscaled Veronese coordinate is

```
νₖ(x)ₐ = ∏ i, xᵢ ^ aᵢ.
```

We index the target by the subtype of
`Finset.piAntidiag Finset.univ k`.  Thus membership and total degree are
carried by the index itself, while the target remains a genuine finite
coordinate space.

The multinomially weighted quadratic form is

```
Q(y) = ∑ a, multinomial(a) * yₐ².
```

The main theorem is the exact normalization from equation (15.3):

```
Q(νₖ(x)) = (∑ i, xᵢ²)^k.
```

All algebraic definitions and identities are stated over a commutative
semiring.  The positivity results are then specialized to natural and real
coefficients.
-/

namespace HGAS.Veronese

open scoped BigOperators

/-- The finite set of degree-`k` multiindices in `n` variables. -/
def multiIndexFinset (n k : ℕ) : Finset (Fin n → ℕ) :=
  Finset.piAntidiag Finset.univ k

/-- A degree-`k` multiindex in `n` variables.  Its proof component records
that the coordinate sum is exactly `k`. -/
abbrev MultiIndex (n k : ℕ) :=
  ↥(multiIndexFinset n k)

variable {n k : ℕ}

/-- Every bundled multiindex belongs to the defining antidiagonal. -/
theorem multiIndex_mem (a : MultiIndex n k) :
    a.1 ∈ Finset.piAntidiag
      (Finset.univ : Finset (Fin n)) k :=
  a.2

/-- The entries of a degree-`k` multiindex sum to `k`. -/
theorem multiIndex_degree (a : MultiIndex n k) :
    ∑ i, a.1 i = k := by
  exact (Finset.mem_piAntidiag.mp a.2).1

/-- The monomial belonging to a multiindex. -/
def monomial {R : Type*} [CommMonoid R]
    (x : Fin n → R) (a : MultiIndex n k) : R :=
  ∏ i, x i ^ a.1 i

/-- The unscaled degree-`k` Veronese map. -/
def veroneseMap {R : Type*} [CommMonoid R]
    (x : Fin n → R) : MultiIndex n k → R :=
  fun a ↦ monomial x a

@[simp]
theorem veroneseMap_apply {R : Type*} [CommMonoid R]
    (x : Fin n → R) (a : MultiIndex n k) :
    veroneseMap x a = ∏ i, x i ^ a.1 i :=
  rfl

/-- The multinomial weight attached to a degree-`k` multiindex. -/
def multinomialWeight (a : MultiIndex n k) : ℕ :=
  Nat.multinomial (Finset.univ : Finset (Fin n)) a.1

/-- Every multinomial weight is a strictly positive natural number. -/
theorem multinomialWeight_pos (a : MultiIndex n k) :
    0 < multinomialWeight a :=
  Nat.multinomial_pos (Finset.univ : Finset (Fin n)) a.1

/-- The same coefficient is strictly positive after coercion to `ℝ`. -/
theorem multinomialWeight_real_pos (a : MultiIndex n k) :
    0 < (multinomialWeight a : ℝ) := by
  exact_mod_cast multinomialWeight_pos a

/-- The multinomially weighted quadratic form on Veronese coordinates. -/
def Q {R : Type*} [CommSemiring R]
    (y : MultiIndex n k → R) : R :=
  ∑ a, (multinomialWeight a : R) * y a ^ 2

/-- A Veronese monomial has scaling degree `k`. -/
theorem veroneseMap_smul_apply
    {R : Type*} [CommSemiring R]
    (c : R) (x : Fin n → R) (a : MultiIndex n k) :
    veroneseMap (c • x) a = c ^ k * veroneseMap x a := by
  simp only [veroneseMap, monomial, Pi.smul_apply, smul_eq_mul,
    mul_pow]
  rw [Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum]
  rw [multiIndex_degree a]

/-- Function-valued form of homogeneous scaling for the Veronese map. -/
theorem veroneseMap_smul
    {R : Type*} [CommSemiring R]
    (c : R) (x : Fin n → R) :
    veroneseMap (k := k) (c • x) =
      c ^ k • veroneseMap (k := k) x := by
  funext a
  exact veroneseMap_smul_apply c x a

/-- The weighted form `Q` is quadratic in its Veronese coordinates. -/
theorem Q_smul
    {R : Type*} [CommSemiring R]
    (c : R) (y : MultiIndex n k → R) :
    Q (c • y) = c ^ 2 * Q y := by
  simp only [Q, Pi.smul_apply, smul_eq_mul, mul_pow,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ac_rfl

/-- Exact multinomial normalization, equation (15.3):

`Q(νₖ(x)) = (∑ᵢ xᵢ²)^k`.

The proof is the multinomial theorem applied to the entries `xᵢ²`; the
only remaining algebra is
`(∏ᵢ xᵢ^{aᵢ})² = ∏ᵢ (xᵢ²)^{aᵢ}`. -/
@[simp]
theorem Q_veroneseMap
    {R : Type*} [CommSemiring R]
    (x : Fin n → R) :
    Q (veroneseMap (k := k) x) =
      (∑ i, x i ^ 2) ^ k := by
  simp only [Q, multinomialWeight, veroneseMap, monomial,
    multiIndexFinset]
  change
    (∑ a : ↥(Finset.piAntidiag
        (Finset.univ : Finset (Fin n)) k),
      (Nat.multinomial
        (Finset.univ : Finset (Fin n)) a.1 : R) *
          (∏ i, x i ^ a.1 i) ^ 2) =
      (∑ i, x i ^ 2) ^ k
  rw [Finset.sum_coe_sort
    (Finset.piAntidiag
      (Finset.univ : Finset (Fin n)) k)
    (fun a ↦
      (Nat.multinomial
        (Finset.univ : Finset (Fin n)) a : R) *
          (∏ i, x i ^ a i) ^ 2)]
  rw [Finset.sum_pow_eq_sum_piAntidiag
    (Finset.univ : Finset (Fin n))
    (fun i ↦ x i ^ 2) k]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  rw [← Finset.prod_pow
    (Finset.univ : Finset (Fin n)) 2
    (fun i ↦ x i ^ a i)]
  apply Finset.prod_congr rfl
  intro i _
  simp only [← pow_mul]
  rw [Nat.mul_comm]

/-- Over `ℝ`, the weighted quadratic form is nonnegative. -/
theorem Q_nonneg_real (y : MultiIndex n k → ℝ) :
    0 ≤ Q y := by
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

/-- Because every multinomial coefficient is positive, the real quadratic
form is positive definite. -/
theorem Q_eq_zero_iff_real (y : MultiIndex n k → ℝ) :
    Q y = 0 ↔ y = 0 := by
  constructor
  · intro hQ
    funext a
    have hterm :
        (multinomialWeight a : ℝ) * y a ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun b _ ↦
          mul_nonneg (Nat.cast_nonneg _) (sq_nonneg (y b)))).mp
        hQ a (Finset.mem_univ a)
    rcases mul_eq_zero.mp hterm with hweight | hsquare
    · exact False.elim
        ((ne_of_gt (multinomialWeight_real_pos a)) hweight)
    · exact sq_eq_zero_iff.mp hsquare
  · rintro rfl
    simp [Q]

/-- Stars and bars: the Veronese target has
`choose (n+k-1) k` coordinates.

Mathlib defines the finitely-supported antidiagonal by mapping the attached
ordinary antidiagonal.  Mapping preserves cardinality, after which its
general `finsuppAntidiag` cardinality theorem applies. -/
theorem card_multiIndex (n k : ℕ) :
    Fintype.card (MultiIndex n k) =
      Nat.choose (n + k - 1) k := by
  calc
    Fintype.card (MultiIndex n k) =
        (Finset.piAntidiag
          (Finset.univ : Finset (Fin n)) k).card := by
      simp [MultiIndex, multiIndexFinset]
    _ =
        (Finset.finsuppAntidiag
          (Finset.univ : Finset (Fin n)) k).card := by
      simp [Finset.finsuppAntidiag]
    _ =
        ((Finset.univ : Finset (Fin n)).card + k - 1).choose k :=
      Finset.card_finsuppAntidiag_nat_eq_choose k
    _ = Nat.choose (n + k - 1) k := by
      simp

end HGAS.Veronese
