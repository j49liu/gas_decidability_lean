import HGAS.Veronese.Map
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

/-!
# Quadratic relations of the Veronese map

Let `Aₖ` be the finite set of multiindices of total degree `k`.  The
coordinate ring of the degree-`k` Veronese map has one variable `Y_a` for
each `a ∈ Aₖ`.  Whenever

```
a + b = c + d
```

coordinatewise, the quadratic binomial

```
Y_a Y_b - Y_c Y_d
```

vanishes after the substitution `Y_a = x^a`.  This file packages **all**
such balanced quadruples as a finite type.  Thus it gives a concrete finite
family, rather than making a nonconstructive choice of generators.

Two versions of the construction are useful:

* `toricBinomial r` is the literal polynomial over `ℚ`;
* `toricRelation r y` evaluates the same expression in an arbitrary
  commutative ring.

Their sum-of-squares penalty is

```
toricPenalty y = ∑ r, toricRelation r y ^ 2.
```

The polynomial itself is `toricPenaltyPolynomial`.  We prove that the
relations are homogeneous quadratic polynomials and that their penalty is
homogeneous quartic.  Over `ℝ`, nonnegativity of squares gives the exact
zero-set statement

```
toricPenalty y = 0 ↔ every indexed relation vanishes at y.
```

We also prove that every Veronese point, and its negative, lies in this
zero set.  This is the elementary inclusion needed in equations
(15.4)--(15.6) of the paper.

## Deliberate boundary

No converse parametrization of the real zero set is asserted here.  The
claim that every nonzero real common zero is a scalar Veronese point is the
substantive real-cone theorem; it requires additional projective or toric
geometry beyond the algebraic identities proved in this module.
-/

namespace HGAS.Veronese

open scoped BigOperators

variable {n k : ℕ}

/-- An index for one quadratic Veronese relation.

The proof field says exactly that the two products have the same exponent
vector after substitution by Veronese monomials.  Since `MultiIndex n k`
is finite and the balancing condition is decidable, the complete family of
these indices is finite as well. -/
@[ext]
structure ToricRelationIndex (n k : ℕ) where
  alpha : MultiIndex n k
  beta : MultiIndex n k
  gamma : MultiIndex n k
  delta : MultiIndex n k
  balanced :
    ∀ i, alpha.1 i + beta.1 i = gamma.1 i + delta.1 i
deriving DecidableEq, Fintype

/-- The explicit finite set indexing all balanced quadratic relations. -/
def toricRelationIndices (n k : ℕ) :
    Finset (ToricRelationIndex n k) :=
  Finset.univ

@[simp]
theorem mem_toricRelationIndices (r : ToricRelationIndex n k) :
    r ∈ toricRelationIndices n k := by
  simp [toricRelationIndices]

/-- Evaluation of the quadratic binomial belonging to `r`.

This definition works over an arbitrary commutative ring, so the same
identity can be reused for exact rational calculations and for real
dynamics. -/
def toricRelation {R : Type*} [CommRing R]
    (r : ToricRelationIndex n k) (y : MultiIndex n k → R) : R :=
  y r.alpha * y r.beta - y r.gamma * y r.delta

/-- The literal quadratic binomial over `ℚ`.

Its four coefficients are `1, 1, -1, -1` after multiplying the indicated
variables, so this is an exact rational polynomial rather than merely a
pointwise function. -/
noncomputable def toricBinomial (r : ToricRelationIndex n k) :
    MvPolynomial (MultiIndex n k) ℚ :=
  MvPolynomial.X r.alpha * MvPolynomial.X r.beta -
    MvPolynomial.X r.gamma * MvPolynomial.X r.delta

/-- Evaluating the rational polynomial gives the pointwise relation. -/
theorem eval_toricBinomial
    (r : ToricRelationIndex n k) (y : MultiIndex n k → ℚ) :
    MvPolynomial.eval y (toricBinomial r) = toricRelation r y := by
  simp [toricBinomial, toricRelation]

/-- Every indexed binomial is homogeneous of degree two. -/
theorem toricBinomial_isHomogeneous (r : ToricRelationIndex n k) :
    (toricBinomial r).IsHomogeneous 2 := by
  unfold toricBinomial
  have hl :=
    (MvPolynomial.isHomogeneous_X (R := ℚ) r.alpha).mul
      (MvPolynomial.isHomogeneous_X (R := ℚ) r.beta)
  have hr :=
    (MvPolynomial.isHomogeneous_X (R := ℚ) r.gamma).mul
      (MvPolynomial.isHomogeneous_X (R := ℚ) r.delta)
  norm_num at hl hr ⊢
  exact hl.sub hr

/-- Every Veronese point annihilates every balanced quadratic relation.

Both products become

```
∏ i, x_i ^ (alpha_i + beta_i),
```

and `r.balanced` identifies the two exponent vectors. -/
@[simp]
theorem toricRelation_veronese
    {R : Type*} [CommRing R]
    (r : ToricRelationIndex n k) (x : Fin n → R) :
    toricRelation r (veroneseMap (k := k) x) = 0 := by
  simp only [toricRelation, veroneseMap_apply]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply sub_eq_zero.mpr
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_add, ← pow_add, r.balanced i]

/-- A quadratic relation is unchanged when every coordinate is negated. -/
@[simp]
theorem toricRelation_neg
    {R : Type*} [CommRing R]
    (r : ToricRelationIndex n k) (y : MultiIndex n k → R) :
    toricRelation r (-y) = toricRelation r y := by
  simp only [toricRelation, Pi.neg_apply]
  ring

/-- Consequently the negative of every Veronese point also annihilates
every indexed relation. -/
@[simp]
theorem toricRelation_neg_veronese
    {R : Type*} [CommRing R]
    (r : ToricRelationIndex n k) (x : Fin n → R) :
    toricRelation r (-veroneseMap (k := k) x) = 0 := by
  simp

/-- Each relation has scaling degree two in the ambient coordinates. -/
theorem toricRelation_smul
    {R : Type*} [CommRing R]
    (r : ToricRelationIndex n k) (c : R)
    (y : MultiIndex n k → R) :
    toricRelation r (c • y) = c ^ 2 * toricRelation r y := by
  simp only [toricRelation, Pi.smul_apply, smul_eq_mul]
  ring

/-- The finite sum-of-squares penalty from equation (15.5).

We sum over all balanced quadruples.  This may contain redundant or trivial
relations, but it is finite, explicit, and has exactly the same common zero
set as the complete quadratic family. -/
def toricPenalty {R : Type*} [CommRing R]
    (y : MultiIndex n k → R) : R :=
  ∑ r : ToricRelationIndex n k, toricRelation r y ^ 2

/-- The same penalty as a polynomial with rational coefficients. -/
noncomputable def toricPenaltyPolynomial (n k : ℕ) :
    MvPolynomial (MultiIndex n k) ℚ :=
  ∑ r : ToricRelationIndex n k, toricBinomial r ^ 2

/-- Evaluation of the rational sum-of-squares polynomial agrees with the
pointwise rational penalty. -/
theorem eval_toricPenaltyPolynomial (y : MultiIndex n k → ℚ) :
    MvPolynomial.eval y (toricPenaltyPolynomial n k) =
      toricPenalty y := by
  simp [toricPenaltyPolynomial, toricPenalty, eval_toricBinomial]

/-- The rational penalty is homogeneous of degree four. -/
theorem toricPenaltyPolynomial_isHomogeneous (n k : ℕ) :
    (toricPenaltyPolynomial n k).IsHomogeneous 4 := by
  unfold toricPenaltyPolynomial
  refine MvPolynomial.IsHomogeneous.sum Finset.univ
    (fun r ↦ toricBinomial r ^ 2) 4 ?_
  intro r _
  simpa using (toricBinomial_isHomogeneous r).pow 2

/-- Function-level quartic scaling of the sum-of-squares penalty. -/
theorem toricPenalty_smul
    {R : Type*} [CommRing R]
    (c : R) (y : MultiIndex n k → R) :
    toricPenalty (c • y) = c ^ 4 * toricPenalty y := by
  simp only [toricPenalty, toricRelation_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- The penalty vanishes on every Veronese point. -/
@[simp]
theorem toricPenalty_veronese
    {R : Type*} [CommRing R] (x : Fin n → R) :
    toricPenalty (veroneseMap (k := k) x) = 0 := by
  simp [toricPenalty]

/-- The penalty also vanishes on the negative Veronese sheet. -/
@[simp]
theorem toricPenalty_neg_veronese
    {R : Type*} [CommRing R] (x : Fin n → R) :
    toricPenalty (-veroneseMap (k := k) x) = 0 := by
  simp [toricPenalty]

/-- The algebraic zero set cut out by the complete finite quadratic family.

This is the set denoted `𝒱` in equation (15.6).  Calling it a zero set is
intentional: this definition by itself does not assert the hard converse
that its real points possess a Veronese parametrization. -/
def toricZeroSet {R : Type*} [CommRing R] (n k : ℕ) :
    Set (MultiIndex n k → R) :=
  {y | ∀ r : ToricRelationIndex n k, toricRelation r y = 0}

theorem mem_toricZeroSet_iff
    {R : Type*} [CommRing R] (y : MultiIndex n k → R) :
    y ∈ toricZeroSet (R := R) n k ↔
      ∀ r : ToricRelationIndex n k, toricRelation r y = 0 :=
  Iff.rfl

/-- The quadratic zero set contains the image of the Veronese map. -/
theorem veronese_mem_toricZeroSet
    {R : Type*} [CommRing R] (x : Fin n → R) :
    veroneseMap (k := k) x ∈ toricZeroSet (R := R) n k := by
  intro r
  exact toricRelation_veronese r x

/-- The quadratic zero set also contains the negative Veronese image. -/
theorem neg_veronese_mem_toricZeroSet
    {R : Type*} [CommRing R] (x : Fin n → R) :
    -veroneseMap (k := k) x ∈ toricZeroSet (R := R) n k := by
  intro r
  exact toricRelation_neg_veronese r x

/-- The common zero set is a cone: it is closed under scalar
multiplication. -/
theorem smul_mem_toricZeroSet
    {R : Type*} [CommRing R]
    {y : MultiIndex n k → R}
    (hy : y ∈ toricZeroSet (R := R) n k) (c : R) :
    c • y ∈ toricZeroSet (R := R) n k := by
  intro r
  rw [toricRelation_smul, hy r, mul_zero]

/-- Over the reals the penalty is nonnegative, because it is a finite sum
of ordinary squares. -/
theorem toricPenalty_nonneg_real (y : MultiIndex n k → ℝ) :
    0 ≤ toricPenalty y := by
  exact Finset.sum_nonneg fun r _ ↦ sq_nonneg (toricRelation r y)

/-- Over the reals, the penalty vanishes exactly when every one of the
finitely indexed quadratic relations vanishes. -/
theorem toricPenalty_eq_zero_iff_real (y : MultiIndex n k → ℝ) :
    toricPenalty y = 0 ↔
      ∀ r : ToricRelationIndex n k, toricRelation r y = 0 := by
  constructor
  · intro h r
    have hsquare : toricRelation r y ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun s _ ↦ sq_nonneg (toricRelation s y))).mp
        h r (Finset.mem_univ r)
    exact sq_eq_zero_iff.mp hsquare
  · intro h
    simp only [toricPenalty]
    apply Finset.sum_eq_zero
    intro r _
    rw [h r]
    norm_num

/-- Set-theoretic form of the real zero-set characterization. -/
theorem toricPenalty_eq_zero_iff_mem_toricZeroSet_real
    (y : MultiIndex n k → ℝ) :
    toricPenalty y = 0 ↔ y ∈ toricZeroSet (R := ℝ) n k :=
  toricPenalty_eq_zero_iff_real y

/-- The intersection `𝒱 ∩ S_Q` from equation (15.6). -/
def toricSphereZeroSet (n k : ℕ) :
    Set (MultiIndex n k → ℝ) :=
  {y | y ∈ toricZeroSet (R := ℝ) n k ∧ Q y = 1}

theorem mem_toricSphereZeroSet_iff (y : MultiIndex n k → ℝ) :
    y ∈ toricSphereZeroSet n k ↔
      y ∈ toricZeroSet (R := ℝ) n k ∧ Q y = 1 :=
  Iff.rfl

/-- A unit vector maps into the normalized quadratic zero set.

This is the forward inclusion in the real-sheet statement and uses only
the multinomial normalization `Q(νₖ(x)) = (∑ xᵢ²)^k`. -/
theorem veronese_mem_toricSphereZeroSet_of_unit
    (x : Fin n → ℝ) (hunit : ∑ i, x i ^ 2 = 1) :
    veroneseMap (k := k) x ∈ toricSphereZeroSet n k := by
  constructor
  · exact veronese_mem_toricZeroSet x
  · rw [Q_veroneseMap, hunit]
    simp

/-- The negative of a unit Veronese point lies on the other possible
normalized sheet. -/
theorem neg_veronese_mem_toricSphereZeroSet_of_unit
    (x : Fin n → ℝ) (hunit : ∑ i, x i ^ 2 = 1) :
    -veroneseMap (k := k) x ∈ toricSphereZeroSet n k := by
  constructor
  · exact neg_veronese_mem_toricZeroSet x
  · calc
      Q (-veroneseMap (k := k) x) =
          Q (veroneseMap (k := k) x) := by
        simp [Q]
      _ = (∑ i, x i ^ 2) ^ k := Q_veroneseMap x
      _ = 1 := by rw [hunit]; simp

end HGAS.Veronese
