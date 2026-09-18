import HGAS.Veronese.Map
import Mathlib.Tactic

/-!
# Differential and weighted geometry of the Veronese map

This module develops the differential algebra used after the normalization
`Q(νₖ(x)) = (∑ᵢ xᵢ²)^k`.

For a multiindex `a`, the coordinate formula is

```
(Dνₖ(x) h)ₐ =
  ∑ i, aᵢ hᵢ xᵢ^(aᵢ-1) ∏_{j ≠ i} xⱼ^aⱼ.
```

The factor `aᵢ` makes this formula valid even when `aᵢ = 0`, without
division or a nonzero-coordinate hypothesis.  We prove its linearity in
`h` and the Euler identity

```
Dνₖ(x) x = k • νₖ(x).
```

The second half formalizes the diagonal metric defined by the multinomial
weights.  It gives:

* the weighted inner product and norm-square whose quadratic form is `Q`;
* the exact first-order differential and quadratic expansion of `Q`;
* the ambient weighted gradient `M⁻¹ ∇W` over `ℝ`;
* orthogonal projection to `Q(y)=1`;
* the quartic specializations
  `grad_S W = grad_Q W - 4 W y` and
  `‖grad_S W‖_Q² = ‖grad_Q W‖_Q² - 16 W²`.

The last two statements assume the quartic Euler identity
`y · ∇W = 4W`.  They are precisely the pointwise algebra in
equations (15.8)--(15.10); no toric-ideal or real-cone theorem is needed.
-/

namespace HGAS.Veronese

open scoped BigOperators

variable {n k : ℕ}

/-! ## Coordinate differential of the Veronese map -/

/-- Formal directional derivative of one Veronese monomial.

The product over `univ.erase i` is the product over all coordinates other
than `i`.  When `aᵢ = 0`, the coefficient `aᵢ` kills the corresponding
summand. -/
def dMonomial {R : Type*} [CommSemiring R]
    (x h : Fin n → R) (a : MultiIndex n k) : R :=
  ∑ i,
    (a.1 i : R) * h i * x i ^ (a.1 i - 1) *
      (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
        x j ^ a.1 j)

/-- Coordinate definition of `Dνₖ(x) h`. -/
def dVeronese {R : Type*} [CommSemiring R]
    (x h : Fin n → R) : MultiIndex n k → R :=
  fun a ↦ dMonomial x h a

@[simp]
theorem dVeronese_apply {R : Type*} [CommSemiring R]
    (x h : Fin n → R) (a : MultiIndex n k) :
    dVeronese x h a =
      ∑ i,
        (a.1 i : R) * h i * x i ^ (a.1 i - 1) *
          (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
            x j ^ a.1 j) :=
  rfl

theorem dMonomial_add {R : Type*} [CommSemiring R]
    (x h₁ h₂ : Fin n → R) (a : MultiIndex n k) :
    dMonomial x (h₁ + h₂) a =
      dMonomial x h₁ a + dMonomial x h₂ a := by
  simp only [dMonomial, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem dMonomial_smul {R : Type*} [CommSemiring R]
    (c : R) (x h : Fin n → R) (a : MultiIndex n k) :
    dMonomial x (c • h) a = c * dMonomial x h a := by
  simp only [dMonomial, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- `Dνₖ(x)` is additive in its direction argument. -/
theorem dVeronese_add {R : Type*} [CommSemiring R]
    (x h₁ h₂ : Fin n → R) :
    dVeronese (k := k) x (h₁ + h₂) =
      dVeronese (k := k) x h₁ +
        dVeronese (k := k) x h₂ := by
  funext a
  exact dMonomial_add x h₁ h₂ a

/-- `Dνₖ(x)` commutes with scalar multiplication in its direction
argument. -/
theorem dVeronese_smul {R : Type*} [CommSemiring R]
    (c : R) (x h : Fin n → R) :
    dVeronese (k := k) x (c • h) =
      c • dVeronese (k := k) x h := by
  funext a
  exact dMonomial_smul c x h a

/-- One summand in the radial differential equals `aᵢ` times the full
monomial.  The proof separates the harmless case `aᵢ=0` from the successor
case and uses `Finset.mul_prod_erase`. -/
theorem dMonomial_self_summand {R : Type*} [CommSemiring R]
    (x : Fin n → R) (a : MultiIndex n k) (i : Fin n) :
    (a.1 i : R) * x i * x i ^ (a.1 i - 1) *
        (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          x j ^ a.1 j) =
      (a.1 i : R) * monomial x a := by
  rcases h : a.1 i with _ | m
  · simp
  · simp only [Nat.succ_sub_one]
    have hp :=
      Finset.mul_prod_erase
        (Finset.univ : Finset (Fin n))
        (fun j ↦ x j ^ a.1 j) (Finset.mem_univ i)
    simp only [h] at hp
    calc
      ((m + 1 : ℕ) : R) * x i * x i ^ m *
          (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
            x j ^ a.1 j) =
        ((m + 1 : ℕ) : R) *
          (x i ^ (m + 1) *
            (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
              x j ^ a.1 j)) := by
                rw [pow_succ]
                ring
      _ = ((m + 1 : ℕ) : R) * monomial x a := by
        rw [hp]
        rfl

/-- Coordinate form of Euler's identity for a degree-`k` monomial. -/
theorem dMonomial_self {R : Type*} [CommSemiring R]
    (x : Fin n → R) (a : MultiIndex n k) :
    dMonomial x x a = k • monomial x a := by
  simp only [dMonomial]
  rw [Finset.sum_congr rfl
    (fun i _ ↦ dMonomial_self_summand x a i)]
  rw [← Finset.sum_mul]
  rw [← Nat.cast_sum]
  rw [multiIndex_degree a]
  simp [nsmul_eq_mul]

/-- Euler identity for the whole unscaled Veronese map:
`Dνₖ(x) x = k • νₖ(x)`. -/
theorem dVeronese_self {R : Type*} [CommSemiring R]
    (x : Fin n → R) :
    dVeronese (k := k) x x =
      k • veroneseMap (k := k) x := by
  funext a
  exact dMonomial_self x a

/-! ## Multinomially weighted metric and the differential of `Q` -/

/-- Bilinear form whose diagonal coefficients are the multinomial weights
of `Q`. -/
def weightedInner {R : Type*} [CommSemiring R]
    (u v : MultiIndex n k → R) : R :=
  ∑ a, (multinomialWeight a : R) * u a * v a

/-- Algebraic weighted norm-square. -/
def weightedNormSq {R : Type*} [CommSemiring R]
    (u : MultiIndex n k → R) : R :=
  weightedInner u u

theorem weightedInner_comm {R : Type*} [CommSemiring R]
    (u v : MultiIndex n k → R) :
    weightedInner u v = weightedInner v u := by
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem weightedInner_add_right {R : Type*} [CommSemiring R]
    (u v w : MultiIndex n k → R) :
    weightedInner u (v + w) =
      weightedInner u v + weightedInner u w := by
  simp only [weightedInner, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]

theorem weightedInner_smul_right {R : Type*} [CommSemiring R]
    (c : R) (u v : MultiIndex n k → R) :
    weightedInner u (c • v) = c * weightedInner u v := by
  simp only [weightedInner, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ac_rfl

theorem weightedInner_sub_right {R : Type*} [CommRing R]
    (u v w : MultiIndex n k → R) :
    weightedInner u (v - w) =
      weightedInner u v - weightedInner u w := by
  simp only [weightedInner, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib]

/-- The metric norm-square is exactly the quadratic form `Q`. -/
theorem weightedInner_self {R : Type*} [CommSemiring R]
    (u : MultiIndex n k → R) :
    weightedInner u u = Q u := by
  simp only [weightedInner, Q]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The named norm-square is exactly `Q`. -/
@[simp]
theorem weightedNormSq_eq_Q {R : Type*} [CommSemiring R]
    (u : MultiIndex n k → R) :
    weightedNormSq u = Q u :=
  weightedInner_self u

/-- Coordinate formula for the first-order differential of `Q`. -/
def QDifferential {R : Type*} [CommSemiring R]
    (y h : MultiIndex n k → R) : R :=
  ∑ a, 2 * (multinomialWeight a : R) * y a * h a

theorem QDifferential_eq_two_weightedInner
    {R : Type*} [CommSemiring R]
    (y h : MultiIndex n k → R) :
    QDifferential y h = 2 * weightedInner y h := by
  simp only [QDifferential, weightedInner, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The exact quadratic expansion proves algebraically that
`QDifferential y` is the first-order differential of `Q`. -/
theorem Q_add_smul_expansion
    {R : Type*} [CommSemiring R]
    (t : R) (y h : MultiIndex n k → R) :
    Q (y + t • h) =
      Q y + t * QDifferential y h + t ^ 2 * Q h := by
  simp only [Q, QDifferential, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [show
    (∑ a, (multinomialWeight a : R) *
        (y a + t * h a) ^ 2) =
      ∑ a,
        ((multinomialWeight a : R) * y a ^ 2 +
          t * (2 * (multinomialWeight a : R) * y a * h a) +
          t ^ 2 * ((multinomialWeight a : R) * h a ^ 2)) by
    apply Finset.sum_congr rfl
    intro a _
    ring]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]

/-- Radial Euler identity for the quadratic form. -/
theorem QDifferential_self {R : Type*} [CommSemiring R]
    (y : MultiIndex n k → R) :
    QDifferential y y = 2 * Q y := by
  rw [QDifferential_eq_two_weightedInner, weightedInner_self]

/-- A direction is tangent to a level set of `Q` when its first-order
`Q`-variation vanishes. -/
def IsQTangent {R : Type*} [CommSemiring R]
    (y h : MultiIndex n k → R) : Prop :=
  QDifferential y h = 0

theorem isQTangent_iff_weightedOrthogonal_real
    (y h : MultiIndex n k → ℝ) :
    IsQTangent y h ↔ weightedInner y h = 0 := by
  rw [IsQTangent, QDifferential_eq_two_weightedInner]
  constructor
  · intro hzero
    linarith
  · intro hzero
    rw [hzero]
    ring

/-! ## Ambient and spherical weighted gradients -/

/-- Ordinary coordinate dot product on Veronese coordinate space. -/
def coordinateDot
    (u v : MultiIndex n k → ℝ) : ℝ :=
  ∑ a, u a * v a

/-- Equation (15.8).  If `g` is the ordinary coordinate gradient
`∇W`, dividing coordinate `a` by its positive multinomial weight gives
the gradient for the `Q` metric, `M⁻¹ ∇W`. -/
noncomputable def ambientQGradient
    (g : MultiIndex n k → ℝ) : MultiIndex n k → ℝ :=
  fun a ↦ g a / (multinomialWeight a : ℝ)

@[simp]
theorem ambientQGradient_apply
    (g : MultiIndex n k → ℝ) (a : MultiIndex n k) :
    ambientQGradient g a =
      g a / (multinomialWeight a : ℝ) :=
  rfl

/-- The coordinate formula really represents the metric gradient:
pairing `M⁻¹g` with `h` in the `Q` metric gives the ordinary coordinate
pairing of `g` with `h`. -/
theorem weightedInner_ambientQGradient
    (g h : MultiIndex n k → ℝ) :
    weightedInner (ambientQGradient g) h =
      coordinateDot g h := by
  apply Finset.sum_congr rfl
  intro a _
  have hweight :
      (multinomialWeight a : ℝ) ≠ 0 :=
    ne_of_gt (multinomialWeight_real_pos a)
  simp only [ambientQGradient]
  field_simp

theorem weightedInner_left_ambientQGradient
    (y g : MultiIndex n k → ℝ) :
    weightedInner y (ambientQGradient g) =
      coordinateDot y g := by
  rw [weightedInner_comm, weightedInner_ambientQGradient]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Orthogonal projection of an ambient vector onto the tangent hyperplane
to the unit `Q`-sphere at `y`. -/
def tangentialProjection {R : Type*} [CommRing R]
    (y g : MultiIndex n k → R) : MultiIndex n k → R :=
  g - weightedInner y g • y

/-- The projected vector is `Q`-orthogonal to `y` on `Q(y)=1`. -/
theorem weightedInner_tangentialProjection
    {R : Type*} [CommRing R]
    (y g : MultiIndex n k → R) (hQ : Q y = 1) :
    weightedInner y (tangentialProjection y g) = 0 := by
  rw [tangentialProjection, weightedInner_sub_right,
    weightedInner_smul_right, weightedInner_self, hQ]
  ring

/-- General Pythagorean identity for the tangent projection. -/
theorem weightedNormSq_sub_smul
    {R : Type*} [CommRing R]
    (y g : MultiIndex n k → R) (c : R) :
    weightedNormSq (g - c • y) =
      weightedNormSq g -
        2 * c * weightedInner y g +
        c ^ 2 * weightedNormSq y := by
  simp only [weightedNormSq, weightedInner, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [show
    (∑ a, (multinomialWeight a : R) *
        (g a - c * y a) * (g a - c * y a)) =
      ∑ a,
        ((multinomialWeight a : R) * g a * g a -
          2 * c *
            ((multinomialWeight a : R) * y a * g a) +
          c ^ 2 *
            ((multinomialWeight a : R) * y a * y a)) by
    apply Finset.sum_congr rfl
    intro a _
    ring]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]

theorem weightedNormSq_tangentialProjection
    {R : Type*} [CommRing R]
    (y g : MultiIndex n k → R) (hQ : Q y = 1) :
    weightedNormSq (tangentialProjection y g) =
      weightedNormSq g - weightedInner y g ^ 2 := by
  have hy : weightedNormSq y = 1 := by
    rw [weightedNormSq_eq_Q, hQ]
  rw [tangentialProjection, weightedNormSq_sub_smul, hy]
  ring

/-- Equation (15.9), written from an ordinary gradient `g = ∇W` and the
scalar value `W(y)`. -/
noncomputable def quarticSphereGradient
    (y : MultiIndex n k → ℝ) (W : ℝ)
    (g : MultiIndex n k → ℝ) : MultiIndex n k → ℝ :=
  ambientQGradient g - (4 * W) • y

/-- Euler's identity converts the displayed formula `grad_Q W - 4Wy`
into the ordinary orthogonal tangent projection. -/
theorem quarticSphereGradient_eq_tangentialProjection
    (y : MultiIndex n k → ℝ) (W : ℝ)
    (g : MultiIndex n k → ℝ)
    (hEuler : coordinateDot y g = 4 * W) :
    quarticSphereGradient y W g =
      tangentialProjection y (ambientQGradient g) := by
  rw [quarticSphereGradient, tangentialProjection,
    weightedInner_left_ambientQGradient, hEuler]

/-- Equation (15.9) is tangent to the unit `Q`-sphere. -/
theorem weightedInner_quarticSphereGradient
    (y : MultiIndex n k → ℝ) (W : ℝ)
    (g : MultiIndex n k → ℝ)
    (hQ : Q y = 1)
    (hEuler : coordinateDot y g = 4 * W) :
    weightedInner y (quarticSphereGradient y W g) = 0 := by
  rw [quarticSphereGradient, weightedInner_sub_right,
    weightedInner_smul_right,
    weightedInner_left_ambientQGradient, hEuler,
    weightedInner_self, hQ]
  ring

/-- Differential form of tangency for equation (15.9). -/
theorem quarticSphereGradient_isQTangent
    (y : MultiIndex n k → ℝ) (W : ℝ)
    (g : MultiIndex n k → ℝ)
    (hQ : Q y = 1)
    (hEuler : coordinateDot y g = 4 * W) :
    IsQTangent y (quarticSphereGradient y W g) := by
  rw [isQTangent_iff_weightedOrthogonal_real]
  exact weightedInner_quarticSphereGradient y W g hQ hEuler

/-- Equation (15.10):
`‖grad_{S_Q} W‖_Q² = ‖grad_Q W‖_Q² - 16W²`. -/
theorem weightedNormSq_quarticSphereGradient
    (y : MultiIndex n k → ℝ) (W : ℝ)
    (g : MultiIndex n k → ℝ)
    (hQ : Q y = 1)
    (hEuler : coordinateDot y g = 4 * W) :
    weightedNormSq (quarticSphereGradient y W g) =
      weightedNormSq (ambientQGradient g) - 16 * W ^ 2 := by
  have hy : weightedNormSq y = 1 := by
    rw [weightedNormSq_eq_Q, hQ]
  rw [quarticSphereGradient, weightedNormSq_sub_smul,
    weightedInner_left_ambientQGradient, hEuler, hy]
  ring

/-- The ambient gradient splits into its spherical part and the quartic
normal component. -/
theorem ambientQGradient_decomposition
    (y : MultiIndex n k → ℝ) (W : ℝ)
    (g : MultiIndex n k → ℝ) :
    ambientQGradient g =
      quarticSphereGradient y W g + (4 * W) • y := by
  funext a
  simp [quarticSphereGradient]

end HGAS.Veronese
