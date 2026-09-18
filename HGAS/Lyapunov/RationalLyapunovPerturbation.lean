import HGAS.Analysis.RationalPolynomialApproximation
import HGAS.Lyapunov.RationalCertificateAlgebra
import Mathlib.Tactic

/-!
# Rational perturbation of a real Lyapunov numerator

The homogeneous converse Lyapunov theorem naturally returns a polynomial
`p` with real coefficients.  The certificate search in this development
enumerates rational polynomials, so one must prove that rationalizing the
coefficients does not destroy either of the two strict inequalities

```
p(x) > 0,
q(F,p,r)(x) > 0
```

on the unit sphere.  Here

```
q(F,p,r) = -ρ (∇p · F) + 2r p (x · F)
```

is the numerator of `-d(p/ρ^r)/dt`.

This file supplies that bridge without appealing to an abstract
finite-dimensional topology.  The proof is quantitative and elementary:

1. define the real-coefficient version of every polynomial in the displayed
   formula and prove that coefficient embedding `ℚ → ℝ` commutes with the
   whole construction;
2. use compactness of the unit sphere to obtain positive margins `εV` and
   `εQ`;
3. expand `p` in its finite monomial support;
4. for every supported monomial `X^e`, bound the unit-cube response
   `q(F,X^e,r)` by the sum of the absolute values of its rational
   coefficients;
5. approximate every coefficient of `p` by a rational within one common
   tolerance.  The tolerance is divided by the finite sum of all response
   bounds, so both total errors are smaller than
   `min εV εQ`.

Because no new monomial is introduced, homogeneity is preserved exactly.
The final theorem
`exists_rational_homogeneous_lyapunov_perturbation` is the precise
rational-coefficient bridge required after a real converse Lyapunov
witness has been obtained.
-/

namespace HGAS

open MvPolynomial
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- A polynomial vector field with real coefficients.  This mirrors
`PolynomialField`, whose coefficients are rational. -/
abbrev RealPolynomialField (n : ℕ) :=
  Fin n → MvPolynomial (Fin n) ℝ

/-- Embed every coefficient of a rational polynomial field into `ℝ`. -/
def realPolynomialFieldOfRational
    (F : PolynomialField n) : RealPolynomialField n :=
  fun i => MvPolynomial.map (algebraMap ℚ ℝ) (F i)

/-- The real-coefficient radial form `ρ = ∑ᵢ Xᵢ²`. -/
def realRhoPolynomial : MvPolynomial (Fin n) ℝ :=
  ∑ i, X i ^ 2

/-- The real polynomial `∇p · F`. -/
def realGradientDotField
    (p : MvPolynomial (Fin n) ℝ) (F : RealPolynomialField n) :
    MvPolynomial (Fin n) ℝ :=
  ∑ i, pderiv i p * F i

/-- The real polynomial `x · F(x)`. -/
def realRadialDotPolynomial
    (F : RealPolynomialField n) :
    MvPolynomial (Fin n) ℝ :=
  ∑ i, X i * F i

/-- Real-coefficient analogue of `rationalLyapunovNumerator`.

It represents the numerator of `-d(p/ρ^r)/dt`. -/
def realRationalLyapunovNumerator
    (F : RealPolynomialField n)
    (p : MvPolynomial (Fin n) ℝ) (r : ℕ) :
    MvPolynomial (Fin n) ℝ :=
  -(realRhoPolynomial * realGradientDotField p F) +
    C (2 * (r : ℝ)) * p * realRadialDotPolynomial F

/-- Coefficient embedding commutes with the radial polynomial. -/
@[simp]
theorem map_rhoPolynomial :
    MvPolynomial.map (algebraMap ℚ ℝ)
        (rhoPolynomial (n := n)) =
      realRhoPolynomial := by
  simp [rhoPolynomial, realRhoPolynomial]

/-- Coefficient embedding commutes with the formal directional
derivative. -/
@[simp]
theorem map_gradientDotField
    (F : PolynomialField n)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.map (algebraMap ℚ ℝ)
        (gradientDotField p F) =
      realGradientDotField
        (MvPolynomial.map (algebraMap ℚ ℝ) p)
        (realPolynomialFieldOfRational F) := by
  simp [gradientDotField, realGradientDotField,
    realPolynomialFieldOfRational, MvPolynomial.pderiv_map]

/-- Coefficient embedding commutes with the radial dot polynomial. -/
@[simp]
theorem map_radialDotPolynomial
    (F : PolynomialField n) :
    MvPolynomial.map (algebraMap ℚ ℝ)
        (radialDotPolynomial F) =
      realRadialDotPolynomial
        (realPolynomialFieldOfRational F) := by
  simp [radialDotPolynomial, realRadialDotPolynomial,
    realPolynomialFieldOfRational]

/-- Coefficient embedding commutes with the complete Lyapunov decay
numerator. -/
@[simp]
theorem map_rationalLyapunovNumerator
    (F : PolynomialField n)
    (p : MvPolynomial (Fin n) ℚ) (r : ℕ) :
    MvPolynomial.map (algebraMap ℚ ℝ)
        (rationalLyapunovNumerator F p r) =
      realRationalLyapunovNumerator
        (realPolynomialFieldOfRational F)
        (MvPolynomial.map (algebraMap ℚ ℝ) p) r := by
  simp [rationalLyapunovNumerator,
    realRationalLyapunovNumerator]

/-- For fixed `F` and `r`, the real decay-numerator construction is
additive in `p`. -/
theorem realRationalLyapunovNumerator_add
    (F : RealPolynomialField n)
    (p q : MvPolynomial (Fin n) ℝ) (r : ℕ) :
    realRationalLyapunovNumerator F (p + q) r =
      realRationalLyapunovNumerator F p r +
        realRationalLyapunovNumerator F q r := by
  simp only [realRationalLyapunovNumerator,
    realGradientDotField, map_add, add_mul, mul_add,
    Finset.sum_add_distrib]
  ring

/-- The real decay-numerator construction sends zero to zero. -/
@[simp]
theorem realRationalLyapunovNumerator_zero
    (F : RealPolynomialField n) (r : ℕ) :
    realRationalLyapunovNumerator F 0 r = 0 := by
  simp [realRationalLyapunovNumerator, realGradientDotField]

/-- The decay-numerator construction bundled as an additive homomorphism.
This lets finite monomial sums be mapped without repeating an induction. -/
def realRationalLyapunovNumeratorAddHom
    (F : RealPolynomialField n) (r : ℕ) :
    MvPolynomial (Fin n) ℝ →+
      MvPolynomial (Fin n) ℝ where
  toFun := fun p ↦ realRationalLyapunovNumerator F p r
  map_zero' := realRationalLyapunovNumerator_zero F r
  map_add' := fun p q ↦
    realRationalLyapunovNumerator_add F p q r

/-- For fixed `F` and `r`, the decay-numerator construction is linear with
respect to real constant coefficients. -/
theorem realRationalLyapunovNumerator_C_mul
    (F : RealPolynomialField n)
    (c : ℝ) (p : MvPolynomial (Fin n) ℝ) (r : ℕ) :
    realRationalLyapunovNumerator F (C c * p) r =
      C c * realRationalLyapunovNumerator F p r := by
  simp only [realRationalLyapunovNumerator,
    realGradientDotField, pderiv_C_mul]
  have hgrad :
      (∑ i, C c * pderiv i p * F i) =
        C c * ∑ i, pderiv i p * F i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hgrad]
  ring

/-- Response of the real decay operator to one scalar monomial.  The unit
monomial response is rational and is embedded only after it is computed. -/
theorem realRationalLyapunovNumerator_monomial
    (F : PolynomialField n)
    (e : Fin n →₀ ℕ) (c : ℝ) (r : ℕ) :
    realRationalLyapunovNumerator
        (realPolynomialFieldOfRational F) (monomial e c) r =
      C c * MvPolynomial.map (algebraMap ℚ ℝ)
        (rationalLyapunovNumerator F (monomial e 1) r) := by
  calc
    realRationalLyapunovNumerator
        (realPolynomialFieldOfRational F) (monomial e c) r =
      realRationalLyapunovNumerator
        (realPolynomialFieldOfRational F)
        (C c * monomial e 1) r := by
          rw [C_mul_monomial, mul_one]
    _ = C c * realRationalLyapunovNumerator
        (realPolynomialFieldOfRational F) (monomial e 1) r :=
      realRationalLyapunovNumerator_C_mul _ _ _ _
    _ = C c * MvPolynomial.map (algebraMap ℚ ℝ)
        (rationalLyapunovNumerator F (monomial e 1) r) := by
      rw [map_rationalLyapunovNumerator]
      simp

/-- Apply the real decay operator termwise to a finite monomial sum. -/
theorem realRationalLyapunovNumerator_sum_monomial
    {ι : Type*}
    (s : Finset ι) (e : ι → Fin n →₀ ℕ) (c : ι → ℝ)
    (F : RealPolynomialField n) (r : ℕ) :
    realRationalLyapunovNumerator F
        (∑ i ∈ s, monomial (e i) (c i)) r =
      ∑ i ∈ s,
        C (c i) *
          realRationalLyapunovNumerator F (monomial (e i) 1) r := by
  classical
  change
    (realRationalLyapunovNumeratorAddHom F r)
        (∑ i ∈ s, monomial (e i) (c i)) =
      ∑ i ∈ s,
        C (c i) *
          realRationalLyapunovNumerator F (monomial (e i) 1) r
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [show monomial (e i) (c i) =
      C (c i) * monomial (e i) 1 by
    rw [C_mul_monomial, mul_one]]
  exact realRationalLyapunovNumerator_C_mul F (c i)
    (monomial (e i) 1) r

/-- Expand the decay numerator of a real polynomial over the polynomial's
finite support. -/
theorem realRationalLyapunovNumerator_support_sum
    (F : RealPolynomialField n)
    (p : MvPolynomial (Fin n) ℝ) (r : ℕ) :
    realRationalLyapunovNumerator F p r =
      ∑ e ∈ p.support,
        C (p.coeff e) *
          realRationalLyapunovNumerator F (monomial e 1) r := by
  calc
    realRationalLyapunovNumerator F p r =
        realRationalLyapunovNumerator F
          (∑ e ∈ p.support, monomial e (p.coeff e)) r := by
      rw [p.support_sum_monomial_coeff]
    _ = ∑ e ∈ p.support,
        C (p.coeff e) *
          realRationalLyapunovNumerator F (monomial e 1) r :=
      realRationalLyapunovNumerator_sum_monomial
        p.support id p.coeff F r

/-- A real polynomial which is strictly positive on the unit sphere has a
uniform positive lower margin there. -/
theorem exists_pos_lower_bound_mvPolynomial_eval_on_unitSphere
    (p : MvPolynomial (Fin n) ℝ)
    (hpos : ∀ x : Fin n → ℝ, ‖x‖ = 1 →
      0 < MvPolynomial.eval x p) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : Fin n → ℝ, ‖x‖ = 1 →
      ε ≤ MvPolynomial.eval x p := by
  obtain ⟨ε, hε, hbound⟩ :=
    (isCompact_sphere (0 : Fin n → ℝ) 1).exists_forall_le'
      (continuous_mvPolynomial_eval p).continuousOn
      (a := 0) (by
        intro x hx
        exact hpos x (by
          simpa [Metric.mem_sphere, dist_zero_right] using hx))
  refine ⟨ε, hε, ?_⟩
  intro x hx
  exact hbound x (by
    simpa [Metric.mem_sphere, dist_zero_right] using hx)

/-- Coefficient bound for the response of the Lyapunov numerator operator
to one monomial basis vector. -/
def rationalLyapunovBasisCubeBound
    (F : PolynomialField n) (r : ℕ) (e : Fin n →₀ ℕ) : ℝ :=
  polynomialCubeAbsBound
    (rationalLyapunovNumerator F (monomial e 1) r)

/-- Every monomial response bound is nonnegative. -/
theorem rationalLyapunovBasisCubeBound_nonneg
    (F : PolynomialField n) (r : ℕ) (e : Fin n →₀ ℕ) :
    0 ≤ rationalLyapunovBasisCubeBound F r e :=
  polynomialCubeAbsBound_nonneg _

/-- The value of a unit-monomial decay response on the coordinate cube is
bounded by its coefficient `ℓ¹` norm. -/
theorem abs_eval_realRationalLyapunovNumerator_monomial_one_le
    (F : PolynomialField n) (r : ℕ)
    (e : Fin n →₀ ℕ) (x : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ 1) :
    |MvPolynomial.eval x
      (realRationalLyapunovNumerator
        (realPolynomialFieldOfRational F) (monomial e 1) r)| ≤
      rationalLyapunovBasisCubeBound F r e := by
  simpa [rationalLyapunovBasisCubeBound, ratMvPolynomialEval] using
    (abs_ratMvPolynomialEval_le_cubeAbsBound
      (rationalLyapunovNumerator F (monomial e 1) r) x hx)

/-- Coefficientwise perturbations of a finite monomial sum control its
evaluation error on the coordinate unit cube. -/
theorem abs_eval_sum_monomial_sub_le
    {ι : Type*}
    (s : Finset ι) (e : ι → Fin n →₀ ℕ)
    (a b : ι → ℝ) (x : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ 1) :
    |MvPolynomial.eval x
        (∑ j ∈ s, monomial (e j) (a j)) -
      MvPolynomial.eval x
        (∑ j ∈ s, monomial (e j) (b j))| ≤
      ∑ j ∈ s, |a j - b j| := by
  classical
  simp only [map_sum, eval_monomial]
  calc
    |(∑ j ∈ s, a j * ∏ i ∈ (e j).support, x i ^ e j i) -
      ∑ j ∈ s, b j * ∏ i ∈ (e j).support, x i ^ e j i| =
        |∑ j ∈ s, (a j - b j) *
          ∏ i ∈ (e j).support, x i ^ e j i| := by
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ ≤ ∑ j ∈ s,
        |(a j - b j) *
          ∏ i ∈ (e j).support, x i ^ e j i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ s, |a j - b j| := by
      apply Finset.sum_le_sum
      intro j _hj
      rw [abs_mul]
      have hmonomial :
          |∏ i ∈ (e j).support, x i ^ e j i| ≤ 1 := by
        rw [Finset.abs_prod]
        apply Finset.prod_le_one
        · intro i _hi
          positivity
        · intro i _hi
          rw [abs_pow]
          exact pow_le_one₀ (abs_nonneg _) (hx i)
      simpa using
        (mul_le_mul_of_nonneg_left hmonomial (abs_nonneg (a j - b j)))

/-- Operator-compatible perturbation estimate.

The evaluation error after applying `q(F,·,r)` is bounded by the sum of
the coefficient errors weighted by the cube bounds of the corresponding
monomial responses. -/
theorem abs_eval_realRationalLyapunovNumerator_sum_monomial_sub_le
    {ι : Type*}
    (s : Finset ι) (e : ι → Fin n →₀ ℕ)
    (a b : ι → ℝ)
    (F : PolynomialField n) (r : ℕ)
    (x : Fin n → ℝ) (hx : ∀ i, |x i| ≤ 1) :
    |MvPolynomial.eval x
        (realRationalLyapunovNumerator
          (realPolynomialFieldOfRational F)
          (∑ j ∈ s, monomial (e j) (a j)) r) -
      MvPolynomial.eval x
        (realRationalLyapunovNumerator
          (realPolynomialFieldOfRational F)
          (∑ j ∈ s, monomial (e j) (b j)) r)| ≤
      ∑ j ∈ s,
        |a j - b j| * rationalLyapunovBasisCubeBound F r (e j) := by
  classical
  let u : ι → ℝ := fun j ↦
    MvPolynomial.eval x
      (realRationalLyapunovNumerator
        (realPolynomialFieldOfRational F) (monomial (e j) 1) r)
  rw [realRationalLyapunovNumerator_sum_monomial,
    realRationalLyapunovNumerator_sum_monomial]
  simp only [map_sum, map_mul, eval_C]
  change
    |(∑ j ∈ s, a j * u j) - ∑ j ∈ s, b j * u j| ≤
      ∑ j ∈ s,
        |a j - b j| * rationalLyapunovBasisCubeBound F r (e j)
  calc
    |(∑ j ∈ s, a j * u j) - ∑ j ∈ s, b j * u j| =
        |∑ j ∈ s, (a j - b j) * u j| := by
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ ≤ ∑ j ∈ s,
        |(a j - b j) * u j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ s,
        |a j - b j| * rationalLyapunovBasisCubeBound F r (e j) := by
      apply Finset.sum_le_sum
      intro j _hj
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (by
          dsimp only [u]
          exact
            abs_eval_realRationalLyapunovNumerator_monomial_one_le
              F r (e j) x hx)
        (abs_nonneg (a j - b j))

/-- **Rational perturbation theorem for converse Lyapunov witnesses.**

Rational coefficients can be chosen close enough to a real homogeneous
numerator that both its value and its decay numerator retain their strict
unit-sphere margins.  The output uses only monomials already present in
`p`, so its homogeneous degree remains exactly `D`.

The proof chooses a single coefficient tolerance

```
δ = min(εV, εQ) / (S + 1),
```

where `S` is the finite sum of `1` plus all monomial-response bounds.  The
extra `1` simultaneously controls the direct value error, while the
response bound controls the decay-numerator error. -/
theorem exists_rational_homogeneous_lyapunov_perturbation
    (F : PolynomialField n)
    (p : MvPolynomial (Fin n) ℝ) (r D : ℕ)
    (hp : p.IsHomogeneous D)
    (hvaluePos : ∀ x : Fin n → ℝ, ‖x‖ = 1 →
      0 < MvPolynomial.eval x p)
    (hdecayPos : ∀ x : Fin n → ℝ, ‖x‖ = 1 →
      0 < MvPolynomial.eval x
        (realRationalLyapunovNumerator
          (realPolynomialFieldOfRational F) p r)) :
    ∃ pQ : MvPolynomial (Fin n) ℚ,
      pQ.IsHomogeneous D ∧
      (∀ x : Fin n → ℝ, ‖x‖ = 1 →
        0 < ratMvPolynomialEval pQ x) ∧
      (∀ x : Fin n → ℝ, ‖x‖ = 1 →
        0 < ratMvPolynomialEval
          (rationalLyapunovNumerator F pQ r) x) := by
  obtain ⟨εV, hεV, hVmargin⟩ :=
    exists_pos_lower_bound_mvPolynomial_eval_on_unitSphere p hvaluePos
  obtain ⟨εQ, hεQ, hQmargin⟩ :=
    exists_pos_lower_bound_mvPolynomial_eval_on_unitSphere
      (realRationalLyapunovNumerator
        (realPolynomialFieldOfRational F) p r)
      hdecayPos
  let η : ℝ := min εV εQ
  have hη : 0 < η := lt_min hεV hεQ
  let weight : (Fin n →₀ ℕ) → ℝ := fun e ↦
    1 + rationalLyapunovBasisCubeBound F r e
  let S : ℝ := ∑ e ∈ p.support, weight e
  have hweight : ∀ e, 1 ≤ weight e := by
    intro e
    dsimp only [weight]
    exact le_add_of_nonneg_right
      (rationalLyapunovBasisCubeBound_nonneg F r e)
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact Finset.sum_nonneg fun e _he ↦
      (zero_le_one.trans (hweight e))
  let δ : ℝ := η / (S + 1)
  have hden : 0 < S + 1 := by linarith
  have hδ : 0 < δ := div_pos hη hden
  have hSδ : S * δ < η := by
    dsimp only [δ]
    calc
      S * (η / (S + 1)) =
          η * (S / (S + 1)) := by ring
      _ < η * 1 := by
        exact mul_lt_mul_of_pos_left
          ((div_lt_one hden).2 (by linarith)) hη
      _ = η := mul_one η
  have hδS : δ * S < η := by
    simpa [mul_comm] using hSδ
  choose a ha using
    fun e : Fin n →₀ ℕ ↦ exists_rat_near (p.coeff e) hδ
  let pQ : MvPolynomial (Fin n) ℚ :=
    ∑ e ∈ p.support, monomial e (a e)
  let pA : MvPolynomial (Fin n) ℝ :=
    ∑ e ∈ p.support, monomial e (a e : ℝ)
  let pSupport : MvPolynomial (Fin n) ℝ :=
    ∑ e ∈ p.support, monomial e (p.coeff e)
  have hpQhom : pQ.IsHomogeneous D := by
    apply IsHomogeneous.sum p.support
      (fun e ↦ monomial e (a e)) D
    intro e he
    apply isHomogeneous_monomial
    rw [Finsupp.degree_eq_weight_one]
    exact hp (mem_support_iff.mp he)
  have hmap_pQ :
      MvPolynomial.map (algebraMap ℚ ℝ) pQ = pA := by
    simp [pQ, pA]
  have hpSupport : p = pSupport := by
    exact p.support_sum_monomial_coeff.symm
  have hweighted :
      (∑ e ∈ p.support,
        |(a e : ℝ) - p.coeff e| * weight e) ≤ δ * S := by
    calc
      (∑ e ∈ p.support,
          |(a e : ℝ) - p.coeff e| * weight e) ≤
          ∑ e ∈ p.support, δ * weight e := by
        apply Finset.sum_le_sum
        intro e _he
        exact mul_le_mul_of_nonneg_right
          (by
            simpa [abs_sub_comm] using (ha e).le)
          (zero_le_one.trans (hweight e))
      _ = δ * S := by
        dsimp only [S]
        rw [Finset.mul_sum]
  refine ⟨pQ, hpQhom, ?_, ?_⟩
  · intro x hx
    have hcoord : ∀ i, |x i| ≤ 1 := by
      intro i
      simpa [Real.norm_eq_abs, hx] using norm_le_pi_norm x i
    have hraw :=
      abs_eval_sum_monomial_sub_le
        p.support id
        (fun e ↦ (a e : ℝ)) p.coeff x hcoord
    have hunweighted :
        (∑ e ∈ p.support,
          |(a e : ℝ) - p.coeff e|) ≤
        ∑ e ∈ p.support,
          |(a e : ℝ) - p.coeff e| * weight e := by
      apply Finset.sum_le_sum
      intro e _he
      exact le_mul_of_one_le_right
        (abs_nonneg ((a e : ℝ) - p.coeff e))
        (hweight e)
    have hclose :
        |ratMvPolynomialEval pQ x -
          MvPolynomial.eval x p| < η := by
      rw [ratMvPolynomialEval, hmap_pQ, hpSupport]
      exact hraw.trans
        (hunweighted.trans hweighted) |>.trans_lt hδS
    have hlower := hVmargin x hx
    have hetaV : η ≤ εV := min_le_left _ _
    have habs := (abs_lt.mp hclose).1
    linarith
  · intro x hx
    have hcoord : ∀ i, |x i| ≤ 1 := by
      intro i
      simpa [Real.norm_eq_abs, hx] using norm_le_pi_norm x i
    have hraw :=
      abs_eval_realRationalLyapunovNumerator_sum_monomial_sub_le
        p.support id
        (fun e ↦ (a e : ℝ)) p.coeff F r x hcoord
    have hbasisWeight :
        (∑ e ∈ p.support,
          |(a e : ℝ) - p.coeff e| *
            rationalLyapunovBasisCubeBound F r e) ≤
        ∑ e ∈ p.support,
          |(a e : ℝ) - p.coeff e| * weight e := by
      apply Finset.sum_le_sum
      intro e _he
      apply mul_le_mul_of_nonneg_left
      · dsimp only [weight]
        exact le_add_of_nonneg_left zero_le_one
      · exact abs_nonneg _
    have hclose :
        |ratMvPolynomialEval
            (rationalLyapunovNumerator F pQ r) x -
          MvPolynomial.eval x
            (realRationalLyapunovNumerator
              (realPolynomialFieldOfRational F) p r)| < η := by
      rw [ratMvPolynomialEval, map_rationalLyapunovNumerator,
        hmap_pQ, hpSupport]
      exact hraw.trans
        (hbasisWeight.trans hweighted) |>.trans_lt hδS
    have hlower := hQmargin x hx
    have hetaQ : η ≤ εQ := min_le_right _ _
    have habs := (abs_lt.mp hclose).1
    linarith

end

end HGAS
