import HGAS.Analysis.EvenC1Lyapunov
import HGAS.Analysis.EvenPolynomialPart
import HGAS.Algebra.HomogeneousEvaluation
import HGAS.Lyapunov.RationalCertificateSoundness
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic

/-!
# Tangential form of the homogeneous rational Lyapunov numerator

The polynomial approximation theorem works intrinsically on the Euclidean
unit sphere.  The certificate checker, on the other hand, uses the
homogeneous numerator

```
q = -ρ (∇p · F) + 2 r p (x · F),
```

where `p` has degree `2(r+1)`.  This file proves the exact identity joining
those two descriptions.

At a point with `ρ(x)=1`, decompose

```
F(x) = F_T(x) + (x · F(x)) x,
F_T(x) = F(x) - (x · F(x))x.
```

Euler's identity gives `Dp(x)[x] = 2(r+1)p(x)`.  Substitution and
cancellation therefore yield

```
q(x) = -Dp(x)[F_T(x)] - 2 p(x) (x · F(x)).
```

This is the key cancellation in the Ahmadi--El Khadir homogenization
argument: radial homogenization preserves the first term, while value
approximation controls the second.
-/

namespace HGAS

open _root_.MvPolynomial
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- Componentwise homogeneity for a real polynomial vector field. -/
def IsRealHomogeneousOfDegree
    (d : ℕ) (F : RealPolynomialField n) : Prop :=
  ∀ i, (F i).IsHomogeneous d

/-- Evaluate every component of a real polynomial vector field. -/
def realPolynomialFieldEval
    (F : RealPolynomialField n) (x : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i ↦ MvPolynomial.eval x (F i)

/-- Evaluating a real polynomial vector field gives a continuous ambient
vector field. -/
theorem continuous_realPolynomialFieldEval
    (F : RealPolynomialField n) :
    Continuous (realPolynomialFieldEval F) := by
  apply continuous_pi
  intro i
  exact continuous_mvPolynomial_eval (F i)

/-- Evaluating the coefficient-embedded real field agrees with evaluating
the original rational field through the rational algebra structure. -/
theorem realPolynomialFieldEval_realPolynomialFieldOfRational
    (F : PolynomialField n) (x : Fin n → ℝ) :
    realPolynomialFieldEval
        (realPolynomialFieldOfRational F) x =
      evalPolynomialField F x := by
  funext i
  simp only [realPolynomialFieldEval,
    realPolynomialFieldOfRational, evalPolynomialField_apply,
    ← MvPolynomial.eval₂_eq_eval_map]
  rfl

/-- A rational homogeneous field of odd degree evaluates to an odd real
map. -/
theorem realPolynomialFieldEval_neg_of_odd
    {d : ℕ} (F : PolynomialField n)
    (hF : IsHomogeneousOfDegree d F) (hd : Odd d)
    (x : Fin n → ℝ) :
    realPolynomialFieldEval
        (realPolynomialFieldOfRational F) (-x) =
      -realPolynomialFieldEval
        (realPolynomialFieldOfRational F) x := by
  rw [realPolynomialFieldEval_realPolynomialFieldOfRational,
    realPolynomialFieldEval_realPolynomialFieldOfRational]
  exact map_neg_of_scalesAsDegree_of_odd
    (evalPolynomialField F) d
    (fun c y ↦ evalPolynomialField_smul F hF c y)
    hd x

/-- Evaluation of the formal gradient--field pairing is the differential
of the scalar polynomial applied to the evaluated field. -/
theorem eval_realGradientDotField
    (F : RealPolynomialField n)
    (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval x (realGradientDotField p F) =
      mvPolynomialDifferential p x (realPolynomialFieldEval F x) := by
  simp only [realGradientDotField, map_sum, map_mul,
    mvPolynomialDifferential_apply, realPolynomialFieldEval]

/-- Evaluation of the formal radial pairing is the coordinate dot
product. -/
theorem eval_realRadialDotPolynomial
    (F : RealPolynomialField n) (x : Fin n → ℝ) :
    MvPolynomial.eval x (realRadialDotPolynomial F) =
      dot x (realPolynomialFieldEval F x) := by
  simp only [realRadialDotPolynomial, map_sum, map_mul, eval_X,
    realPolynomialFieldEval, dot]

/-- Orthogonal projection of a vector to the tangent hyperplane of the
algebraic Euclidean unit sphere at `x`. -/
def euclideanTangentComponent
    (x v : Fin n → ℝ) : Fin n → ℝ :=
  v - dot x v • x

/-- The radial scalar of a continuous field is continuous. -/
theorem continuous_dot_field
    {G : (Fin n → ℝ) → (Fin n → ℝ)}
    (hG : Continuous G) :
    Continuous (fun x ↦ dot x (G x)) := by
  unfold dot
  fun_prop

/-- The tangential projection of a continuous field is continuous. -/
theorem continuous_euclideanTangentComponent_field
    {G : (Fin n → ℝ) → (Fin n → ℝ)}
    (hG : Continuous G) :
    Continuous
      (fun x ↦ euclideanTangentComponent x (G x)) := by
  unfold euclideanTangentComponent
  exact hG.sub ((continuous_dot_field hG).smul continuous_id)

/-- The projected component is tangent when `x` has algebraic squared norm
one. -/
theorem dot_euclideanTangentComponent_eq_zero
    (x v : Fin n → ℝ) (hx : normSq x = 1) :
    dot x (euclideanTangentComponent x v) = 0 := by
  simp only [euclideanTangentComponent, dot, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hradial :
      (∑ i : Fin n,
          x i * ((∑ j : Fin n, x j * v j) * x i)) =
        (∑ j : Fin n, x j * v j) *
          ∑ i : Fin n, x i * x i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hradial]
  change dot x v - dot x v * normSq x = 0
  rw [hx]
  ring

/-- Tangential plus radial components reconstruct the original vector. -/
theorem euclideanTangentComponent_add_radial
    (x v : Fin n → ℝ) :
    euclideanTangentComponent x v + dot x v • x = v := by
  funext i
  simp [euclideanTangentComponent]

/-- Euler's homogeneous identity expressed using the bundled polynomial
differential. -/
theorem mvPolynomialDifferential_self_of_isHomogeneous
    {p : MvPolynomial (Fin n) ℝ} {D : ℕ}
    (hp : p.IsHomogeneous D) (x : Fin n → ℝ) :
    mvPolynomialDifferential p x x =
      (D : ℝ) * MvPolynomial.eval x p := by
  have hEuler := hp.sum_X_mul_pderiv
  have hEval :=
    congrArg (fun q : MvPolynomial (Fin n) ℝ ↦
      MvPolynomial.eval x q) hEuler
  simp only [map_sum, map_mul, eval_X, nsmul_eq_mul,
    map_natCast] at hEval
  rw [mvPolynomialDifferential_apply]
  calc
    (∑ i : Fin n,
        MvPolynomial.eval x (pderiv i p) * x i) =
        ∑ i : Fin n,
          x i * MvPolynomial.eval x (pderiv i p) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = (D : ℝ) * MvPolynomial.eval x p := hEval

/-- Apply a differential after splitting a vector into its tangential and
radial components. -/
theorem mvPolynomialDifferential_tangent_add_radial
    (p : MvPolynomial (Fin n) ℝ) (x v : Fin n → ℝ) :
    mvPolynomialDifferential p x v =
      mvPolynomialDifferential p x
          (euclideanTangentComponent x v) +
        dot x v * mvPolynomialDifferential p x x := by
  conv_lhs =>
    rw [← euclideanTangentComponent_add_radial x v]
  simp only [map_add, map_smul, smul_eq_mul]

/-- Direct evaluated form of the real rational Lyapunov numerator. -/
theorem eval_realRationalLyapunovNumerator
    (F : RealPolynomialField n)
    (p : MvPolynomial (Fin n) ℝ) (r : ℕ)
    (x : Fin n → ℝ) :
    MvPolynomial.eval x
        (realRationalLyapunovNumerator F p r) =
      -(normSq x *
          mvPolynomialDifferential p x
            (realPolynomialFieldEval F x)) +
        2 * (r : ℝ) * MvPolynomial.eval x p *
          dot x (realPolynomialFieldEval F x) := by
  simp only [realRationalLyapunovNumerator, map_add, map_neg,
    map_mul, eval_realRhoPolynomial, eval_realGradientDotField,
    eval_C, eval_realRadialDotPolynomial]

/-- On the Euclidean unit sphere, the certificate numerator is exactly
the negative tangential derivative minus the degree-two radial term. -/
theorem eval_realRationalLyapunovNumerator_of_normSq_eq_one
    (F : RealPolynomialField n)
    (p : MvPolynomial (Fin n) ℝ) (r : ℕ)
    (hp : p.IsHomogeneous (2 * (r + 1)))
    (x : Fin n → ℝ) (hx : normSq x = 1) :
    MvPolynomial.eval x
        (realRationalLyapunovNumerator F p r) =
      -mvPolynomialDifferential p x
          (euclideanTangentComponent x
            (realPolynomialFieldEval F x)) -
        2 * MvPolynomial.eval x p *
          dot x (realPolynomialFieldEval F x) := by
  rw [eval_realRationalLyapunovNumerator, hx, one_mul,
    mvPolynomialDifferential_tangent_add_radial,
    mvPolynomialDifferential_self_of_isHomogeneous hp]
  push_cast
  ring

/-! ## Homogeneity and propagation away from the Euclidean sphere -/

/-- Embedding the coefficients of a rational homogeneous field preserves
its componentwise degree. -/
theorem realPolynomialFieldOfRational_isHomogeneous
    {d : ℕ} (F : PolynomialField n)
    (hF : IsHomogeneousOfDegree d F) :
    IsRealHomogeneousOfDegree d
      (realPolynomialFieldOfRational F) := by
  intro i
  exact (hF i).map (algebraMap ℚ ℝ)

/-- The real gradient--field polynomial has its expected degree. -/
theorem realGradientDotField_isHomogeneous
    {pDegree fieldDegree : ℕ}
    (p : MvPolynomial (Fin n) ℝ)
    (F : RealPolynomialField n)
    (hp : p.IsHomogeneous pDegree)
    (hF : IsRealHomogeneousOfDegree fieldDegree F) :
    (realGradientDotField p F).IsHomogeneous
      ((pDegree - 1) + fieldDegree) := by
  apply IsHomogeneous.sum Finset.univ
    (fun i : Fin n ↦ pderiv i p * F i)
    ((pDegree - 1) + fieldDegree)
  intro i _hi
  exact (hp.pderiv (i := i)).mul (hF i)

/-- The real radial pairing has degree one more than the field. -/
theorem realRadialDotPolynomial_isHomogeneous
    {fieldDegree : ℕ} (F : RealPolynomialField n)
    (hF : IsRealHomogeneousOfDegree fieldDegree F) :
    (realRadialDotPolynomial F).IsHomogeneous
      (fieldDegree + 1) := by
  have h :
      (realRadialDotPolynomial F).IsHomogeneous
        (1 + fieldDegree) := by
    apply IsHomogeneous.sum Finset.univ
      (fun i : Fin n ↦ X i * F i) (1 + fieldDegree)
    intro i _hi
    exact (isHomogeneous_X ℝ i).mul (hF i)
  simpa [Nat.add_comm] using h

/-- Real-coefficient version of the degree calculation for the rational
Lyapunov numerator. -/
theorem realRationalLyapunovNumerator_isHomogeneous
    {fieldDegree : ℕ} (F : RealPolynomialField n)
    (p : MvPolynomial (Fin n) ℝ) (r : ℕ)
    (hF : IsRealHomogeneousOfDegree fieldDegree F)
    (hp : p.IsHomogeneous (2 * r + 2)) :
    (realRationalLyapunovNumerator F p r).IsHomogeneous
      (2 * r + fieldDegree + 3) := by
  have hgrad :=
    realGradientDotField_isHomogeneous p F hp hF
  have hrad :=
    realRadialDotPolynomial_isHomogeneous F hF
  have hfirst :
      (realRhoPolynomial * realGradientDotField p F).IsHomogeneous
        (2 * r + fieldDegree + 3) := by
    convert realRhoPolynomial_isHomogeneous.mul hgrad using 1
    omega
  have hsecond :
      (C (2 * (r : ℝ)) * p *
          realRadialDotPolynomial F).IsHomogeneous
        (2 * r + fieldDegree + 3) := by
    have hc :
        (C (2 * (r : ℝ)) :
          MvPolynomial (Fin n) ℝ).IsHomogeneous 0 :=
      isHomogeneous_C _ _
    convert (hc.mul hp).mul hrad using 1
    omega
  exact hfirst.neg.add hsecond

/-- Strict positivity of a real homogeneous polynomial on the algebraic
Euclidean unit sphere propagates to every nonzero point. -/
theorem eval_pos_of_isHomogeneous_of_normSq_one_pos
    {p : MvPolynomial (Fin n) ℝ} {D : ℕ}
    (hp : p.IsHomogeneous D)
    (hunit : ∀ x : Fin n → ℝ, normSq x = 1 →
      0 < MvPolynomial.eval x p) :
    ∀ x : Fin n → ℝ, x ≠ 0 →
      0 < MvPolynomial.eval x p := by
  intro x hx
  let c : ℝ := Real.sqrt (normSq x)
  let y : Fin n → ℝ := c⁻¹ • x
  have hρpos : 0 < normSq x :=
    normSq_pos_of_ne_zero hx
  have hc : 0 < c := by
    exact Real.sqrt_pos.2 hρpos
  have hcSq : c ^ 2 = normSq x := by
    exact Real.sq_sqrt (normSq_nonneg x)
  have hy : normSq y = 1 := by
    dsimp only [y]
    rw [normSq_smul]
    dsimp only [c]
    rw [inv_pow, hcSq]
    field_simp
  have hxy : c • y = x := by
    simp [y, smul_smul, hc.ne']
  change eval₂Hom (RingHom.id ℝ) x p > 0
  calc
    eval₂Hom (RingHom.id ℝ) x p =
        eval₂Hom (RingHom.id ℝ) (c • y) p := by
      rw [hxy]
    _ = c ^ D * eval₂Hom (RingHom.id ℝ) y p :=
      MvPolynomial.IsHomogeneous.eval₂Hom_smul
        hp (RingHom.id ℝ) y c
    _ > 0 := mul_pos (pow_pos hc D) (by
      change 0 < MvPolynomial.eval y p
      exact hunit y hy)

end

end HGAS
