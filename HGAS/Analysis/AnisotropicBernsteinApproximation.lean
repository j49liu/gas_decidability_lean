import HGAS.Analysis.IteratedBernsteinOperator
import HGAS.Analysis.MultivariateC0PolynomialApproximation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Anisotropic tensor Bernstein approximation

For derivative convergence one coordinate naturally has degree `m`,
while all untouched coordinates have degree `m+1`.  It is therefore
useful to allow a separate Bernstein degree in every coordinate.

The main result of this file is uniform convergence for every continuous
function on a finite cube as all coordinate degrees tend to infinity.
The proof is deliberately modular:

1. tensor Bernstein weights form a positive partition of unity;
2. polynomial functions have an exact product formula, so their
   convergence follows from the one-dimensional theorem;
3. Stone--Weierstrass approximates an arbitrary continuous function by a
   polynomial, and positivity transfers the approximation error without
   amplification.

This avoids repeating the probabilistic tail estimate in every
dimension and makes the anisotropic statement no harder than the
isotropic one.
-/

namespace HGAS

open Filter ContinuousMap
open scoped BigOperators Topology unitInterval Polynomial

noncomputable section

variable {n : ℕ}

/-- The tensor grid with a possibly different degree in each
coordinate. -/
def anisotropicBernsteinGrid
    (degree : Fin n → ℕ)
    (k : ∀ i, Fin (degree i + 1)) :
    UnitCube n :=
  fun i ↦ _root_.bernstein.z (k i)

/-- Product of the one-dimensional Bernstein weights. -/
def anisotropicBernsteinWeight
    (degree : Fin n → ℕ)
    (k : ∀ i, Fin (degree i + 1))
    (x : UnitCube n) : ℝ :=
  ∏ i : Fin n,
    _root_.bernstein (degree i) (k i) (x i)

/-- The anisotropic tensor Bernstein average of `f`. -/
def anisotropicBernsteinValue
    (degree : Fin n → ℕ)
    (f : UnitCube n → ℝ)
    (x : UnitCube n) : ℝ :=
  ∑ k : ∀ i, Fin (degree i + 1),
    f (anisotropicBernsteinGrid degree k) *
      anisotropicBernsteinWeight degree k x

/-- An anisotropic Bernstein weight is nonnegative. -/
theorem anisotropicBernsteinWeight_nonneg
    (degree : Fin n → ℕ)
    (k : ∀ i, Fin (degree i + 1))
    (x : UnitCube n) :
    0 ≤ anisotropicBernsteinWeight degree k x := by
  apply Finset.prod_nonneg
  intro i hi
  exact _root_.bernstein_nonneg

/-- Anisotropic tensor weights form a partition of unity. -/
theorem sum_anisotropicBernsteinWeight_eq_one
    (degree : Fin n → ℕ) (x : UnitCube n) :
    ∑ k : ∀ i, Fin (degree i + 1),
      anisotropicBernsteinWeight degree k x = 1 := by
  simp only [anisotropicBernsteinWeight]
  calc
    (∑ k : ∀ i, Fin (degree i + 1),
        ∏ i : Fin n,
          _root_.bernstein (degree i) (k i) (x i)) =
        ∏ i : Fin n,
          ∑ k : Fin (degree i + 1),
            _root_.bernstein (degree i) k (x i) :=
      (Fintype.prod_sum
        (fun i : Fin n ↦
          fun k : Fin (degree i + 1) ↦
            _root_.bernstein (degree i) k (x i))).symm
    _ = 1 := by
      simp_rw [_root_.bernstein.probability]
      simp

/-- Positive tensor averaging does not amplify a uniform error. -/
theorem abs_anisotropicBernsteinDifference_le
    (degree : Fin n → ℕ)
    (f g : UnitCube n → ℝ) (C : ℝ)
    (hfg : ∀ x, |f x - g x| ≤ C)
    (x : UnitCube n) :
    |anisotropicBernsteinValue degree f x -
        anisotropicBernsteinValue degree g x| ≤ C := by
  calc
    |anisotropicBernsteinValue degree f x -
          anisotropicBernsteinValue degree g x| =
        |∑ k : ∀ i, Fin (degree i + 1),
          (f (anisotropicBernsteinGrid degree k) -
            g (anisotropicBernsteinGrid degree k)) *
              anisotropicBernsteinWeight degree k x| := by
      rw [anisotropicBernsteinValue,
        anisotropicBernsteinValue,
        ← Finset.sum_sub_distrib]
      apply congrArg abs
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ ∑ k : ∀ i, Fin (degree i + 1),
        |(f (anisotropicBernsteinGrid degree k) -
          g (anisotropicBernsteinGrid degree k)) *
            anisotropicBernsteinWeight degree k x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : ∀ i, Fin (degree i + 1),
        anisotropicBernsteinWeight degree k x *
          |f (anisotropicBernsteinGrid degree k) -
            g (anisotropicBernsteinGrid degree k)| := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [abs_mul,
        abs_of_nonneg
          (anisotropicBernsteinWeight_nonneg degree k x),
        mul_comm]
    _ ≤ ∑ k : ∀ i, Fin (degree i + 1),
        anisotropicBernsteinWeight degree k x * C := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left
        (hfg _) (anisotropicBernsteinWeight_nonneg degree k x)
    _ = C := by
      rw [← Finset.sum_mul,
        sum_anisotropicBernsteinWeight_eq_one, one_mul]

/-- The continuous power function `t ↦ t^r` on the unit interval. -/
def unitIntervalPower (r : ℕ) :
    C(Set.Icc (0 : ℝ) 1, ℝ) where
  toFun t := (t : ℝ) ^ r
  continuous_toFun := by
    fun_prop

@[simp]
theorem unitIntervalPower_apply
    (r : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    unitIntervalPower r t = (t : ℝ) ^ r :=
  rfl

/-- Projection from the cube to coordinate `i`. -/
def unitCubeCoordinate (i : Fin n) :
    C(UnitCube n, Set.Icc (0 : ℝ) 1) where
  toFun x := x i
  continuous_toFun := continuous_apply i

@[simp]
theorem unitCubeCoordinate_apply
    (i : Fin n) (x : UnitCube n) :
    unitCubeCoordinate i x = x i :=
  rfl

/-- The one-dimensional Bernstein approximation of `t^r`, pulled back
to coordinate `i` of the cube. -/
def coordinatePowerBernsteinMap
    (degree : Fin n → ℕ) (r : ℕ) (i : Fin n) :
    C(UnitCube n, ℝ) :=
  (_root_.bernsteinApproximation
    (degree i) (unitIntervalPower r)).comp
      (unitCubeCoordinate i)

@[simp]
theorem coordinatePowerBernsteinMap_apply
    (degree : Fin n → ℕ) (r : ℕ)
    (i : Fin n) (x : UnitCube n) :
    coordinatePowerBernsteinMap degree r i x =
      ∑ k : Fin (degree i + 1),
        _root_.bernstein (degree i) k (x i) *
          ((k : ℝ) / degree i) ^ r := by
  rw [coordinatePowerBernsteinMap,
    ContinuousMap.comp_apply,
    _root_.bernsteinApproximation.apply]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [unitIntervalPower_apply,
    unitCubeCoordinate_apply, smul_eq_mul,
    _root_.bernstein.z]

/-- Product-form expression for tensor Bernstein averaging of a
multivariate polynomial. -/
def polynomialAnisotropicBernsteinMap
    (degree : Fin n → ℕ)
    (p : MvPolynomial (Fin n) ℝ) :
    C(UnitCube n, ℝ) :=
  ∑ u ∈ p.support,
    ContinuousMap.const (UnitCube n) (p.coeff u) *
      ∏ i : Fin n,
        coordinatePowerBernsteinMap degree (u i) i

/-- Evaluation of a multivariate polynomial on the subtype-valued unit
cube. -/
def mvPolynomialUnitCubeMap
    (p : MvPolynomial (Fin n) ℝ) :
    C(UnitCube n, ℝ) where
  toFun x := MvPolynomial.eval (fun i ↦ (x i : ℝ)) p
  continuous_toFun :=
    (continuous_mvPolynomial_eval p).comp <| by
      fun_prop

@[simp]
theorem mvPolynomialUnitCubeMap_apply
    (p : MvPolynomial (Fin n) ℝ)
    (x : UnitCube n) :
    mvPolynomialUnitCubeMap p x =
      MvPolynomial.eval (fun i ↦ (x i : ℝ)) p :=
  rfl

/-- Exact factorization of tensor Bernstein averaging on polynomial
functions into one-dimensional Bernstein approximations of powers. -/
theorem anisotropicBernsteinValue_mvPolynomial
    (degree : Fin n → ℕ)
    (p : MvPolynomial (Fin n) ℝ)
    (x : UnitCube n) :
    anisotropicBernsteinValue degree
        (mvPolynomialUnitCubeMap p) x =
      polynomialAnisotropicBernsteinMap degree p x := by
  rw [anisotropicBernsteinValue,
    polynomialAnisotropicBernsteinMap]
  simp only [mvPolynomialUnitCubeMap_apply,
    anisotropicBernsteinWeight]
  rw [ContinuousMap.sum_apply]
  simp only [
    ContinuousMap.mul_apply,
    ContinuousMap.const_apply,
    ContinuousMap.prod_apply]
  simp_rw [MvPolynomial.eval_eq']
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  apply congrArg (p.coeff u * ·)
  calc
    (∑ k : ∀ i, Fin (degree i + 1),
        (∏ i : Fin n,
            ((anisotropicBernsteinGrid degree k i : ℝ) ^
              u i)) *
          ∏ i : Fin n,
            _root_.bernstein (degree i) (k i) (x i)) =
        ∑ k : ∀ i, Fin (degree i + 1),
          ∏ i : Fin n,
            (((anisotropicBernsteinGrid degree k i : ℝ) ^
                u i) *
              _root_.bernstein (degree i) (k i) (x i)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.prod_mul_distrib]
    _ = ∏ i : Fin n,
        ∑ k : Fin (degree i + 1),
          (((k : ℝ) / degree i) ^ u i *
            _root_.bernstein (degree i) k (x i)) := by
      rw [Fintype.prod_sum]
      rfl
    _ = ∏ i : Fin n,
        coordinatePowerBernsteinMap degree (u i) i x := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [coordinatePowerBernsteinMap_apply]
      apply Finset.sum_congr rfl
      intro k hk
      ring

/-- Each coordinate of a degree profile tends to infinity when the whole
profile tends to infinity in the product order. -/
theorem tendsto_degree_apply_atTop (i : Fin n) :
    Tendsto (fun degree : Fin n → ℕ ↦ degree i)
      atTop atTop := by
  rw [tendsto_atTop]
  intro N
  filter_upwards [
    eventually_ge_atTop (fun _ : Fin n ↦ N)] with degree hdegree
  exact hdegree i

/-- One coordinate-power factor converges in the continuous-function
space as its coordinate degree tends to infinity. -/
theorem tendsto_coordinatePowerBernsteinMap
    (r : ℕ) (i : Fin n) :
    Tendsto
      (fun degree : Fin n → ℕ ↦
        coordinatePowerBernsteinMap degree r i)
      atTop
      (𝓝 ((unitIntervalPower r).comp
        (unitCubeCoordinate i))) := by
  have hBernstein :
      Tendsto
        (fun degree : Fin n → ℕ ↦
          _root_.bernsteinApproximation
            (degree i) (unitIntervalPower r))
        atTop
        (𝓝 (unitIntervalPower r)) :=
    (_root_.bernsteinApproximation_uniform
      (unitIntervalPower r)).comp
        (tendsto_degree_apply_atTop i)
  exact
    (ContinuousMap.continuous_precomp
      (unitCubeCoordinate i)).continuousAt.tendsto.comp
        hBernstein

/-- The product-form polynomial Bernstein expression converges in the
space of continuous functions on the cube. -/
theorem tendsto_polynomialAnisotropicBernsteinMap
    (p : MvPolynomial (Fin n) ℝ) :
    Tendsto
      (fun degree : Fin n → ℕ ↦
        polynomialAnisotropicBernsteinMap degree p)
      atTop
      (𝓝 (mvPolynomialUnitCubeMap p)) := by
  have hmonomial :
      ∀ u : Fin n →₀ ℕ,
        Tendsto
          (fun degree : Fin n → ℕ ↦
            ContinuousMap.const (UnitCube n) (p.coeff u) *
              ∏ i : Fin n,
                coordinatePowerBernsteinMap degree (u i) i)
          atTop
          (𝓝 (ContinuousMap.const (UnitCube n) (p.coeff u) *
            ∏ i : Fin n,
              (unitIntervalPower (u i)).comp
                (unitCubeCoordinate i))) := by
    intro u
    apply tendsto_const_nhds.mul
    simpa using
      (tendsto_finsetProd (Finset.univ : Finset (Fin n))
        (fun i hi ↦
          tendsto_coordinatePowerBernsteinMap
            (u i) i))
  have hsum :
      Tendsto
        (fun degree : Fin n → ℕ ↦
          ∑ u ∈ p.support,
            ContinuousMap.const (UnitCube n) (p.coeff u) *
              ∏ i : Fin n,
                coordinatePowerBernsteinMap degree (u i) i)
        atTop
        (𝓝 (∑ u ∈ p.support,
          ContinuousMap.const (UnitCube n) (p.coeff u) *
            ∏ i : Fin n,
              (unitIntervalPower (u i)).comp
                (unitCubeCoordinate i))) :=
    tendsto_finsetSum p.support
      (fun u hu ↦ hmonomial u)
  have htarget :
      (∑ u ∈ p.support,
          ContinuousMap.const (UnitCube n) (p.coeff u) *
            ∏ i : Fin n,
              (unitIntervalPower (u i)).comp
                (unitCubeCoordinate i)) =
        mvPolynomialUnitCubeMap p := by
    ext x
    rw [ContinuousMap.sum_apply]
    simp only [ContinuousMap.mul_apply,
      ContinuousMap.const_apply,
      ContinuousMap.prod_apply,
      ContinuousMap.comp_apply,
      unitIntervalPower_apply,
      unitCubeCoordinate_apply,
      mvPolynomialUnitCubeMap_apply,
      MvPolynomial.eval_eq']
  simpa only [polynomialAnisotropicBernsteinMap,
    htarget] using hsum

/-- Uniform pointwise form of polynomial anisotropic Bernstein
convergence. -/
theorem eventually_anisotropicBernsteinValue_mvPolynomial_near
    (p : MvPolynomial (Fin n) ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ degree : Fin n → ℕ in atTop,
      ∀ x : UnitCube n,
        |anisotropicBernsteinValue degree
            (mvPolynomialUnitCubeMap p) x -
          mvPolynomialUnitCubeMap p x| < ε := by
  have hconv :=
    tendsto_polynomialAnisotropicBernsteinMap p
  filter_upwards [
    Metric.tendsto_nhds.mp hconv ε hε] with degree hdegree
  rw [dist_eq_norm, norm_lt_iff _ hε] at hdegree
  intro x
  have hx := hdegree x
  rw [anisotropicBernsteinValue_mvPolynomial]
  simpa only [ContinuousMap.sub_apply,
    Real.norm_eq_abs] using hx

/-- The ordinary real-coordinate closed unit cube. -/
def closedUnitCubeSet (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ ↦ Set.Icc (0 : ℝ) 1)

@[simp]
theorem mem_closedUnitCubeSet
    (x : Fin n → ℝ) :
    x ∈ closedUnitCubeSet n ↔
      ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
  simp only [closedUnitCubeSet, Set.mem_pi,
    Set.mem_univ, Set.mem_Icc, forall_const]

/-- The closed unit cube is compact. -/
theorem isCompact_closedUnitCubeSet :
    IsCompact (closedUnitCubeSet n) := by
  exact isCompact_univ_pi
    (fun _ : Fin n ↦ isCompact_Icc)

/-- Forget the interval-membership proofs in a subtype-valued cube
point. -/
def unitCubeRealPoint (x : UnitCube n) :
    Fin n → ℝ :=
  fun i ↦ x i

@[simp]
theorem unitCubeRealPoint_apply
    (x : UnitCube n) (i : Fin n) :
    unitCubeRealPoint x i = x i :=
  rfl

theorem unitCubeRealPoint_mem
    (x : UnitCube n) :
    unitCubeRealPoint x ∈ closedUnitCubeSet n := by
  rw [mem_closedUnitCubeSet]
  intro i
  exact (x i).property

/-- Full anisotropic tensor Bernstein convergence for continuous
functions on the closed cube.

The degrees may grow at different rates; only eventual coordinatewise
largeness is required. -/
theorem eventually_anisotropicBernsteinValue_near
    (f : (Fin n → ℝ) → ℝ)
    (hf : ContinuousOn f (closedUnitCubeSet n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ degree : Fin n → ℕ in atTop,
      ∀ x : UnitCube n,
        |anisotropicBernsteinValue degree
            (fun y ↦ f (unitCubeRealPoint y)) x -
          f (unitCubeRealPoint x)| < ε := by
  have hthird : 0 < ε / 3 := by
    positivity
  obtain ⟨p, hp⟩ :=
    exists_mvPolynomial_near_of_isCompact
      (closedUnitCubeSet n)
      isCompact_closedUnitCubeSet f hf hthird
  have hpolynomial :=
    eventually_anisotropicBernsteinValue_mvPolynomial_near
      p hthird
  filter_upwards [hpolynomial] with degree hdegree
  intro x
  let fCube : UnitCube n → ℝ :=
    fun y ↦ f (unitCubeRealPoint y)
  have hsample :
      ∀ y : UnitCube n,
        |fCube y - mvPolynomialUnitCubeMap p y| ≤
          ε / 3 := by
    intro y
    have hy :=
      hp (unitCubeRealPoint y)
        (unitCubeRealPoint_mem y)
    rw [abs_sub_comm] at hy
    exact hy.le
  have haverage :=
    abs_anisotropicBernsteinDifference_le
      degree fCube (mvPolynomialUnitCubeMap p)
        (ε / 3) hsample x
  have hpolyAverage := hdegree x
  have hpoint :=
    hp (unitCubeRealPoint x)
      (unitCubeRealPoint_mem x)
  have htriangle :
      |anisotropicBernsteinValue degree fCube x -
          fCube x| ≤
        |anisotropicBernsteinValue degree fCube x -
          anisotropicBernsteinValue degree
            (mvPolynomialUnitCubeMap p) x| +
        |anisotropicBernsteinValue degree
            (mvPolynomialUnitCubeMap p) x -
          mvPolynomialUnitCubeMap p x| +
        |mvPolynomialUnitCubeMap p x - fCube x| := by
    calc
      |anisotropicBernsteinValue degree fCube x -
          fCube x| =
          |(anisotropicBernsteinValue degree fCube x -
              anisotropicBernsteinValue degree
                (mvPolynomialUnitCubeMap p) x) +
            (anisotropicBernsteinValue degree
                (mvPolynomialUnitCubeMap p) x -
              mvPolynomialUnitCubeMap p x) +
            (mvPolynomialUnitCubeMap p x - fCube x)| := by
        congr 1
        ring
      _ ≤ _ := (abs_add_three _ _ _)
  have hpoint' :
      |mvPolynomialUnitCubeMap p x - fCube x| <
        ε / 3 := by
    simpa only [mvPolynomialUnitCubeMap_apply,
      fCube] using hpoint
  change
    |anisotropicBernsteinValue degree fCube x -
        fCube x| < ε
  nlinarith

end

end HGAS
