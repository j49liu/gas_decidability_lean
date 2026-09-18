import HGAS.Lyapunov.RationalLyapunovPerturbation
import Mathlib.Tactic

/-!
# Radial homogenization of a finite polynomial

The Bernstein step in the rational converse-Lyapunov theorem first
constructs an ordinary polynomial `C` on a cube.  After symmetrization,
every monomial of `C` has even total degree.  Fixing an even target degree
`M` above all those degrees, one replaces a term `c X^e` by

```
c X^e ρ^((M - |e|)/2),       ρ = ∑ᵢ Xᵢ².
```

Every new term has degree `M`, and on the unit sphere (`ρ=1`) its value is
unchanged.  This file formalizes that algebraic operation independently of
Bernstein approximation.  The construction is useful anywhere an
inhomogeneous polynomial on a sphere must be represented by a homogeneous
ambient polynomial.
-/

namespace HGAS

open MvPolynomial
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- The support condition needed for radial homogenization to target
degree `M`: every supported monomial has degree at most `M`, and its degree
has the same parity as `M`. -/
def HasRadialHomogenizationParity
    (M : ℕ) (C : MvPolynomial (Fin n) ℝ) : Prop :=
  ∀ e ∈ C.support, e.degree ≤ M ∧ Even (M - e.degree)

/-- Replace every supported monomial by the same monomial times the radial
power that raises its total degree to `M`. -/
def radialHomogenization
    (M : ℕ) (C : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ e ∈ C.support,
    monomial e (C.coeff e) *
      realRhoPolynomial ^ ((M - e.degree) / 2)

/-- The real radial polynomial is homogeneous of degree two. -/
theorem realRhoPolynomial_isHomogeneous :
    (realRhoPolynomial (n := n)).IsHomogeneous 2 := by
  apply IsHomogeneous.sum Finset.univ (fun i : Fin n ↦ X i ^ 2) 2
  intro i _hi
  exact isHomogeneous_X_pow i 2

/-- Evaluation of the real radial polynomial is the algebraic squared
Euclidean norm. -/
@[simp]
theorem eval_realRhoPolynomial (x : Fin n → ℝ) :
    MvPolynomial.eval x (realRhoPolynomial (n := n)) = normSq x := by
  simp [realRhoPolynomial, normSq, dot, pow_two]

/-- The parity hypothesis gives the exact degree identity used term by
term. -/
theorem degree_add_twice_half_sub_eq
    {a M : ℕ} (ha : a ≤ M) (hparity : Even (M - a)) :
    a + 2 * ((M - a) / 2) = M := by
  obtain ⟨k, hk⟩ := hparity
  omega

/-- Radial homogenization is genuinely homogeneous of its target degree. -/
theorem radialHomogenization_isHomogeneous
    (M : ℕ) (C : MvPolynomial (Fin n) ℝ)
    (hC : HasRadialHomogenizationParity M C) :
    (radialHomogenization M C).IsHomogeneous M := by
  apply IsHomogeneous.sum C.support
    (fun e ↦
      monomial e (C.coeff e) *
        realRhoPolynomial ^ ((M - e.degree) / 2)) M
  intro e he
  obtain ⟨heM, heParity⟩ := hC e he
  have hmonomial :
      (monomial e (C.coeff e) :
        MvPolynomial (Fin n) ℝ).IsHomogeneous e.degree :=
    isHomogeneous_monomial (C.coeff e) rfl
  have hradial :
      (realRhoPolynomial ^ ((M - e.degree) / 2) :
        MvPolynomial (Fin n) ℝ).IsHomogeneous
          (2 * ((M - e.degree) / 2)) :=
    realRhoPolynomial_isHomogeneous.pow _
  convert hmonomial.mul hradial using 1
  exact (degree_add_twice_half_sub_eq heM heParity).symm

/-- On the algebraic unit sphere `ρ=1`, radial homogenization agrees
exactly with the original polynomial. -/
theorem eval_radialHomogenization_of_normSq_eq_one
    (M : ℕ) (C : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) (hx : normSq x = 1) :
    MvPolynomial.eval x (radialHomogenization M C) =
      MvPolynomial.eval x C := by
  calc
    MvPolynomial.eval x (radialHomogenization M C) =
        ∑ e ∈ C.support,
          MvPolynomial.eval x (monomial e (C.coeff e)) *
            MvPolynomial.eval x realRhoPolynomial ^
              ((M - e.degree) / 2) := by
      simp [radialHomogenization]
    _ = ∑ e ∈ C.support,
        MvPolynomial.eval x (monomial e (C.coeff e)) := by
      simp [hx]
    _ = MvPolynomial.eval x
        (∑ e ∈ C.support, monomial e (C.coeff e)) := by
      rw [map_sum]
    _ = MvPolynomial.eval x C := by
      rw [C.support_sum_monomial_coeff]

/-! ## Tangential differentials

The radial factors do not change first derivatives tangent to the unit
sphere.  This is the differential fact used in the Bernstein
homogenization argument. -/

/-- Differential of `ρ` in the direction `v`. -/
theorem pderiv_realRhoPolynomial (i : Fin n) :
    MvPolynomial.pderiv i realRhoPolynomial =
      C 2 * X i := by
  classical
  have hderiv :
      pderiv i (realRhoPolynomial (n := n)) =
        (2 : MvPolynomial (Fin n) ℝ) * X i := by
    simp [realRhoPolynomial, Pi.single_apply]
  have hconstant :
      (2 : MvPolynomial (Fin n) ℝ) = C (2 : ℝ) :=
    (map_ofNat (C : ℝ →+* MvPolynomial (Fin n) ℝ) 2).symm
  rw [hderiv, hconstant]

/-- Differential of `ρ` in the direction `v`. -/
theorem mvPolynomialDifferential_realRhoPolynomial_apply
    (x v : Fin n → ℝ) :
    mvPolynomialDifferential realRhoPolynomial x v =
      2 * dot x v := by
  rw [mvPolynomialDifferential_apply]
  simp_rw [pderiv_realRhoPolynomial]
  simp only [map_mul, eval_C, eval_X]
  change
    (∑ i : Fin n, 2 * x i * v i) =
      2 * ∑ i : Fin n, x i * v i
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Every radial power has zero differential in a tangent direction. -/
theorem mvPolynomialDifferential_realRhoPolynomial_pow_apply_eq_zero
    (k : ℕ) (x v : Fin n → ℝ) (htangent : dot x v = 0) :
    mvPolynomialDifferential (realRhoPolynomial ^ k) x v = 0 := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [pow_succ, mvPolynomialDifferential_mul]
      simp only [ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [ih, mvPolynomialDifferential_realRhoPolynomial_apply,
        htangent]
      ring

/-- The polynomial differential commutes with a finite sum, after
evaluation on one direction. -/
theorem mvPolynomialDifferential_finsetSum_apply
    {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial (Fin n) ℝ)
    (x v : Fin n → ℝ) :
    mvPolynomialDifferential (∑ i ∈ s, P i) x v =
      ∑ i ∈ s, mvPolynomialDifferential (P i) x v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        mvPolynomialDifferential_add,
        ContinuousLinearMap.add_apply, ih]

/-- Radial homogenization preserves directional derivatives tangent to the
algebraic unit sphere. -/
theorem mvPolynomialDifferential_radialHomogenization_apply_of_tangent
    (M : ℕ) (C : MvPolynomial (Fin n) ℝ)
    (x v : Fin n → ℝ)
    (hx : normSq x = 1) (htangent : dot x v = 0) :
    mvPolynomialDifferential (radialHomogenization M C) x v =
      mvPolynomialDifferential C x v := by
  have hterm :
      ∀ e ∈ C.support,
        mvPolynomialDifferential
            (monomial e (C.coeff e) *
              realRhoPolynomial ^ ((M - e.degree) / 2)) x v =
          mvPolynomialDifferential
            (monomial e (C.coeff e)) x v := by
    intro e he
    rw [mvPolynomialDifferential_mul]
    simp only [ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul,
      MvPolynomial.eval_pow, eval_realRhoPolynomial, hx, one_pow]
    rw [
      mvPolynomialDifferential_realRhoPolynomial_pow_apply_eq_zero
        ((M - e.degree) / 2) x v htangent]
    ring
  calc
    mvPolynomialDifferential (radialHomogenization M C) x v =
        ∑ e ∈ C.support,
          mvPolynomialDifferential
            (monomial e (C.coeff e) *
              realRhoPolynomial ^ ((M - e.degree) / 2)) x v := by
      rw [radialHomogenization,
        mvPolynomialDifferential_finsetSum_apply]
    _ = ∑ e ∈ C.support,
        mvPolynomialDifferential
          (monomial e (C.coeff e)) x v := by
      apply Finset.sum_congr rfl
      intro e he
      exact hterm e he
    _ = mvPolynomialDifferential
        (∑ e ∈ C.support, monomial e (C.coeff e)) x v := by
      rw [mvPolynomialDifferential_finsetSum_apply]
    _ = mvPolynomialDifferential C x v := by
      rw [C.support_sum_monomial_coeff]

end

end HGAS
