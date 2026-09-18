import HGAS.Analysis.MvPolynomialCalculus
import HGAS.Veronese.CubicLiftAlgebra
import Mathlib.Tactic

/-!
# Smoothness of polynomial fields on arbitrary finite coordinate spaces

The basic multivariate-polynomial calculus module uses variables indexed by
`Fin n`.  Veronese coordinate spaces are instead indexed by the finite type
`MultiIndex n k`.  This file records the same elementary smoothness theorem
for an arbitrary finite index type and applies it componentwise to rational
coordinate fields.

The proof is algebraic induction on a polynomial: constants and sums are
immediate, and multiplication by a variable uses the continuous linear
coordinate projection.
-/

namespace HGAS

open MvPolynomial

noncomputable section

/-- Evaluation of a real multivariate polynomial in any finite family of
variables is smooth of every order. -/
theorem contDiff_mvPolynomial_eval_fintype
    {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) :
    ContDiff ℝ ⊤ (fun x : ι → ℝ ↦ MvPolynomial.eval x p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
      simpa using
        (contDiff_const : ContDiff ℝ ⊤
          (fun _ : ι → ℝ ↦ a))
  | add p q hp hq =>
      simpa only [MvPolynomial.eval_add] using hp.add hq
  | mul_X p j hp =>
      have hj : ContDiff ℝ ⊤ (fun x : ι → ℝ ↦ x j) :=
        (ContinuousLinearMap.proj j :
          (ι → ℝ) →L[ℝ] ℝ).contDiff
      simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X] using
        hp.mul hj

/-- Rational coefficients may be embedded in the reals before evaluation
without changing smoothness. -/
theorem contDiff_eval₂Hom_rational_real_fintype
    {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℚ) :
    ContDiff ℝ ⊤
      (fun x : ι → ℝ ↦
        MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x p) := by
  have h :=
    contDiff_mvPolynomial_eval_fintype
      (MvPolynomial.map (algebraMap ℚ ℝ) p)
  simpa only [MvPolynomial.eval_map] using h

end

namespace Veronese

open HGAS

noncomputable section

/-- Evaluation of a rational polynomial coordinate field on a finite
coordinate space is a smooth real vector field. -/
theorem contDiff_evalCoordinateField_real
    {ι : Type*} [Fintype ι]
    (G : RationalCoordinateField ι) :
    ContDiff ℝ ⊤
      (fun y : ι → ℝ ↦ evalCoordinateField G y) := by
  rw [contDiff_pi]
  intro a
  exact contDiff_eval₂Hom_rational_real_fintype (G a)

end

end Veronese

end HGAS
