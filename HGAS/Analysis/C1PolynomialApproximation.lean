import HGAS.Analysis.MultivariateC0PolynomialApproximation
import HGAS.Analysis.UnivariateC1PolynomialApproximation
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic

/-!
# The `C¹` polynomial-approximation interface

This file records the exact multivariate approximation property needed by
the converse Lyapunov argument and proves it completely in one dimension.
Keeping the interface independent of a particular construction lets the
eventual tensor-Bernstein convergence theorem plug in without changing
downstream modules.

The genuinely missing analytic step for dimensions at least two is now
sharply isolated: simultaneous uniform convergence of tensor Bernstein
polynomials and all their coordinate derivatives.  No unproved theorem is
postulated here.
-/

namespace HGAS

open Set
open scoped Polynomial

noncomputable section

variable {n : ℕ}

/-- Uniform `C¹` approximability on `s` by real multivariate polynomials.
`D x i` is the intended `i`-th coordinate derivative of `f` at `x`. -/
def HasC1MvPolynomialApproximationOn
    (s : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ)
    (D : (Fin n → ℝ) → Fin n → ℝ) : Prop :=
  ∀ ⦃ε : ℝ⦄, 0 < ε →
    ∃ p : MvPolynomial (Fin n) ℝ,
      (∀ x ∈ s, |MvPolynomial.eval x p - f x| < ε) ∧
      (∀ x ∈ s, ∀ i,
        |MvPolynomial.eval x (MvPolynomial.pderiv i p) -
          D x i| < ε)

/-- The canonical vector in one-dimensional coordinate space with value
`t`. -/
def finOnePoint (t : ℝ) : Fin 1 → ℝ :=
  fun _ ↦ t

@[simp]
theorem finOnePoint_apply (t : ℝ) (i : Fin 1) :
    finOnePoint t i = t :=
  rfl

/-- Every vector indexed by `Fin 1` is determined by its zeroth
coordinate. -/
theorem finOnePoint_zero_eq (x : Fin 1 → ℝ) :
    finOnePoint (x 0) = x := by
  funext i
  exact congrArg x (Subsingleton.elim 0 i)

/-- Evaluating the partial derivative of an embedded univariate
polynomial agrees with evaluating its ordinary derivative. -/
theorem eval_pderiv_toMvPolynomial_finOne
    (q : ℝ[X]) (x : Fin 1 → ℝ) :
    MvPolynomial.eval x
        (MvPolynomial.pderiv 0 (q.toMvPolynomial 0)) =
      q.derivative.eval (x 0) := by
  let γ : ℝ → (Fin 1 → ℝ) := finOnePoint
  have hγ :
      HasDerivAt γ (finOnePoint 1) (x 0) := by
    rw [hasDerivAt_pi]
    intro i
    simpa only [γ, finOnePoint_apply] using
      (hasDerivAt_id (𝕜 := ℝ) (x 0))
  have hp :=
    HGAS.HasDerivAt.mvPolynomial_eval hγ (q.toMvPolynomial 0)
  have hp' :
      HasDerivAt (fun t : ℝ ↦ q.eval t)
        (MvPolynomial.eval x
          (MvPolynomial.pderiv 0 (q.toMvPolynomial 0))) (x 0) := by
    have hxγ : γ (x 0) = x :=
      finOnePoint_zero_eq x
    simpa only [γ, MvPolynomial.eval_toMvPolynomial,
      Fin.sum_univ_one, finOnePoint_apply, mul_one, hxγ] using hp
  exact hp'.unique (_root_.Polynomial.hasDerivAt q (x 0))

/-- The multivariate `C¹` approximation property on an interval in
one-dimensional coordinate space.

This is a direct corollary of
`exists_polynomial_near_with_derivative`, followed by the canonical
embedding `ℝ[X] → MvPolynomial (Fin 1) ℝ`. -/
theorem hasC1MvPolynomialApproximationOn_finOne_interval
    {a b : ℝ} (hab : a ≤ b)
    (f : (Fin 1 → ℝ) → ℝ)
    (D : (Fin 1 → ℝ) → Fin 1 → ℝ)
    (hD :
      ContinuousOn
        (fun t : ℝ ↦ D (finOnePoint t) 0) (Icc a b))
    (hf :
      ∀ t ∈ Icc a b,
        HasDerivAt (fun u : ℝ ↦ f (finOnePoint u))
          (D (finOnePoint t) 0) t) :
    HasC1MvPolynomialApproximationOn
      {x : Fin 1 → ℝ | x 0 ∈ Icc a b} f D := by
  intro ε hε
  obtain ⟨q, hqValue, hqDerivative⟩ :=
    exists_polynomial_near_with_derivative hab
      (fun t : ℝ ↦ f (finOnePoint t))
      (fun t : ℝ ↦ D (finOnePoint t) 0)
      hD hf hε
  let p : MvPolynomial (Fin 1) ℝ :=
    q.toMvPolynomial 0
  refine ⟨p, ?_, ?_⟩
  · intro x hx
    have hx' := hqValue (x 0) hx
    have hpoint : finOnePoint (x 0) = x :=
      finOnePoint_zero_eq x
    simpa only [p, MvPolynomial.eval_toMvPolynomial,
      hpoint] using hx'
  · intro x hx i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    have hx' := hqDerivative (x 0) hx
    have hpoint : finOnePoint (x 0) = x :=
      finOnePoint_zero_eq x
    simpa only [p, eval_pderiv_toMvPolynomial_finOne,
      hpoint] using hx'

end

end HGAS
