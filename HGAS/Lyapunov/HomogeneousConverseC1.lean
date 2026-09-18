import HGAS.Analysis.C1PolynomialApproximation
import HGAS.Lyapunov.HomogeneousConverseApproximation
import Mathlib.Tactic

/-!
# The `C¹` approximation interface implies the real homogeneous witness

This file connects the reusable approximation predicate
`HasC1MvPolynomialApproximationOn` to the exact Lyapunov witness used by
the executable certificate search.

The target Lyapunov function is assumed even.  An arbitrary approximating
polynomial `C` is replaced by its even-total-degree part.  Because the
target value is even and its derivative is odd, antipodal averaging does
not increase either coordinatewise approximation error.  Compact
spherical margins then give the two strict open inequalities required by
`HomogeneousConverseApproximation`.

The final theorem also packages the preceding antipodal-averaging result:
for an odd field, one may start with any strict homogeneous `C¹` Lyapunov
function and approximate its canonical evenization.
-/

namespace HGAS

open _root_.MvPolynomial Set

noncomputable section

variable {n : ℕ}

/-- An even strict degree-two homogeneous `C¹` Lyapunov function that has
the standard coordinatewise polynomial `C¹` approximation property on the
Euclidean unit sphere yields a real homogeneous rational-Lyapunov
witness. -/
theorem realRationalLyapunovWitness_of_even_C1_approximation
    {d : ℕ} (F : PolynomialField n)
    (hF : IsHomogeneousOfDegree d F)
    (L : StrictHomogeneousC1Lyapunov
      (realPolynomialFieldEval
        (realPolynomialFieldOfRational F)) 2)
    (hEven : ∀ x : Fin n → ℝ, L.V (-x) = L.V x)
    (happrox :
      HasC1MvPolynomialApproximationOn
        (euclideanUnitSphere n) L.V
        (fun x i ↦ fderiv ℝ L.V x (Pi.single i 1))) :
    Nonempty (RealRationalLyapunovWitness F) := by
  let G : (Fin n → ℝ) → (Fin n → ℝ) :=
    realPolynomialFieldEval
      (realPolynomialFieldOfRational F)
  have hG : Continuous G :=
    continuous_realPolynomialFieldEval _
  obtain ⟨ε, hε, htolerance⟩ :=
    exists_uniform_coordinate_C1_tolerance_for_open_errors L hG
  obtain ⟨C, hCvalue, hCpartial⟩ :=
    happrox hε
  let E : MvPolynomial (Fin n) ℝ :=
    evenPolynomialPart C
  have hEvalue :
      ∀ x : Fin n → ℝ, normSq x = 1 →
        |MvPolynomial.eval x E - L.V x| < ε := by
    intro x hx
    have hnegx : normSq (-x) = 1 := by
      simpa using hx
    exact
      abs_eval_evenPolynomialPart_sub_lt_of_even_target
        C L.V x (hEven x)
        (hCvalue x hx)
        (hCvalue (-x) hnegx)
  have hEpartial :
      ∀ x : Fin n → ℝ, normSq x = 1 → ∀ i : Fin n,
        |MvPolynomial.eval x (pderiv i E) -
          fderiv ℝ L.V x (Pi.single i 1)| < ε := by
    intro x hx i
    have hnegx : normSq (-x) = 1 := by
      simpa using hx
    let ei : Fin n → ℝ := Pi.single i 1
    have hDneg :
        fderiv ℝ L.V (-x) ei =
          -fderiv ℝ L.V x ei := by
      rw [fderiv_neg_of_even
        (L.contDiff.differentiable (by norm_num)) hEven x]
      rfl
    have hxpartial :
        |mvPolynomialDifferential C x ei -
          fderiv ℝ L.V x ei| < ε := by
      simpa only [ei, mvPolynomialDifferential_piSingle_one] using
        hCpartial x hx i
    have hnegpartial :
        |mvPolynomialDifferential C (-x) ei -
          fderiv ℝ L.V (-x) ei| < ε := by
      simpa only [ei, mvPolynomialDifferential_piSingle_one] using
        hCpartial (-x) hnegx i
    have havg :=
      abs_mvPolynomialDifferential_evenPolynomialPart_sub_lt
        C (fun y v ↦ fderiv ℝ L.V y v) x ei
        hDneg hxpartial hnegpartial
    simpa only [E, ei,
      mvPolynomialDifferential_piSingle_one] using havg
  have hopen :=
    htolerance E hEvalue hEpartial
  apply realRationalLyapunovWitness_of_open_polynomial_approximation
    F hF L C
  · intro x hx
    exact (hopen x hx).1
  · intro x hx
    exact (hopen x hx).2

/-- For an odd field, the previous theorem applies to the canonical
antipodal average of an arbitrary strict homogeneous `C¹` Lyapunov
function. -/
theorem realRationalLyapunovWitness_of_odd_C1_approximation
    {d : ℕ} (F : PolynomialField n)
    (hF : IsHomogeneousOfDegree d F)
    (L : StrictHomogeneousC1Lyapunov
      (realPolynomialFieldEval
        (realPolynomialFieldOfRational F)) 2)
    (hodd :
      ∀ x : Fin n → ℝ,
        realPolynomialFieldEval
            (realPolynomialFieldOfRational F) (-x) =
          -realPolynomialFieldEval
            (realPolynomialFieldOfRational F) x)
    (happrox :
      HasC1MvPolynomialApproximationOn
        (euclideanUnitSphere n)
        (L.evenized hodd).V
        (fun x i ↦
          fderiv ℝ (L.evenized hodd).V x (Pi.single i 1))) :
    Nonempty (RealRationalLyapunovWitness F) := by
  apply realRationalLyapunovWitness_of_even_C1_approximation
    F hF (L.evenized hodd)
  · exact (L.evenized_V_neg hodd)
  · exact happrox

/-- Odd polynomial degree supplies the odd-map hypothesis automatically. -/
theorem realRationalLyapunovWitness_of_oddDegree_C1_approximation
    {d : ℕ} (F : PolynomialField n)
    (hF : IsHomogeneousOfDegree d F) (hd : Odd d)
    (L : StrictHomogeneousC1Lyapunov
      (realPolynomialFieldEval
        (realPolynomialFieldOfRational F)) 2)
    (happrox :
      HasC1MvPolynomialApproximationOn
        (euclideanUnitSphere n)
        (L.evenized
          (realPolynomialFieldEval_neg_of_odd F hF hd)).V
        (fun x i ↦
          fderiv ℝ
            (L.evenized
              (realPolynomialFieldEval_neg_of_odd F hF hd)).V
            x (Pi.single i 1))) :
    Nonempty (RealRationalLyapunovWitness F) := by
  exact realRationalLyapunovWitness_of_odd_C1_approximation
    F hF L
      (realPolynomialFieldEval_neg_of_odd F hF hd)
      happrox

end

end HGAS
