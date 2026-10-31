import Stability.Simulation.FormulaSmoothness
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Polynomial chain rules on arbitrary finite coordinate spaces

The derivative is the finite sum of evaluated formal partial derivatives
times coordinate velocities. This extends the preserved `Fin n` interface
to the tagged finite coordinates used by the radical compiler, without
requiring a choice of enumeration.
-/

namespace Stability.Simulation.AbsFormula

noncomputable section

variable {σ : Type*} [Fintype σ]

/-- Chain rule for rational polynomial evaluation along a coordinatewise
differentiable real curve, with the literal formal partial derivatives. -/
theorem hasDerivAt_polynomialValue (p : MvPolynomial σ ℚ)
    {x : ℝ → σ → ℝ} {v : σ → ℝ} {t : ℝ}
    (hx : ∀ i, HasDerivAt (fun s ↦ x s i) (v i) t) :
    HasDerivAt (fun s ↦ polynomialValue (x s) p)
      (∑ i, polynomialValue (x t) (MvPolynomial.pderiv i p) * v i) t := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simpa [polynomialValue] using hasDerivAt_const t (c : ℝ)
  | add p q hp hq =>
      simpa [polynomialValue, add_mul, Finset.sum_add_distrib] using hp.add hq
  | mul_X p j hp =>
      have hX (i : σ) : MvPolynomial.eval₂ (algebraMap ℚ ℝ) (x t)
          (MvPolynomial.pderiv i (MvPolynomial.X j)) = if i = j then 1 else 0 := by
        by_cases hij : i = j
        · subst i
          simp
        · simp [MvPolynomial.pderiv_X_of_ne (Ne.symm hij), hij]
      convert hp.mul (hx j) using 1
      · ext s
        simp [polynomialValue]
      · simp only [MvPolynomial.pderiv_mul, polynomialValue,
          MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
          hX, add_mul,
          Finset.sum_add_distrib]
        simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        congr 1
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring

end

end Stability.Simulation.AbsFormula
