import Stability.Simulation.PolynomialFraction
import Stability.Simulation.PolynomialCurveDerivative

/-!
# Formal polynomial derivatives along rational coordinate fields

The finite sum below is built from numerator/denominator arithmetic.
Its evaluation is exactly the usual directional derivative, and its
denominator is at least one whenever the coordinate denominators are.
-/

namespace Stability.Simulation.PolynomialFraction

noncomputable section

open AbsFormula

variable {σ : Type*} [Fintype σ]

def directional (p : MvPolynomial σ ℚ) (V : σ → PolynomialFraction σ) :
    PolynomialFraction σ :=
  sumOver (fun i ↦ mulPolynomial (MvPolynomial.pderiv i p) (V i))

theorem directional_denominator_one_le (p : MvPolynomial σ ℚ)
    (V : σ → PolynomialFraction σ) (x : σ → ℝ)
    (hV : ∀ i, 1 ≤ polynomialValue x (V i).denominator) :
    1 ≤ polynomialValue x (directional p V).denominator :=
  sumOver_denominator_one_le x _ hV

theorem value_directional (p : MvPolynomial σ ℚ) (V : σ → PolynomialFraction σ)
    (x : σ → ℝ) (hV : ∀ i, 1 ≤ polynomialValue x (V i).denominator) :
    value x (directional p V) =
      ∑ i, polynomialValue x (MvPolynomial.pderiv i p) * value x (V i) := by
  rw [directional, value_sumOver x (fun i ↦ mulPolynomial (MvPolynomial.pderiv i p) (V i))
    (fun i ↦ hV i)]
  simp only [value_mulPolynomial]

end

end Stability.Simulation.PolynomialFraction
