import Stability.Simulation.PolynomialFractionSubtraction
import Stability.Simulation.PolynomialFractionResources

/-!
# Degrees of polynomial subtraction from a literal fraction

The denominator is unchanged. The new numerator is the old numerator
minus the polynomial times that denominator, so its degree grows by at
most the polynomial's degree budget.
-/

namespace Stability.Simulation.PolynomialFraction

noncomputable section

variable {σ : Type*}

theorem subPolynomial_degreesLE {f : PolynomialFraction σ} (p : MvPolynomial σ ℚ)
    {b d : ℕ} (hf : DegreesLE f b) (hp : p.totalDegree ≤ d) :
    DegreesLE (subPolynomial f p) (d + b) := by
  constructor
  · apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le (hf.1.trans (Nat.le_add_left _ _))
    exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hp hf.2)
  · exact hf.2.trans (Nat.le_add_left _ _)

end

end Stability.Simulation.PolynomialFraction
