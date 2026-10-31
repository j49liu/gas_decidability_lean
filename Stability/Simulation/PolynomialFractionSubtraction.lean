import Stability.Simulation.PolynomialFraction

/-! Subtracting a polynomial without changing a stored denominator. -/

namespace Stability.Simulation.PolynomialFraction

noncomputable section

open AbsFormula

variable {σ : Type*}

def subPolynomial (f : PolynomialFraction σ) (p : MvPolynomial σ ℚ) :
    PolynomialFraction σ := ⟨f.numerator - p * f.denominator, f.denominator⟩

theorem value_subPolynomial (x : σ → ℝ) (f : PolynomialFraction σ)
    (p : MvPolynomial σ ℚ) (hf : polynomialValue x f.denominator ≠ 0) :
    value x (subPolynomial f p) = value x f - polynomialValue x p := by
  simp only [value, subPolynomial, polynomialValue, MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_mul]
  dsimp only [polynomialValue] at hf
  field_simp [hf]

end

end Stability.Simulation.PolynomialFraction
