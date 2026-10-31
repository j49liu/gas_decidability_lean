import Stability.Simulation.PolynomialFraction
import Stability.Simulation.RadicalSmoothness

/-! Regularity of explicit polynomial fractions with nonzero denominators. -/

namespace Stability.Simulation.PolynomialFraction

noncomputable section

open AbsFormula

variable {σ : Type*} [Finite σ]

theorem continuous_value (f : PolynomialFraction σ)
    (hf : ∀ x : σ → ℝ, polynomialValue x f.denominator ≠ 0) :
    Continuous (fun x ↦ value x f) := by
  letI := Fintype.ofFinite σ
  have hnum : Continuous (fun x : σ → ℝ ↦ polynomialValue x f.numerator) :=
    (contDiff_polynomialValue (fun i ↦ by fun_prop) f.numerator).continuous
  have hden : Continuous (fun x : σ → ℝ ↦ polynomialValue x f.denominator) :=
    (contDiff_polynomialValue (fun i ↦ by fun_prop) f.denominator).continuous
  exact hnum.div hden hf

end

end Stability.Simulation.PolynomialFraction
