import Stability.Simulation.TriangularLift
import Stability.Simulation.RadicalInvariant

/-!
# Smoothness and invariant constraints of the actual triangular field

The recursively constructed rational field is globally smooth when its
base denominators and radicands are at least one. Along a supplied
solution segment, the full polynomial chain rule identifies each D_j'.
The constructed auxiliary velocity then makes w_j^4/D_j constant.
No separate differential equation for D_j is assumed.
-/

namespace Stability.Simulation.TriangularLift

noncomputable section

open AbsFormula PolynomialFraction Set

variable {σ : Type*} [Fintype σ] {J : ℕ}

def realize (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (F : σ → PolynomialFraction (σ ⊕ Fin J)) (x : σ ⊕ Fin J → ℝ) :
    σ ⊕ Fin J → ℝ := fun i ↦ value x (field D F i)

theorem contDiff_realize (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (F : σ → PolynomialFraction (σ ⊕ Fin J))
    (hF : ∀ x i, 1 ≤ polynomialValue x (F i).denominator)
    (hD : ∀ x i, 1 ≤ polynomialValue x (D i)) :
    ContDiff ℝ ⊤ (realize D F) := by
  rw [contDiff_pi]
  intro i
  exact (HGAS.contDiff_eval₂Hom_rational_real_fintype (field D F i).numerator).div
    (HGAS.contDiff_eval₂Hom_rational_real_fintype (field D F i).denominator)
    (fun x ↦ ne_of_gt (zero_lt_one.trans_le (field_denominator_one_le D F x (hF x) (hD x) i)))

/-- The conserved quantity follows from the actual vector equation and
formal triangularity; its radicand derivative is computed by the chain rule. -/
theorem ratio_eq_initial (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (F : σ → PolynomialFraction (σ ⊕ Fin J))
    (htri : ∀ j, RadicalProgram.FiniteDependsBelow (D j) j.val)
    (hF : ∀ x i, 1 ≤ polynomialValue x (F i).denominator)
    (hD : ∀ x i, 1 ≤ polynomialValue x (D i))
    {a b : ℝ} {x : ℝ → σ ⊕ Fin J → ℝ}
    (hx : ContinuousOn x (Icc a b))
    (hcurve : ∀ t ∈ Ioo a b, HasDerivAt x (realize D F (x t)) t)
    (j : Fin J) {t : ℝ} (ht : t ∈ Icc a b) :
    x t (Sum.inr j) ^ 4 / polynomialValue (x t) (D j) =
      x a (Sum.inr j) ^ 4 / polynomialValue (x a) (D j) := by
  let rate : ℝ → ℝ := fun u ↦ ∑ i,
    polynomialValue (x u) (MvPolynomial.pderiv i (D j)) * value (x u) (field D F i)
  have hpoly : ContinuousOn (fun u ↦ polynomialValue (x u) (D j)) (Icc a b) :=
    (HGAS.contDiff_eval₂Hom_rational_real_fintype (D j)).continuous.comp_continuousOn hx
  apply radicalRatio_eq_initial ((continuous_apply (Sum.inr j)).comp_continuousOn hx)
    hpoly (fun u _ ↦ zero_lt_one.trans_le (hD (x u) j)) (rate := rate) _ _ ht
  · intro u hu
    have hcoord := (hasDerivAt_pi.mp (hcurve u hu)) (Sum.inr j)
    change HasDerivAt (fun z ↦ x z (Sum.inr j))
      (value (x u) (rootVelocity D F j)) u at hcoord
    rw [rootVelocity_value_eq D F htri (x u) (hF (x u)) (hD (x u)) j] at hcoord
    exact hcoord
  · intro u hu
    exact hasDerivAt_polynomialValue (D j) (hasDerivAt_pi.mp (hcurve u hu))

/-- Exact quartic constraints persist along actual solutions of the
constructed rational vector field. No attracting-graph assertion is made. -/
theorem fourth_eq_of_initial (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (F : σ → PolynomialFraction (σ ⊕ Fin J))
    (htri : ∀ j, RadicalProgram.FiniteDependsBelow (D j) j.val)
    (hF : ∀ x i, 1 ≤ polynomialValue x (F i).denominator)
    (hD : ∀ x i, 1 ≤ polynomialValue x (D i))
    {a b : ℝ} {x : ℝ → σ ⊕ Fin J → ℝ}
    (hx : ContinuousOn x (Icc a b))
    (hcurve : ∀ t ∈ Ioo a b, HasDerivAt x (realize D F (x t)) t)
    (j : Fin J) (hinitial : x a (Sum.inr j) ^ 4 = polynomialValue (x a) (D j))
    {t : ℝ} (ht : t ∈ Icc a b) :
    x t (Sum.inr j) ^ 4 = polynomialValue (x t) (D j) := by
  have hr := ratio_eq_initial D F htri hF hD hx hcurve j ht
  rw [hinitial, div_self (ne_of_gt (zero_lt_one.trans_le (hD (x a) j)))] at hr
  exact (div_eq_one_iff_eq (ne_of_gt (zero_lt_one.trans_le (hD (x t) j)))).mp hr

end

end Stability.Simulation.TriangularLift
