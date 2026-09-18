import HGAS.Modular.RecurrentUnaryMomentGenericity
import Mathlib.Tactic

/-!
# Selector moments exclude degeneracy at every nonzero unary clock

The elementary moment argument does not depend on the normalization
`κ = iπ`.  It only uses:

* invariance of the three divisors `A = 0`, `C = 0`, and `A + C = 0`;
* recurrence, to make a recurrent point on a divisor an equilibrium; and
* the coefficient-link residuals, which turn one corrected moment into a
  fixed nonzero constant on each degenerate branch.

This module exposes that normalization-free conclusion.  Time is rescaled
to `iπ` only after genericity has been established.
-/

namespace HGAS.Modular

open Filter MeasureTheory Topology

noncomputable section

/-- Zero corrected selector moments force the generic unary locus for an
arbitrary constant complex clock.  Recurrence and nonvanishing of the
clock are not needed for this divisor-exclusion step. -/
theorem recurrentUnary_generic_of_selectorMomentLimits_arbitraryClock
    {κ : ℂ}
    {z : ℝ → LinkedJacobiState ℂ}
    (hz :
      IsScaledUnaryModularTrajectory κ
        (fun t ↦ (z t).unary))
    {t₀ : ℝ}
    (hresidual :
      ∀ t (r : LinkedJacobiResidualIndex),
        linkedJacobiResidual r (z t) = 0)
    {T : ℕ → ℝ}
    (hT : Tendsto T atTop atTop)
    (χ : ℝ → ℂ)
    (hY :
      Tendsto
        (fun n ↦ HGAS.Analysis.cesaroMeanAt
          (unaryMeanObservable z) (T n))
        atTop (𝓝 0))
    (hp4 :
      Tendsto
        (fun n ↦ HGAS.Analysis.cesaroMeanAt
          (rootP4MeanObservable z) (T n))
        atTop (𝓝 0))
    (hp2 :
      Tendsto
        (fun n ↦ HGAS.Analysis.cesaroMeanAt
          (rootP2MeanObservable z χ) (T n))
        atTop (𝓝 0)) :
    (z t₀).unary.A ≠ 0 ∧
      (z t₀).unary.C ≠ 0 ∧
      UnaryModularState.B (z t₀).unary ≠ 0 := by
  by_cases hA : (z t₀).unary.A = 0
  · have hAall := hz.A_eq_zero hA
    have hp2zero : ∀ t, (z t).jacobi.p2 = 0 := by
      intro t
      have hlink := hresidual t .coefficientLinkTwo
      change
        (z t).jacobi.p2 ^ 2 - (z t).unary.A = 0 at hlink
      rw [hAall t, sub_zero] at hlink
      exact (sq_eq_zero_iff).mp hlink
    have hconst :
        ∀ t, rootP2MeanObservable z χ t = -(1 / 4 : ℂ) := by
      intro t
      simp [rootP2MeanObservable, hp2zero t]
    exact False.elim <|
      not_tendsto_zero_cesaroMeanAt_of_eq_const
        hT (by norm_num : -(1 / 4 : ℂ) ≠ 0)
        hconst hp2
  by_cases hC : (z t₀).unary.C = 0
  · have hCall := hz.C_eq_zero hC
    have hp4zero : ∀ t, (z t).jacobi.p4 = 0 := by
      intro t
      have hlink := hresidual t .coefficientLinkFour
      change
        (z t).jacobi.p4 ^ 2 - (z t).unary.C = 0 at hlink
      rw [hCall t, sub_zero] at hlink
      exact (sq_eq_zero_iff).mp hlink
    have hconst :
        ∀ t, rootP4MeanObservable z t = -(1 : ℂ) := by
      intro t
      simp [rootP4MeanObservable, hp4zero t]
    exact False.elim <|
      not_tendsto_zero_cesaroMeanAt_of_eq_const
        hT (by norm_num : -(1 : ℂ) ≠ 0)
        hconst hp4
  by_cases hB :
      UnaryModularState.B (z t₀).unary = 0
  · have hBall := hz.B_eq_zero hB
    have hYzero : ∀ t, (z t).unary.Y = 0 := by
      intro t
      have hjacobi := hresidual t .unaryJacobi
      change
        (z t).unary.Y ^ 4 -
            (z t).unary.A - (z t).unary.C = 0 at hjacobi
      have hsum :
          (z t).unary.A + (z t).unary.C = 0 := by
        simpa only [UnaryModularState.B] using hBall t
      have hpow : (z t).unary.Y ^ 4 = 0 := by
        linear_combination hjacobi + hsum
      exact
        (pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).mp hpow
    have hconst :
        ∀ t, unaryMeanObservable z t = -(1 : ℂ) := by
      intro t
      simp [unaryMeanObservable, hYzero t]
    exact False.elim <|
      not_tendsto_zero_cesaroMeanAt_of_eq_const
        hT (by norm_num : -(1 : ℂ) ≠ 0)
        hconst hY
  exact ⟨hA, hC, hB⟩

end

end HGAS.Modular
