import HGAS.Analysis.CesaroExponentialSeriesArbitraryHorizon
import HGAS.Modular.RecurrentUnarySelectorReduction
import Mathlib.Tactic

/-!
# Unary selector moments exclude every recurrent degenerate divisor

The recurrent unary reduction has two alternatives: an equilibrium on
one of `A = 0`, `C = 0`, `A + C = 0`, or a generic canonical-lambda lift.
The first, third, and fourth corrected selector moments rule out the
degenerate alternative without any modular measure classification.

Indeed:

* on `A = 0`, the coefficient link gives `p₂ = 0`, so the corrected
  `p₂` root moment is constantly `-1/4`;
* on `C = 0`, the coefficient link gives `p₄ = 0`, so the `p₄` root
  moment is constantly `-1`; and
* on `A + C = 0`, the unary Jacobi residual gives `Y = 0`, so the unary
  mean moment is constantly `-1`.

None of these nonzero constants can have Cesàro limit zero.  The argument
works along every sequence of real horizons tending to `+∞`, and the
auxiliary phase character in the `p₂` moment is completely arbitrary.
-/

namespace HGAS.Modular

open Filter MeasureTheory Topology
open UpperHalfPlane hiding I
open scoped Interval

noncomputable section

/-- Cesàro averaging a constant along any nonzero horizon returns that
constant. -/
theorem cesaroMeanAt_const
    (c : ℂ) {T : ℝ} (hT : T ≠ 0) :
    HGAS.Analysis.cesaroMeanAt (fun _ : ℝ ↦ c) T = c := by
  rw [HGAS.Analysis.cesaroMeanAt,
    intervalIntegral.integral_const]
  simp only [sub_zero, Complex.real_smul]
  rw [← mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hT),
    one_mul]

/-- Pointwise equality with a nonzero constant contradicts zero Cesàro
limit along unbounded horizons. -/
theorem not_tendsto_zero_cesaroMeanAt_of_eq_const
    {f : ℝ → ℂ} {T : ℕ → ℝ}
    (hT : Tendsto T atTop atTop)
    {c : ℂ} (hc : c ≠ 0)
    (hf : ∀ t, f t = c) :
    ¬ Tendsto
        (fun n ↦ HGAS.Analysis.cesaroMeanAt f (T n))
        atTop (𝓝 0) := by
  intro hzero
  have hTne : ∀ᶠ n in atTop, T n ≠ 0 :=
    (hT.eventually (eventually_gt_atTop 0)).mono
      fun _ hn ↦ hn.ne'
  have hconst :
      Tendsto
        (fun n ↦ HGAS.Analysis.cesaroMeanAt f (T n))
        atTop (𝓝 c) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hTne] with n hn
    rw [show f = fun _ : ℝ ↦ c by funext t; exact hf t]
    exact (cesaroMeanAt_const c hn).symm
  exact hc (tendsto_nhds_unique hconst hzero)

/-- The three elementary corrected unary/root observables used to reject
the invariant divisors.  The function `χ` is the arbitrary controller
character appearing in the `p₂` root moment. -/
def unaryMeanObservable
    (z : ℝ → LinkedJacobiState ℂ) (t : ℝ) : ℂ :=
  (z t).unary.Y - 1

def rootP4MeanObservable
    (z : ℝ → LinkedJacobiState ℂ) (t : ℝ) : ℂ :=
  (z t).jacobi.p4 - 1

def rootP2MeanObservable
    (z : ℝ → LinkedJacobiState ℂ)
    (χ : ℝ → ℂ) (t : ℝ) : ℂ :=
  (z t).jacobi.p2 * χ t - (1 / 4 : ℂ)

/-- **Degenerate-branch elimination by corrected selector moments.**

For a recurrent linked trajectory on the full residual locus, zero
Cesàro limits of the unary mean and the two root moments force the unary
state into the generic locus.  The all-cases recurrent reduction then
supplies its global horizontal-or-horocycle canonical-lambda lift.

The result intentionally assumes only the unary component of the ODE.
The elliptic clock, gauge, controller radii, and the phase character `χ`
play no role in excluding the three modular divisors. -/
theorem recurrentUnary_generic_of_selectorMomentLimits
    {z : ℝ → LinkedJacobiState ℂ}
    (hz :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock
        (fun t ↦ (z t).unary))
    {t₀ : ℝ}
    (hrec :
      ForwardRecurrentUnaryModularAt
        (fun t ↦ (z t).unary) t₀)
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
      UnaryModularState.B (z t₀).unary ≠ 0 ∧
      ∃ lift : ℝ → ℍ,
        Continuous lift ∧
        (∀ t,
          UnaryModularState.lambdaCoordinate (z t).unary =
            canonicalLambda (lift t)) ∧
        IsHorizontalOrHorocycleLift
          (fun t ↦ (z t).unary) lift t₀ := by
  rcases
      recurrentUnarySelectorReduction hz hrec
        (hresidual t₀ .unaryJacobi) with
    hdegenerate | hgeneric
  · rcases hdegenerate.1 with hA | hC | hB
    · have hAall := hz.A_eq_zero hA
      have hp2zero : ∀ t, (z t).jacobi.p2 = 0 := by
        intro t
        have hlink :=
          hresidual t .coefficientLinkTwo
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
    · have hCall := hz.C_eq_zero hC
      have hp4zero : ∀ t, (z t).jacobi.p4 = 0 := by
        intro t
        have hlink :=
          hresidual t .coefficientLinkFour
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
    · have hBall := hz.B_eq_zero hB
      have hYzero : ∀ t, (z t).unary.Y = 0 := by
        intro t
        have hjacobi :=
          hresidual t .unaryJacobi
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
  · exact hgeneric

end

end HGAS.Modular
