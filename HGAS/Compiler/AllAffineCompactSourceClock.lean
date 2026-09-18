import HGAS.Compiler.AllAffineCompactSourceTrajectory
import HGAS.Dynamics.FiniteFlowGenericPoint
import HGAS.Dynamics.PositiveMeanTimeReparametrization
import Mathlib.Tactic

/-!
# The physical clock of the all-affine compact source

The finite central chart recovers an affine trajectory satisfying

```
                 z' = a_K(z) P(z),
       a_K(z) = (1 + ‖z‖²)⁻ᴷ.
```

Although `a_K` is everywhere positive, it has no uniform positive lower
bound on affine space.  This file packages it as a bounded continuous
observable on the finite compactification chart and applies
`PositiveMeanTimeReparametrization`: a recurrent generic point whose
`a_K`-average is positive has a global physical clock.  Inverting that
clock produces an ordinary forward trajectory of `z' = P(z)` and
preserves recurrence.
-/

namespace HGAS

open Filter Function Set Topology
open scoped BoundedContinuousFunction

noncomputable section

namespace CompactAccumulatorPipelineCode

namespace AllAffineCompactSourceClock

open AllAffineCompactSourceChart
open AllAffineCompactSourceTrajectory

variable {n m : ℕ}

/-- Intrinsic compactification speed, bundled as a bounded continuous
observable on the finite source chart. -/
def affineSpeedBCF (K : ℕ) :
    FiniteSourceSpace n m →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun v ↦ affineSpeed K (affinePoint v),
      (continuous_affineSpeed K).comp continuous_affinePoint⟩
    1
    (by
      intro x y
      rw [Real.dist_eq]
      have hx0 : 0 ≤ affineSpeed K (affinePoint x) :=
        affineSpeed_nonneg K (affinePoint x)
      have hx1 : affineSpeed K (affinePoint x) ≤ 1 :=
        affineSpeed_le_one K (affinePoint x)
      have hy0 : 0 ≤ affineSpeed K (affinePoint y) :=
        affineSpeed_nonneg K (affinePoint y)
      have hy1 : affineSpeed K (affinePoint y) ≤ 1 :=
        affineSpeed_le_one K (affinePoint y)
      change
        |affineSpeed K (affinePoint x) -
          affineSpeed K (affinePoint y)| ≤ 1
      rw [abs_le]
      constructor <;> linarith)

@[simp]
theorem affineSpeedBCF_apply
    (K : ℕ) (v : FiniteSourceSpace n m) :
    affineSpeedBCF K v = affineSpeed K (affinePoint v) :=
  rfl

variable
  (K : ℕ) (κ : RationalCode)
  (P : PolynomialFieldCode n)
  (h : Fin m → PolynomialCode n)
  (hP :
    ∀ j,
      MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
        (layout n) (2 * K) (P j))
  (ϕ : Flow ℝ (SourceSpace n m))
  (hcurve :
    ∀ v,
      IsIntegralCurve
        (fun t ↦ (ϕ t v).1)
        (fun _ x ↦
          PolynomialFieldCode.realize
            (fieldCode (layout n) (2 * K) κ P h) x))
  (hinv :
    IsInvariant ϕ (sourceFiniteInteriorSet (m := m) (layout n)))

/-- The affine curve recovered from a finite-chart compact orbit. -/
def affineCurve (v : FiniteSourceSpace n m) (t : ℝ) :
    Fin n → ℝ :=
  affinePoint ((ϕ.restrict hinv) t v)

theorem continuous_affineCurve
    (v : FiniteSourceSpace n m) :
    Continuous (affineCurve ϕ hinv v) := by
  exact continuous_affinePoint.comp
    ((ϕ.restrict hinv).continuous continuous_id continuous_const)

include hP hcurve in
/-- The recovered curve is a forward trajectory of the intrinsically
time-scaled affine polynomial field. -/
theorem affineCurve_isForwardTrajectory
    (v : FiniteSourceSpace n m) :
    IsForwardTrajectory
      (timeScaledField (affineSpeed K)
        (PolynomialFieldCode.realize P))
      (affineCurve ϕ hinv v) (affinePoint v) := by
  constructor
  · simp [affineCurve]
  · intro t _
    exact
      (affinePoint_isIntegralCurve K κ P h hP
        ϕ hcurve hinv v t).hasDerivWithinAt

/-- The forward-extended state clock agrees, on every nonnegative
horizon, with the orbit integral of the bundled speed observable. -/
theorem integralClock_stateClockWeight_eq_orbitIntegral
    (v : FiniteSourceSpace n m) {T : ℝ} (hT : 0 ≤ T) :
    integralClock
          (stateClockWeight (affineSpeed K)
            (affineCurve ϕ hinv v)) T =
      Dynamics.orbitIntegral (ϕ.restrict hinv)
        (affineSpeedBCF K) T v := by
  unfold integralClock Dynamics.orbitIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hT] at ht
  simp only [stateClockWeight,
    forwardExtension_of_nonneg _ ht.1,
    affineCurve, affineSpeedBCF_apply]

/-- A positive generic mean of the intrinsic speed produces a global
physical clock for the recovered affine trajectory. -/
theorem positiveClock_of_genericSpeed
    (v : FiniteSourceSpace n m)
    {c : ℝ} (hc : 0 < c)
    (hgeneric :
      Tendsto
        (fun q : ℕ ↦
          Dynamics.integerOrbitAverageObservable
            (ϕ.restrict hinv) (affineSpeedBCF K) (q + 1) v)
        atTop (𝓝 c)) :
    PositiveIntegralClock
      (stateClockWeight (affineSpeed K)
        (affineCurve ϕ hinv v)) := by
  let w : ℝ → ℝ :=
    stateClockWeight (affineSpeed K) (affineCurve ϕ hinv v)
  have hw : Continuous w := by
    exact
      (continuous_affineSpeed K).comp
        (continuous_forwardExtension
          (continuous_affineCurve ϕ hinv v).continuousOn)
  have hwpos : ∀ t, 0 < w t := by
    intro t
    exact affineSpeed_pos K _
  have hmean :
      Tendsto
        (fun q : ℕ ↦
          (positiveIntegerHorizon q)⁻¹ *
            integralClock w (positiveIntegerHorizon q))
        atTop (𝓝 c) := by
    have heq :
        (fun q : ℕ ↦
          Dynamics.integerOrbitAverageObservable
            (ϕ.restrict hinv) (affineSpeedBCF K) (q + 1) v) =
          fun q : ℕ ↦
            (positiveIntegerHorizon q)⁻¹ *
              integralClock w (positiveIntegerHorizon q) := by
      funext q
      rw [Dynamics.integerOrbitAverageObservable_apply]
      simp only [positiveIntegerHorizon, Nat.cast_add,
        Nat.cast_one]
      rw [integralClock_stateClockWeight_eq_orbitIntegral
        K ϕ hinv v (by positivity : 0 ≤ (q : ℝ) + 1)]
    rw [← heq]
    exact hgeneric
  have hbot :
      Tendsto (integralClock w) atBot atBot := by
    exact
      stateClockWeight_tendsto_atBot
        (by simp [affineCurve])
        (affineSpeed_pos K (affinePoint v))
  exact
    positiveIntegralClock_of_positive_integerMean
      hw hwpos hc hmean hbot

/-- The ordinary affine trajectory obtained by inverting a global
physical clock. -/
def physicalCurve
    (v : FiniteSourceSpace n m)
    (hclock :
      PositiveIntegralClock
        (stateClockWeight (affineSpeed K)
          (affineCurve ϕ hinv v)))
    (τ : ℝ) :
    Fin n → ℝ :=
  affineCurve ϕ hinv v
    ((PositiveIntegralClock.orderIso hclock).symm τ)

include hP hcurve in
/-- In physical time the recovered curve solves the unscaled polynomial
source ODE exactly. -/
theorem physicalCurve_isForwardTrajectory
    (v : FiniteSourceSpace n m)
    (hclock :
      PositiveIntegralClock
        (stateClockWeight (affineSpeed K)
          (affineCurve ϕ hinv v))) :
    IsForwardTrajectory
      (PolynomialFieldCode.realize P)
      (physicalCurve K ϕ hinv v hclock)
      (affinePoint v) := by
  exact
    (affineCurve_isForwardTrajectory K κ P h hP
      ϕ hcurve hinv v).reparametrize_from_timeScaledField hclock

/-- Forward recurrence of the compact finite-chart orbit survives in the
ordinary affine physical trajectory. -/
theorem physicalCurve_forwardRecurrentAt
    (v : FiniteSourceSpace n m)
    (hclock :
      PositiveIntegralClock
        (stateClockWeight (affineSpeed K)
          (affineCurve ϕ hinv v)))
    (hrec :
      ForwardRecurrentAt
        (fun t : ℝ ↦ (ϕ.restrict hinv) t v) 0) :
    ForwardRecurrentAt
      (physicalCurve K ϕ hinv v hclock) 0 := by
  exact
    (hrec.map continuous_affinePoint).inverseClock hclock

end AllAffineCompactSourceClock

end CompactAccumulatorPipelineCode

end

end HGAS
