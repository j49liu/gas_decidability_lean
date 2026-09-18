import HGAS.Compiler.AllAffineCompactSourceClock
import HGAS.Dynamics.FiniteFlowTwoSidedGenericZeroOrbit
import HGAS.Dynamics.IntegralCurveStateTimeChange
import Mathlib.Tactic

/-!
# A genuine two-sided physical clock for an all-affine source orbit

The original compact-source clock uses a constant extension on negative
time because forward stability only needs `t ≥ 0`.  For recurrent
classification we instead use the actual intrinsic speed

```text
       w(t) = (1 + ‖z(t)‖²)⁻ᴷ
```

at every real compact time.  If the selected compact orbit is generic for
this speed in both time directions, both ends of its clock diverge.  The
inverse clock therefore converts the complete slowed affine orbit into a
complete integral curve of the unscaled polynomial source.
-/

namespace HGAS

open Filter Function Set Topology
open scoped BoundedContinuousFunction Interval

noncomputable section

namespace CompactAccumulatorPipelineCode

namespace AllAffineCompactSourceTwoSidedClock

open AllAffineCompactSourceChart
open AllAffineCompactSourceClock
open AllAffineCompactSourceTrajectory

variable {n m : ℕ}

/-- The unmodified compactification speed along a complete affine orbit. -/
def twoSidedClockWeight
    (K : ℕ) (γ : ℝ → (Fin n → ℝ)) (t : ℝ) : ℝ :=
  affineSpeed K (γ t)

theorem continuous_twoSidedClockWeight
    (K : ℕ) {γ : ℝ → (Fin n → ℝ)}
    (hγ : Continuous γ) :
    Continuous (twoSidedClockWeight K γ) :=
  (continuous_affineSpeed K).comp hγ

theorem twoSidedClockWeight_pos
    (K : ℕ) (γ : ℝ → (Fin n → ℝ)) (t : ℝ) :
    0 < twoSidedClockWeight K γ t :=
  affineSpeed_pos K (γ t)

/-- Reversing the speed reverses its integral clock. -/
theorem integralClock_comp_neg
    (w : ℝ → ℝ) (T : ℝ) :
    integralClock (fun t ↦ w (-t)) T =
      -integralClock w (-T) := by
  rw [integralClock, intervalIntegral.integral_comp_neg]
  simp only [neg_zero]
  rw [intervalIntegral.integral_symm]
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

/-- The clock integral is the orbit integral of the intrinsic speed on
every nonnegative horizon. -/
theorem integralClock_twoSidedWeight_eq_orbitIntegral
    (v : FiniteSourceSpace n m) (T : ℝ) :
    integralClock
        (twoSidedClockWeight K (affineCurve ϕ hinv v)) T =
      Dynamics.orbitIntegral (ϕ.restrict hinv)
        (affineSpeedBCF K) T v := by
  unfold integralClock Dynamics.orbitIntegral
    twoSidedClockWeight affineCurve
  apply intervalIntegral.integral_congr
  intro t _
  rfl

/-- A positive common speed mean for the forward and reversed restricted
flows makes the actual two-sided speed a global positive integral clock. -/
theorem positiveClock_of_twoSidedGenericSpeed
    (v : FiniteSourceSpace n m)
    {c : ℝ} (hc : 0 < c)
    (hforward :
      Tendsto
        (fun q : ℕ ↦
          Dynamics.integerOrbitAverageObservable
            (ϕ.restrict hinv) (affineSpeedBCF K) (q + 1) v)
        atTop (𝓝 c))
    (hreverse :
      Tendsto
        (fun q : ℕ ↦
          Dynamics.integerOrbitAverageObservable
            (ϕ.restrict hinv).reverse
            (affineSpeedBCF K) (q + 1) v)
        atTop (𝓝 c)) :
    PositiveIntegralClock
      (twoSidedClockWeight K (affineCurve ϕ hinv v)) := by
  let w : ℝ → ℝ :=
    twoSidedClockWeight K (affineCurve ϕ hinv v)
  let wrev : ℝ → ℝ := fun t ↦ w (-t)
  have hw : Continuous w :=
    continuous_twoSidedClockWeight K
      (continuous_affineCurve ϕ hinv v)
  have hwpos : ∀ t, 0 < w t :=
    fun t ↦ twoSidedClockWeight_pos K
      (affineCurve ϕ hinv v) t
  have hwrev : Continuous wrev := by
    exact hw.comp continuous_neg
  have hwrevpos : ∀ t, 0 < wrev t :=
    fun t ↦ hwpos (-t)
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
      simp only [positiveIntegerHorizon, Nat.cast_add, Nat.cast_one]
      rw [integralClock_twoSidedWeight_eq_orbitIntegral
        K ϕ hinv v]
    rw [← heq]
    exact hforward
  have hmeanReverse :
      Tendsto
        (fun q : ℕ ↦
          (positiveIntegerHorizon q)⁻¹ *
            integralClock wrev (positiveIntegerHorizon q))
        atTop (𝓝 c) := by
    have heq :
        (fun q : ℕ ↦
          Dynamics.integerOrbitAverageObservable
            (ϕ.restrict hinv).reverse
            (affineSpeedBCF K) (q + 1) v) =
          fun q : ℕ ↦
            (positiveIntegerHorizon q)⁻¹ *
              integralClock wrev (positiveIntegerHorizon q) := by
      funext q
      rw [Dynamics.integerOrbitAverageObservable_apply]
      simp only [positiveIntegerHorizon, Nat.cast_add, Nat.cast_one]
      rfl
    rw [← heq]
    exact hreverse
  have htop :
      Tendsto (integralClock w) atTop atTop :=
    integralClock_tendsto_atTop_of_positive_integerMean
      hw hwpos hc hmean
  have hrevTop :
      Tendsto (integralClock wrev) atTop atTop :=
    integralClock_tendsto_atTop_of_positive_integerMean
      hwrev hwrevpos hc hmeanReverse
  have hnegRev :
      Tendsto (fun T ↦ -integralClock wrev T)
        atTop atBot :=
    tendsto_neg_atTop_atBot.comp hrevTop
  have hcomp :
      Tendsto (fun T ↦ integralClock w (-T))
        atTop atBot := by
    apply hnegRev.congr'
    exact Eventually.of_forall fun T ↦ by
      change
        -integralClock (fun t ↦ w (-t)) T =
          integralClock w (-T)
      rw [integralClock_comp_neg]
      ring
  have hbot :
      Tendsto (integralClock w) atBot atBot := by
    have h :=
      hcomp.comp (tendsto_neg_atBot_atTop :
        Tendsto (fun t : ℝ ↦ -t) atBot atTop)
    simpa only [Function.comp_def, neg_neg] using h
  exact
    { continuous := hw
      positive := hwpos
      tendsto_atTop := htop
      tendsto_atBot := hbot }

/-- The genuine inverse-clock affine curve. -/
def physicalCurve
    (v : FiniteSourceSpace n m)
    (hclock :
      PositiveIntegralClock
        (twoSidedClockWeight K (affineCurve ϕ hinv v)))
    (τ : ℝ) :
    Fin n → ℝ :=
  affineCurve ϕ hinv v
    ((PositiveIntegralClock.orderIso hclock).symm τ)

include hP hcurve in
/-- In physical time the genuine two-sided curve is a complete integral
curve of the unscaled source field. -/
theorem physicalCurve_isIntegralCurve
    (v : FiniteSourceSpace n m)
    (hclock :
      PositiveIntegralClock
        (twoSidedClockWeight K (affineCurve ϕ hinv v))) :
    IsIntegralCurve
      (physicalCurve K ϕ hinv v hclock)
      (fun _ x ↦ PolynomialFieldCode.realize P x) := by
  have hscaled :=
    affinePoint_isIntegralCurve
      K κ P h hP ϕ hcurve hinv v
  simpa only [physicalCurve, affineCurve,
    twoSidedClockWeight] using
    HGAS.IsIntegralCurve.reparametrize_from_timeScaledField
      hscaled hclock

/-- Forward recurrence also survives this unmodified inverse clock. -/
theorem physicalCurve_forwardRecurrentAt
    (v : FiniteSourceSpace n m)
    (hclock :
      PositiveIntegralClock
        (twoSidedClockWeight K (affineCurve ϕ hinv v)))
    (hrec :
      ForwardRecurrentAt
        (fun t : ℝ ↦ (ϕ.restrict hinv) t v) 0) :
    ForwardRecurrentAt
      (physicalCurve K ϕ hinv v hclock) 0 := by
  exact
    (hrec.map continuous_affinePoint).inverseClock hclock

end AllAffineCompactSourceTwoSidedClock

end CompactAccumulatorPipelineCode

end

end HGAS
