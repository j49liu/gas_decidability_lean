import HGAS.Analysis.CesaroExponentialSeriesArbitraryHorizon
import Mathlib.Tactic

/-!
# Linearity of finite-horizon Cesàro means

These elementary identities are useful when a physical observable differs
from a canonical Fourier observable by a fixed nonzero complex twist.
-/

noncomputable section

open Filter MeasureTheory Topology
open scoped Interval

namespace HGAS.Analysis

/-- If two observables agree on the nonnegative ray, their Cesàro means
agree eventually along every horizon tending to `+∞`. -/
theorem eventually_cesaroMeanAt_eq_of_eqOn_nonnegative
    {f g : ℝ → ℂ} {T : ℕ → ℝ}
    (hT : Tendsto T atTop atTop)
    (hfg : ∀ t, 0 ≤ t → f t = g t) :
    (fun q ↦ cesaroMeanAt f (T q)) =ᶠ[atTop]
      fun q ↦ cesaroMeanAt g (T q) := by
  have hTpos : ∀ᶠ q in atTop, 0 < T q :=
    hT.eventually (eventually_gt_atTop 0)
  filter_upwards [hTpos] with q hq
  unfold cesaroMeanAt
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hq.le] at ht
  exact hfg t ht.1

/-- A constant complex scalar may be pulled through a finite-horizon
Cesàro mean. -/
theorem cesaroMeanAt_const_mul
    (c : ℂ) (f : ℝ → ℂ) (T : ℝ) :
    cesaroMeanAt (fun t ↦ c * f t) T =
      c * cesaroMeanAt f T := by
  unfold cesaroMeanAt
  rw [intervalIntegral.integral_const_mul]
  ring

/-- Multiplication by a fixed scalar transports an arbitrary-horizon
Cesàro limit. -/
theorem tendsto_cesaroMeanAt_const_mul
    (c L : ℂ) (f : ℝ → ℂ) {T : ℕ → ℝ}
    (h :
      Tendsto (fun q ↦ cesaroMeanAt f (T q))
        atTop (𝓝 L)) :
    Tendsto
      (fun q ↦ cesaroMeanAt (fun t ↦ c * f t) (T q))
      atTop (𝓝 (c * L)) := by
  have hmul :=
    (tendsto_const_nhds.mul h :
      Tendsto
        (fun q ↦ c * cesaroMeanAt f (T q))
        atTop (𝓝 (c * L)))
  exact hmul.congr'
    (Eventually.of_forall fun q ↦
      (cesaroMeanAt_const_mul c f (T q)).symm)

end HGAS.Analysis
