import HGAS.Modular.UnaryConstantTimeRescaling
import HGAS.Modular.UnaryComparisonReconstruction
import HGAS.Analysis.CesaroConstantTimeRescaling
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Forward-only normalization of signed unary clocks

Complex conjugation changes the unary clock `i * Ω` into `-i * Ω`
because the unary vector field has rational coefficients. It preserves
forward recurrence and coordinate norms at the same physical times.
Conjugating a negative-frequency trajectory before a positive time
rescaling therefore normalizes its clock without assuming reverse
recurrence or backward Cesàro bounds.

This module supplies only that normalization step. It does not assert
canonical selection or the broader source-trajectory equivalence.
-/

namespace Stability.Selection

open HGAS HGAS.Modular Filter Topology

noncomputable section

/-- Coordinatewise complex conjugation of the unary modular state. -/
def conjugateUnary (z : UnaryModularState ℂ) : UnaryModularState ℂ where
  A := star z.A
  C := star z.C
  E := star z.E
  Y := star z.Y

@[simp]
theorem conjugateUnary_involutive (z : UnaryModularState ℂ) :
    conjugateUnary (conjugateUnary z) = z := by
  ext <;> simp [conjugateUnary]

/-- The rational unary vector field commutes with complex conjugation. -/
theorem conjugateUnary_vectorField (z : UnaryModularState ℂ) :
    conjugateUnary (UnaryModularState.vectorField z) =
      UnaryModularState.vectorField (conjugateUnary z) := by
  ext <;> simp [conjugateUnary, UnaryModularState.vectorField]

/-- The Jacobi residual is conjugated, so its vanishing is preserved. -/
theorem conjugateUnary_jacobiResidual (z : UnaryModularState ℂ) :
    UnaryModularState.jacobiResidual (conjugateUnary z) =
      star (UnaryModularState.jacobiResidual z) := by
  simp [conjugateUnary, UnaryModularState.jacobiResidual]

/-- Coordinate magnitudes are unchanged at the same physical time. Thus
any growth bound expressed in these magnitudes is preserved. -/
theorem conjugateUnary_norms (z : UnaryModularState ℂ) :
    ‖(conjugateUnary z).A‖ = ‖z.A‖ ∧
    ‖(conjugateUnary z).C‖ = ‖z.C‖ ∧
    ‖(conjugateUnary z).E‖ = ‖z.E‖ ∧
    ‖(conjugateUnary z).Y‖ = ‖z.Y‖ := by
  simp [conjugateUnary]

/-- Conjugating a unary trajectory conjugates its clock without reversing
time. -/
theorem conjugateUnary_isScaledTrajectory
    {κ : ℂ} {z : ℝ → UnaryModularState ℂ}
    (hz : IsScaledUnaryModularTrajectory κ z) :
    IsScaledUnaryModularTrajectory (star κ) (fun t ↦ conjugateUnary (z t)) := by
  constructor
  · intro t
    simpa [conjugateUnary, UnaryModularState.vectorField] using (hz.A t).star
  · intro t
    simpa [conjugateUnary, UnaryModularState.vectorField] using (hz.C t).star
  · intro t
    simpa [conjugateUnary, UnaryModularState.vectorField] using (hz.E t).star
  · intro t
    simpa [conjugateUnary, UnaryModularState.vectorField] using (hz.Y t).star

/-- The same return-time sequence proves recurrence after conjugation. -/
def conjugateUnary_forwardRecurrentAt
    {z : ℝ → UnaryModularState ℂ} {t₀ : ℝ}
    (hrec : ForwardRecurrentUnaryModularAt z t₀) :
    ForwardRecurrentUnaryModularAt (fun t ↦ conjugateUnary (z t)) t₀ where
  times := hrec.times
  times_tendsto := hrec.times_tendsto
  A_tendsto := hrec.A_tendsto.star
  C_tendsto := hrec.C_tendsto.star
  E_tendsto := hrec.E_tendsto.star
  Y_tendsto := hrec.Y_tendsto.star

/-- Select the original or conjugate state according to the clock sign.
This selection changes state coordinates, never the direction of time. -/
def orientUnary (Ω : ℝ) (z : UnaryModularState ℂ) : UnaryModularState ℂ :=
  if 0 ≤ Ω then z else conjugateUnary z

/-- Sign orientation changes the unary frequency to its absolute value. -/
theorem orientUnary_isScaledTrajectory
    {Ω : ℝ} {z : ℝ → UnaryModularState ℂ}
    (hz : IsScaledUnaryModularTrajectory (Complex.I * (Ω : ℂ)) z) :
    IsScaledUnaryModularTrajectory (Complex.I * (|Ω| : ℝ))
      (fun t ↦ orientUnary Ω (z t)) := by
  by_cases hΩ : 0 ≤ Ω
  · simpa only [orientUnary, if_pos hΩ, abs_of_nonneg hΩ] using hz
  · have hΩneg : Ω < 0 := lt_of_not_ge hΩ
    simpa [orientUnary, hΩ, abs_of_neg hΩneg] using
      conjugateUnary_isScaledTrajectory hz

/-- Forward recurrence survives sign orientation with no reverse-time
hypothesis. -/
def orientUnary_forwardRecurrentAt
    (Ω : ℝ) {z : ℝ → UnaryModularState ℂ} {t₀ : ℝ}
    (hrec : ForwardRecurrentUnaryModularAt z t₀) :
    ForwardRecurrentUnaryModularAt (fun t ↦ orientUnary Ω (z t)) t₀ := by
  by_cases hΩ : 0 ≤ Ω
  · simpa only [orientUnary, if_pos hΩ] using hrec
  · simpa only [orientUnary, if_neg hΩ] using conjugateUnary_forwardRecurrentAt hrec

/-- The positive time scale needed after sign orientation. -/
def forwardUnaryScale (Ω : ℝ) : ℝ := Real.pi / |Ω|

theorem forwardUnaryScale_pos {Ω : ℝ} (hΩ : Ω ≠ 0) :
    0 < forwardUnaryScale Ω :=
  div_pos Real.pi_pos (abs_pos.mpr hΩ)

/-- The normalized trajectory uses only a positive change of time. -/
def forwardStandardizedUnary (Ω : ℝ) (z : ℝ → UnaryModularState ℂ)
    (t : ℝ) : UnaryModularState ℂ :=
  orientUnary Ω (z (forwardUnaryScale Ω * t))

theorem forwardStandardizedUnary_isScaledTrajectory
    {Ω : ℝ} (hΩ : Ω ≠ 0) {z : ℝ → UnaryModularState ℂ}
    (hz : IsScaledUnaryModularTrajectory (Complex.I * (Ω : ℂ)) z) :
    IsScaledUnaryModularTrajectory modularIndependentVariableClock
      (forwardStandardizedUnary Ω z) := by
  have hscale : forwardUnaryScale Ω * |Ω| = Real.pi := by
    dsimp [forwardUnaryScale]
    exact div_mul_cancel₀ _ (abs_ne_zero.mpr hΩ)
  have hclock : (forwardUnaryScale Ω : ℂ) * (Complex.I * (|Ω| : ℝ)) =
      modularIndependentVariableClock := by
    unfold modularIndependentVariableClock
    calc
      _ = ((forwardUnaryScale Ω * |Ω| : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      _ = _ := by rw [hscale]
  have h := (orientUnary_isScaledTrajectory hz).rescale (forwardUnaryScale Ω)
  simpa only [hclock, forwardStandardizedUnary] using h

/-- A nonzero clock can be normalized using forward recurrence alone. -/
def forwardStandardizedUnary_forwardRecurrentAt
    {Ω : ℝ} (hΩ : Ω ≠ 0) {z : ℝ → UnaryModularState ℂ}
    (hrec : ForwardRecurrentUnaryModularAt z 0) :
    ForwardRecurrentUnaryModularAt (forwardStandardizedUnary Ω z) 0 :=
  (orientUnary_forwardRecurrentAt Ω hrec).rescale_zero (forwardUnaryScale_pos hΩ)

/-- Complex conjugation commutes with every finite-horizon Cesàro mean. -/
theorem cesaroMeanAt_star (f : ℝ → ℂ) (T : ℝ) :
    HGAS.Analysis.cesaroMeanAt (fun t ↦ star (f t)) T =
      star (HGAS.Analysis.cesaroMeanAt f T) := by
  simp [HGAS.Analysis.cesaroMeanAt, intervalIntegral, integral_conj]

/-- Forward means conjugate along exactly the same horizons. -/
theorem tendsto_cesaroMeanAt_star
    {ι : Type*} {l : Filter ι} {f : ℝ → ℂ} {T : ι → ℝ} {L : ℂ}
    (h : Tendsto (fun n ↦ HGAS.Analysis.cesaroMeanAt f (T n)) l (𝓝 L)) :
    Tendsto (fun n ↦ HGAS.Analysis.cesaroMeanAt (fun t ↦ star (f t)) (T n))
      l (𝓝 (star L)) := by
  simpa only [cesaroMeanAt_star] using h.star

/-- Conjugation sends the first-harmonic test at phase `α` to the same
test at phase `-α`. Thus real prescribed moments retain their values. -/
theorem star_firstHarmonic (Y : ℂ) (α : ℝ) :
    star (Y * Complex.exp (-(α : ℂ) * Complex.I)) =
      star Y * Complex.exp (-((-α : ℝ) : ℂ) * Complex.I) := by
  simp [← Complex.exp_conj]

/-- The signed normalization preserves every finite-horizon coordinate
growth integral exactly, before the positive time rescaling. -/
theorem integral_norm_star_rpow (f : ℝ → ℂ) (μ T : ℝ) :
    (∫ t in (0 : ℝ)..T, ‖star (f t)‖ ^ μ) =
      ∫ t in (0 : ℝ)..T, ‖f t‖ ^ μ := by
  simp

/-- A positive change of time transports forward power means by dividing
the horizon. Conjugation leaves the integrand unchanged in norm. -/
theorem normPowerMean_conjugate_rescale
    (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (μ T : ℝ) :
    (T / a)⁻¹ * (∫ t in (0 : ℝ)..T / a, ‖star (f (a * t))‖ ^ μ) =
      T⁻¹ * (∫ t in (0 : ℝ)..T, ‖f t‖ ^ μ) := by
  simp only [norm_star]
  rw [intervalIntegral.integral_comp_mul_left (fun t ↦ ‖f t‖ ^ μ) ha.ne']
  simp only [mul_zero, smul_eq_mul, mul_div_cancel₀ _ ha.ne']
  field_simp

/-- A full forward Cesàro limit is preserved by positive time rescaling;
the corresponding limit for a conjugated observable is conjugated. -/
theorem tendsto_cesaroMeanAt_conjugate_rescale
    (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) {L : ℂ}
    (hmean : Tendsto (HGAS.Analysis.cesaroMeanAt f) atTop (𝓝 L)) :
    Tendsto
      (HGAS.Analysis.cesaroMeanAt (fun t ↦ star (f (a * t))))
      atTop (𝓝 (star L)) := by
  have hscaled := hmean.comp (tendsto_id.const_mul_atTop ha)
  have hid (T : ℝ) :
      HGAS.Analysis.cesaroMeanAt (fun t ↦ f (a * t)) T =
        HGAS.Analysis.cesaroMeanAt f (a * T) := by
    have h := HGAS.Analysis.cesaroMeanAt_comp_mul_div f (T := a * T) ha.ne'
    simpa only [mul_div_cancel_left₀ _ ha.ne'] using h
  have hforward :
      Tendsto (HGAS.Analysis.cesaroMeanAt (fun t ↦ f (a * t))) atTop (𝓝 L) := by
    change Tendsto (fun T : ℝ ↦
      HGAS.Analysis.cesaroMeanAt (fun t ↦ f (a * t)) T) atTop (𝓝 L)
    simpa only [Function.comp_def, hid, id_eq] using hscaled
  exact tendsto_cesaroMeanAt_star hforward

end

end Stability.Selection
