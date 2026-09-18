import HGAS.Analysis.FiniteCoordinateNormSq
import HGAS.Analysis.JacobiThetaHorizontalUniformBounds
import HGAS.Arithmetic.CanonicalFixedDetectorAlignment
import HGAS.Arithmetic.NormalizedCorrectedCanonicalFixedDetectorGraph
import HGAS.Modular.EisensteinBounds
import Mathlib.Tactic

/-!
# A uniform bound for the canonical raw detector orbit

Central compactification sends an affine point `z` to the positive
spherical chart with scalar coordinate

```
                         w = (1 + ‖z‖²)^(-1/2).
```

To obtain a uniform positive lower bound for `w`, one must first prove
that the *whole* canonical detector state is uniformly bounded, not only
the final detector observable.  This file performs that estimate at the
structured-state level.

The analytic input is elementary:

* all controller and terminal phases have unit radius;
* horizontal theta series and their first derivatives have Gaussian
  majorants independent of the real parts of their arguments;
* the centered `theta_3` series has a uniform positive gap from zero;
* the gauge has radius `1/4`; and
* every Poisson denominator `1 - χ/2` has modulus at least `1/2`.

The resulting constants are intentionally coarse.  Their only purpose is
to be finite, explicit, and independent of time.
-/

noncomputable section

open scoped BigOperators

namespace HGAS.CanonicalFixedDetectorRawOrbitBound

open HGAS
open HGAS.Analysis.JacobiThetaHorizontalUniformBounds
open HGAS.Clocks
open HGAS.Modular
open Complex Real

variable {eqs vars : ℕ}

/-- One common Gaussian bound used for every theta value appearing in
the canonical linked block. -/
def canonicalThetaBound : ℝ :=
  thetaBound thetaGaugeHeight thetaGaugeHeight

/-- One common Gaussian bound used for every first elliptic theta
derivative appearing in the canonical linked block. -/
def canonicalThetaPrimeBound : ℝ :=
  thetaPrimeBound thetaGaugeHeight thetaGaugeHeight

/-- Explicit `E₂` bound inherited from the divisor-sum majorant. -/
def canonicalE2Bound : ℝ :=
  1 + 24 * ∑' n : ℕ+, e2Majorant n

/-- Coarse bound for `Delta = theta_1'/pi`. -/
def canonicalDeltaBound : ℝ :=
  (Real.pi * canonicalThetaBound +
      canonicalThetaPrimeBound) / Real.pi

theorem one_le_thetaGaugeHeight :
    (1 : ℝ) ≤ thetaGaugeHeight := by
  have hlog :
      Real.log (256 : ℝ) = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
    norm_num
  have hpi := Real.pi_le_four
  have htwo := log_two_gt_d9
  unfold thetaGaugeHeight
  rw [div_eq_mul_inv]
  apply (le_mul_inv_iff₀ Real.pi_pos).2
  rw [hlog]
  nlinarith

theorem canonicalThetaBound_nonneg :
    0 ≤ canonicalThetaBound :=
  thetaBound_nonneg _ _

theorem canonicalThetaPrimeBound_nonneg :
    0 ≤ canonicalThetaPrimeBound :=
  thetaPrimeBound_nonneg _ _

theorem canonicalE2Bound_nonneg :
    0 ≤ canonicalE2Bound := by
  unfold canonicalE2Bound
  have hsum : 0 ≤ ∑' n : ℕ+, e2Majorant n :=
    tsum_nonneg fun n ↦ by
      unfold e2Majorant
      positivity
  positivity

theorem canonicalDeltaBound_nonneg :
    0 ≤ canonicalDeltaBound := by
  unfold canonicalDeltaBound
  exact div_nonneg
    (add_nonneg
      (mul_nonneg Real.pi_pos.le canonicalThetaBound_nonneg)
      canonicalThetaPrimeBound_nonneg)
    Real.pi_pos.le

private abbrev tauPath
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) (t : ℝ) : UpperHalfPlane :=
  CanonicalFixedDetectorTrajectory.modularPath
    thetaGaugeBasePoint
    (CanonicalFixedDetectorTrajectory.omegaFrequency
      parameters controller j) t

private abbrev centeredPath
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) (t : ℝ) : ℂ :=
  CanonicalFixedDetectorChart.centeredEllipticPath 0
    (CanonicalFixedDetectorTrajectory.numberFrequency
      parameters I controller j) t

private abbrev ellipticPath
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) (t : ℝ) : ℂ :=
  CanonicalFixedDetectorTrajectory.ellipticPath
    (CanonicalFixedDetectorChart.halfPeriodInitialElliptic
      0 thetaGaugeBasePoint)
    (CanonicalFixedDetectorTrajectory.omegaFrequency
      parameters controller j)
    (CanonicalFixedDetectorTrajectory.numberFrequency
      parameters I controller j) t

@[simp]
theorem tauPath_im
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) (t : ℝ) :
    ((tauPath parameters controller j t : UpperHalfPlane) : ℂ).im =
      thetaGaugeHeight := by
  rw [CanonicalFixedDetectorChart.modularPath_im]
  change (thetaGaugeBasePoint : ℂ).im = thetaGaugeHeight
  exact thetaGaugeBasePoint_im

@[simp]
theorem centeredPath_im
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) (t : ℝ) :
    (centeredPath parameters I controller j t).im = 0 := by
  rw [CanonicalFixedDetectorChart.centeredEllipticPath_im]
  simp

@[simp]
theorem ellipticPath_im
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) (t : ℝ) :
    (ellipticPath parameters I controller j t).im =
      thetaGaugeHeight / 2 := by
  rw [show
      ellipticPath parameters I controller j t =
        centeredPath parameters I controller j t +
          (1 + (tauPath parameters controller j t : ℂ)) / 2 by
      exact
        CanonicalFixedDetectorChart.ellipticPath_halfPeriod_decomposition
          0 thetaGaugeBasePoint
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j)
          (CanonicalFixedDetectorTrajectory.numberFrequency
            parameters I controller j) t]
  simp only [Complex.add_im, Complex.div_im,
    Complex.one_im, centeredPath_im]
  have hτ :=
    tauPath_im parameters controller j t
  change (tauPath parameters controller j t : ℂ).im =
    thetaGaugeHeight at hτ
  rw [hτ]
  norm_num [Complex.normSq_apply]
  ring

private theorem abs_im_le_height
    {z : ℂ} (hz : z.im = thetaGaugeHeight / 2) :
    |z.im| ≤ thetaGaugeHeight := by
  rw [hz, abs_of_nonneg
    (div_nonneg thetaGaugeHeight_pos.le (by norm_num))]
  linarith [thetaGaugeHeight_pos]

private theorem abs_shifted_im_le_height
    {z τ : ℂ}
    (hz : z.im = thetaGaugeHeight / 2)
    (hτ : τ.im = thetaGaugeHeight) :
    |(z + τ / 2).im| ≤ thetaGaugeHeight := by
  rw [Complex.add_im, Complex.div_im, hz, hτ]
  norm_num
  rw [show
      thetaGaugeHeight / 2 + thetaGaugeHeight * 2 / 4 =
        thetaGaugeHeight by ring]
  rw [abs_of_pos thetaGaugeHeight_pos]

/-- Uniform bound for the basic theta series at every argument used by
the canonical Jacobi coordinates. -/
theorem norm_jacobiTheta₂_le_canonical
    {z τ : ℂ}
    (hz : |z.im| ≤ thetaGaugeHeight)
    (hτ : τ.im = thetaGaugeHeight) :
    ‖jacobiTheta₂ z τ‖ ≤ canonicalThetaBound := by
  unfold canonicalThetaBound
  apply norm_jacobiTheta₂_le_thetaBound thetaGaugeHeight_pos hz
  exact hτ.ge

/-- Uniform bound for its first elliptic derivative at those arguments. -/
theorem norm_jacobiTheta₂'_le_canonical
    {z τ : ℂ}
    (hz : |z.im| ≤ thetaGaugeHeight)
    (hτ : τ.im = thetaGaugeHeight) :
    ‖jacobiTheta₂' z τ‖ ≤ canonicalThetaPrimeBound := by
  unfold canonicalThetaPrimeBound
  apply norm_jacobiTheta₂'_le_thetaPrimeBound thetaGaugeHeight_pos hz
  exact hτ.ge

/-- An exponential half-period factor whose argument has nonnegative
imaginary part has norm at most one. -/
private theorem norm_halfPeriodFactor_le_one
    {w : ℂ} (hw : 0 ≤ w.im) :
    ‖Complex.exp (Real.pi * Complex.I * w)‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have hre :
      (↑Real.pi * Complex.I * w).re =
        -Real.pi * w.im := by
    simp [mul_re, mul_im]
  rw [hre, ← Real.exp_zero, Real.exp_le_exp]
  nlinarith [Real.pi_pos]

/-- The divisor-sum expansion gives a common bound for `E₂` on the
canonical horizontal line. -/
theorem norm_E2_tauPath_le
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) (t : ℝ) :
    ‖EisensteinSeries.E2 (tauPath parameters controller j t)‖ ≤
      canonicalE2Bound := by
  let τ := tauPath parameters controller j t
  have hτone : 1 ≤ τ.im := by
    rw [show τ.im = thetaGaugeHeight by
      exact tauPath_im parameters controller j t]
    exact one_le_thetaGaugeHeight
  rw [EisensteinSeries.E2_eq_tsum_cexp]
  let term : ℕ+ → ℂ := fun n ↦
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * τ) ^ (n : ℕ)
  have hterm :
      Summable fun n : ℕ+ ↦ ‖term n‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (fun n ↦ norm_e2_qterm_le_majorant τ hτone n)
      summable_e2Majorant
  have hsum :
      ‖∑' n : ℕ+, term n‖ ≤ ∑' n : ℕ+, e2Majorant n :=
    (norm_tsum_le_tsum_norm hterm).trans
      (hterm.tsum_le_tsum
        (fun n ↦ norm_e2_qterm_le_majorant τ hτone n)
        summable_e2Majorant)
  change ‖1 - 24 * ∑' n : ℕ+, term n‖ ≤ canonicalE2Bound
  calc
    ‖1 - 24 * ∑' n : ℕ+, term n‖
        ≤ ‖(1 : ℂ)‖ + ‖(24 : ℂ) * ∑' n : ℕ+, term n‖ :=
      norm_sub_le _ _
    _ = 1 + 24 * ‖∑' n : ℕ+, term n‖ := by simp
    _ ≤ 1 + 24 * ∑' n : ℕ+, e2Majorant n := by gcongr
    _ = canonicalE2Bound := rfl

/-! ## Bounds for the ten Jacobi coordinates -/

private theorem halfPeriodArgument_im_nonneg
    {z τ : ℂ}
    (hz : z.im = thetaGaugeHeight / 2)
    (hτ : τ.im = thetaGaugeHeight) :
    0 ≤ (τ / 4 + z).im := by
  rw [Complex.add_im, Complex.div_im, hz, hτ]
  norm_num [Complex.normSq_apply]
  nlinarith [thetaGaugeHeight_pos]

theorem norm_jacobiTheta3_le_canonical
    {z τ : ℂ}
    (hz : z.im = thetaGaugeHeight / 2)
    (hτ : τ.im = thetaGaugeHeight) :
    ‖jacobiTheta3 z τ‖ ≤ canonicalThetaBound := by
  unfold jacobiTheta3
  exact
    norm_jacobiTheta₂_le_canonical
      (abs_im_le_height hz) hτ

theorem norm_jacobiTheta4_le_canonical
    {z τ : ℂ}
    (hz : z.im = thetaGaugeHeight / 2)
    (hτ : τ.im = thetaGaugeHeight) :
    ‖jacobiTheta4 z τ‖ ≤ canonicalThetaBound := by
  unfold jacobiTheta4
  apply norm_jacobiTheta₂_le_canonical
  · have him :
        (z + (1 / 2 : ℂ)).im =
          thetaGaugeHeight / 2 := by
      simp [hz]
    exact abs_im_le_height him
  · exact hτ

theorem norm_jacobiTheta2_le_canonical
    {z τ : ℂ}
    (hz : z.im = thetaGaugeHeight / 2)
    (hτ : τ.im = thetaGaugeHeight) :
    ‖jacobiTheta2 z τ‖ ≤ canonicalThetaBound := by
  unfold jacobiTheta2
  rw [norm_mul]
  have hfactor :
      ‖Complex.exp (Real.pi * Complex.I * (τ / 4 + z))‖ ≤ 1 :=
    norm_halfPeriodFactor_le_one
      (halfPeriodArgument_im_nonneg hz hτ)
  have htheta :
      ‖jacobiTheta₂ (z + τ / 2) τ‖ ≤ canonicalThetaBound :=
    norm_jacobiTheta₂_le_canonical
      (abs_shifted_im_le_height hz hτ) hτ
  exact
    (mul_le_mul hfactor htheta
      (norm_nonneg _) (by norm_num)).trans_eq
      (one_mul canonicalThetaBound)

theorem norm_jacobiTheta1_le_canonical
    {z τ : ℂ}
    (hz : z.im = thetaGaugeHeight / 2)
    (hτ : τ.im = thetaGaugeHeight) :
    ‖jacobiTheta1 z τ‖ ≤ canonicalThetaBound := by
  unfold jacobiTheta1
  rw [norm_neg]
  apply norm_jacobiTheta2_le_canonical
  · simp [hz]
  · exact hτ

theorem norm_jacobiTheta1Prime_le_canonical
    {z τ : ℂ}
    (hz : z.im = thetaGaugeHeight / 2)
    (hτ : τ.im = thetaGaugeHeight) :
    ‖jacobiTheta1Prime z τ‖ ≤
      Real.pi * canonicalThetaBound +
        canonicalThetaPrimeBound := by
  unfold jacobiTheta1Prime jacobiTheta2Prime
  rw [norm_neg, norm_mul]
  let z' : ℂ := z + 1 / 2
  have hz' : z'.im = thetaGaugeHeight / 2 := by
    simp [z', hz]
  have hfactor :
      ‖Complex.exp (Real.pi * Complex.I * (τ / 4 + z'))‖ ≤ 1 :=
    norm_halfPeriodFactor_le_one
      (halfPeriodArgument_im_nonneg hz' hτ)
  have htheta :
      ‖jacobiTheta₂ (z' + τ / 2) τ‖ ≤ canonicalThetaBound :=
    norm_jacobiTheta₂_le_canonical
      (abs_shifted_im_le_height hz' hτ) hτ
  have hprime :
      ‖jacobiTheta₂' (z' + τ / 2) τ‖ ≤
        canonicalThetaPrimeBound :=
    norm_jacobiTheta₂'_le_canonical
      (abs_shifted_im_le_height hz' hτ) hτ
  calc
    ‖Complex.exp (Real.pi * Complex.I * (τ / 4 + z'))‖ *
        ‖Real.pi * Complex.I * jacobiTheta₂ (z' + τ / 2) τ +
          jacobiTheta₂' (z' + τ / 2) τ‖
        ≤
      1 *
        (‖Real.pi * Complex.I *
            jacobiTheta₂ (z' + τ / 2) τ‖ +
          ‖jacobiTheta₂' (z' + τ / 2) τ‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ Real.pi * canonicalThetaBound +
        canonicalThetaPrimeBound := by
      have hpi :
          ‖(Real.pi : ℂ) * Complex.I *
              jacobiTheta₂ (z' + τ / 2) τ‖ ≤
            Real.pi * canonicalThetaBound := by
        rw [norm_mul, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg Real.pi_pos.le, norm_I, mul_one]
        exact mul_le_mul_of_nonneg_left htheta Real.pi_pos.le
      simpa only [one_mul] using add_le_add hpi hprime

theorem norm_canonicalDelta_le
    {z τ : ℂ}
    (hz : z.im = thetaGaugeHeight / 2)
    (hτ : τ.im = thetaGaugeHeight) :
    ‖jacobiTheta1Prime z τ / Real.pi‖ ≤
      canonicalDeltaBound := by
  rw [norm_div, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  unfold canonicalDeltaBound
  exact div_le_div_of_nonneg_right
    (norm_jacobiTheta1Prime_le_canonical hz hτ)
    Real.pi_pos.le

/-- The reciprocal odd-theta coordinate is uniformly bounded because
the opposite-half-period identity reduces it to the centered
`theta_3`, whose constant term has a strict common gap. -/
theorem norm_halfPeriod_jacobiTheta1_inv_le
    {z τ : ℂ}
    (hz : z.im = 0)
    (hτ : τ.im = thetaGaugeHeight) :
    ‖(jacobiTheta1 (z + (1 + τ) / 2) τ)⁻¹‖ ≤
      centralThetaGap⁻¹ := by
  have hy : 4 / 5 ≤ τ.im := by
    rw [hτ]
    exact four_fifths_le_thetaGaugeHeight
  have hzcenter : |z.im| ≤ τ.im / 4 := by
    rw [hz, abs_zero, hτ]
    exact div_nonneg thetaGaugeHeight_pos.le (by norm_num)
  have hinv :
      ‖(jacobiTheta3 z τ)⁻¹‖ ≤ centralThetaGap⁻¹ := by
    unfold jacobiTheta3
    exact
      norm_jacobiTheta₂_inv_le_centralThetaGap_inv
        hy hzcenter
  let factor : ℂ :=
    Complex.exp (Real.pi * Complex.I * (z + τ / 4))
  have hfactor : ‖factor‖ ≤ 1 := by
    apply norm_halfPeriodFactor_le_one
    dsimp only [factor]
    rw [Complex.add_im, Complex.div_im, hz, hτ]
    norm_num [Complex.normSq_apply]
    exact div_nonneg
      (mul_nonneg thetaGaugeHeight_pos.le (by norm_num))
      (by norm_num)
  have hid :
      jacobiTheta3 z τ =
        factor * jacobiTheta1 (z + (1 + τ) / 2) τ := by
    exact jacobiTheta3_eq_halfPeriod_jacobiTheta1 z τ
  have hfactor0 : factor ≠ 0 :=
    Complex.exp_ne_zero _
  have htheta3 :
      jacobiTheta3 z τ ≠ 0 := by
    unfold jacobiTheta3
    exact
      jacobiTheta₂_ne_zero_of_im_large_of_im_centered
        hy hzcenter
  have htheta1 :
      jacobiTheta1 (z + (1 + τ) / 2) τ ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hid
    exact htheta3 hid
  have hinverse :
      (jacobiTheta1 (z + (1 + τ) / 2) τ)⁻¹ =
        factor * (jacobiTheta3 z τ)⁻¹ := by
    rw [hid, mul_inv_rev]
    field_simp [hfactor0, htheta1]
  rw [hinverse, norm_mul]
  exact
    (mul_le_mul hfactor hinv
      (norm_nonneg _) (by norm_num)).trans_eq
      (one_mul centralThetaGap⁻¹)

/-! ## One common linked-block coordinate bound -/

/-- A deliberately coarse common norm bound for all fourteen complex
coordinates of one linked unary--Jacobi block. -/
def canonicalLinkedCoordinateBound : ℝ :=
  1 + canonicalThetaBound +
    canonicalThetaBound ^ 2 +
    canonicalThetaBound ^ 4 +
    canonicalE2Bound +
    canonicalDeltaBound +
    centralThetaGap⁻¹

theorem canonicalLinkedCoordinateBound_nonneg :
    0 ≤ canonicalLinkedCoordinateBound := by
  unfold canonicalLinkedCoordinateBound
  have hgap : 0 ≤ centralThetaGap⁻¹ :=
    inv_nonneg.mpr centralThetaGap_pos.le
  nlinarith [canonicalThetaBound_nonneg,
    canonicalE2Bound_nonneg, canonicalDeltaBound_nonneg,
    sq_nonneg canonicalThetaBound,
    pow_nonneg canonicalThetaBound_nonneg 4]

private theorem norm_theta3_tauPath_le
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) (t : ℝ) :
    ‖theta₃ (tauPath parameters controller j t)‖ ≤
      canonicalThetaBound := by
  rw [theta₃_eq_jacobiTheta₂]
  apply norm_jacobiTheta₂_le_canonical
  · simp only [zero_im, abs_zero]
    exact thetaGaugeHeight_pos.le
  · exact tauPath_im parameters controller j t

private theorem norm_theta4_tauPath_le
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) (t : ℝ) :
    ‖theta₄ (tauPath parameters controller j t)‖ ≤
      canonicalThetaBound := by
  rw [theta₄_eq_jacobiTheta₂]
  apply norm_jacobiTheta₂_le_canonical
  · simp only [one_div, inv_im, im_ofNat, neg_zero, normSq_ofNat,
      zero_div, abs_zero]
    exact thetaGaugeHeight_pos.le
  · exact tauPath_im parameters controller j t

private theorem norm_theta2_tauPath_le
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) (t : ℝ) :
    ‖theta₂ (tauPath parameters controller j t)‖ ≤
      canonicalThetaBound := by
  let τ : UpperHalfPlane := tauPath parameters controller j t
  rw [theta₂_eq_jacobiTheta₂, norm_mul]
  have hτ : (τ : ℂ).im = thetaGaugeHeight := by
    exact tauPath_im parameters controller j t
  have hfactor :
      ‖Complex.exp (Real.pi * Complex.I * (τ : ℂ) / 4)‖ ≤ 1 := by
    rw [show
      (Real.pi : ℂ) * Complex.I * (τ : ℂ) / 4 =
        (Real.pi : ℂ) * Complex.I * ((τ : ℂ) / 4) by ring]
    apply norm_halfPeriodFactor_le_one
    rw [Complex.div_im, hτ]
    norm_num [Complex.normSq_apply]
    exact div_nonneg
      (mul_nonneg thetaGaugeHeight_pos.le (by norm_num))
      (by norm_num)
  have him :
      |((τ : ℂ) / 2).im| ≤ thetaGaugeHeight := by
    rw [Complex.div_im, hτ]
    norm_num [Complex.normSq_apply]
    rw [show thetaGaugeHeight * 2 / 4 =
      thetaGaugeHeight / 2 by ring]
    rw [abs_of_pos (half_pos thetaGaugeHeight_pos)]
    linarith [thetaGaugeHeight_pos]
  have htheta :
      ‖jacobiTheta₂ ((τ : ℂ) / 2) τ‖ ≤ canonicalThetaBound :=
    norm_jacobiTheta₂_le_canonical him hτ
  exact
    (mul_le_mul hfactor htheta
      (norm_nonneg _) (by norm_num)).trans_eq
      (one_mul canonicalThetaBound)

private theorem norm_E2_div_twelve_tauPath_le
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) (t : ℝ) :
    ‖EisensteinSeries.E2 (tauPath parameters controller j t) / 12‖ ≤
      canonicalE2Bound := by
  rw [norm_div]
  have hnorm12 : ‖(12 : ℂ)‖ = 12 := by norm_num
  rw [hnorm12]
  have hE := norm_E2_tauPath_le parameters controller j t
  have hbound := canonicalE2Bound_nonneg
  nlinarith

private theorem norm_pow_le_pow_canonicalThetaBound
    {z : ℂ} {k : ℕ}
    (hz : ‖z‖ ≤ canonicalThetaBound) :
    ‖z ^ k‖ ≤ canonicalThetaBound ^ k := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg z) hz k

/-- Every complex coordinate of the canonical linked state satisfies one
common bound. -/
theorem norm_canonicalLinkedPoint_le
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) (t : ℝ)
    (i : Fin LinkedJacobiPolynomialCode.dimension) :
    ‖LinkedJacobiPolynomialCode.point
        ((CanonicalFixedDetectorTrajectory.linkedSourcePath
          parameters I controller
          LockedControllerPhaseTrajectory.onePhase
          (fun _ ↦
            CanonicalFixedDetectorChart.halfPeriodInitialElliptic
              0 thetaGaugeBasePoint)
          (fun _ ↦ thetaGaugeBasePoint) t).linked j) i‖ ≤
      canonicalLinkedCoordinateBound := by
  let τ : UpperHalfPlane := tauPath parameters controller j t
  let ξ : ℂ := ellipticPath parameters I controller j t
  let z : ℂ := centeredPath parameters I controller j t
  have hτ : (τ : ℂ).im = thetaGaugeHeight :=
    tauPath_im parameters controller j t
  have hξ : ξ.im = thetaGaugeHeight / 2 :=
    ellipticPath_im parameters I controller j t
  have hz : z.im = 0 :=
    centeredPath_im parameters I controller j t
  have hdecomp :
      ξ = z + (1 + (τ : ℂ)) / 2 := by
    exact
      CanonicalFixedDetectorChart.ellipticPath_halfPeriod_decomposition
        0 thetaGaugeBasePoint
        (CanonicalFixedDetectorTrajectory.omegaFrequency
          parameters controller j)
        (CanonicalFixedDetectorTrajectory.numberFrequency
          parameters I controller j) t
  have hθ2 :=
    norm_theta2_tauPath_le parameters controller j t
  have hθ3 :=
    norm_theta3_tauPath_le parameters controller j t
  have hθ4 :=
    norm_theta4_tauPath_le parameters controller j t
  have hE :=
    norm_E2_tauPath_le parameters controller j t
  have hH :=
    norm_E2_div_twelve_tauPath_le parameters controller j t
  have hT1 := norm_jacobiTheta1_le_canonical hξ hτ
  have hT2 := norm_jacobiTheta2_le_canonical hξ hτ
  have hT3 := norm_jacobiTheta3_le_canonical hξ hτ
  have hT4 := norm_jacobiTheta4_le_canonical hξ hτ
  have hDelta := norm_canonicalDelta_le hξ hτ
  have hU :
      ‖(jacobiTheta1 ξ (τ : ℂ))⁻¹‖ ≤ centralThetaGap⁻¹ := by
    rw [hdecomp]
    exact norm_halfPeriod_jacobiTheta1_inv_le hz hτ
  have hB := canonicalThetaBound_nonneg
  have hE0 := canonicalE2Bound_nonneg
  have hD0 := canonicalDeltaBound_nonneg
  have hG0 : 0 ≤ centralThetaGap⁻¹ :=
    inv_nonneg.mpr centralThetaGap_pos.le
  have hThetaLe :
      canonicalThetaBound ≤ canonicalLinkedCoordinateBound := by
    unfold canonicalLinkedCoordinateBound
    nlinarith [sq_nonneg canonicalThetaBound,
      pow_nonneg hB 4]
  have hThetaSqLe :
      canonicalThetaBound ^ 2 ≤
        canonicalLinkedCoordinateBound := by
    unfold canonicalLinkedCoordinateBound
    nlinarith [sq_nonneg canonicalThetaBound,
      pow_nonneg hB 4]
  have hThetaFourthLe :
      canonicalThetaBound ^ 4 ≤
        canonicalLinkedCoordinateBound := by
    unfold canonicalLinkedCoordinateBound
    nlinarith [sq_nonneg canonicalThetaBound,
      pow_nonneg hB 4]
  have hELe :
      canonicalE2Bound ≤ canonicalLinkedCoordinateBound := by
    unfold canonicalLinkedCoordinateBound
    nlinarith [sq_nonneg canonicalThetaBound,
      pow_nonneg hB 4]
  have hDeltaLe :
      canonicalDeltaBound ≤ canonicalLinkedCoordinateBound := by
    unfold canonicalLinkedCoordinateBound
    nlinarith [sq_nonneg canonicalThetaBound,
      pow_nonneg hB 4]
  have hGapLe :
      centralThetaGap⁻¹ ≤ canonicalLinkedCoordinateBound := by
    unfold canonicalLinkedCoordinateBound
    nlinarith [sq_nonneg canonicalThetaBound,
      pow_nonneg hB 4]
  change
    ‖LinkedJacobiPolynomialCode.point
      (canonicalLinkedJacobiThetaMovingPath
        (fun u ↦
          CanonicalFixedDetectorTrajectory.ellipticPath
            (CanonicalFixedDetectorChart.halfPeriodInitialElliptic
              0 thetaGaugeBasePoint)
            (CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j)
            (CanonicalFixedDetectorTrajectory.numberFrequency
              parameters I controller j) u)
        (fun u ↦
          CanonicalFixedDetectorTrajectory.modularPath
            thetaGaugeBasePoint
            (CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j) u) t) i‖ ≤ _
  simp only [canonicalLinkedJacobiThetaMovingPath,
    canonicalUnaryThetaMovingPath,
    canonicalJacobiThetaMovingPath]
  obtain ⟨u | q, rfl⟩ := finSumFinEquiv.surjective i
  · fin_cases u
    · change ‖theta₂ τ ^ 4‖ ≤ _
      have hp := norm_pow_le_pow_canonicalThetaBound
        (k := 4) hθ2
      exact hp.trans hThetaFourthLe
    · change ‖theta₄ τ ^ 4‖ ≤ _
      have hp := norm_pow_le_pow_canonicalThetaBound
        (k := 4) hθ4
      exact hp.trans hThetaFourthLe
    · change ‖EisensteinSeries.E2 τ‖ ≤ _
      exact hE.trans hELe
    · change ‖theta₃ τ‖ ≤ _
      exact hθ3.trans hThetaLe
  · fin_cases q
    · change ‖theta₂ τ ^ 2‖ ≤ _
      have hp := norm_pow_le_pow_canonicalThetaBound
        (k := 2) hθ2
      exact hp.trans hThetaSqLe
    · change ‖theta₃ τ ^ 2‖ ≤ _
      have hp := norm_pow_le_pow_canonicalThetaBound
        (k := 2) hθ3
      exact hp.trans hThetaSqLe
    · change ‖theta₄ τ ^ 2‖ ≤ _
      have hp := norm_pow_le_pow_canonicalThetaBound
        (k := 2) hθ4
      exact hp.trans hThetaSqLe
    · change ‖EisensteinSeries.E2 τ / 12‖ ≤ _
      exact hH.trans hELe
    · change ‖jacobiTheta1 ξ τ‖ ≤ _
      exact hT1.trans hThetaLe
    · change ‖jacobiTheta2 ξ τ‖ ≤ _
      exact hT2.trans hThetaLe
    · change ‖jacobiTheta3 ξ τ‖ ≤ _
      exact hT3.trans hThetaLe
    · change ‖jacobiTheta4 ξ τ‖ ≤ _
      exact hT4.trans hThetaLe
    · change ‖jacobiTheta1Prime ξ τ / Real.pi‖ ≤ _
      exact hDelta.trans hDeltaLe
    · change ‖(jacobiTheta1 ξ τ)⁻¹‖ ≤ _
      exact hU.trans hGapLe

/-! ## Assembly of the complete real raw state -/

/-- One common absolute bound for every real coordinate of the complete
raw detector state. -/
def canonicalRawCoordinateBound : ℝ :=
  2 + canonicalLinkedCoordinateBound

theorem canonicalRawCoordinateBound_nonneg :
    0 ≤ canonicalRawCoordinateBound := by
  unfold canonicalRawCoordinateBound
  linarith [canonicalLinkedCoordinateBound_nonneg]

theorem one_le_canonicalRawCoordinateBound :
    (1 : ℝ) ≤ canonicalRawCoordinateBound := by
  unfold canonicalRawCoordinateBound
  linarith [canonicalLinkedCoordinateBound_nonneg]

theorem two_le_canonicalRawCoordinateBound :
    (2 : ℝ) ≤ canonicalRawCoordinateBound := by
  unfold canonicalRawCoordinateBound
  linarith [canonicalLinkedCoordinateBound_nonneg]

theorem linked_le_canonicalRawCoordinateBound :
    canonicalLinkedCoordinateBound ≤ canonicalRawCoordinateBound := by
  unfold canonicalRawCoordinateBound
  linarith

private theorem abs_component_le_one_of_radiusSq_eq_one
    {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    |a| ≤ 1 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg b, sq_nonneg (a - 1),
    sq_nonneg (a + 1)]

private theorem abs_clockPoint_le_one
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (t : ℝ)
    (a : Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars))
    (q : Fin ControllerPolynomialCode.dimension) :
    |ControllerPolynomialCode.point
        (CanonicalFixedDetectorTrajectory.clockPath
          parameters controller
          LockedControllerPhaseTrajectory.onePhase t a) q| ≤ 1 := by
  have hc :
      (controller a).r ^ 2 + (controller a).s ^ 2 = 1 := by
    simpa [Controller.controllerRadiusSq, pow_two] using
      hcontroller a
  have hp :
      (CanonicalFixedDetectorTrajectory.clockPath
          parameters controller
          LockedControllerPhaseTrajectory.onePhase t a).phase.c ^ 2 +
        (CanonicalFixedDetectorTrajectory.clockPath
          parameters controller
          LockedControllerPhaseTrajectory.onePhase t a).phase.d ^ 2 =
        1 := by
    have hr :=
      NormalizedCorrectedCanonicalFixedDetectorGraph.phasePath_radiusSq
        (LockedControllerPhaseTrajectory.angularVelocity
          parameters controller a)
        (LockedControllerPhaseTrajectory.onePhase a) t
    simpa [CanonicalFixedDetectorTrajectory.clockPath,
      LockedControllerPhaseTrajectory.stateFamily,
      Controller.phaseRadiusSq, pow_two] using hr
  fin_cases q
  · change |(controller a).r| ≤ 1
    exact abs_component_le_one_of_radiusSq_eq_one hc
  · change |(controller a).s| ≤ 1
    have hs :
        (controller a).s ^ 2 + (controller a).r ^ 2 = 1 := by
      linarith
    exact abs_component_le_one_of_radiusSq_eq_one hs
  · change
      |(CanonicalFixedDetectorTrajectory.clockPath
        parameters controller
        LockedControllerPhaseTrajectory.onePhase t a).phase.c| ≤ 1
    exact abs_component_le_one_of_radiusSq_eq_one hp
  · change
      |(CanonicalFixedDetectorTrajectory.clockPath
        parameters controller
        LockedControllerPhaseTrajectory.onePhase t a).phase.d| ≤ 1
    have hp' :
        (CanonicalFixedDetectorTrajectory.clockPath
            parameters controller
            LockedControllerPhaseTrajectory.onePhase t a).phase.d ^ 2 +
          (CanonicalFixedDetectorTrajectory.clockPath
            parameters controller
            LockedControllerPhaseTrajectory.onePhase t a).phase.c ^ 2 =
          1 := by
      linarith
    exact abs_component_le_one_of_radiusSq_eq_one hp'

private theorem abs_canonicalControllersPoint_le
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (t : ℝ)
    (q : Fin
      (ControllerProductLinkedJacobiFamilyPolynomialCode.controllerDimension
        (CanonicalFixedDetectorTrajectory.clockCount eqs vars))) :
    |ControllerPhaseProductPolynomialCode.point
        (CanonicalFixedDetectorTrajectory.clockPath
          parameters controller
          LockedControllerPhaseTrajectory.onePhase t) q| ≤
      canonicalRawCoordinateBound := by
  apply
    (HGAS.Analysis.FiniteCoordinateNormSq.abs_flattenPoint_le
      (fun a ↦
        ControllerPolynomialCode.point
          (CanonicalFixedDetectorTrajectory.clockPath
            parameters controller
            LockedControllerPhaseTrajectory.onePhase t a))
      (fun a i ↦
        abs_clockPoint_le_one
          parameters controller hcontroller t a i) q).trans
  exact one_le_canonicalRawCoordinateBound

private theorem abs_canonicalLinkedFamilyPoint_le
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ)
    (q : Fin
      (ControllerProductLinkedJacobiFamilyPolynomialCode.linkedFamilyDimension
        vars)) :
    |ControllerProductLinkedJacobiFamilyPolynomialCode.linkedFamilyPoint
        (CanonicalFixedDetectorTrajectory.linkedSourcePath
          parameters I controller
          LockedControllerPhaseTrajectory.onePhase
          (fun _ ↦
            CanonicalFixedDetectorChart.halfPeriodInitialElliptic
              0 thetaGaugeBasePoint)
          (fun _ ↦ thetaGaugeBasePoint) t) q| ≤
      canonicalRawCoordinateBound := by
  have hlocal :
      ∀ (a : Fin vars)
        (r : Fin
          ControllerProductLinkedJacobiFamilyPolynomialCode.localLinkedRealDimension),
        |ComplexCoordinates.realifyPoint
          (LinkedJacobiPolynomialCode.point
            ((CanonicalFixedDetectorTrajectory.linkedSourcePath
              parameters I controller
              LockedControllerPhaseTrajectory.onePhase
              (fun _ ↦
                CanonicalFixedDetectorChart.halfPeriodInitialElliptic
                  0 thetaGaugeBasePoint)
              (fun _ ↦ thetaGaugeBasePoint) t).linked a)) r| ≤
          canonicalLinkedCoordinateBound := by
    intro a r
    exact
      HGAS.Analysis.FiniteCoordinateNormSq.abs_realifyPoint_le
        (LinkedJacobiPolynomialCode.point
          ((CanonicalFixedDetectorTrajectory.linkedSourcePath
            parameters I controller
            LockedControllerPhaseTrajectory.onePhase
            (fun _ ↦
              CanonicalFixedDetectorChart.halfPeriodInitialElliptic
                0 thetaGaugeBasePoint)
            (fun _ ↦ thetaGaugeBasePoint) t).linked a))
        (norm_canonicalLinkedPoint_le
          parameters I controller a t) r
  have hflat :=
    HGAS.Analysis.FiniteCoordinateNormSq.abs_flattenPoint_le
      (fun a ↦
        ComplexCoordinates.realifyPoint
          (LinkedJacobiPolynomialCode.point
            ((CanonicalFixedDetectorTrajectory.linkedSourcePath
              parameters I controller
              LockedControllerPhaseTrajectory.onePhase
              (fun _ ↦
                CanonicalFixedDetectorChart.halfPeriodInitialElliptic
                  0 thetaGaugeBasePoint)
              (fun _ ↦ thetaGaugeBasePoint) t).linked a)))
      hlocal q
  exact hflat.trans linked_le_canonicalRawCoordinateBound

private theorem norm_poissonReciprocalPath_le_two
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ)
    (k : Fin (DetectorPoissonReciprocalCode.reciprocalCount vars)) :
    ‖CanonicalFixedDetectorTrajectory.poissonReciprocalPath
        parameters I controller
        LockedControllerPhaseTrajectory.onePhase t k‖ ≤ 2 := by
  unfold CanonicalFixedDetectorTrajectory.poissonReciprocalPath
  have h :=
    norm_inv_one_sub_real_mul_le
      (η := (1 / 2 : ℝ))
      (w :=
        CanonicalFixedDetectorTrajectory.poissonCharacterPath
          parameters I controller
          LockedControllerPhaseTrajectory.onePhase t k)
      (by norm_num) (by norm_num)
      (CanonicalFixedDetectorTrajectory.norm_poissonCharacterPath_eq_one
        parameters I controller
        LockedControllerPhaseTrajectory.onePhase t k)
  norm_num at h ⊢
  exact h

private theorem abs_rhsPath_le_one
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (q : Fin 2) :
    |![((CanonicalFixedDetectorTrajectory.rhsPath
          parameters I controller (1 : Circle) t).c),
        ((CanonicalFixedDetectorTrajectory.rhsPath
          parameters I controller (1 : Circle) t).d)] q| ≤ 1 := by
  have hr :=
    NormalizedCorrectedCanonicalFixedDetectorGraph.phasePath_radiusSq
      (-4 *
        CanonicalFixedDetectorTrajectory.rhsFrequency
          parameters I controller)
      (1 : Circle) t
  have hr' :
      (CanonicalFixedDetectorTrajectory.rhsPath
          parameters I controller (1 : Circle) t).c ^ 2 +
        (CanonicalFixedDetectorTrajectory.rhsPath
          parameters I controller (1 : Circle) t).d ^ 2 = 1 := by
    simpa [CanonicalFixedDetectorTrajectory.rhsPath,
      Controller.phaseRadiusSq, pow_two] using hr
  fin_cases q
  · exact abs_component_le_one_of_radiusSq_eq_one hr'
  · have hr'' :
        (CanonicalFixedDetectorTrajectory.rhsPath
            parameters I controller (1 : Circle) t).d ^ 2 +
          (CanonicalFixedDetectorTrajectory.rhsPath
            parameters I controller (1 : Circle) t).c ^ 2 = 1 := by
      linarith
    exact abs_component_le_one_of_radiusSq_eq_one hr''

/-- The fully aligned canonical raw detector state.  Giving this state a
name keeps the bound below identical to the state used by the analytic
Fourier crosswalk. -/
def canonicalRawState
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) :
    FixedDetectorPolynomialCode.State eqs vars :=
  CanonicalFixedDetectorTrajectory.fixedDetectorPath
    parameters I controller
    LockedControllerPhaseTrajectory.onePhase
    (fun _ ↦
      CanonicalFixedDetectorChart.halfPeriodInitialElliptic
        0 thetaGaugeBasePoint)
    (fun _ ↦ thetaGaugeBasePoint)
    (1 : Circle) t

private theorem abs_canonicalLinkedSourcePoint_le
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (t : ℝ)
    (q : Fin
      (ControllerProductLinkedJacobiFamilyPolynomialCode.dimension
        (CanonicalFixedDetectorTrajectory.clockCount eqs vars) vars)) :
    |ControllerProductLinkedJacobiFamilyPolynomialCode.point
        (CanonicalFixedDetectorTrajectory.linkedSourcePath
          parameters I controller
          LockedControllerPhaseTrajectory.onePhase
          (fun _ ↦
            CanonicalFixedDetectorChart.halfPeriodInitialElliptic
              0 thetaGaugeBasePoint)
          (fun _ ↦ thetaGaugeBasePoint) t) q| ≤
      canonicalRawCoordinateBound := by
  unfold ControllerProductLinkedJacobiFamilyPolynomialCode.point
  exact
    HGAS.Analysis.FiniteCoordinateNormSq.abs_blockPoint_le
      _ _
      (abs_canonicalControllersPoint_le
        parameters controller hcontroller t)
      (abs_canonicalLinkedFamilyPoint_le
        parameters I controller t) q

private theorem norm_canonicalGaugePath_le
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) (j : Fin vars) :
    ‖CanonicalFixedDetectorTrajectory.gaugePath
        parameters I controller
        LockedControllerPhaseTrajectory.onePhase t j‖ ≤
      canonicalRawCoordinateBound := by
  rw [CanonicalFixedDetectorTrajectory.norm_gaugePath]
  exact (by norm_num : (1 / 4 : ℝ) ≤ 1).trans
    one_le_canonicalRawCoordinateBound

private theorem abs_canonicalGaugeSourcePoint_le
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (t : ℝ)
    (q : Fin (DetectorJacobiGaugeData.dimension eqs vars)) :
    |ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
        (CanonicalFixedDetectorTrajectory.gaugeSourcePath
          parameters I controller
          LockedControllerPhaseTrajectory.onePhase
          (fun _ ↦
            CanonicalFixedDetectorChart.halfPeriodInitialElliptic
              0 thetaGaugeBasePoint)
          (fun _ ↦ thetaGaugeBasePoint) t) q| ≤
      canonicalRawCoordinateBound := by
  simpa only [
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point,
      ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.rawState,
      ComplexGaugeFamilyPolynomialCode.point,
      ComplexReciprocalFamilyPolynomialCode.point,
      ComplexReciprocalFamilyPolynomialCode.reciprocalPoint,
      CanonicalFixedDetectorTrajectory.gaugeSourcePath] using
    (HGAS.Analysis.FiniteCoordinateNormSq.abs_blockComplexFamilyPoint_le
      (ControllerProductLinkedJacobiFamilyPolynomialCode.point
        (CanonicalFixedDetectorTrajectory.linkedSourcePath
          parameters I controller
          LockedControllerPhaseTrajectory.onePhase
          (fun _ ↦
            CanonicalFixedDetectorChart.halfPeriodInitialElliptic
              0 thetaGaugeBasePoint)
          (fun _ ↦ thetaGaugeBasePoint) t))
      (CanonicalFixedDetectorTrajectory.gaugePath
        parameters I controller
        LockedControllerPhaseTrajectory.onePhase t)
      (abs_canonicalLinkedSourcePoint_le
        parameters I controller hcontroller t)
      (norm_canonicalGaugePath_le
        parameters I controller t) q)

private theorem abs_canonicalPoissonSourcePoint_le
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (t : ℝ)
    (q : Fin (DetectorPoissonReciprocalCode.dimension eqs vars)) :
    |DetectorPoissonReciprocalCode.point
        (CanonicalFixedDetectorTrajectory.poissonSourcePath
          parameters I controller
          LockedControllerPhaseTrajectory.onePhase
          (fun _ ↦
            CanonicalFixedDetectorChart.halfPeriodInitialElliptic
              0 thetaGaugeBasePoint)
          (fun _ ↦ thetaGaugeBasePoint) t) q| ≤
      canonicalRawCoordinateBound := by
  have hreciprocal :
      ∀ k : Fin (DetectorPoissonReciprocalCode.reciprocalCount vars),
        ‖CanonicalFixedDetectorTrajectory.poissonReciprocalPath
            parameters I controller
            LockedControllerPhaseTrajectory.onePhase t k‖ ≤
          canonicalRawCoordinateBound := fun k ↦
    (norm_poissonReciprocalPath_le_two
      parameters I controller t k).trans
        two_le_canonicalRawCoordinateBound
  simpa only [
      DetectorPoissonReciprocalCode.point,
      DetectorPoissonReciprocalCode.rawState,
      ComplexReciprocalFamilyPolynomialCode.point,
      ComplexReciprocalFamilyPolynomialCode.reciprocalPoint,
      CanonicalFixedDetectorTrajectory.poissonSourcePath] using
    (HGAS.Analysis.FiniteCoordinateNormSq.abs_blockComplexFamilyPoint_le
      (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
        (CanonicalFixedDetectorTrajectory.gaugeSourcePath
          parameters I controller
          LockedControllerPhaseTrajectory.onePhase
          (fun _ ↦
            CanonicalFixedDetectorChart.halfPeriodInitialElliptic
              0 thetaGaugeBasePoint)
          (fun _ ↦ thetaGaugeBasePoint) t))
      (CanonicalFixedDetectorTrajectory.poissonReciprocalPath
        parameters I controller
        LockedControllerPhaseTrajectory.onePhase t)
      (abs_canonicalGaugeSourcePoint_le
        parameters I controller hcontroller t)
      hreciprocal q)

/-- Every real coordinate of the fully assembled aligned canonical
detector orbit has the same explicit, time-independent bound. -/
theorem abs_canonicalRawPoint_le
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (t : ℝ)
    (q : Fin (FixedDetectorPolynomialCode.dimension eqs vars)) :
    |FixedDetectorPolynomialCode.point
        (canonicalRawState parameters I controller t) q| ≤
      canonicalRawCoordinateBound := by
  simpa only [canonicalRawState,
      CanonicalFixedDetectorTrajectory.fixedDetectorPath,
      FixedDetectorPolynomialCode.point,
      RHSOscillatorPolynomialCode.combinedPoint] using
    (HGAS.Analysis.FiniteCoordinateNormSq.abs_blockPoint_le
      (DetectorPoissonReciprocalCode.point
        (CanonicalFixedDetectorTrajectory.poissonSourcePath
          parameters I controller
          LockedControllerPhaseTrajectory.onePhase
          (fun _ ↦
            CanonicalFixedDetectorChart.halfPeriodInitialElliptic
              0 thetaGaugeBasePoint)
          (fun _ ↦ thetaGaugeBasePoint) t))
      ![((CanonicalFixedDetectorTrajectory.rhsPath
          parameters I controller (1 : Circle) t).c),
        ((CanonicalFixedDetectorTrajectory.rhsPath
          parameters I controller (1 : Circle) t).d)]
      (abs_canonicalPoissonSourcePoint_le
        parameters I controller hcontroller t)
      (fun i ↦ (abs_rhsPath_le_one
        parameters I controller t i).trans
          one_le_canonicalRawCoordinateBound)
      q)

/-- Explicit squared-norm bound for the canonical raw detector orbit. -/
def canonicalRawNormSqBound (eqs vars : ℕ) : ℝ :=
  (FixedDetectorPolynomialCode.dimension eqs vars : ℝ) *
    canonicalRawCoordinateBound ^ 2

theorem canonicalRawNormSqBound_nonneg :
    0 ≤ canonicalRawNormSqBound eqs vars := by
  unfold canonicalRawNormSqBound
  positivity

/-- The whole raw canonical orbit stays in one fixed Euclidean ball. -/
theorem normSq_canonicalRawPoint_le
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (t : ℝ) :
    normSq
        (FixedDetectorPolynomialCode.point
          (canonicalRawState parameters I controller t)) ≤
      canonicalRawNormSqBound eqs vars := by
  exact
    HGAS.Analysis.FiniteCoordinateNormSq.normSq_le_card_mul_sq_of_abs_le
      _
      (abs_canonicalRawPoint_le
        parameters I controller hcontroller t)

end HGAS.CanonicalFixedDetectorRawOrbitBound
