import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic

/-!
# The canonical height for the rational fourth-root theta gauge

The detector fixes

```text
                    λ = 1/256,   λ^(1/4) = 1/4.
```

For the half-period identity to match the polynomial gauge literally, the
initial modular parameter must have height

```text
                    y₀ = log(256)/π.
```

Indeed `exp(-π y₀)=1/256` and
`exp(-π y₀/4)=1/4`.  This module proves those identities, verifies the
quantitative lower bound `y₀ ≥ 4/5` used by the theta nonvanishing
estimate, and packages the corresponding point `i y₀` of the upper half
plane.

The numerical proof is deliberately coarse: `π ≤ 4` and Mathlib's
certified decimal lower bound for `log 2` are much stronger than needed.
-/

namespace HGAS.Modular

open Complex Real

noncomputable section

/-- Height at which the nome has modulus exactly `1/256`. -/
def thetaGaugeHeight : ℝ :=
  Real.log 256 / Real.pi

theorem thetaGaugeHeight_pos :
    0 < thetaGaugeHeight := by
  unfold thetaGaugeHeight
  positivity

/-- The canonical height lies in the quantitative nonvanishing region
used for the central-strip estimate. -/
theorem four_fifths_le_thetaGaugeHeight :
    4 / 5 ≤ thetaGaugeHeight := by
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

/-- Exact nome modulus at the canonical height. -/
theorem exp_neg_pi_mul_thetaGaugeHeight :
    Real.exp (-Real.pi * thetaGaugeHeight) = 1 / 256 := by
  unfold thetaGaugeHeight
  rw [show
      -Real.pi * (Real.log 256 / Real.pi) =
        -Real.log 256 by
      field_simp [Real.pi_ne_zero]]
  rw [Real.exp_neg]
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 256)]
  norm_num

/-- Exact fourth-root modulus at the canonical height. -/
theorem exp_neg_pi_mul_thetaGaugeHeight_div_four :
    Real.exp (-Real.pi * thetaGaugeHeight / 4) = 1 / 4 := by
  have hpow :
      Real.exp (-Real.pi * thetaGaugeHeight / 4) ^ 4 =
        (1 / 4 : ℝ) ^ 4 := by
    rw [← Real.exp_nat_mul]
    rw [show
        (4 : ℕ) * (-Real.pi * thetaGaugeHeight / 4) =
          -Real.pi * thetaGaugeHeight by
        push_cast
        ring]
    rw [exp_neg_pi_mul_thetaGaugeHeight]
    norm_num
  exact
    (pow_left_inj₀ (Real.exp_pos _).le
      (by norm_num) (by norm_num)).mp hpow

/-- Purely imaginary upper-half-plane base point whose nome and
fourth-root modulus have the desired rational values. -/
def thetaGaugeBasePoint : UpperHalfPlane :=
  ⟨Complex.I * (thetaGaugeHeight : ℂ),
    by simp [thetaGaugeHeight_pos]⟩

@[simp]
theorem thetaGaugeBasePoint_re :
    (thetaGaugeBasePoint : ℂ).re = 0 := by
  simp [thetaGaugeBasePoint]

@[simp]
theorem thetaGaugeBasePoint_im :
    (thetaGaugeBasePoint : ℂ).im = thetaGaugeHeight := by
  simp [thetaGaugeBasePoint]

theorem thetaGaugeBasePoint_im_ge_four_fifths :
    4 / 5 ≤ thetaGaugeBasePoint.im := by
  change 4 / 5 ≤ (thetaGaugeBasePoint : ℂ).im
  rw [thetaGaugeBasePoint_im]
  exact four_fifths_le_thetaGaugeHeight

end

end HGAS.Modular
