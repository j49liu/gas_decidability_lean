import HGAS.Modular.JacobiBlochAffine
import HGAS.Modular.JacobiBlochGaugeCovariance
import HGAS.Modular.JacobiThetaMovingTrajectory
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# The simultaneous affine Jacobi--Bloch trajectory

This module proves directly that the classical affine Bloch formula is a
trajectory of the polynomial Jacobi system.  No completeness theorem for
special functions is imported.

For real horizontal speeds `ν, κ`, fixed `a₀,b₀,C₀`, and

```text
  τ(t) = u₀ + κt + iγ,
  ξ(t) = w₀ + νt + a₀τ(t) + b₀,
  S(t) = C₀ exp(π i a₀(2w(t)+a₀τ(t))),
```

the canonical theta state at `(ξ(t),τ(t))` has clocks

```text
  π(ν+a₀κ),        π i κ.
```

The Bloch slope is `L=2ia₀`.  The covariance theorem in
`JacobiBlochGaugeCovariance` shows that the common multiplier changes the
first clock to `πν`, while leaving the modular clock `πiκ` unchanged.
All normalization constants are checked below.
-/

namespace HGAS.Modular

open Complex Real
open UpperHalfPlane hiding I

noncomputable section

namespace AffineBlochParameters

/-- Constant normalized logarithmic slope of the affine Bloch factor. -/
def jacobiSlope (p : AffineBlochParameters) : ℂ :=
  2 * I * p.a0

/-- The derivative of the horizontal elliptic base coordinate. -/
theorem hasDerivAt_w
    (p : AffineBlochParameters) (t : ℝ) :
    HasDerivAt p.w (p.nu : ℂ) t := by
  have hcast :
      HasDerivAt (fun s : ℝ ↦ (s : ℂ)) 1 t :=
    (hasDerivAt_id t).ofReal_comp
  have hlinear :=
    hcast.const_mul (p.nu : ℂ)
  have hraw :=
    (hasDerivAt_const t p.w0).add hlinear
  convert hraw using 1
  · funext s
    simp only [w, affineHorizontalComplexLine,
      Pi.add_apply]
    push_cast
    rfl
  · ring

/-- The derivative of the horizontal modular lift in ambient complex
coordinates. -/
theorem hasDerivAt_tauComplex
    (p : AffineBlochParameters) (t : ℝ) :
    HasDerivAt p.tauComplex (p.kappa : ℂ) t := by
  have hcast :
      HasDerivAt (fun s : ℝ ↦ (s : ℂ)) 1 t :=
    (hasDerivAt_id t).ofReal_comp
  have hlinear :=
    hcast.const_mul (p.kappa : ℂ)
  have hraw :=
    (hasDerivAt_const t p.tau0).add hlinear
  convert hraw using 1
  · funext s
    simp only [tauComplex, affineHorizontalComplexLine,
      Pi.add_apply]
    push_cast
    rfl
  · ring

/-- The affine theta argument has velocity `ν+a₀κ`. -/
theorem hasDerivAt_xi
    (p : AffineBlochParameters) (t : ℝ) :
    HasDerivAt p.xi
      ((p.nu : ℂ) + p.a0 * (p.kappa : ℂ)) t := by
  have hraw :=
    ((p.hasDerivAt_w t).add
      ((p.hasDerivAt_tauComplex t).const_mul p.a0)).add_const
        p.b0
  simpa only [xi] using hraw

/-- The linear exponent rate of the affine common scale. -/
theorem commonScale_hasDerivAt
    (p : AffineBlochParameters) (t : ℝ) :
    HasDerivAt p.commonScale
      (p.scaleLinearExponent * p.commonScale t) t := by
  have hcast :
      HasDerivAt (fun s : ℝ ↦ (s : ℂ)) 1 t :=
    (hasDerivAt_id t).ofReal_comp
  have hlinear :
      HasDerivAt
        (fun s : ℝ ↦
          p.scaleConstantExponent +
            (s : ℂ) * p.scaleLinearExponent)
        p.scaleLinearExponent t := by
    have hproduct :=
      hcast.mul_const p.scaleLinearExponent
    simpa only [Pi.add_apply, zero_add, one_mul] using
      (hasDerivAt_const t p.scaleConstantExponent).add
        hproduct
  have hexp := hlinear.cexp.const_mul p.c0
  convert hexp using 1
  · funext s
    exact p.commonScale_eq_affineComplexExponential s
  · rw [p.commonScale_eq_affineComplexExponential]
    ring

/-- The exponent rate is exactly the scalar drift required by Bloch
covariance. -/
theorem scaleLinearExponent_eq_blochGaugeDrift
    (p : AffineBlochParameters) :
    p.scaleLinearExponent =
      JacobiState.blochGaugeLogarithmicDrift
        ((π : ℂ) * (p.nu : ℂ))
        ((π : ℂ) * I * (p.kappa : ℂ))
        p.jacobiSlope := by
  simp only [scaleLinearExponent, jacobiSlope,
    JacobiState.blochGaugeLogarithmicDrift]
  ring_nf
  rw [show (I : ℂ) ^ 3 = -I by
    rw [show (3 : ℕ) = 2 + 1 by norm_num,
      pow_add, I_sq, pow_one, neg_one_mul]]
  ring

/-- The canonical theta argument clock is the shifted target clock
appearing in simultaneous Bloch covariance. -/
theorem canonicalEllipticClock_eq_shifted
    (p : AffineBlochParameters) :
    (π : ℂ) *
        ((p.nu : ℂ) + p.a0 * (p.kappa : ℂ)) =
      (π : ℂ) * (p.nu : ℂ) -
        ((π : ℂ) * I * (p.kappa : ℂ)) *
          p.jacobiSlope / 2 := by
  simp only [jacobiSlope]
  ring_nf
  rw [I_sq]
  ring

/-- Canonical theta state underlying the affine Bloch solution. -/
def canonicalJacobiPath
    (p : AffineBlochParameters) (t : ℝ) :
    JacobiState ℂ :=
  canonicalJacobiThetaMovingPath p.xi p.tau t

/-- Complete affine Jacobi--Bloch state. -/
def jacobiBlochPath
    (p : AffineBlochParameters) (t : ℝ) :
    JacobiState ℂ :=
  jacobiBlochGaugePath
    p.commonScale p.jacobiSlope p.canonicalJacobiPath t

/-- **Direct simultaneous-solution theorem.**

Wherever the reciprocal theta chart remains regular, the affine Bloch
formula solves the exact combined polynomial Jacobi field with clocks
`πν` and `πiκ`. -/
theorem jacobiBlochPath_isScaledTrajectory
    (p : AffineBlochParameters)
    (hc0 : p.c0 ≠ 0)
    (hregular :
      ∀ t,
        jacobiTheta1 (p.xi t) (p.tau t : ℂ) ≠ 0) :
    IsScaledJacobiTrajectory
      ((π : ℂ) * (p.nu : ℂ))
      ((π : ℂ) * I * (p.kappa : ℂ))
      p.jacobiBlochPath := by
  have hbaseRaw :=
    canonicalJacobiThetaMovingPath_isScaledTrajectory
      (fun t ↦ p.hasDerivAt_xi t)
      (fun t ↦ p.hasDerivAt_tauComplex t)
      hregular
  have hbase :
      IsScaledJacobiTrajectory
        ((π : ℂ) * (p.nu : ℂ) -
          ((π : ℂ) * I * (p.kappa : ℂ)) *
            p.jacobiSlope / 2)
        ((π : ℂ) * I * (p.kappa : ℂ))
        p.canonicalJacobiPath := by
    rw [← p.canonicalEllipticClock_eq_shifted]
    simpa only [canonicalJacobiPath] using hbaseRaw
  apply jacobiBlochGaugePath_isScaledTrajectory hbase
  · intro t
    rw [← p.scaleLinearExponent_eq_blochGaugeDrift]
    exact p.commonScale_hasDerivAt t
  · exact p.commonScale_ne_zero hc0
  · intro t
    simp only [canonicalJacobiPath,
      canonicalJacobiThetaMovingPath,
      canonicalJacobiThetaState_U,
      canonicalJacobiThetaState_T1]
    exact inv_mul_cancel₀ (hregular t)

end AffineBlochParameters

end

end HGAS.Modular
