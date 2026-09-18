import HGAS.Analysis.AffineComplexExponential
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic

/-!
# Affine bookkeeping for a Jacobi--Bloch trajectory

The nonreal-Bloch argument uses only an elementary part of the full Jacobi
classification.  On a horizontal lift, write

```text
  τ(t) = u₀ + κ t + iγ,                 γ > 0,
  w(t) = w₀ + ν t,                      κ,ν ∈ ℝ,
  ξ(t) = w(t) + a₀ τ(t) + b₀.
```

The common theta scale in the Bloch formula is

```text
  S(t) = C₀ exp(π i a₀ (2w(t) + a₀τ(t))).
```

This file records two exact consequences.

First,

```text
  Im ξ(t)
    = (Im a₀) κ t
      + Im w₀ + (Re a₀)γ + (Im a₀)u₀ + Im b₀.
```

Thus the vertical slope is nonzero whenever `Im a₀` and `κ` are nonzero,
and the bounded-error hypothesis of the lattice-reduction theorem holds
with an explicit constant.

Second, the exponent defining `S` is affine in real time:

```text
  S(t) = C₀ exp(A + tB),
```

where `A` and `B` are displayed below.  The general estimate from
`AffineComplexExponential` therefore supplies the exponential lower bound
needed by the theta-escape theorem.  No logarithm branch and no asymptotic
notation is used here.
-/

namespace HGAS.Modular

open Complex Real
open UpperHalfPlane hiding I

noncomputable section

/-- A complex horizontal line with initial point `z₀` and real speed `v`. -/
def affineHorizontalComplexLine
    (z₀ : ℂ) (v t : ℝ) : ℂ :=
  z₀ + ((v * t : ℝ) : ℂ)

@[simp]
theorem affineHorizontalComplexLine_re
    (z₀ : ℂ) (v t : ℝ) :
    (affineHorizontalComplexLine z₀ v t).re =
      z₀.re + v * t := by
  simp [affineHorizontalComplexLine]

@[simp]
theorem affineHorizontalComplexLine_im
    (z₀ : ℂ) (v t : ℝ) :
    (affineHorizontalComplexLine z₀ v t).im =
      z₀.im := by
  simp [affineHorizontalComplexLine]

/-- Constant data in the affine specialization of the Jacobi--Bloch
formula.  The proof `gamma_pos` packages the fact that the modular
horizontal line stays in the upper half-plane. -/
structure AffineBlochParameters where
  /-- Initial real part of the modular parameter. -/
  u0 : ℝ
  /-- Constant imaginary part of the modular parameter. -/
  gamma : ℝ
  /-- Real horizontal speed of the modular parameter. -/
  kappa : ℝ
  /-- Positivity of the modular height. -/
  gamma_pos : 0 < gamma
  /-- Initial elliptic coordinate. -/
  w0 : ℂ
  /-- Real horizontal speed of the elliptic coordinate. -/
  nu : ℝ
  /-- Bloch parameter. -/
  a0 : ℂ
  /-- Additive elliptic integration constant. -/
  b0 : ℂ
  /-- Common theta scale constant; escape theorems assume it is nonzero. -/
  c0 : ℂ

namespace AffineBlochParameters

/-- Initial modular point `u₀+iγ`. -/
def tau0 (p : AffineBlochParameters) : ℂ :=
  Complex.mk p.u0 p.gamma

@[simp]
theorem tau0_re (p : AffineBlochParameters) :
    p.tau0.re = p.u0 :=
  rfl

@[simp]
theorem tau0_im (p : AffineBlochParameters) :
    p.tau0.im = p.gamma :=
  rfl

/-- The complex-valued horizontal modular lift
`τ(t)=u₀+κt+iγ`. -/
def tauComplex
    (p : AffineBlochParameters) (t : ℝ) : ℂ :=
  affineHorizontalComplexLine p.tau0 p.kappa t

@[simp]
theorem tauComplex_re
    (p : AffineBlochParameters) (t : ℝ) :
    (p.tauComplex t).re = p.u0 + p.kappa * t := by
  simp [tauComplex]

@[simp]
theorem tauComplex_im
    (p : AffineBlochParameters) (t : ℝ) :
    (p.tauComplex t).im = p.gamma := by
  simp [tauComplex]

/-- Upper-half-plane packaging of the horizontal modular lift. -/
def tau
    (p : AffineBlochParameters) (t : ℝ) : ℍ :=
  ⟨p.tauComplex t, by
    rw [p.tauComplex_im]
    exact p.gamma_pos⟩

@[simp]
theorem coe_tau
    (p : AffineBlochParameters) (t : ℝ) :
    (p.tau t : ℂ) = p.tauComplex t :=
  rfl

@[simp]
theorem tau_re
    (p : AffineBlochParameters) (t : ℝ) :
    (p.tau t).re = p.u0 + p.kappa * t := by
  exact p.tauComplex_re t

@[simp]
theorem tau_im
    (p : AffineBlochParameters) (t : ℝ) :
    (p.tau t).im = p.gamma := by
  exact p.tauComplex_im t

/-- The horizontal elliptic lift `w(t)=w₀+νt`. -/
def w
    (p : AffineBlochParameters) (t : ℝ) : ℂ :=
  affineHorizontalComplexLine p.w0 p.nu t

@[simp]
theorem w_re
    (p : AffineBlochParameters) (t : ℝ) :
    (p.w t).re = p.w0.re + p.nu * t := by
  simp [w]

@[simp]
theorem w_im
    (p : AffineBlochParameters) (t : ℝ) :
    (p.w t).im = p.w0.im := by
  simp [w]

/-- The elliptic argument in the Bloch theta function:
`ξ=w+a₀τ+b₀`. -/
def xi
    (p : AffineBlochParameters) (t : ℝ) : ℂ :=
  p.w t + p.a0 * p.tauComplex t + p.b0

/-- The coefficient of `t` in `Im ξ(t)`. -/
def verticalSlope (p : AffineBlochParameters) : ℝ :=
  p.a0.im * p.kappa

/-- The constant term in `Im ξ(t)`. -/
def xiImaginaryIntercept
    (p : AffineBlochParameters) : ℝ :=
  p.w0.im + p.a0.re * p.gamma +
    p.a0.im * p.u0 + p.b0.im

/-- Exact affine formula for the imaginary part of the Bloch argument. -/
theorem xi_im_eq_verticalSlope_mul_add
    (p : AffineBlochParameters) (t : ℝ) :
    (p.xi t).im =
      p.verticalSlope * t + p.xiImaginaryIntercept := by
  simp only [xi, add_im, mul_im, w_im,
    tauComplex_re, tauComplex_im,
    verticalSlope, xiImaginaryIntercept]
  ring

/-- The vertical slope is nonzero under exactly the two nondegeneracy
hypotheses used in the manuscript. -/
theorem verticalSlope_ne_zero
    (p : AffineBlochParameters)
    (ha0 : p.a0.im ≠ 0)
    (hkappa : p.kappa ≠ 0) :
    p.verticalSlope ≠ 0 := by
  exact mul_ne_zero ha0 hkappa

/-- The affine imaginary-coordinate estimate has an exact, time-independent
error. -/
theorem abs_xi_im_sub_verticalSlope_mul
    (p : AffineBlochParameters) (t : ℝ) :
    |(p.xi t).im - p.verticalSlope * t| =
      |p.xiImaginaryIntercept| := by
  rw [p.xi_im_eq_verticalSlope_mul_add]
  congr 1
  ring

/-- Filter-independent bounded-error form, ready to instantiate at
`atTop` or `atBot`. -/
theorem eventually_abs_xi_im_sub_verticalSlope_mul_le
    (p : AffineBlochParameters)
    (l : Filter ℝ) :
    ∀ᶠ t in l,
      |(p.xi t).im - p.verticalSlope * t| ≤
        |p.xiImaginaryIntercept| :=
  Filter.Eventually.of_forall fun t ↦
    (p.abs_xi_im_sub_verticalSlope_mul t).le

/-- Constant term in the affine exponential defining the common Bloch
scale. -/
def scaleConstantExponent
    (p : AffineBlochParameters) : ℂ :=
  π * I * p.a0 *
    (2 * p.w0 + p.a0 * p.tau0)

/-- Linear coefficient in the affine exponential defining the common
Bloch scale. -/
def scaleLinearExponent
    (p : AffineBlochParameters) : ℂ :=
  π * I * p.a0 *
    (2 * (p.nu : ℂ) + p.a0 * (p.kappa : ℂ))

/-- The common scale in the Bloch formula
`C₀ exp(π i a₀(2w+a₀τ))`. -/
def commonScale
    (p : AffineBlochParameters) (t : ℝ) : ℂ :=
  p.c0 *
    Complex.exp
      (π * I * p.a0 *
        (2 * p.w t + p.a0 * p.tauComplex t))

/-- The exponent in `commonScale` is exactly affine in real time. -/
theorem scaleExponent_eq_affine
    (p : AffineBlochParameters) (t : ℝ) :
    π * I * p.a0 *
          (2 * p.w t + p.a0 * p.tauComplex t) =
      p.scaleConstantExponent +
        (t : ℂ) * p.scaleLinearExponent := by
  simp only [w, tauComplex, affineHorizontalComplexLine,
    scaleConstantExponent, scaleLinearExponent]
  push_cast
  ring

/-- Exact affine-exponential normal form for the common Bloch scale. -/
theorem commonScale_eq_affineComplexExponential
    (p : AffineBlochParameters) (t : ℝ) :
    p.commonScale t =
      p.c0 *
        Complex.exp
          (p.scaleConstantExponent +
            (t : ℂ) * p.scaleLinearExponent) := by
  rw [commonScale, p.scaleExponent_eq_affine]

/-- The common Bloch scale never vanishes when `C₀` is nonzero. -/
theorem commonScale_ne_zero
    (p : AffineBlochParameters)
    (hc0 : p.c0 ≠ 0)
    (t : ℝ) :
    p.commonScale t ≠ 0 := by
  rw [p.commonScale_eq_affineComplexExponential]
  exact mul_ne_zero hc0 (Complex.exp_ne_zero _)

/-- Explicit linear rate controlling possible decay of the common Bloch
scale. -/
def commonScaleLoss
    (p : AffineBlochParameters) : ℝ :=
  HGAS.Analysis.affineComplexExponentialLoss
    p.c0 p.scaleConstantExponent p.scaleLinearExponent

theorem commonScaleLoss_nonneg
    (p : AffineBlochParameters) :
    0 ≤ p.commonScaleLoss :=
  HGAS.Analysis.affineComplexExponentialLoss_nonneg _ _ _

/-- Global two-sided exponential lower bound for the Bloch common scale. -/
theorem exp_neg_commonScaleLoss_le_norm
    (p : AffineBlochParameters)
    (hc0 : p.c0 ≠ 0)
    (t : ℝ) :
    Real.exp (-p.commonScaleLoss * (1 + |t|)) ≤
      ‖p.commonScale t‖ := by
  rw [p.commonScale_eq_affineComplexExponential]
  exact
    HGAS.Analysis.exp_neg_affineComplexExponentialLoss_le_norm
      hc0 t

/-- The one-sided form consumed directly by the current theta-escape
theorem. -/
theorem eventually_exp_neg_commonScaleLoss_one_add_le_norm
    (p : AffineBlochParameters)
    (hc0 : p.c0 ≠ 0) :
    ∀ᶠ t : ℝ in Filter.atTop,
      Real.exp (-p.commonScaleLoss * (1 + t)) ≤
        ‖p.commonScale t‖ := by
  filter_upwards
    [HGAS.Analysis.eventually_exp_neg_affineComplexExponentialLoss_one_add_le_norm
        (a := p.scaleConstantExponent)
        (b := p.scaleLinearExponent)
        hc0] with t ht
  rw [p.commonScale_eq_affineComplexExponential]
  exact ht

/-- The three quantitative hypotheses contributed by affine Bloch
bookkeeping, packaged in the form used by the nonreal-escape argument. -/
theorem nonreal_escape_parameter_bounds
    (p : AffineBlochParameters)
    (ha0 : p.a0.im ≠ 0)
    (hkappa : p.kappa ≠ 0)
    (hc0 : p.c0 ≠ 0) :
    p.verticalSlope ≠ 0 ∧
      (∀ᶠ t : ℝ in Filter.atTop,
        |(p.xi t).im - p.verticalSlope * t| ≤
          |p.xiImaginaryIntercept|) ∧
      (∀ᶠ t : ℝ in Filter.atTop,
        Real.exp
            (-p.commonScaleLoss * (1 + t)) ≤
          ‖p.commonScale t‖) := by
  exact
    ⟨p.verticalSlope_ne_zero ha0 hkappa,
      p.eventually_abs_xi_im_sub_verticalSlope_mul_le
        Filter.atTop,
      p.eventually_exp_neg_commonScaleLoss_one_add_le_norm
        hc0⟩

end AffineBlochParameters

end

end HGAS.Modular
