import HGAS.Modular.JacobiBlochSelectedContinuation
import HGAS.Modular.JacobiBlochNormalization
import HGAS.Modular.JacobiMomentResonance
import Mathlib.Tactic

/-!
# Exponential-series normal form of a gauged affine Jacobi--Bloch output

This module performs the analytic calculation between the affine
Jacobi--Bloch classification and the three-moment resonance lemma.

For an affine Bloch path, put

```text
  v(t) = w(t) - (1 + τ(t))/2.
```

The fourth-root gauge which changes the odd characteristic `θ₁` into the
integral theta characteristic is, up to one nonzero constant branch,

```text
  G(t) = d exp(π i (v(t) + τ(t)/4)).
```

If the Bloch parameter `a₀` is real, then the `k`-th term of
`G(t) T₁(t)` has temporal frequency

```text
  Ω (k + a₀) (k + a₀ + ρ),
  Ω = π κ,       ρ = (2ν - κ)/κ.
```

Thus the output is literally the `quadraticMomentSeries` used by
`JacobiMomentResonance`; multiplying by the `r`-th moment character merely
subtracts `Ω r(r+ρ)`.

All equalities are proved from Mathlib's defining theta series.  In
particular, the absolute summability assertion below does not appeal to a
formal Fourier manipulation: it is transported from the established
absolute convergence of `jacobiTheta₂`.
-/

namespace HGAS.Modular

open Complex Real
open UpperHalfPlane hiding I

noncomputable section

namespace AffineBlochParameters

/-- The elliptic coordinate centered at the half period used to pass from
the odd theta characteristic to the integral one. -/
def centeredW (p : AffineBlochParameters) (t : ℝ) : ℂ :=
  p.w t - (1 + p.tauComplex t) / 2

@[simp]
theorem centeredW_zero (p : AffineBlochParameters) :
    p.centeredW 0 = p.w0 - (1 + p.tau0) / 2 := by
  simp [centeredW, w, tauComplex, affineHorizontalComplexLine]

/-- The centered coordinate has real speed `ν-κ/2`. -/
theorem centeredW_eq_affine (p : AffineBlochParameters) (t : ℝ) :
    p.centeredW t =
      p.centeredW 0 + (((p.nu - p.kappa / 2) * t : ℝ) : ℂ) := by
  simp only [centeredW, w, tauComplex, affineHorizontalComplexLine]
  push_cast
  ring

/-- A selected fourth-root gauge branch.  The constant `d` contains every
finite fourth-root, characteristic-multiplier, and deck label. -/
def fourthRootGauge
    (p : AffineBlochParameters) (d : ℂ) (t : ℝ) : ℂ :=
  d * Complex.exp
    (π * I * (p.centeredW t + p.tauComplex t / 4))

/-- The gauge angular rate in physical time. -/
def fourthRootGaugeFrequency (p : AffineBlochParameters) : ℝ :=
  π * (p.nu - p.kappa / 4)

/-- Exact affine exponential form of the fourth-root gauge. -/
theorem fourthRootGauge_eq_zero_mul_frequency
    (p : AffineBlochParameters) (d : ℂ) (t : ℝ) :
    p.fourthRootGauge d t =
      p.fourthRootGauge d 0 *
        HGAS.Analysis.realFrequencyExponential
          p.fourthRootGaugeFrequency t := by
  rw [fourthRootGauge, fourthRootGauge,
    centeredW_eq_affine]
  unfold fourthRootGaugeFrequency
    HGAS.Analysis.realFrequencyExponential
  calc
    d *
        Complex.exp
          (π * I *
            (p.centeredW 0 +
              (((p.nu - p.kappa / 2) * t : ℝ) : ℂ) +
              p.tauComplex t / 4)) =
      d *
        Complex.exp
          (π * I *
              (p.centeredW 0 + p.tauComplex 0 / 4) +
            (((π * (p.nu - p.kappa / 4) : ℝ) : ℂ) *
              I * (t : ℂ))) := by
        congr 2
        simp only [tauComplex, affineHorizontalComplexLine]
        push_cast
        ring
    _ =
      d *
          Complex.exp
            (π * I *
              (p.centeredW 0 + p.tauComplex 0 / 4)) *
        Complex.exp
          (((π * (p.nu - p.kappa / 4) : ℝ) : ℂ) *
            I * (t : ℂ)) := by
        rw [Complex.exp_add]
        ring

/-- Physical modular frequency `Ω`. -/
def quadraticOmega (p : AffineBlochParameters) : ℝ :=
  π * p.kappa

/-- Physical linear frequency `N`. -/
def quadraticLinearFrequency (p : AffineBlochParameters) : ℝ :=
  2 * π * p.nu - p.quadraticOmega

/-- Ratio `ρ=N/Ω` used by the quadratic resonance calculation. -/
def quadraticClockRatio (p : AffineBlochParameters) : ℝ :=
  p.quadraticLinearFrequency / p.quadraticOmega

theorem quadraticOmega_ne_zero
    (p : AffineBlochParameters) (hkappa : p.kappa ≠ 0) :
    p.quadraticOmega ≠ 0 := by
  exact mul_ne_zero Real.pi_ne_zero hkappa

/-- With nonzero modular speed, the clock ratio simplifies to
`ρ=(2ν-κ)/κ`. -/
theorem quadraticClockRatio_eq
    (p : AffineBlochParameters) (hkappa : p.kappa ≠ 0) :
    p.quadraticClockRatio =
      (2 * p.nu - p.kappa) / p.kappa := by
  unfold quadraticClockRatio quadraticLinearFrequency quadraticOmega
  field_simp [Real.pi_ne_zero, hkappa]

/-- The single exponent obtained by multiplying the gauge, Bloch scale,
the outer odd-characteristic factor, and one term of Mathlib's basic
theta series. -/
def gaugedBlochExponent
    (p : AffineBlochParameters) (k : ℤ) (t : ℝ) : ℂ :=
  π * I * (p.centeredW t + p.tauComplex t / 4) +
    π * I * p.a0 *
      (2 * p.w t + p.a0 * p.tauComplex t) +
    π * I *
      (p.tauComplex t / 4 + p.xi t + 1 / 2) +
    (2 * π * I * ((k - 1 : ℤ) : ℂ) *
        (p.xi t + 1 / 2 + p.tauComplex t / 2) +
      π * I * ((k - 1 : ℤ) : ℂ) ^ 2 *
        p.tauComplex t)

/-- The same raw theta contribution at time `t`. -/
def gaugedBlochTerm
    (p : AffineBlochParameters) (d : ℂ)
    (k : ℤ) (t : ℝ) : ℂ :=
  -(d * p.c0 * Complex.exp (p.gaugedBlochExponent k t))

/-- Time-independent coefficient of the shifted term. -/
def gaugedBlochCoefficient
    (p : AffineBlochParameters) (d : ℂ) (k : ℤ) : ℂ :=
  p.gaugedBlochTerm d k 0

/-- The time-independent exponent in the human-readable affine-Gaussian
coefficient.  Its three terms are respectively the modular Gaussian,
the centered elliptic phase, and the free Bloch multiplier. -/
def gaugedBlochReducedExponent
    (p : AffineBlochParameters) (k : ℤ) : ℂ :=
  π * I *
    ((((k : ℂ) + p.a0) ^ 2 * p.tauComplex 0) +
      2 * ((k : ℂ) + p.a0) * p.centeredW 0 +
      (2 * (k : ℂ) - 1) * p.b0)

/-- Exact simplification of the raw characteristic exponent.  The last
two summands are an integral `2πi` period and the odd-characteristic
factor `πi`; together with the leading minus sign in
`gaugedBlochTerm`, they produce the positive explicit coefficient below. -/
theorem gaugedBlochExponent_zero_eq_reduced
    (p : AffineBlochParameters) (k : ℤ) :
    p.gaugedBlochExponent k 0 =
      π * I * p.a0 +
        p.gaugedBlochReducedExponent k +
        (((k - 1 : ℤ) : ℂ) * (2 * π * I)) +
        π * I := by
  unfold gaugedBlochExponent gaugedBlochReducedExponent
    centeredW xi w tauComplex tau0 affineHorizontalComplexLine
  simp only [ofReal_zero, mul_zero, add_zero]
  push_cast
  ring

/-- Human-readable coefficient formula.  It displays explicitly the
Gaussian factor in `(k+a₀)²`, the centered elliptic phase, and the free
linear multiplier. -/
theorem gaugedBlochCoefficient_eq_explicit
    (p : AffineBlochParameters) (d : ℂ) (k : ℤ) :
    p.gaugedBlochCoefficient d k =
      d * p.c0 *
        Complex.exp (π * I * p.a0) *
        Complex.exp (p.gaugedBlochReducedExponent k) := by
  unfold gaugedBlochCoefficient gaugedBlochTerm
  rw [p.gaugedBlochExponent_zero_eq_reduced]
  simp only [Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I,
    Complex.exp_pi_mul_I, mul_one]
  ring

/-- The gauged `T₁` coordinate is the sum of the shifted raw terms. -/
theorem fourthRootGauge_mul_jacobiBlochPath_T1_eq_tsum
    (p : AffineBlochParameters) (d : ℂ) (t : ℝ) :
    p.fourthRootGauge d t * (p.jacobiBlochPath t).T1 =
      ∑' k : ℤ, p.gaugedBlochTerm d k t := by
  simp only [jacobiBlochPath, jacobiBlochGaugePath,
    JacobiState.blochGauge, canonicalJacobiPath,
    canonicalJacobiThetaMovingPath, canonicalJacobiThetaState_T1,
    jacobiTheta1, jacobiTheta2, jacobiTheta₂]
  rw [← (Equiv.addRight (-1 : ℤ)).tsum_eq]
  rw [show
      -(Complex.exp
            (π * I *
              ((p.tau t : ℂ) / 4 + (p.xi t + 1 / 2))) *
          ∑' c : ℤ,
            jacobiTheta₂_term ((Equiv.addRight (-1 : ℤ)) c)
              (p.xi t + 1 / 2 + (p.tau t : ℂ) / 2)
              (p.tau t : ℂ)) =
        (-Complex.exp
            (π * I *
              ((p.tau t : ℂ) / 4 + (p.xi t + 1 / 2)))) *
          ∑' c : ℤ,
            jacobiTheta₂_term ((Equiv.addRight (-1 : ℤ)) c)
              (p.xi t + 1 / 2 + (p.tau t : ℂ) / 2)
              (p.tau t : ℂ) by ring]
  rw [← tsum_mul_left]
  rw [← tsum_mul_left]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  simp only [Equiv.coe_addRight, gaugedBlochTerm,
    gaugedBlochExponent, fourthRootGauge, commonScale,
    jacobiTheta₂_term, sub_eq_add_neg, coe_tau]
  simp only [Complex.exp_add]
  ring

/-- Realness of the Bloch parameter, in the form convenient for algebraic
rewriting inside complex expressions. -/
theorem a0_eq_of_im_eq_zero
    (p : AffineBlochParameters) (ha : p.a0.im = 0) :
    p.a0 = (p.a0.re : ℂ) := by
  apply Complex.ext <;> simp [ha]

/-- Coefficientwise phase calculation.  This is the exact bridge from the
theta defining series to the quadratic dispersion relation. -/
theorem gaugedBlochTerm_eq_exponentialSeriesTerm
    (p : AffineBlochParameters) (d : ℂ)
    (ha : p.a0.im = 0) (hkappa : p.kappa ≠ 0)
    (k : ℤ) (t : ℝ) :
    p.gaugedBlochTerm d k t =
      HGAS.Analysis.exponentialSeriesTerm
        (p.gaugedBlochCoefficient d)
        (quadraticMomentFrequency
          p.quadraticOmega p.quadraticClockRatio p.a0.re 0)
        k t := by
  have ha0 := p.a0_eq_of_im_eq_zero ha
  have hexponent :
      p.gaugedBlochExponent k t =
        p.gaugedBlochExponent k 0 +
          (((quadraticMomentFrequency
              p.quadraticOmega p.quadraticClockRatio
              p.a0.re 0 k : ℝ) : ℂ) *
            I * (t : ℂ)) := by
    rw [p.quadraticClockRatio_eq hkappa]
    unfold gaugedBlochExponent centeredW xi w tauComplex tau0
      affineHorizontalComplexLine quadraticMomentFrequency
      quadraticDispersion quadraticOmega
    rw [ha0]
    simp only [ofReal_zero, mul_zero, add_zero, ofReal_re]
    push_cast
    field_simp [hkappa]
    ring
  unfold gaugedBlochCoefficient gaugedBlochTerm
    HGAS.Analysis.exponentialSeriesTerm
    HGAS.Analysis.realFrequencyExponential
  rw [hexponent, Complex.exp_add]
  ring

/-- Absolute summability of the classified coefficient family. -/
theorem summable_norm_gaugedBlochCoefficient
    (p : AffineBlochParameters) (d : ℂ) :
    Summable fun k : ℤ ↦ ‖p.gaugedBlochCoefficient d k‖ := by
  let z0 : ℂ :=
    p.xi 0 + 1 / 2 + p.tauComplex 0 / 2
  let scalar : ℂ :=
    -(p.fourthRootGauge d 0 * p.commonScale 0 *
      Complex.exp
        (π * I *
          (p.tauComplex 0 / 4 + p.xi 0 + 1 / 2)))
  have htheta :
      Summable
        (fun n : ℤ ↦
          jacobiTheta₂_term n z0 (p.tauComplex 0)) := by
    rw [summable_jacobiTheta₂_term_iff]
    simpa only [tauComplex_im] using p.gamma_pos
  have hnorm :
      Summable
        (fun n : ℤ ↦
          ‖scalar * jacobiTheta₂_term n z0
            (p.tauComplex 0)‖) := by
    exact (htheta.mul_left scalar).norm
  have hshift :
      Summable
        (fun k : ℤ ↦
          ‖scalar * jacobiTheta₂_term (k - 1) z0
            (p.tauComplex 0)‖) := by
    have h :=
      (Equiv.addRight (-1 : ℤ)).summable_iff.mpr hnorm
    simpa only [Function.comp_apply, Equiv.coe_addRight,
      sub_eq_add_neg] using h
  exact hshift.congr fun k ↦ by
    simp only [gaugedBlochCoefficient, gaugedBlochTerm,
      gaugedBlochExponent, scalar, z0, fourthRootGauge,
      commonScale, jacobiTheta₂_term]
    simp only [Complex.exp_add]
    ring

/-- **Absolutely summable quadratic-series normal form.**

For a recurrent (hence real-Bloch) affine solution with nonzero modular
clock, the fourth-root-gauged output is exactly the mean-row
`quadraticMomentSeries`. -/
theorem fourthRootGauge_mul_jacobiBlochPath_T1_eq_quadraticMomentSeries
    (p : AffineBlochParameters) (d : ℂ)
    (ha : p.a0.im = 0) (hkappa : p.kappa ≠ 0)
    (t : ℝ) :
    p.fourthRootGauge d t * (p.jacobiBlochPath t).T1 =
      quadraticMomentSeries
        (p.gaugedBlochCoefficient d)
        p.quadraticOmega p.quadraticClockRatio p.a0.re 0 t := by
  rw [p.fourthRootGauge_mul_jacobiBlochPath_T1_eq_tsum]
  unfold quadraticMomentSeries HGAS.Analysis.exponentialSeries
  apply tsum_congr
  intro k
  exact p.gaugedBlochTerm_eq_exponentialSeriesTerm
    d ha hkappa k t

end AffineBlochParameters

/-! ## Twisting by the three selector characters -/

/-- Multiplication by a pure character subtracting the `r`-th dispersion
frequency turns the mean-row series into the `r`-th moment series. -/
theorem realFrequencyExponential_mul_quadraticMomentSeries_zero
    (coefficient : ℤ → ℂ)
    (Ω ρ a : ℝ) (r : ℤ) (t : ℝ) :
    HGAS.Analysis.realFrequencyExponential
          (-Ω * quadraticDispersion ρ (r : ℝ)) t *
        quadraticMomentSeries coefficient Ω ρ a 0 t =
      quadraticMomentSeries coefficient Ω ρ a r t := by
  unfold quadraticMomentSeries HGAS.Analysis.exponentialSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  unfold HGAS.Analysis.exponentialSeriesTerm
    HGAS.Analysis.realFrequencyExponential
    quadraticMomentFrequency
  rw [show
      Complex.exp
            (((-Ω * quadraticDispersion ρ (r : ℝ) : ℝ) : ℂ) *
              I * (t : ℂ)) *
          (coefficient k *
            Complex.exp
              (((Ω *
                  (quadraticDispersion ρ ((k : ℝ) + a) -
                    quadraticDispersion ρ (0 : ℤ)) : ℝ) : ℂ) *
                I * (t : ℂ))) =
        coefficient k *
          (Complex.exp
              (((-Ω * quadraticDispersion ρ (r : ℝ) : ℝ) : ℂ) *
                I * (t : ℂ)) *
            Complex.exp
              (((Ω *
                  (quadraticDispersion ρ ((k : ℝ) + a) -
                    quadraticDispersion ρ (0 : ℤ)) : ℝ) : ℂ) *
                I * (t : ℂ))) by ring]
  rw [← Complex.exp_add]
  congr 2
  push_cast
  norm_num [quadraticDispersion]
  ring

/-- A time-independent phase or amplitude can be absorbed coefficientwise
into a quadratic moment series. -/
theorem const_mul_quadraticMomentSeries
    (c : ℂ) (coefficient : ℤ → ℂ)
    (Ω ρ a : ℝ) (r : ℤ) (t : ℝ) :
    c * quadraticMomentSeries coefficient Ω ρ a r t =
      quadraticMomentSeries (fun k ↦ c * coefficient k)
        Ω ρ a r t := by
  unfold quadraticMomentSeries HGAS.Analysis.exponentialSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  unfold HGAS.Analysis.exponentialSeriesTerm
  ring

/-- Absolute summability is preserved when a constant branch multiplier
is absorbed into the coefficients. -/
theorem summable_norm_const_mul
    (c : ℂ) (coefficient : ℤ → ℂ)
    (hsum : Summable fun k ↦ ‖coefficient k‖) :
    Summable fun k ↦ ‖c * coefficient k‖ := by
  exact (hsum.mul_left ‖c‖).congr fun k ↦ by
    rw [norm_mul]

/-- Mean character: no twist. -/
theorem quadraticMomentSeries_mean_character
    (coefficient : ℤ → ℂ)
    (Ω ρ a t : ℝ) :
    quadraticMomentSeries coefficient Ω ρ a 0 t =
      quadraticMomentSeries coefficient Ω ρ a 0 t :=
  rfl

/-- The `(1,1)` selector character has frequency `-(Ω+N)` when
`N=Ωρ`. -/
theorem quadraticMomentSeries_plus_character
    (coefficient : ℤ → ℂ)
    (Ω ρ a t : ℝ) :
    HGAS.Analysis.realFrequencyExponential
          (-Ω * (1 + ρ)) t *
        quadraticMomentSeries coefficient Ω ρ a 0 t =
      quadraticMomentSeries coefficient Ω ρ a 1 t := by
  have h :=
    realFrequencyExponential_mul_quadraticMomentSeries_zero
      coefficient Ω ρ a 1 t
  have hfrequency :
      quadraticDispersion ρ ((1 : ℤ) : ℝ) = 1 + ρ := by
    norm_num [quadraticDispersion]
  rw [hfrequency] at h
  exact h

/-- The `(1,-1)` selector character has frequency `-(Ω-N)`. -/
theorem quadraticMomentSeries_minus_character
    (coefficient : ℤ → ℂ)
    (Ω ρ a t : ℝ) :
    HGAS.Analysis.realFrequencyExponential
          (-Ω * (1 - ρ)) t *
        quadraticMomentSeries coefficient Ω ρ a 0 t =
      quadraticMomentSeries coefficient Ω ρ a (-1) t := by
  have h :=
    realFrequencyExponential_mul_quadraticMomentSeries_zero
      coefficient Ω ρ a (-1) t
  have hfrequency :
      quadraticDispersion ρ (((-1 : ℤ) : ℝ)) = 1 - ρ := by
    norm_num [quadraticDispersion]
    ring
  rw [hfrequency] at h
  exact h

end

end HGAS.Modular
