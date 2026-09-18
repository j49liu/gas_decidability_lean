import HGAS.Analysis.TorusCohomologicalPrimitive
import Mathlib.Tactic

/-!
# Fourier primitives along a time-changed torus path

Central compactification slows the affine source by a positive
state-dependent factor.  Consequently the phase path in compactified time
is not an equal-time torus translation.  Its Fourier characters instead
satisfy

```text
  d/ds χ_k(x(s))
    = speed(s) * (2π i <k,ω>) * χ_k(x(s)).
```

The usual inverse-frequency Fourier series remains the correct primitive:
the same `speed` multiplies both the derivative of the primitive and the
compiled slowed drift.  This file proves that statement with all
term-by-term differentiation justified.

The API deliberately assumes the displayed derivative for every character,
rather than imposing a manifold model on the torus-valued path.  It
therefore applies directly to phase observations of compact product-sphere
flows.
-/

noncomputable section

open scoped BigOperators

namespace HGAS.Analysis

variable {d ι : Type*} [Fintype d]

/-- One inverse-frequency Fourier term differentiates along an arbitrary
time-changed torus path to `speed` times the corresponding nonresonant
Fourier term. -/
theorem cohomologicalPrimitiveTerm_comp_hasDerivAt_timeChanged
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (ω : d → ℝ)
    (path : ℝ → UnitAddTorus d)
    (speed : ℝ → ℝ)
    (hcharacter :
      ∀ n : d → ℤ, ∀ t : ℝ,
        HasDerivAt
          (fun s ↦ UnitAddTorus.mFourier n (path s))
          (((speed t : ℝ) : ℂ) *
            torusAngularFrequency n ω *
            UnitAddTorus.mFourier n (path t)) t)
    (i : ι) (t : ℝ) :
    HasDerivAt
      (fun s ↦
        torusSeriesTerm
          (cohomologicalPrimitiveCoefficient
            coefficient exponent ω)
          exponent i (path s))
      (((speed t : ℝ) : ℂ) *
        torusSeriesTerm
          (nonresonantCoefficient coefficient exponent ω)
          exponent i (path t)) t := by
  by_cases hpair :
      HGAS.Clocks.RadicalClock.frequencyPairing
        (exponent i) ω = 0
  · simpa [torusSeriesTerm,
      cohomologicalPrimitiveCoefficient,
      nonresonantCoefficient, hpair] using
      (hasDerivAt_const (x := t) (c := (0 : ℂ)))
  · have hscaled :=
      (hcharacter (exponent i) t).const_mul
        (cohomologicalPrimitiveCoefficient
          coefficient exponent ω i)
    apply hscaled.congr_deriv
    rw [torusSeriesTerm,
      cohomologicalPrimitiveCoefficient,
      nonresonantCoefficient, if_neg hpair, if_neg hpair]
    have hang :
        torusAngularFrequency (exponent i) ω ≠ 0 :=
      torusAngularFrequency_ne_zero hpair
    field_simp [hang]

/-- The complete centered primitive differentiates term by term along a
uniformly bounded time-changed torus path.

Only the speed bound is new compared with the equal-time translation
theorem.  It supplies the summable uniform bound
`S * ‖coefficient i‖` for the differentiated terms.
-/
theorem torusCohomologicalPrimitive_comp_hasDerivAt_timeChanged
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (ω : d → ℝ)
    (path : ℝ → UnitAddTorus d)
    (speed : ℝ → ℝ)
    (speedBound : ℝ)
    (hspeedBound_nonneg : 0 ≤ speedBound)
    (hspeedBound : ∀ t, |speed t| ≤ speedBound)
    (hcharacter :
      ∀ n : d → ℤ, ∀ t : ℝ,
        HasDerivAt
          (fun s ↦ UnitAddTorus.mFourier n (path s))
          (((speed t : ℝ) : ℂ) *
            torusAngularFrequency n ω *
            UnitAddTorus.mFourier n (path t)) t)
    (hcoefficient :
      Summable fun i ↦ ‖coefficient i‖)
    (hprimitive :
      Summable fun i ↦
        ‖cohomologicalPrimitiveCoefficient
          coefficient exponent ω i‖)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦
        torusCohomologicalPrimitive
          coefficient exponent ω (path s))
      (((speed t : ℝ) : ℂ) *
        torusFourierSeries
          (nonresonantCoefficient coefficient exponent ω)
          exponent (path t)) t := by
  let primitiveTerm : ι → ℝ → ℂ :=
    fun i s ↦
      torusSeriesTerm
        (cohomologicalPrimitiveCoefficient
          coefficient exponent ω)
        exponent i (path s)
  let derivativeTerm : ι → ℝ → ℂ :=
    fun i s ↦
      ((speed s : ℝ) : ℂ) *
        torusSeriesTerm
          (nonresonantCoefficient coefficient exponent ω)
          exponent i (path s)
  let majorant : ι → ℝ :=
    fun i ↦ speedBound * ‖coefficient i‖
  have hmajorant :
      Summable majorant :=
    hcoefficient.mul_left speedBound
  have hderivative :
      ∀ i s,
        HasDerivAt (primitiveTerm i)
          (derivativeTerm i s) s := by
    intro i s
    exact
      cohomologicalPrimitiveTerm_comp_hasDerivAt_timeChanged
        coefficient exponent ω path speed hcharacter i s
  have hderivativeBound :
      ∀ i s,
        ‖derivativeTerm i s‖ ≤ majorant i := by
    intro i s
    rw [show
        ‖derivativeTerm i s‖ =
          |speed s| *
            ‖nonresonantCoefficient
              coefficient exponent ω i‖ by
      simp only [derivativeTerm, norm_mul, Complex.norm_real,
        Real.norm_eq_abs]
      rw [norm_torusSeriesTerm]]
    calc
      |speed s| *
          ‖nonresonantCoefficient
            coefficient exponent ω i‖ ≤
          speedBound *
            ‖nonresonantCoefficient
              coefficient exponent ω i‖ :=
        mul_le_mul_of_nonneg_right
          (hspeedBound s) (norm_nonneg _)
      _ ≤ speedBound * ‖coefficient i‖ := by
        apply mul_le_mul_of_nonneg_left _ hspeedBound_nonneg
        unfold nonresonantCoefficient
        split_ifs
        · simp
        · exact le_rfl
      _ = majorant i := rfl
  have hprimitiveAtZero :
      Summable fun i ↦ primitiveTerm i 0 := by
    apply hprimitive.of_norm_bounded
    intro i
    exact le_of_eq
      (norm_torusSeriesTerm
        (cohomologicalPrimitiveCoefficient
          coefficient exponent ω)
        exponent i (path 0))
  have h :=
    hasDerivAt_tsum
      hmajorant hderivative hderivativeBound
      hprimitiveAtZero t
  simpa only [primitiveTerm, derivativeTerm,
    torusCohomologicalPrimitive, torusFourierSeries,
    ← tsum_mul_left] using h

/-- Under nonresonance and vanishing zero modes, the differentiated
time-changed primitive recovers `speed` times the original Fourier
series. -/
theorem
    torusCohomologicalPrimitive_comp_hasDerivAt_timeChanged_of_zeroMode
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (ω : d → ℝ)
    (path : ℝ → UnitAddTorus d)
    (speed : ℝ → ℝ)
    (speedBound : ℝ)
    (hspeedBound_nonneg : 0 ≤ speedBound)
    (hspeedBound : ∀ t, |speed t| ≤ speedBound)
    (hcharacter :
      ∀ n : d → ℤ, ∀ t : ℝ,
        HasDerivAt
          (fun s ↦ UnitAddTorus.mFourier n (path s))
          (((speed t : ℝ) : ℂ) *
            torusAngularFrequency n ω *
            UnitAddTorus.mFourier n (path t)) t)
    (hω :
      HGAS.Clocks.RadicalIndependence.HasNoNontrivialIntegerCharacter
        ω)
    (hzero :
      ∀ i, exponent i = 0 → coefficient i = 0)
    (hcoefficient :
      Summable fun i ↦ ‖coefficient i‖)
    (hprimitive :
      Summable fun i ↦
        ‖cohomologicalPrimitiveCoefficient
          coefficient exponent ω i‖)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦
        torusCohomologicalPrimitive
          coefficient exponent ω (path s))
      (((speed t : ℝ) : ℂ) *
        torusFourierSeries coefficient exponent (path t)) t := by
  have hcoeff :
      nonresonantCoefficient coefficient exponent ω =
        coefficient := by
    funext i
    exact
      nonresonantCoefficient_eq_self
        coefficient exponent ω hω hzero i
  simpa only [hcoeff] using
    torusCohomologicalPrimitive_comp_hasDerivAt_timeChanged
      coefficient exponent ω path speed speedBound
      hspeedBound_nonneg hspeedBound hcharacter
      hcoefficient hprimitive t

/-- Real-part form used by a real polynomial drift coordinate. -/
theorem
    torusCohomologicalPrimitive_re_comp_hasDerivAt_timeChanged_of_zeroMode
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (ω : d → ℝ)
    (path : ℝ → UnitAddTorus d)
    (speed : ℝ → ℝ)
    (speedBound : ℝ)
    (hspeedBound_nonneg : 0 ≤ speedBound)
    (hspeedBound : ∀ t, |speed t| ≤ speedBound)
    (hcharacter :
      ∀ n : d → ℤ, ∀ t : ℝ,
        HasDerivAt
          (fun s ↦ UnitAddTorus.mFourier n (path s))
          (((speed t : ℝ) : ℂ) *
            torusAngularFrequency n ω *
            UnitAddTorus.mFourier n (path t)) t)
    (hω :
      HGAS.Clocks.RadicalIndependence.HasNoNontrivialIntegerCharacter
        ω)
    (hzero :
      ∀ i, exponent i = 0 → coefficient i = 0)
    (hcoefficient :
      Summable fun i ↦ ‖coefficient i‖)
    (hprimitive :
      Summable fun i ↦
        ‖cohomologicalPrimitiveCoefficient
          coefficient exponent ω i‖)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦
        (torusCohomologicalPrimitive
          coefficient exponent ω (path s)).re)
      (speed t *
        (torusFourierSeries coefficient exponent (path t)).re) t := by
  have hcomplex :=
    torusCohomologicalPrimitive_comp_hasDerivAt_timeChanged_of_zeroMode
      coefficient exponent ω path speed speedBound
      hspeedBound_nonneg hspeedBound hcharacter hω hzero
      hcoefficient hprimitive t
  have hreal := HGAS.HasDerivAt.complex_re hcomplex
  simpa only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] using hreal

end HGAS.Analysis
