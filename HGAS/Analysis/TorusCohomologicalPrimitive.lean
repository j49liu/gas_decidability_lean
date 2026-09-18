import HGAS.Analysis.ComplexRealTimeDerivative
import HGAS.Analysis.TorusCharacters
import HGAS.Clocks.RadicalClock
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Tactic

/-!
# Fourier primitives for nonresonant torus translations

Let `ω : d → ℝ` generate the translation flow on the finite torus
`(ℝ / ℤ)ᵈ`.  A character with integral exponent `n : d → ℤ` evolves by

```text
  χₙ(x + tω) = χₙ(x) exp(2π i t ⟨n,ω⟩).
```

Consequently a nonresonant Fourier term `cₙ χₙ` has the primitive

```text
  cₙ χₙ / (2π i ⟨n,ω⟩).
```

This module makes that elementary calculation usable for an infinite
Fourier series.  There are exactly two summability assumptions:

* summability of `‖cₙ‖`, which uniformly controls the derivative series;
* summability after division by the nonzero frequencies, which gives the
  primitive itself.

Under these hypotheses the primitive is continuous, has an explicit
uniform norm bound, and differentiates term by term along every torus
orbit.  If the frequency vector has no nontrivial integral resonance and
the zero Fourier modes vanish, its derivative is the original series.

The statements are indexed by an arbitrary countable type rather than by
`ℤᵈ`.  This permits several analytic expression trees, or several copies
of the same character, to be concatenated without first collecting equal
exponents.
-/

noncomputable section

open Function
open scoped BigOperators

namespace HGAS.Analysis

variable {d ι : Type*} [Fintype d]

/-- The complex angular frequency `2π i ⟨n,ω⟩` of a torus character. -/
def torusAngularFrequency
    (n : d → ℤ) (ω : d → ℝ) : ℂ :=
  ((2 * Real.pi *
    HGAS.Clocks.RadicalClock.frequencyPairing n ω : ℝ) : ℂ) *
      Complex.I

/-- A Fourier coefficient with all resonant modes deleted. -/
def nonresonantCoefficient
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (ω : d → ℝ) (i : ι) : ℂ :=
  if HGAS.Clocks.RadicalClock.frequencyPairing
      (exponent i) ω = 0 then
    0
  else
    coefficient i

/-- Coefficient of the centered cohomological primitive.  Resonant modes
are set to zero; every other mode is divided by its angular frequency. -/
def cohomologicalPrimitiveCoefficient
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (ω : d → ℝ) (i : ι) : ℂ :=
  if HGAS.Clocks.RadicalClock.frequencyPairing
      (exponent i) ω = 0 then
    0
  else
    coefficient i /
      torusAngularFrequency (exponent i) ω

/-- An arbitrary countable Fourier series on a finite torus. -/
def torusFourierSeries
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (x : UnitAddTorus d) : ℂ :=
  ∑' i,
    torusSeriesTerm coefficient exponent i x

/-- The centered Fourier primitive obtained by inverse-frequency
division of all nonresonant modes. -/
def torusCohomologicalPrimitive
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (ω : d → ℝ)
    (x : UnitAddTorus d) : ℂ :=
  torusFourierSeries
    (cohomologicalPrimitiveCoefficient coefficient exponent ω)
    exponent x

theorem torusAngularFrequency_ne_zero
    {n : d → ℤ} {ω : d → ℝ}
    (hpair :
      HGAS.Clocks.RadicalClock.frequencyPairing n ω ≠ 0) :
    torusAngularFrequency n ω ≠ 0 := by
  unfold torusAngularFrequency
  apply mul_ne_zero
  · exact_mod_cast
      mul_ne_zero
        (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
          Real.pi_ne_zero)
        hpair
  · exact Complex.I_ne_zero

/-- Exact derivative of one torus character along a translation orbit. -/
theorem mFourier_torusTranslationFlow_hasDerivAt
    (n : d → ℤ) (ω : d → ℝ)
    (x : UnitAddTorus d) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦
        UnitAddTorus.mFourier n
          (HGAS.Clocks.RadicalClock.torusTranslationFlow
            ω s x))
      (torusAngularFrequency n ω *
        UnitAddTorus.mFourier n
          (HGAS.Clocks.RadicalClock.torusTranslationFlow
            ω t x))
      t := by
  let pairing :=
    HGAS.Clocks.RadicalClock.frequencyPairing n ω
  let angular : ℂ :=
    ((2 * Real.pi * pairing : ℝ) : ℂ) * Complex.I
  have hlinear :
      HasDerivAt
        (fun s : ℝ ↦
          angular * (s : ℂ))
        angular t := by
    simpa only [mul_one] using
      ((hasDerivAt_id (t : ℂ)).const_mul angular).comp_ofReal
  have hexp :
      HasDerivAt
        (fun s : ℝ ↦
          Complex.exp (angular * (s : ℂ)))
        (Complex.exp (angular * (t : ℂ)) * angular) t :=
    (Complex.hasDerivAt_exp _).comp t hlinear
  have hterm :=
    hexp.const_mul (UnitAddTorus.mFourier n x)
  have horbit (s : ℝ) :
      UnitAddTorus.mFourier n
          (HGAS.Clocks.RadicalClock.torusTranslationFlow
            ω s x) =
        UnitAddTorus.mFourier n x *
          Complex.exp (angular * (s : ℂ)) := by
    rw [HGAS.Clocks.RadicalClock.torusTranslationFlow_apply,
      HGAS.Clocks.RadicalClock.mFourier_add_point,
      HGAS.Clocks.RadicalClock.mFourier_torusDisplacement]
    congr 1
    dsimp only [angular, pairing]
    push_cast
    ring_nf
  convert hterm using 1
  · funext s
    exact horbit s
  · rw [horbit t]
    dsimp only [torusAngularFrequency, angular, pairing]
    push_cast
    ring_nf

/-- One inverse-frequency Fourier term differentiates to the same term
with its resonant mode deleted. -/
theorem cohomologicalPrimitiveTerm_hasDerivAt
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (ω : d → ℝ)
    (i : ι) (x : UnitAddTorus d) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦
        torusSeriesTerm
          (cohomologicalPrimitiveCoefficient
            coefficient exponent ω)
          exponent i
          (HGAS.Clocks.RadicalClock.torusTranslationFlow
            ω s x))
      (torusSeriesTerm
        (nonresonantCoefficient coefficient exponent ω)
        exponent i
        (HGAS.Clocks.RadicalClock.torusTranslationFlow
          ω t x))
      t := by
  by_cases hpair :
      HGAS.Clocks.RadicalClock.frequencyPairing
        (exponent i) ω = 0
  · simpa [torusSeriesTerm,
      cohomologicalPrimitiveCoefficient,
      nonresonantCoefficient, hpair] using
      (hasDerivAt_const
        (x := t) (c := (0 : ℂ)))
  · have hcharacter :=
      mFourier_torusTranslationFlow_hasDerivAt
        (exponent i) ω x t
    have hscaled :=
      hcharacter.const_mul
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

/-- Absolute coefficient summability gives continuity of the corresponding
Fourier series by uniform convergence. -/
theorem continuous_torusFourierSeries
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (hsummable :
      Summable fun i ↦ ‖coefficient i‖) :
    Continuous (torusFourierSeries coefficient exponent) := by
  unfold torusFourierSeries
  apply continuous_tsum
  · intro i
    exact Continuous.mul continuous_const
      (UnitAddTorus.mFourier (exponent i)).continuous
  · exact hsummable
  · intro i x
    exact le_of_eq
      (norm_torusSeriesTerm coefficient exponent i x)

/-- The inverse-frequency summability hypothesis gives continuity of the
cohomological primitive. -/
theorem continuous_torusCohomologicalPrimitive
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (ω : d → ℝ)
    (hprimitive :
      Summable fun i ↦
        ‖cohomologicalPrimitiveCoefficient
          coefficient exponent ω i‖) :
    Continuous
      (torusCohomologicalPrimitive
        coefficient exponent ω) := by
  exact
    continuous_torusFourierSeries
      (cohomologicalPrimitiveCoefficient
        coefficient exponent ω)
      exponent hprimitive

/-- The coefficient `ℓ¹` norm is a uniform pointwise bound for the
cohomological primitive. -/
theorem norm_torusCohomologicalPrimitive_le
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (ω : d → ℝ)
    (hprimitive :
      Summable fun i ↦
        ‖cohomologicalPrimitiveCoefficient
          coefficient exponent ω i‖)
    (x : UnitAddTorus d) :
    ‖torusCohomologicalPrimitive
        coefficient exponent ω x‖ ≤
      ∑' i,
        ‖cohomologicalPrimitiveCoefficient
          coefficient exponent ω i‖ := by
  let term : ι → ℂ :=
    fun i ↦
      torusSeriesTerm
        (cohomologicalPrimitiveCoefficient
          coefficient exponent ω)
        exponent i x
  have hterm :
      Summable fun i ↦ ‖term i‖ := by
    apply hprimitive.congr
    intro i
    exact (
      norm_torusSeriesTerm
        (cohomologicalPrimitiveCoefficient
          coefficient exponent ω)
        exponent i x).symm
  calc
    ‖torusCohomologicalPrimitive
        coefficient exponent ω x‖ =
        ‖∑' i, term i‖ := rfl
    _ ≤ ∑' i, ‖term i‖ :=
      norm_tsum_le_tsum_norm hterm
    _ = ∑' i,
        ‖cohomologicalPrimitiveCoefficient
          coefficient exponent ω i‖ := by
      apply tsum_congr
      intro i
      exact
        norm_torusSeriesTerm
          (cohomologicalPrimitiveCoefficient
            coefficient exponent ω)
          exponent i x

/-- The complete centered primitive differentiates term by term.  Its
derivative is the Fourier series with precisely the resonant modes
removed. -/
theorem torusCohomologicalPrimitive_hasDerivAt
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (ω : d → ℝ)
    (hcoefficient :
      Summable fun i ↦ ‖coefficient i‖)
    (hprimitive :
      Summable fun i ↦
        ‖cohomologicalPrimitiveCoefficient
          coefficient exponent ω i‖)
    (x : UnitAddTorus d) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦
        torusCohomologicalPrimitive coefficient exponent ω
          (HGAS.Clocks.RadicalClock.torusTranslationFlow
            ω s x))
      (torusFourierSeries
        (nonresonantCoefficient coefficient exponent ω)
        exponent
        (HGAS.Clocks.RadicalClock.torusTranslationFlow
          ω t x))
      t := by
  let primitiveTerm : ι → ℝ → ℂ :=
    fun i s ↦
      torusSeriesTerm
        (cohomologicalPrimitiveCoefficient
          coefficient exponent ω)
        exponent i
        (HGAS.Clocks.RadicalClock.torusTranslationFlow
          ω s x)
  let derivativeTerm : ι → ℝ → ℂ :=
    fun i s ↦
      torusSeriesTerm
        (nonresonantCoefficient coefficient exponent ω)
        exponent i
        (HGAS.Clocks.RadicalClock.torusTranslationFlow
          ω s x)
  have hderivative :
      ∀ i s,
        HasDerivAt (primitiveTerm i)
          (derivativeTerm i s) s := by
    intro i s
    exact
      cohomologicalPrimitiveTerm_hasDerivAt
        coefficient exponent ω i x s
  have hderivativeBound :
      ∀ i s,
        ‖derivativeTerm i s‖ ≤ ‖coefficient i‖ := by
    intro i s
    rw [show
        ‖derivativeTerm i s‖ =
          ‖nonresonantCoefficient
            coefficient exponent ω i‖ by
      exact
        norm_torusSeriesTerm
          (nonresonantCoefficient coefficient exponent ω)
          exponent i
          (HGAS.Clocks.RadicalClock.torusTranslationFlow
            ω s x)]
    unfold nonresonantCoefficient
    split_ifs
    · simp
    · exact le_rfl
  have hprimitiveAtZero :
      Summable fun i ↦ primitiveTerm i 0 := by
    apply hprimitive.of_norm_bounded
    intro i
    exact le_of_eq
      (norm_torusSeriesTerm
        (cohomologicalPrimitiveCoefficient
          coefficient exponent ω)
        exponent i
        (HGAS.Clocks.RadicalClock.torusTranslationFlow
          ω 0 x))
  have h :=
    hasDerivAt_tsum
      hcoefficient hderivative hderivativeBound
      hprimitiveAtZero t
  simpa only [primitiveTerm, derivativeTerm,
    torusCohomologicalPrimitive, torusFourierSeries] using h

/-- For a nonresonant frequency vector, deleting resonant modes merely
deletes the zero exponent.  If every zero-exponent coefficient is already
zero, no coefficient changes. -/
theorem nonresonantCoefficient_eq_self
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (ω : d → ℝ)
    (hω :
      HGAS.Clocks.RadicalIndependence.HasNoNontrivialIntegerCharacter
        ω)
    (hzero :
      ∀ i, exponent i = 0 → coefficient i = 0)
    (i : ι) :
    nonresonantCoefficient coefficient exponent ω i =
      coefficient i := by
  unfold nonresonantCoefficient
  by_cases hpair :
      HGAS.Clocks.RadicalClock.frequencyPairing
        (exponent i) ω = 0
  · rw [if_pos hpair]
    exact (hzero i (hω (exponent i) hpair)).symm
  · rw [if_neg hpair]

/-- Nonresonance and vanishing zero mode turn the centered derivative into
the original Fourier series. -/
theorem torusCohomologicalPrimitive_hasDerivAt_of_zeroMode
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (ω : d → ℝ)
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
    (x : UnitAddTorus d) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦
        torusCohomologicalPrimitive coefficient exponent ω
          (HGAS.Clocks.RadicalClock.torusTranslationFlow
            ω s x))
      (torusFourierSeries coefficient exponent
        (HGAS.Clocks.RadicalClock.torusTranslationFlow
          ω t x))
      t := by
  have hcoeff :
      nonresonantCoefficient coefficient exponent ω =
        coefficient := by
    funext i
    exact
      nonresonantCoefficient_eq_self
        coefficient exponent ω hω hzero i
  simpa only [hcoeff] using
    torusCohomologicalPrimitive_hasDerivAt
      coefficient exponent ω hcoefficient hprimitive x t

/-- Real-part specialization for real polynomial drift coordinates. -/
theorem torusCohomologicalPrimitive_re_hasDerivAt_of_zeroMode
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (ω : d → ℝ)
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
    (x : UnitAddTorus d) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦
        (torusCohomologicalPrimitive coefficient exponent ω
          (HGAS.Clocks.RadicalClock.torusTranslationFlow
            ω s x)).re)
      (torusFourierSeries coefficient exponent
        (HGAS.Clocks.RadicalClock.torusTranslationFlow
          ω t x)).re
      t := by
  exact
    HGAS.HasDerivAt.complex_re
      (torusCohomologicalPrimitive_hasDerivAt_of_zeroMode
        coefficient exponent ω hω hzero
        hcoefficient hprimitive x t)

end HGAS.Analysis
