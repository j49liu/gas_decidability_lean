import HGAS.Analysis.RadicalFourierPrimitiveBounds
import HGAS.Analysis.TimeChangedTorusCohomologicalPrimitive
import HGAS.Analysis.TorusCohomologicalPrimitiveVector
import HGAS.Clocks.ScaledRadicalClock
import HGAS.Compiler.CompactAccumulatorPipelineGapCertificate
import Mathlib.Tactic

/-!
# Finite graphs over time-changed radical-torus components

This is the compiler-facing version of the radical Fourier primitive.
Central compactification changes physical time by a bounded nonnegative
slowdown.  Therefore a phase observation of the compact base need not be an
equal-time factor of torus translation.  What is true, and what this module
uses, is the orbitwise character identity

```text
 d/ds χ_a(phase(flow_s b))
   = speed(flow_s b) * 2π i <a,ω> * χ_a(phase(flow_s b)).
```

If the compiled drift is the same speed times a centered Fourier vector,
the inverse-frequency series is still an exact primitive.  The theorems
below combine:

* the quantitative prime-radical small-divisor bound;
* weighted Fourier coefficient summability;
* termwise differentiation along a bounded time change;
* the finite real-vector norm estimate; and
* the component finite-graph compiler.

No injectivity or surjectivity is required of the phase observation.  This
is important for canonical detector components which may be finite covers
of the arithmetic phase torus.
-/

noncomputable section

open Function MeasureTheory
open scoped BigOperators BoundedContinuousFunction

namespace HGAS.Analysis

open HGAS.Clocks
open HGAS.CompactAccumulatorPipelineCode

universe u v

variable {d : Type u} [Fintype d]
variable {n k l m : ℕ}
variable {layout : Fin n → Fin k ⊕ Fin l}
variable {E M : ℕ} {κ : RationalCode}
variable {P : PolynomialFieldCode n}
variable {h : Fin m → PolynomialCode n}

/-- A selected compact base component carrying a time-changed radical
phase observation and an exact Fourier representation of the compiled
drift. -/
structure RadicalTimeChangedTorusFourierComponent
    (ι : Fin m → Type v)
    (scale : ℝ) (p : d → ℕ) (sign : d → ℤ)
    (coefficient : ∀ q, ι q → ℂ)
    (exponent : ∀ q, ι q → d → ℤ) where
  /-- The selected invariant compact-base component. -/
  component : BaseInvariantComponent layout E M P
  /-- Physical clock phases in additive turns. -/
  phase : component.Space → UnitAddTorus d
  /-- Phase extraction is continuous on the selected component. -/
  phase_continuous : Continuous phase
  /-- State-dependent compactification speed. -/
  speed : component.Space → ℝ
  /-- A uniform absolute bound for the speed. -/
  speedBound : ℝ
  speedBound_nonneg : 0 ≤ speedBound
  speed_le : ∀ b, |speed b| ≤ speedBound
  /-- Orbitwise derivative of every Fourier character. -/
  character_derivative :
    ∀ b (a : d → ℤ) t,
      HasDerivAt
        (fun s ↦
          UnitAddTorus.mFourier a
            (phase (component.flow s b)))
        (((speed (component.flow t b) : ℝ) : ℂ) *
          torusAngularFrequency a
            (ScaledRadicalClock.scaledSignedPrimeSqrtFrequency
              scale p sign) *
          UnitAddTorus.mFourier a
            (phase (component.flow t b))) t
  /-- The literal compiled drift is the same time-change factor times the
  real Fourier vector.  The coefficient family may already include the
  rational accumulator scale `κ`. -/
  drift_eq_fourier :
    ∀ b : component.Space,
      baseDriftBCF layout M κ h b =
        speed b •
          realTorusFourierVector
            ι coefficient exponent (phase b)
  /-- An invariant probability carried by the selected component.
  In the canonical application this is the reciprocal-speed reweighting of
  torus Haar probability. -/
  probability :
    Dynamics.InvariantProbabilityMeasure component.flow

namespace RadicalTimeChangedTorusFourierComponent

variable
    {ι : Fin m → Type v}
    {scale : ℝ} {p : d → ℕ} {sign : d → ℤ}
    {coefficient : ∀ q, ι q → ℂ}
    {exponent : ∀ q, ι q → d → ℤ}

/-- Fully parameterized internal abbreviation. -/
abbrev Model
    (layout : Fin n → Fin k ⊕ Fin l)
    (E M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (h : Fin m → PolynomialCode n)
    (ι : Fin m → Type v)
    (scale : ℝ) (p : d → ℕ) (sign : d → ℤ)
    (coefficient : ∀ q, ι q → ℂ)
    (exponent : ∀ q, ι q → d → ℤ) :=
  RadicalTimeChangedTorusFourierComponent
    (layout := layout) (E := E) (M := M) (κ := κ)
    (P := P) (h := h)
    ι scale p sign coefficient exponent

abbrev frequency
    (scale : ℝ) (p : d → ℕ) (sign : d → ℤ) : d → ℝ :=
  ScaledRadicalClock.scaledSignedPrimeSqrtFrequency scale p sign

/-- Explicit projection of the selected component. -/
abbrev selectedComponent
    (G : Model layout E M κ P h
      ι scale p sign coefficient exponent) :
    BaseInvariantComponent layout E M P :=
  RadicalTimeChangedTorusFourierComponent.component
    (layout := layout) (E := E) (M := M) (κ := κ)
    (P := P) (h := h) G

abbrev ComponentSpace
    (G : Model layout E M κ P h
      ι scale p sign coefficient exponent) :=
  BaseInvariantComponent.Space
    (layout := layout) (E := E) (M := M) (P := P)
    G.selectedComponent

/-- The centered vector primitive pulled back by the physical phase
observation. -/
def primitive
    (G : Model layout E M κ P h
      ι scale p sign coefficient exponent) :
    G.ComponentSpace → FinVector m ℝ :=
  fun b ↦
    realTorusCohomologicalPrimitive
      ι coefficient exponent (frequency scale p sign)
      ((RadicalTimeChangedTorusFourierComponent.phase
        (layout := layout) (E := E) (M := M) (κ := κ)
        (P := P) (h := h) G) b)

/-- Weighted radical summability automatically supplies the
inverse-frequency summability of every output coordinate. -/
theorem primitiveCoefficient_summable
    (hscale : scale ≠ 0)
    (hp : ∀ i : d, (p i).Prime)
    (hinjective : Function.Injective p)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (hweighted :
      ∀ q,
        Summable fun j ↦
          ‖coefficient q j‖ *
            RadicalSmallDivisor.radicalConjugateHeight
                p (exponent q j) ^
              (RadicalSmallDivisor.radicalDegree p - 1)) :
    ∀ q,
      Summable fun j ↦
        ‖cohomologicalPrimitiveCoefficient
          (coefficient q) (exponent q)
          (frequency scale p sign) j‖ := by
  intro q
  exact
    summable_norm_cohomologicalPrimitiveCoefficient_of_radical
      scale hscale p hp hinjective sign hsign
      (coefficient q) (exponent q) (hweighted q)

/-- Continuity of the transported vector primitive. -/
theorem continuous_primitive
    (G : Model layout E M κ P h
      ι scale p sign coefficient exponent)
    (hprimitive :
      ∀ q,
        Summable fun j ↦
          ‖cohomologicalPrimitiveCoefficient
            (coefficient q) (exponent q)
            (frequency scale p sign) j‖) :
    Continuous G.primitive := by
  exact
    (continuous_realTorusCohomologicalPrimitive
      ι coefficient exponent (frequency scale p sign)
      hprimitive).comp
        (RadicalTimeChangedTorusFourierComponent.phase_continuous
          (layout := layout) (E := E) (M := M) (κ := κ)
          (P := P) (h := h) G)

/-- Exact derivative of the transported primitive under the compiled
time-changed base flow. -/
theorem primitive_derivative
    (G : Model layout E M κ P h
      ι scale p sign coefficient exponent)
    (hscale : scale ≠ 0)
    (hp : ∀ i : d, (p i).Prime)
    (hinjective : Function.Injective p)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (hzero :
      ∀ q j, exponent q j = 0 → coefficient q j = 0)
    (hcoefficient :
      ∀ q, Summable fun j ↦ ‖coefficient q j‖)
    (hprimitive :
      ∀ q,
        Summable fun j ↦
          ‖cohomologicalPrimitiveCoefficient
            (coefficient q) (exponent q)
            (frequency scale p sign) j‖)
    (b : G.ComponentSpace) (q : Fin m) (t : ℝ) :
    HasDerivAt
      (fun s ↦ G.primitive (G.selectedComponent.flow s b) q)
      (baseDriftBCF layout M κ h
        (G.selectedComponent.flow t b) q) t := by
  let phase :=
    RadicalTimeChangedTorusFourierComponent.phase
      (layout := layout) (E := E) (M := M) (κ := κ)
      (P := P) (h := h) G
  let speed :=
    RadicalTimeChangedTorusFourierComponent.speed
      (layout := layout) (E := E) (M := M) (κ := κ)
      (P := P) (h := h) G
  let path : ℝ → UnitAddTorus d :=
    fun s ↦ phase (G.selectedComponent.flow s b)
  let speedPath : ℝ → ℝ :=
    fun s ↦ speed (G.selectedComponent.flow s b)
  have hω :
      RadicalIndependence.HasNoNontrivialIntegerCharacter
        (frequency scale p sign) :=
    ScaledRadicalClock.scaledSignedPrimeSqrtFrequency_hasNoCharacter
      scale hscale p hp hinjective sign hsign
  have hspeed :
      ∀ s, |speedPath s| ≤
        RadicalTimeChangedTorusFourierComponent.speedBound
          (layout := layout) (E := E) (M := M) (κ := κ)
          (P := P) (h := h) G := by
    intro s
    exact
      RadicalTimeChangedTorusFourierComponent.speed_le
        (layout := layout) (E := E) (M := M) (κ := κ)
        (P := P) (h := h) G
        (G.selectedComponent.flow s b)
  have hcharacter :
      ∀ a : d → ℤ, ∀ s : ℝ,
        HasDerivAt
          (fun u ↦ UnitAddTorus.mFourier a (path u))
          (((speedPath s : ℝ) : ℂ) *
            torusAngularFrequency a (frequency scale p sign) *
            UnitAddTorus.mFourier a (path s)) s := by
    intro a s
    exact
      RadicalTimeChangedTorusFourierComponent.character_derivative
        (layout := layout) (E := E) (M := M) (κ := κ)
        (P := P) (h := h) G b a s
  have hderiv :=
    torusCohomologicalPrimitive_re_comp_hasDerivAt_timeChanged_of_zeroMode
      (coefficient q) (exponent q)
      (frequency scale p sign)
      path speedPath
      (RadicalTimeChangedTorusFourierComponent.speedBound
        (layout := layout) (E := E) (M := M) (κ := κ)
        (P := P) (h := h) G)
      (RadicalTimeChangedTorusFourierComponent.speedBound_nonneg
        (layout := layout) (E := E) (M := M) (κ := κ)
        (P := P) (h := h) G)
      hspeed hcharacter hω (hzero q)
      (hcoefficient q) (hprimitive q) t
  have hdrift :=
    congrFun
      (RadicalTimeChangedTorusFourierComponent.drift_eq_fourier
        (layout := layout) (E := E) (M := M) (κ := κ)
        (P := P) (h := h) G
        (G.selectedComponent.flow t b)) q
  change
    baseDriftBCF layout M κ h
        (G.selectedComponent.flow t b) q =
      speedPath t *
        (torusFourierSeries
          (coefficient q) (exponent q) (path t)).re at hdrift
  exact hderiv.congr_deriv hdrift.symm

/-- The same finite squared-norm bound as in the equal-time case. -/
theorem normSq_primitive_le
    (G : Model layout E M κ P h
      ι scale p sign coefficient exponent)
    (hprimitive :
      ∀ q,
        Summable fun j ↦
          ‖cohomologicalPrimitiveCoefficient
            (coefficient q) (exponent q)
            (frequency scale p sign) j‖)
    (b : G.ComponentSpace) :
    normSq (G.primitive b) ≤
      ∑ q : Fin m,
        (primitiveCoordinateBound
          ι coefficient exponent (frequency scale p sign) q) ^ 2 := by
  exact
    normSq_realTorusCohomologicalPrimitive_le
      ι coefficient exponent (frequency scale p sign)
      hprimitive
      ((RadicalTimeChangedTorusFourierComponent.phase
        (layout := layout) (E := E) (M := M) (κ := κ)
        (P := P) (h := h) G) b)

/-- Construct the exact component finite-graph certificate. -/
def componentFiniteGraphCertificate
    (G : Model layout E M κ P h
      ι scale p sign coefficient exponent)
    (hscale : scale ≠ 0)
    (hp : ∀ i : d, (p i).Prime)
    (hinjective : Function.Injective p)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (hzero :
      ∀ q j, exponent q j = 0 → coefficient q j = 0)
    (hcoefficient :
      ∀ q, Summable fun j ↦ ‖coefficient q j‖)
    (hweighted :
      ∀ q,
        Summable fun j ↦
          ‖coefficient q j‖ *
            RadicalSmallDivisor.radicalConjugateHeight
                p (exponent q j) ^
              (RadicalSmallDivisor.radicalDegree p - 1))
    (wStar : ℝ)
    (hprimitiveScale :
      4 *
          (∑ q : Fin m,
            (primitiveCoordinateBound
              ι coefficient exponent (frequency scale p sign) q) ^ 2) ≤
        wStar)
    (hcentral :
      ∀ b : G.ComponentSpace,
        wStar ≤ baseCentralWeightProduct layout b.1) :
    ComponentFiniteGraphCertificate layout E M κ P h := by
  let hprimitive :=
    primitiveCoefficient_summable
      hscale hp hinjective hsign hweighted
  refine
    { component := G.selectedComponent
      primitive := G.primitive
      primitive_continuous := G.continuous_primitive hprimitive
      primitive_derivative := ?_
      probability :=
        RadicalTimeChangedTorusFourierComponent.probability
          (layout := layout) (E := E) (M := M) (κ := κ)
          (P := P) (h := h) G
      wStar := wStar
      primitive_norm_ae := ?_
      centralWeight_ae := ?_ }
  · intro b q t
    exact
      G.primitive_derivative
        hscale hp hinjective hsign hzero hcoefficient
        hprimitive b q t
  · filter_upwards [] with b
    have hnorm := G.normSq_primitive_le hprimitive b
    linarith
  · filter_upwards [] with b
    exact hcentral b

/-- Direct no-instance reward statement in the exact form consumed by
`CanonicalCompactAccumulatorGap.finite_graph`. -/
theorem finite_graph
    {eqs vars : ℕ}
    (I : DQLSystem eqs vars)
    (G :
      ¬I.Solvable →
        Model layout E M κ P h
          ι scale p sign coefficient exponent)
    (hscale : scale ≠ 0)
    (hp : ∀ i : d, (p i).Prime)
    (hinjective : Function.Injective p)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (hzero :
      ∀ _hnot : ¬I.Solvable,
        ∀ q j, exponent q j = 0 → coefficient q j = 0)
    (hcoefficient :
      ∀ q, Summable fun j ↦ ‖coefficient q j‖)
    (hweighted :
      ∀ q,
        Summable fun j ↦
          ‖coefficient q j‖ *
            RadicalSmallDivisor.radicalConjugateHeight
                p (exponent q j) ^
              (RadicalSmallDivisor.radicalDegree p - 1))
    (wStar delta : ℝ)
    (hprimitiveScale :
      4 *
          (∑ q : Fin m,
            (primitiveCoordinateBound
              ι coefficient exponent (frequency scale p sign) q) ^ 2) ≤
        wStar)
    (hcentral :
      ∀ hnot : ¬I.Solvable,
        ∀ b : (G hnot).ComponentSpace,
          wStar ≤ baseCentralWeightProduct layout b.1)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
    (hh : ∀ i, PolynomialCode.TermsDegreeLE E (h i))
    (ε : RationalCode)
    (hcompactBase : BaseCompactTangency layout M P)
    (hdelta :
      delta ≤ 3 * wStar / 2 - (ε.decode : ℝ)) :
    ¬I.Solvable →
      ∃ μ :
          Dynamics.InvariantProbabilityMeasure
            (sourceFlow layout E M κ P h ε),
        delta ≤
          Dynamics.observableAverage
            (UnitSpherePolynomialWrapper.sourceRewardBCF
              (sourceBlock (m := m) layout)
              (rewardCode (n := n) (k := k) (m := m) ε))
            μ.measure := by
  intro hnot
  let certificate :=
    (G hnot).componentFiniteGraphCertificate
      hscale hp hinjective hsign (hzero hnot)
      hcoefficient hweighted wStar hprimitiveScale
      (hcentral hnot)
  obtain ⟨μ, hμ⟩ :=
    certificate.exists_sourceProbability_reward_lower
      hP hh ε hcompactBase
  exact
    ⟨μ, hdelta.trans (by
      simpa only [certificate, componentFiniteGraphCertificate] using
        hμ)⟩

end RadicalTimeChangedTorusFourierComponent

end HGAS.Analysis
