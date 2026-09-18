import HGAS.Analysis.RadicalFourierPrimitiveBounds
import HGAS.Analysis.TorusCohomologicalPrimitiveVector
import HGAS.Clocks.ScaledRadicalClock
import HGAS.Compiler.CompactAccumulatorPipelineGapCertificate
import Mathlib.Tactic

/-!
# Finite accumulator graphs over radical-torus components

This module packages the last abstract step in the no-instance
finite-graph construction.

Suppose that one invariant component of the compactified polynomial base
is homeomorphic to a finite torus and that, under this homeomorphism,

* the base flow is translation by a commonly scaled signed-prime-root
  frequency;
* every coordinate of the compactified drift is a specified absolutely
  convergent Fourier series.

If the zero Fourier modes vanish and the coefficients are summable after
multiplication by the fixed polynomial radical height, then the
small-divisor theorem constructs a continuous real vector primitive on the
torus.  Transporting it through the homeomorphism gives a primitive on the
actual compact base component.  Haar probability transports to an invariant
probability on that component.

The main constructor below then produces the exact
`ComponentFiniteGraphCertificate` consumed by
`CanonicalCompactAccumulatorGap.finite_graph`.  Thus concrete detector
modules need only prove the geometric torus model, the literal Fourier
crosswalk, coefficient summability, and two transparent pointwise bounds;
all analytic and accumulator bookkeeping is discharged here.
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

/-- A concrete invariant compact-base component modeled by a radical
translation torus, together with the exact Fourier representation of its
compiled drift.

The Fourier index type may depend on the real output coordinate.  This is
useful for a heterogeneous drift vector: a validity coordinate can use a
finite or singleton index, selector moments can use one-dimensional theta
indices, and the final detector can use its full product lattice.
-/
structure RadicalTorusFourierComponent
    (ι : Fin m → Type v)
    (scale : ℝ) (p : d → ℕ) (sign : d → ℤ)
    (coefficient : ∀ q, ι q → ℂ)
    (exponent : ∀ q, ι q → d → ℤ) where
  /-- The selected measurable invariant component of the compiled base. -/
  component : BaseInvariantComponent layout E M P
  /-- Explicit phase coordinates on the whole selected component. -/
  phaseHomeomorph :
    UnitAddTorus d ≃ₜ component.Space
  /-- The phase coordinates conjugate radical translation to the restricted
  compiled base flow. -/
  flow_equivariant :
    ∀ t : ℝ,
      Semiconj phaseHomeomorph
        (RadicalClock.torusTranslationFlow
          (ScaledRadicalClock.scaledSignedPrimeSqrtFrequency
            scale p sign) t)
        (component.flow t)
  /-- Literal equality between the compiled drift and its real Fourier
  series on the selected component. -/
  drift_eq_fourier :
    ∀ x : UnitAddTorus d,
      baseDriftBCF layout M κ h (phaseHomeomorph x) =
        realTorusFourierVector ι coefficient exponent x

namespace RadicalTorusFourierComponent

variable
    {ι : Fin m → Type v}
    {scale : ℝ} {p : d → ℕ} {sign : d → ℤ}
    {coefficient : ∀ q, ι q → ℂ}
    {exponent : ∀ q, ι q → d → ℤ}

/-- A short fully parameterized name used internally.  Mentioning the
compiler parameters explicitly is important because several of them occur
only in dependent fields of the underlying structure. -/
abbrev Model
    (layout : Fin n → Fin k ⊕ Fin l)
    (E M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (h : Fin m → PolynomialCode n)
    (ι : Fin m → Type v)
    (scale : ℝ) (p : d → ℕ) (sign : d → ℤ)
    (coefficient : ∀ q, ι q → ℂ)
    (exponent : ∀ q, ι q → d → ℤ) :=
  RadicalTorusFourierComponent
    (layout := layout) (E := E) (M := M) (κ := κ)
    (P := P) (h := h)
    ι scale p sign coefficient exponent

/-- The selected component projection with every compiler parameter made
explicit. -/
abbrev selectedComponent
    (G : Model layout E M κ P h
      ι scale p sign coefficient exponent) :
    BaseInvariantComponent layout E M P :=
  RadicalTorusFourierComponent.component
    (layout := layout) (E := E) (M := M) (κ := κ)
    (P := P) (h := h) G

/-- The selected component as a topological phase space. -/
abbrev ComponentSpace
    (G : Model layout E M κ P h
      ι scale p sign coefficient exponent) :=
  BaseInvariantComponent.Space
    (layout := layout) (E := E) (M := M) (P := P)
    (G.selectedComponent)

/-- The torus coordinates, with all compiler parameters explicit. -/
abbrev phaseEquiv
    (G : Model layout E M κ P h
      ι scale p sign coefficient exponent) :
    UnitAddTorus d ≃ₜ G.ComponentSpace :=
  RadicalTorusFourierComponent.phaseHomeomorph
    (layout := layout) (E := E) (M := M) (κ := κ)
    (P := P) (h := h) G

/-- The commonly scaled signed radical frequency used by a component. -/
abbrev frequency
    (scale : ℝ) (p : d → ℕ) (sign : d → ℤ) : d → ℝ :=
  ScaledRadicalClock.scaledSignedPrimeSqrtFrequency scale p sign

/-- The centered real Fourier primitive, transported from phase coordinates
to the actual compact base component. -/
def primitive
    (G : Model layout E M κ P h
      ι scale p sign coefficient exponent) :
    G.ComponentSpace → FinVector m ℝ :=
  fun b ↦
    realTorusCohomologicalPrimitive
      ι coefficient exponent (frequency scale p sign)
      (G.phaseEquiv.symm b)

/-- Weighted radical summability supplies the inverse-frequency
summability required by every coordinate of the vector primitive. -/
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

/-- The transported vector primitive is continuous. -/
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
        G.phaseEquiv.symm.continuous

/-- Flow conjugacy written in inverse phase coordinates. -/
theorem phaseHomeomorph_symm_flow
    (G : Model layout E M κ P h
      ι scale p sign coefficient exponent)
    (t : ℝ) (b : G.ComponentSpace) :
    G.phaseEquiv.symm (G.selectedComponent.flow t b) =
      RadicalClock.torusTranslationFlow
        (frequency scale p sign) t
        (G.phaseEquiv.symm b) := by
  apply G.phaseEquiv.injective
  rw [G.phaseEquiv.apply_symm_apply]
  exact
    (by
      simpa only [selectedComponent, phaseEquiv, ComponentSpace,
        frequency, Homeomorph.apply_symm_apply] using
      ((RadicalTorusFourierComponent.flow_equivariant
      (layout := layout) (E := E) (M := M) (κ := κ)
      (P := P) (h := h) G) t
      (G.phaseEquiv.symm b)).symm)

/-- The transported primitive differentiates to the literal compiled base
drift on the selected component.

This theorem is the central commuting square: differentiation is performed
in torus coordinates, while the conclusion is stated solely in the
polynomial compiler's `baseDriftBCF` language.
-/
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
  let x : UnitAddTorus d :=
    G.phaseEquiv.symm b
  have hω :
      RadicalIndependence.HasNoNontrivialIntegerCharacter
        (frequency scale p sign) :=
    ScaledRadicalClock.scaledSignedPrimeSqrtFrequency_hasNoCharacter
      scale hscale p hp hinjective sign hsign
  have hderiv :=
    realTorusCohomologicalPrimitive_hasDerivAt
      ι coefficient exponent (frequency scale p sign)
      hω hzero hcoefficient hprimitive x q t
  have hpath :
      (fun s ↦ G.primitive (G.selectedComponent.flow s b) q) =
        fun s ↦
          realTorusCohomologicalPrimitive
            ι coefficient exponent (frequency scale p sign)
            (RadicalClock.torusTranslationFlow
              (frequency scale p sign) s x) q := by
    funext s
    simp only [primitive, x]
    rw [G.phaseHomeomorph_symm_flow]
  rw [hpath]
  convert hderiv using 1
  have hequiv :=
    (RadicalTorusFourierComponent.flow_equivariant
      (layout := layout) (E := E) (M := M) (κ := κ)
      (P := P) (h := h) G) t x
  have hpoint :
      G.phaseEquiv
          (RadicalClock.torusTranslationFlow
            (frequency scale p sign) t x) =
        G.selectedComponent.flow t b := by
    simpa only [x, G.phaseEquiv.apply_symm_apply] using
      hequiv
  rw [← hpoint,
    RadicalTorusFourierComponent.drift_eq_fourier
      (layout := layout) (E := E) (M := M) (κ := κ)
      (P := P) (h := h) G]

/-- Pointwise squared-norm bound for the transported primitive. -/
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
      hprimitive (G.phaseEquiv.symm b)

/-- Haar probability on the radical torus, transported to the selected
compact base component. -/
def invariantProbability
    (G : Model layout E M κ P h
      ι scale p sign coefficient exponent) :
    Dynamics.InvariantProbabilityMeasure G.selectedComponent.flow :=
  (RadicalClock.torusHaarInvariantProbability
      (frequency scale p sign)).mapEquivariant
    G.phaseEquiv G.phaseEquiv.continuous
    (RadicalTorusFourierComponent.flow_equivariant
      (layout := layout) (E := E) (M := M) (κ := κ)
      (P := P) (h := h) G)

/-- Construct the exact finite-graph certificate from weighted Fourier
data.

The inequality `4 * K² ≤ wStar` is the stereographic accumulator scaling
condition, where `K²` is the displayed finite sum of squared coordinate
`ℓ¹` bounds.  The second inequality is the positive central-chart bound on
the selected component.  Both are pointwise, so the certificate's
almost-everywhere fields follow for the transported Haar probability
without any additional measure theory.
-/
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
      primitive_continuous :=
        G.continuous_primitive hprimitive
      primitive_derivative := ?_
      probability := G.invariantProbability
      wStar := wStar
      primitive_norm_ae := ?_
      centralWeight_ae := ?_ }
  · intro b q t
    exact
      G.primitive_derivative
        hscale hp hinjective hsign hzero hcoefficient
        hprimitive b q t
  · filter_upwards [] with b
    have hnorm :=
      G.normSq_primitive_le hprimitive b
    linarith
  · filter_upwards [] with b
    exact hcentral b

/-- Direct reward lower bound on the complete compact source generated by
a radical-torus Fourier component.  This is the existence statement needed
by the `finite_graph` field of the semantic gap certificate. -/
theorem exists_sourceProbability_reward_lower
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
        wStar ≤ baseCentralWeightProduct layout b.1)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
    (hh : ∀ i, PolynomialCode.TermsDegreeLE E (h i))
    (ε : RationalCode)
    (hcompactBase :
      BaseCompactTangency layout M P) :
    ∃ μ :
        Dynamics.InvariantProbabilityMeasure
          (sourceFlow layout E M κ P h ε),
      3 * wStar / 2 - (ε.decode : ℝ) ≤
        Dynamics.observableAverage
          (UnitSpherePolynomialWrapper.sourceRewardBCF
            (sourceBlock (m := m) layout)
            (rewardCode (n := n) (k := k) (m := m) ε))
          μ.measure := by
  let certificate :=
    G.componentFiniteGraphCertificate
      hscale hp hinjective hsign hzero hcoefficient
      hweighted wStar hprimitiveScale hcentral
  exact
    by
      simpa only [certificate, componentFiniteGraphCertificate] using
        certificate.exists_sourceProbability_reward_lower
          hP hh ε hcompactBase

/-- Final bridge in exactly the form of
`CanonicalCompactAccumulatorGap.finite_graph`, allowing a convenient
smaller positive margin `delta`. -/
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
    (hcompactBase :
      BaseCompactTangency layout M P)
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
  obtain ⟨μ, hμ⟩ :=
    (G hnot).exists_sourceProbability_reward_lower
      hscale hp hinjective hsign (hzero hnot)
      hcoefficient hweighted wStar hprimitiveScale
      (hcentral hnot) hP hh ε hcompactBase
  exact ⟨μ, hdelta.trans hμ⟩

end RadicalTorusFourierComponent

end HGAS.Analysis
