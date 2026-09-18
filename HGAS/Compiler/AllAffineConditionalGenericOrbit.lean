import HGAS.Compiler.AllAffineErgodicPhysicalOrbit
import HGAS.Compiler.CompactAccumulatorPipelineGapCertificate
import HGAS.Dynamics.ErgodicFullMeasureRestriction
import Mathlib.Tactic

/-!
# From a conditional compact mean to one generic physical orbit

`CanonicalCompactAccumulatorGap.nonzero_mean` is stated using the base
probability obtained by conditioning a complete compact-source measure on
the finite interior and then pushing it to the compact base.  The
pointwise selector, by contrast, needs one point of the restricted source
flow.

For the one-block all-affine layout, this file proves the exact bridge:
zero base-drift means pull back to zero means of the finite-chart scalar
drift observables, the positive restriction of an ergodic measure remains
ergodic, and one recurrent point can then be selected simultaneously for
the speed and every drift coordinate.
-/

namespace HGAS

open Filter Function MeasureTheory Set Topology
open scoped BoundedContinuousFunction

noncomputable section

namespace CompactAccumulatorPipelineCode

namespace AllAffineConditionalGenericOrbit

open AllAffineCompactSourceChart
open AllAffineCompactSourceClock
open AllAffineCompactSourceDrift
open AllAffineErgodicPhysicalOrbit

variable {n m : ℕ}

/-- Canonical compact source flow for the one-block all-affine layout. -/
def compactFlow
    (E K : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (h : Fin m → PolynomialCode n)
    (ε : RationalCode) :
    Flow ℝ (SourceSpace n m) :=
  sourceFlow (layout n) E (2 * K) κ P h ε

/-- Its canonical invariant finite interior. -/
def finiteInvariant
    (E K : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
    (h : Fin m → PolynomialCode n)
    (hh : ∀ i, PolynomialCode.TermsDegreeLE E (h i))
    (ε : RationalCode) :
    IsInvariant (compactFlow E K κ P h ε)
      (sourceFiniteInteriorSet (m := m) (layout n)) :=
  canonicalFiniteInteriorInvariant
    (layout n) E (2 * K) κ P hP h hh ε
    (by
      intro _
      dsimp
      intro c
      exact Fin.elim0 c)

variable
  (E K : ℕ) (κ : RationalCode)
  (P : PolynomialFieldCode n)
  (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
  (h : Fin m → PolynomialCode n)
  (hh : ∀ i, PolynomialCode.TermsDegreeLE E (h i))
  (ε : RationalCode)

/-- Zero means on the conditional compact base produce one recurrent
finite-chart point which is simultaneously generic for positive speed and
all zero drift coordinates. -/
theorem exists_recurrent_genericPhysicalPoint_of_conditionalBase_zero
    (μ :
      Dynamics.InvariantProbabilityMeasure
        (compactFlow E K κ P h ε))
    (hμ :
      Dynamics.IsErgodicInvariantProbability
        (compactFlow E K κ P h ε) μ.measure)
    (hpos :
      (μ.measure : Measure (SourceSpace n m))
        (sourceFiniteInteriorSet (m := m) (layout n)) ≠ 0)
    (hzero :
      ∀ i : Fin m,
        (∫ b, baseDriftBCF (layout n) (2 * K) κ h b i
          ∂((conditionalBaseProbability
              (layout n) E (2 * K) κ P hP h hh ε
              (by
                intro _
                dsimp
                intro c
                exact Fin.elim0 c)
              μ hpos).measure :
            Measure (BaseSpace (layout n)))) = 0) :
    ∃ (v : FiniteSourceSpace n m) (c : ℝ),
      PositiveIntegralClock
          (stateClockWeight (affineSpeed K)
            (affineCurve
              (compactFlow E K κ P h ε)
              (finiteInvariant E K κ P hP h hh ε) v)) ∧
      0 < c ∧
      ForwardRecurrentAt
        (fun t : ℝ ↦
          ((compactFlow E K κ P h ε).restrict
            (finiteInvariant E K κ P hP h hh ε)) t v) 0 ∧
      Tendsto
        (fun q : ℕ ↦
          Dynamics.integerOrbitAverageObservable
            ((compactFlow E K κ P h ε).restrict
              (finiteInvariant E K κ P hP h hh ε))
            (affineSpeedBCF K) (q + 1) v)
        atTop (𝓝 c) ∧
      ∀ i : Fin m,
        Tendsto
          (fun q : ℕ ↦
            Dynamics.integerOrbitAverageObservable
              ((compactFlow E K κ P h ε).restrict
                (finiteInvariant E K κ P hP h hh ε))
              (finiteDriftCoordinateBCF K κ h i)
              (q + 1) v)
          atTop (𝓝 0) := by
  let hinv :=
    finiteInvariant E K κ P hP h hh ε
  let ν :=
    μ.restrictToPositiveInvariant
      (measurableSet_sourceFiniteInteriorSet
        (m := m) (layout n))
      hpos hinv
  have hν :
      Dynamics.IsErgodicInvariantProbability
        ((compactFlow E K κ P h ε).restrict hinv)
        ν.measure := by
    exact
      hμ.restrictToPositiveInvariant μ
        (measurableSet_sourceFiniteInteriorSet
          (m := m) (layout n))
        hpos hinv
  have hzeroFinite :
      ∀ i : Fin m,
        (∫ v, finiteDriftCoordinateBCF K κ h i v
          ∂(ν.measure : Measure (FiniteSourceSpace n m))) = 0 := by
    intro i
    have hi := hzero i
    change
      (∫ b, baseDriftBCF (layout n) (2 * K) κ h b i
        ∂((ν.mapEquivariant
          (restrictedBaseProjection (m := m) (layout n))
          (continuous_restrictedBaseProjection
            (m := m) (layout n))
          (canonicalRestrictedBaseProjection_semiconj
            (layout n) E (2 * K) κ P hP h hh ε
            (by
              intro _
              dsimp
              intro c
              exact Fin.elim0 c))).measure :
          Measure (BaseSpace (layout n)))) = 0 at hi
    rw [Dynamics.InvariantProbabilityMeasure.mapEquivariant_measure] at hi
    change
      (∫ b : BaseSpace (layout n),
        baseDriftBCF (layout n) (2 * K) κ h b i
        ∂Measure.map
          (restrictedBaseProjection (m := m) (layout n))
          (ν.measure : Measure (FiniteSourceSpace n m))) = 0 at hi
    rw [integral_map
      (f := fun b : BaseSpace (layout n) ↦
        baseDriftBCF (layout n) (2 * K) κ h b i)
      (φ := restrictedBaseProjection (m := m) (layout n))
      (continuous_restrictedBaseProjection
        (m := m) (layout n)).measurable.aemeasurable
      ((continuous_apply i).comp
        (baseDriftBCF (layout n) (2 * K) κ h).continuous
        ).aestronglyMeasurable] at hi
    simpa only [finiteDriftCoordinateBCF_apply] using hi
  have hexists :=
    exists_recurrent_genericPhysicalPoint
      K κ h
      (compactFlow E K κ P h ε)
      hinv ν hν hzeroFinite
  simpa only [hinv] using hexists

end AllAffineConditionalGenericOrbit

end CompactAccumulatorPipelineCode

end

end HGAS
