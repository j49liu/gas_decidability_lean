import HGAS.Compiler.AllAffineConditionalGenericOrbit
import HGAS.Compiler.AllAffineErgodicPhysicalZeroOrbit
import Mathlib.Tactic

/-!
# A conditional generic physical orbit on a pointwise zero locus

This is the conditional-measure counterpart of
`AllAffineErgodicPhysicalZeroOrbit`.  Zero conditional base means are
pulled back to the positive finite-chart restriction.  When one drift
coordinate is nonnegative, the selected recurrent generic orbit lies in
its zero locus for every real compact time.
-/

namespace HGAS

open Filter Function MeasureTheory Set Topology
open scoped BoundedContinuousFunction

noncomputable section

namespace CompactAccumulatorPipelineCode

namespace AllAffineConditionalGenericZeroOrbit

open AllAffineCompactSourceChart
open AllAffineCompactSourceClock
open AllAffineCompactSourceDrift
open AllAffineConditionalGenericOrbit
open AllAffineErgodicPhysicalZeroOrbit

variable {n m : ℕ}

variable
  (E K : ℕ) (κ : RationalCode)
  (P : PolynomialFieldCode n)
  (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
  (h : Fin m → PolynomialCode n)
  (hh : ∀ i, PolynomialCode.TermsDegreeLE E (h i))
  (ε : RationalCode)

/-- Conditional zero means, together with nonnegativity of one selected
compact drift coordinate, yield one recurrent generic physical point on
which that coordinate vanishes for all compact time. -/
theorem exists_recurrent_genericPhysicalPoint_zeroCoordinate_of_conditionalBase_zero
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
            Measure (BaseSpace (layout n)))) = 0)
    (q₀ : Fin m)
    (hq₀_nonneg :
      ∀ v : FiniteSourceSpace n m,
        0 ≤ finiteDriftCoordinateBCF K κ h q₀ v) :
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
      (∀ t : ℝ,
        finiteDriftCoordinateBCF K κ h q₀
          (((compactFlow E K κ P h ε).restrict
            (finiteInvariant E K κ P hP h hh ε)) t v) = 0) ∧
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
    exists_recurrent_genericPhysicalPoint_zeroCoordinate
      K κ h
      (compactFlow E K κ P h ε) hinv
      ν hν hzeroFinite q₀ hq₀_nonneg
  simpa only [hinv] using hexists

end AllAffineConditionalGenericZeroOrbit

end CompactAccumulatorPipelineCode

end

end HGAS
