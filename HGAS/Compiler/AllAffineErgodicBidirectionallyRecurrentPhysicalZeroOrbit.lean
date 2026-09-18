import HGAS.Compiler.AllAffineErgodicTwoSidedPhysicalZeroOrbit
import HGAS.Dynamics.FiniteFlowBidirectionallyRecurrentGenericZeroOrbit
import Mathlib.Tactic

/-!
# A physical selector recurrent in both compact-time directions

This module strengthens the two-sided generic physical selector by
retaining Poincare recurrence for the reversed compact flow.  Forward
and reverse recurrence are genuinely separate full-measure conditions.
Their conjunction is what later permits either sign of a private
frequency to be normalized to the standard modular speed.
-/

namespace HGAS

open Filter Function MeasureTheory Set Topology
open scoped BoundedContinuousFunction

noncomputable section

namespace CompactAccumulatorPipelineCode

namespace AllAffineErgodicBidirectionallyRecurrentPhysicalZeroOrbit

open AllAffineCompactSourceChart
open AllAffineCompactSourceClock
open AllAffineCompactSourceDrift
open AllAffineCompactSourceTwoSidedClock
open AllAffineErgodicPhysicalOrbit

variable {n m : ℕ}

variable
  (K : ℕ) (κ : RationalCode)
  (P : PolynomialFieldCode n)
  (h : Fin m → PolynomialCode n)
  (hP :
    ∀ j,
      MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
        (layout n) (2 * K) (P j))
  (ϕ : Flow ℝ (SourceSpace n m))
  (hcurve :
    ∀ v,
      IsIntegralCurve
        (fun t ↦ (ϕ t v).1)
        (fun _ x ↦
          PolynomialFieldCode.realize
            (fieldCode (layout n) (2 * K) κ P h) x))
  (hinv :
    IsInvariant ϕ (sourceFiniteInteriorSet (m := m) (layout n)))

/-- Select a zero-locus physical orbit whose compact representative is
recurrent for both the original and reversed compact flows. -/
theorem exists_birecurrent_twoSidedGenericPhysicalPoint_zeroCoordinate
    (ν :
      Dynamics.InvariantProbabilityMeasure
        (ϕ.restrict hinv))
    (hν :
      Dynamics.IsErgodicInvariantProbability
        (ϕ.restrict hinv) ν.measure)
    (hzero :
      ∀ i : Fin m,
        (∫ v, finiteDriftCoordinateBCF K κ h i v
          ∂(ν.measure : Measure (FiniteSourceSpace n m))) = 0)
    (q₀ : Fin m)
    (hq₀_nonneg :
      ∀ v : FiniteSourceSpace n m,
        0 ≤ finiteDriftCoordinateBCF K κ h q₀ v) :
    ∃ (v : FiniteSourceSpace n m) (c : ℝ),
      PositiveIntegralClock
          (twoSidedClockWeight K (affineCurve ϕ hinv v)) ∧
      0 < c ∧
      ForwardRecurrentAt
        (fun t : ℝ ↦ (ϕ.restrict hinv) t v) 0 ∧
      ForwardRecurrentAt
        (fun t : ℝ ↦ (ϕ.restrict hinv).reverse t v) 0 ∧
      (∀ t : ℝ,
        finiteDriftCoordinateBCF K κ h q₀
          ((ϕ.restrict hinv) t v) = 0) ∧
      Tendsto
        (fun q : ℕ ↦
          Dynamics.integerOrbitAverageObservable
            (ϕ.restrict hinv) (affineSpeedBCF K) (q + 1) v)
        atTop (𝓝 c) ∧
      Tendsto
        (fun q : ℕ ↦
          Dynamics.integerOrbitAverageObservable
            (ϕ.restrict hinv).reverse
            (affineSpeedBCF K) (q + 1) v)
        atTop (𝓝 c) ∧
      (∀ i : Fin m,
        Tendsto
          (fun q : ℕ ↦
            Dynamics.integerOrbitAverageObservable
              (ϕ.restrict hinv)
              (finiteDriftCoordinateBCF K κ h i)
              (q + 1) v)
          atTop (𝓝 0)) ∧
      ∀ i : Fin m,
        Tendsto
          (fun q : ℕ ↦
            Dynamics.integerOrbitAverageObservable
              (ϕ.restrict hinv).reverse
              (finiteDriftCoordinateBCF K κ h i)
              (q + 1) v)
          atTop (𝓝 0) := by
  let c : ℝ :=
    ∫ v, affineSpeedBCF K v
      ∂(ν.measure : Measure (FiniteSourceSpace n m))
  have hc : 0 < c :=
    integral_affineSpeedBCF_pos ν K
  obtain
      ⟨v, hrec, hrecReverse, hq₀orbit, hgenericForward,
        hgenericReverse⟩ :=
    hν.exists_birecurrent_twoSidedGenericPoint_fin_zeroOrbit
      ν (speedAndDriftBCF K κ h)
      (finiteDriftCoordinateBCF K κ h q₀)
      hq₀_nonneg (hzero q₀)
  have hspeed :
      Tendsto
        (fun q : ℕ ↦
          Dynamics.integerOrbitAverageObservable
            (ϕ.restrict hinv) (affineSpeedBCF K) (q + 1) v)
        atTop (𝓝 c) := by
    simpa only [speedAndDriftBCF_speed, c] using
      hgenericForward (finSumFinEquiv (Sum.inl (0 : Fin 1)))
  have hspeedReverse :
      Tendsto
        (fun q : ℕ ↦
          Dynamics.integerOrbitAverageObservable
            (ϕ.restrict hinv).reverse
            (affineSpeedBCF K) (q + 1) v)
        atTop (𝓝 c) := by
    simpa only [speedAndDriftBCF_speed, c] using
      hgenericReverse (finSumFinEquiv (Sum.inl (0 : Fin 1)))
  have hdrift :
      ∀ i : Fin m,
        Tendsto
          (fun q : ℕ ↦
            Dynamics.integerOrbitAverageObservable
              (ϕ.restrict hinv)
              (finiteDriftCoordinateBCF K κ h i)
              (q + 1) v)
          atTop (𝓝 0) := by
    intro i
    simpa only [speedAndDriftBCF_drift, hzero i] using
      hgenericForward (finSumFinEquiv (Sum.inr i))
  have hdriftReverse :
      ∀ i : Fin m,
        Tendsto
          (fun q : ℕ ↦
            Dynamics.integerOrbitAverageObservable
              (ϕ.restrict hinv).reverse
              (finiteDriftCoordinateBCF K κ h i)
              (q + 1) v)
          atTop (𝓝 0) := by
    intro i
    simpa only [speedAndDriftBCF_drift, hzero i] using
      hgenericReverse (finSumFinEquiv (Sum.inr i))
  let hclock :
      PositiveIntegralClock
        (twoSidedClockWeight K (affineCurve ϕ hinv v)) :=
    positiveClock_of_twoSidedGenericSpeed
      K ϕ hinv v hc hspeed hspeedReverse
  exact
    ⟨v, c, hclock, hc, hrec, hrecReverse, hq₀orbit,
      hspeed, hspeedReverse, hdrift, hdriftReverse⟩

end AllAffineErgodicBidirectionallyRecurrentPhysicalZeroOrbit

end CompactAccumulatorPipelineCode

end

end HGAS
