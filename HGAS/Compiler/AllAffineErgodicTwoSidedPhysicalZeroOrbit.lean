import HGAS.Compiler.AllAffineCompactSourceTwoSidedClock
import HGAS.Compiler.AllAffineErgodicPhysicalOrbit
import HGAS.Dynamics.FiniteFlowTwoSidedGenericZeroOrbit
import Mathlib.Tactic

/-!
# A two-sided generic physical orbit on a pointwise zero locus

This is the complete-trajectory counterpart of
`AllAffineErgodicPhysicalZeroOrbit`.  The selected compact point is
generic for the speed and all drift coordinates for both the flow and its
reverse.  Its unmodified intrinsic clock is therefore global in both
directions, and the corresponding physical trajectory is a complete
integral curve.
-/

namespace HGAS

open Filter Function MeasureTheory Set Topology
open scoped BoundedContinuousFunction

noncomputable section

namespace CompactAccumulatorPipelineCode

namespace AllAffineErgodicTwoSidedPhysicalZeroOrbit

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

/-- Select one recurrent zero-locus orbit, generic in both directions for
the speed and every drift coordinate, together with its genuine global
physical clock. -/
theorem exists_recurrent_twoSidedGenericPhysicalPoint_zeroCoordinate
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
      ⟨v, hrec, hq₀orbit, hgenericForward,
        hgenericReverse⟩ :=
    hν.exists_recurrent_twoSidedGenericPoint_fin_zeroOrbit
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
    ⟨v, c, hclock, hc, hrec, hq₀orbit, hspeed,
      hspeedReverse, hdrift, hdriftReverse⟩

end AllAffineErgodicTwoSidedPhysicalZeroOrbit

end CompactAccumulatorPipelineCode

end

end HGAS
