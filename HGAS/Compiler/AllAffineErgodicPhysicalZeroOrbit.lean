import HGAS.Compiler.AllAffineErgodicPhysicalOrbit
import HGAS.Dynamics.FiniteFlowGenericZeroOrbit
import Mathlib.Tactic

/-!
# A generic physical orbit on a pointwise zero drift locus

This strengthens `AllAffineErgodicPhysicalOrbit` when one distinguished
compact drift coordinate is nonnegative.  If every drift mean vanishes,
the selected recurrent, speed-generic point may be chosen so that this
distinguished coordinate vanishes along the whole compact orbit.

For the fixed detector the distinguished coordinate is the residual
sum-of-squares.  Its pointwise vanishing is what licenses the later
modular and Jacobi trajectory classification.
-/

namespace HGAS

open Filter Function MeasureTheory Set Topology
open scoped BoundedContinuousFunction

noncomputable section

namespace CompactAccumulatorPipelineCode

namespace AllAffineErgodicPhysicalZeroOrbit

open AllAffineCompactSourceChart
open AllAffineCompactSourceClock
open AllAffineCompactSourceDrift
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

/-- Select one recurrent orbit which is generic for the speed and every
drift coordinate and lies for all time in the zero locus of a designated
nonnegative drift coordinate. -/
theorem exists_recurrent_genericPhysicalPoint_zeroCoordinate
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
          (stateClockWeight (affineSpeed K)
            (affineCurve ϕ hinv v)) ∧
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
      ∀ i : Fin m,
        Tendsto
          (fun q : ℕ ↦
            Dynamics.integerOrbitAverageObservable
              (ϕ.restrict hinv)
              (finiteDriftCoordinateBCF K κ h i)
              (q + 1) v)
          atTop (𝓝 0) := by
  let c : ℝ :=
    ∫ v, affineSpeedBCF K v
      ∂(ν.measure : Measure (FiniteSourceSpace n m))
  have hc : 0 < c :=
    integral_affineSpeedBCF_pos ν K
  obtain ⟨v, hrec, hq₀orbit, hgeneric⟩ :=
    hν.exists_recurrent_genericPoint_fin_zeroOrbit
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
      hgeneric (finSumFinEquiv (Sum.inl (0 : Fin 1)))
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
      hgeneric (finSumFinEquiv (Sum.inr i))
  let hclock :
      PositiveIntegralClock
        (stateClockWeight (affineSpeed K)
          (affineCurve ϕ hinv v)) :=
    positiveClock_of_genericSpeed K ϕ hinv v hc hspeed
  exact
    ⟨v, c, hclock, hc, hrec, hq₀orbit, hspeed, hdrift⟩

end AllAffineErgodicPhysicalZeroOrbit

end CompactAccumulatorPipelineCode

end

end HGAS
