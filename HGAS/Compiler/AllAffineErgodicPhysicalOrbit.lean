import HGAS.Compiler.AllAffineCompactSourceDrift
import HGAS.Dynamics.FiniteFlowGenericPoint
import Mathlib.Tactic

/-!
# One recurrent generic physical orbit in the finite affine chart

This module performs the finite-intersection step needed by the selector.
For an ergodic invariant probability on the restricted finite-chart flow,
it chooses one point which is simultaneously:

* recurrent;
* generic for the positive compactification speed; and
* generic for every coordinate of the compact accumulator drift.

The speed has strictly positive invariant mean because it is an everywhere
positive bounded continuous function on a probability space.  Therefore
the chosen orbit has a global physical clock.
-/

namespace HGAS

open Filter Function MeasureTheory Set Topology
open scoped BoundedContinuousFunction

noncomputable section

namespace CompactAccumulatorPipelineCode

namespace AllAffineErgodicPhysicalOrbit

open AllAffineCompactSourceChart
open AllAffineCompactSourceClock
open AllAffineCompactSourceDrift

variable {n m : ℕ}

/-- One speed observable followed by all compact drift coordinates. -/
def speedAndDriftBCF
    (K : ℕ) (κ : RationalCode)
    (h : Fin m → PolynomialCode n) :
    Fin (1 + m) → FiniteSourceSpace n m →ᵇ ℝ :=
  fun q ↦
    match finSumFinEquiv.symm q with
    | Sum.inl _ => affineSpeedBCF K
    | Sum.inr i => finiteDriftCoordinateBCF K κ h i

@[simp]
theorem speedAndDriftBCF_speed
    (K : ℕ) (κ : RationalCode)
    (h : Fin m → PolynomialCode n) :
    speedAndDriftBCF K κ h
        (finSumFinEquiv (Sum.inl (0 : Fin 1))) =
      affineSpeedBCF K := by
  simp [speedAndDriftBCF]

@[simp]
theorem speedAndDriftBCF_drift
    (K : ℕ) (κ : RationalCode)
    (h : Fin m → PolynomialCode n) (i : Fin m) :
    speedAndDriftBCF K κ h
        (finSumFinEquiv (Sum.inr i)) =
      finiteDriftCoordinateBCF K κ h i := by
  simp [speedAndDriftBCF]

/-- The invariant mean of the intrinsic speed is strictly positive. -/
theorem integral_affineSpeedBCF_pos
    {ϕ : Flow ℝ (FiniteSourceSpace n m)}
    (ν : Dynamics.InvariantProbabilityMeasure ϕ)
    (K : ℕ) :
    0 <
      ∫ v, affineSpeedBCF K v
        ∂(ν.measure : Measure (FiniteSourceSpace n m)) := by
  have hnonneg :
      0 ≤ (affineSpeedBCF K :
        FiniteSourceSpace n m → ℝ) :=
    fun v ↦ affineSpeed_nonneg K (affinePoint v)
  have hint :
      Integrable (affineSpeedBCF K)
        (ν.measure : Measure (FiniteSourceSpace n m)) :=
    ν.integrable_boundedContinuous (affineSpeedBCF K)
  rw [integral_pos_iff_support_of_nonneg hnonneg hint]
  have hsupport :
      Function.support
          (affineSpeedBCF K :
            FiniteSourceSpace n m → ℝ) =
        Set.univ := by
    ext v
    simp only [Function.mem_support, Set.mem_univ,
      iff_true]
    exact ne_of_gt (affineSpeed_pos K (affinePoint v))
  rw [hsupport]
  simp

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

/-- Simultaneously choose a recurrent speed-generic and zero-drift-generic
point.  The clock included in the conclusion is the global physical clock
of that same point; no observable-dependent subsequences occur. -/
theorem exists_recurrent_genericPhysicalPoint
    (ν :
      Dynamics.InvariantProbabilityMeasure
        (ϕ.restrict hinv))
    (hν :
      Dynamics.IsErgodicInvariantProbability
        (ϕ.restrict hinv) ν.measure)
    (hzero :
      ∀ i : Fin m,
        (∫ v, finiteDriftCoordinateBCF K κ h i v
          ∂(ν.measure : Measure (FiniteSourceSpace n m))) = 0) :
    ∃ (v : FiniteSourceSpace n m) (c : ℝ),
      PositiveIntegralClock
          (stateClockWeight (affineSpeed K)
            (affineCurve ϕ hinv v)) ∧
      0 < c ∧
      ForwardRecurrentAt
        (fun t : ℝ ↦ (ϕ.restrict hinv) t v) 0 ∧
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
  obtain ⟨v, hrec, hgeneric⟩ :=
    hν.exists_recurrent_genericPoint_fin ν
      (speedAndDriftBCF K κ h)
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
  exact ⟨v, c, hclock, hc, hrec, hspeed, hdrift⟩

end AllAffineErgodicPhysicalOrbit

end CompactAccumulatorPipelineCode

end

end HGAS
