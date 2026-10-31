import HGAS.Arithmetic.NormalizedCorrectedCanonicalOrbitClosureModel
import HGAS.Dynamics.PoincareRecurrence

/-!
# Complete recurrent trajectories on the canonical orbit closure

The canonical bounded source orbit has a compact orbit closure whose affine
chart is uniformly separated from the equator. A recurrent point on that
closure therefore gives a complete, bounded, pointwise-valid trajectory of
the literal source field in ordinary time. Only forward recurrence is used.

This supplies the geometric part of Section 8, Corollary `cor:yes`. The
vanishing test averages are a separate analytic assertion.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Analysis HGAS.Clocks Filter Topology
open HGAS.NormalizedCorrectedCanonicalOrbitClosureChart
open HGAS.NormalizedCorrectedCanonicalOrbitClosurePhase
open HGAS.NormalizedCorrectedCanonicalDriftFourierCrosswalk

/-- An increasing global clock transports a forward return sequence without
requiring any recurrence in negative time. -/
theorem forwardRecurrentAt_inverseClock
    {X : Type*} [TopologicalSpace X] {x : ℝ → X} {w : ℝ → ℝ}
    (hrec : ForwardRecurrentAt x 0) (hclock : PositiveIntegralClock w) :
    ForwardRecurrentAt (fun t ↦ x ((hclock.orderIso).symm t)) 0 := by
  obtain ⟨t, ht, hreturn⟩ := hrec
  refine ⟨fun n ↦ hclock.orderIso (t n), hclock.orderIso.tendsto_atTop.comp ht, ?_⟩
  simpa only [OrderIso.symm_apply_apply, PositiveIntegralClock.symm_zero] using hreturn

variable {eqs vars : ℕ}
variable (parameters : Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) → RationalCode)
variable (I : DQLSystem eqs vars)
variable (controller : Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
  Controller.ControllerState ℝ)
variable (hcontroller : ∀ i, Controller.controllerRadiusSq (controller i) = 1)
variable (hlock : ∀ i, Controller.IsControllerEquilibrium
  (RationalCode.decode (parameters i) : ℝ) (controller i))

include parameters I controller hcontroller hlock

/-- Pointwise validity extends to the entire canonical orbit closure by
continuity of the actual validity polynomial. -/
theorem intended_rawState_valid
    (b : (component parameters I controller).Space) :
    NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
      (rawState parameters I controller hcontroller hlock b) = 0 := by
  have hcontinuous : Continuous (fun b ↦
      NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
        (rawState parameters I controller hcontroller hlock b)) := by
    exact (continuous_apply
      (NormalizedCorrectedFixedDetectorDriftCode.validityIndex vars)).comp
        (NormalizedCorrectedCanonicalOrbitClosureModel.continuous_rawDriftValue
          parameters I controller hcontroller hlock)
  have heq := orbitClosureBaseComponent.eq_of_continuous_on_orbit
    (seed parameters I controller) _ (fun _ ↦ (0 : ℝ)) hcontinuous continuous_const
    (fun t ↦ by
      rw [rawState_orbitPoint]
      exact canonicalState_normalizedValidityEnergyValue_eq_zero
        parameters I controller hcontroller _)
  exact congrFun heq b

/-- The explicit Euclidean bound on the canonical trajectory is preserved
on its orbit closure. -/
theorem intended_rawPoint_normSq_le
    (b : (component parameters I controller).Space) :
    normSq (rawPoint parameters I controller hcontroller hlock b) ≤
      CanonicalFixedDetectorRawOrbitBound.canonicalRawNormSqBound eqs vars := by
  induction b using (orbitClosureBaseComponent.denseRange_orbitPoint
    (seed parameters I controller)).induction_on
  · apply isClosed_le _ continuous_const
    have hc := continuous_rawPoint parameters I controller hcontroller hlock
    unfold normSq dot
    fun_prop
  · rename_i t
    rw [rawPoint_orbitPoint]
    exact CanonicalFixedDetectorRawOrbitBound.normSq_canonicalRawPoint_le
      parameters I controller hcontroller _

/-- Every ordinary-time orbit based in the canonical closure has zero
validity residual at every real time. -/
theorem intended_physicalCurve_valid
    (b : (component parameters I controller).Space) (t : ℝ) :
    NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
      (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
        (physicalCurve parameters I controller hcontroller hlock b) t) = 0 := by
  exact intended_rawState_valid parameters I controller hcontroller hlock _

/-- Every ordinary-time orbit based in the canonical closure has the same
uniform Euclidean bound, in both time directions. -/
theorem intended_physicalCurve_normSq_le
    (b : (component parameters I controller).Space) (t : ℝ) :
    normSq (physicalCurve parameters I controller hcontroller hlock b t) ≤
      CanonicalFixedDetectorRawOrbitBound.canonicalRawNormSqBound eqs vars := by
  exact intended_rawPoint_normSq_le parameters I controller hcontroller hlock _

/-- There is a forward recurrent ordinary-time source orbit in the canonical
closure. The invariant probability used to find its initial point is
constructed from that compact closure, not assumed as input. -/
theorem exists_intended_recurrent_physicalCurve :
    ∃ b : (component parameters I controller).Space,
      ForwardRecurrentAt (physicalCurve parameters I controller hcontroller hlock b) 0 := by
  obtain ⟨b, hb⟩ := (orbitClosureBaseComponent.probability
    (seed parameters I controller)).exists_forwardRecurrentAt_zero
  exact ⟨b, forwardRecurrentAt_inverseClock
    (hb.map (continuous_rawPoint parameters I controller hcontroller hlock))
    (physicalClock parameters I controller hcontroller hlock b)⟩

/-- The literal source field has a complete, bounded, valid, forward
recurrent trajectory. This statement alone makes no claim about its test
averages or the arithmetic instance. -/
theorem exists_intended_complete_bounded_valid_recurrent_trajectory :
    ∃ x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ,
      IsIntegralCurve x (fun _ y ↦ PolynomialFieldCode.realize
        (FixedDetectorPolynomialCode.fieldCode parameters I) y) ∧
      ForwardRecurrentAt x 0 ∧
      (∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
        (FixedDetectorReverseTrajectoryCrosswalk.recoveredState x t) = 0) ∧
      ∀ t, normSq (x t) ≤
        CanonicalFixedDetectorRawOrbitBound.canonicalRawNormSqBound eqs vars := by
  obtain ⟨b, hb⟩ := exists_intended_recurrent_physicalCurve
    parameters I controller hcontroller hlock
  exact ⟨physicalCurve parameters I controller hcontroller hlock b,
    physicalCurve_isIntegralCurve parameters I controller hcontroller hlock b, hb,
    intended_physicalCurve_valid parameters I controller hcontroller hlock b,
    intended_physicalCurve_normSq_le parameters I controller hcontroller hlock b⟩

end Stability.Selection
