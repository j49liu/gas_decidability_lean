import Stability.Selection.OrdinaryTimePhysicalClock
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorColumnRecurrence
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorTwoSidedCompleteControllerLocking
import HGAS.Analysis.FiniteCoordinateNormSq

/-!
# Ordinary-time projections of the concrete detector

The source is the literal flattened polynomial field. Its forward return
sequence projects to each clock and linked block. Zero normalized
validity supplies the graph and circle equations; recurrence locks the
controllers for all real time. A Euclidean growth bound controls each
linked block at the same exponent and the same real horizons.

These are the projection steps in Section 8, Theorem `thm:selector`.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Modular HGAS.Clocks Filter MeasureTheory Topology
open HGAS.FixedDetectorReverseTrajectoryCrosswalk
open HGAS.NormalizedCorrectedFixedDetectorColumnRecurrence.SelectedTwoSidedValidityOrbit
open HGAS.NormalizedCorrectedFixedDetectorTwoSidedControllerLocking.SelectedTwoSidedValidityOrbit
open HGAS.NormalizedCorrectedFixedDetectorNormalizationConsequences

variable {eqs vars : ℕ}

/-- The ten compiler residuals impose exactly the eight displayed linked
relations. The unsigned third-coefficient link and coefficient curve
equation are consequences, not extra hypotheses. -/
theorem linkedResiduals_zero_iff_eight_relations (z : LinkedJacobiState ℂ) :
    (∀ r : LinkedJacobiResidualIndex, linkedJacobiResidual r z = 0) ↔
      LinkedJacobiState.jacobiResidual z = 0 ∧
      LinkedJacobiState.link2 z = 0 ∧
      LinkedJacobiState.signedLink3 z = 0 ∧
      LinkedJacobiState.link4 z = 0 ∧
      LinkedJacobiState.linkH z = 0 ∧
      JacobiState.residualR1 z.jacobi = 0 ∧
      JacobiState.residualR2 z.jacobi = 0 ∧
      JacobiState.residualRU z.jacobi = 0 := by
  constructor
  · intro h
    exact ⟨h .unaryJacobi, h .coefficientLinkTwo, h .signedRootLinkThree,
      h .coefficientLinkFour, h .eisensteinLink, h .thetaQuadricOne,
      h .thetaQuadricTwo, h .reciprocalChart⟩
  · rintro ⟨hY, h2, h3, h4, hH, hR1, hR2, hU⟩ r
    have hlink3 : LinkedJacobiState.link3 z = 0 := by
      unfold LinkedJacobiState.link3
      have hs : z.jacobi.p3 = z.unary.Y ^ 2 := sub_eq_zero.mp h3
      rw [hs]
      ring
    cases r with
    | coefficientCurve =>
      simp only [linkedJacobiResidual, LinkedJacobiState.residualR0_eq_links,
        hlink3, h2, h4, hY, sub_self, add_zero]
    | thetaQuadricOne => exact hR1
    | thetaQuadricTwo => exact hR2
    | reciprocalChart => exact hU
    | unaryJacobi => exact hY
    | coefficientLinkTwo => exact h2
    | coefficientLinkThree => exact hlink3
    | coefficientLinkFour => exact h4
    | eisensteinLink => exact hH
    | signedRootLinkThree => exact h3

/-- The actual linked column read from the flattened source. -/
def detectorLinkedColumn
    (x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (j : Fin vars) (t : ℝ) : LinkedJacobiState ℂ :=
  (recoveredState x t).base.base.source.linked j

/-- The actual raw clock coordinates of the source. -/
def detectorClockPoint
    (x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (t : ℝ) : Fin (ControllerPhaseProductPolynomialCode.dimension
      (FixedDetectorPolynomialCode.clockCount eqs vars)) → ℝ :=
  ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint
    (recoveredState x t).base.base.source

/-- Initial controller pairs, with their actual signs retained. -/
def detectorInitialController
    (x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (i : Fin (FixedDetectorPolynomialCode.clockCount eqs vars)) :
    Controller.ControllerState ℝ :=
  ((recoveredState x 0).base.base.source.controllers i).controller

theorem detectorLinkedColumn_forwardRecurrentAt
    {x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ}
    (hrec : ForwardRecurrentAt x 0) (j : Fin vars) :
    ForwardRecurrentAt
      (fun t ↦ LinkedJacobiPolynomialCode.point (detectorLinkedColumn x j t)) 0 := by
  exact hrec.map (continuous_linkedPointProjection j)

theorem detectorClockPoint_forwardRecurrentAt
    {x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ}
    (hrec : ForwardRecurrentAt x 0) :
    ForwardRecurrentAt (detectorClockPoint x) 0 := by
  exact hrec.map continuous_clockProjection

theorem detectorClockPoint_onClockCircles
    (I : DQLSystem eqs vars)
    {x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ}
    (hvalid : ∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
      (recoveredState x t) = 0) (t : ℝ) :
    ControllerPhaseProductSphereFlow.OnClockCircles (detectorClockPoint x t) :=
  onClockCircles_of_validityEnergyValue_eq_zero I _ (hvalid t)

theorem detectorLinkedColumn_residual_zero
    (I : DQLSystem eqs vars)
    {x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ}
    (hvalid : ∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
      (recoveredState x t) = 0) (j : Fin vars) (t : ℝ) (r : LinkedJacobiResidualIndex) :
    linkedJacobiResidual r (detectorLinkedColumn x j t) = 0 := by
  have hgraphs :=
    (NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue_eq_zero_iff
      I (recoveredState x t)).mp (hvalid t)
  exact hgraphs.1.1 j r

/-- Forward recurrence locks each controller; completeness extends the
result to all real times through ODE uniqueness, not reverse recurrence. -/
theorem detector_controller_eq_initial
    (parameters : Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → RationalCode)
    (hp : ∀ i, (1 : ℝ) < (parameters i).decode) (I : DQLSystem eqs vars)
    {x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ}
    (hx : IsIntegralCurve x (fun _ y ↦ PolynomialFieldCode.realize
      (FixedDetectorPolynomialCode.fieldCode parameters I) y))
    (hrec : ForwardRecurrentAt x 0)
    (hvalid : ∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
      (recoveredState x t) = 0) (t : ℝ)
    (i : Fin (FixedDetectorPolynomialCode.clockCount eqs vars)) :
    ((recoveredState x t).base.base.source.controllers i).controller =
      detectorInitialController x i := by
  have hs := isStructuredTrajectory_of_isIntegralCurve parameters I x hx
  have h := CompleteRecurrentNormalizedControllerProduct.controller_state_eq_zero
    parameters hp (detectorClockPoint x) (detectorClockPoint_onClockCircles I hvalid)
    hs.controllers (detectorClockPoint_forwardRecurrentAt hrec) t i
  simpa only [detectorClockPoint, detectorInitialController,
    ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint,
    ControllerPhaseProductPolynomialCode.state_point] using h

/-- The concrete source column has the physical clocks prescribed by its
initial controllers. Their signs are unchanged. -/
theorem detectorLinkedColumn_isScaledTrajectory
    (parameters : Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → RationalCode)
    (hp : ∀ i, (1 : ℝ) < (parameters i).decode) (I : DQLSystem eqs vars)
    {x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ}
    (hx : IsIntegralCurve x (fun _ y ↦ PolynomialFieldCode.realize
      (FixedDetectorPolynomialCode.fieldCode parameters I) y))
    (hrec : ForwardRecurrentAt x 0)
    (hvalid : ∀ t, NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
      (recoveredState x t) = 0) (j : Fin vars) :
    IsScaledLinkedJacobiTrajectory
      (((CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters (detectorInitialController x) j +
        CanonicalFixedDetectorTrajectory.numberFrequency
          parameters I (detectorInitialController x) j) /
        2 : ℝ) : ℂ)
      (Complex.I * (CanonicalFixedDetectorTrajectory.omegaFrequency parameters
        (detectorInitialController x) j : ℂ)) (detectorLinkedColumn x j) := by
  have hlock := detector_controller_eq_initial parameters hp I hx hrec hvalid
  have hω (t : ℝ) :
      ControllerProductLinkedJacobiFamilyPolynomialCode.omega
        (fun a i ↦ (DetectorCharacterCode.omegaWeights (eqs := eqs) a i).decode)
        (fun i ↦ (parameters i).decode) (recoveredState x t).base.base.source j =
      CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters (detectorInitialController x) j := by
    unfold ControllerProductLinkedJacobiFamilyPolynomialCode.omega
      ControllerPhaseProductLinearFrequencyCode.value
      CanonicalFixedDetectorTrajectory.omegaFrequency
    apply Finset.sum_congr rfl
    intro i _
    rw [hlock t i]
  have hN (t : ℝ) :
      ControllerProductLinkedJacobiFamilyPolynomialCode.number
        (fun a i ↦ (DetectorCharacterCode.numberWeights I a i).decode)
        (fun i ↦ (parameters i).decode) (recoveredState x t).base.base.source j =
      CanonicalFixedDetectorTrajectory.numberFrequency
        parameters I (detectorInitialController x) j := by
    unfold ControllerProductLinkedJacobiFamilyPolynomialCode.number
      ControllerPhaseProductLinearFrequencyCode.value
      CanonicalFixedDetectorTrajectory.numberFrequency
    apply Finset.sum_congr rfl
    intro i _
    rw [hlock t i]
  apply linked_isScaledTrajectory parameters I x
    (isStructuredTrajectory_of_isIntegralCurve parameters I x hx) j
  · intro t
    simp only [ControllerProductLinkedJacobiFamilyPolynomialCode.kappaZ, hω t, hN t]
  · intro t
    simp only [ControllerProductLinkedJacobiFamilyPolynomialCode.kappaPhi, hω t]

/-- The coordinate supremum norm is at most the Euclidean norm. -/
theorem detector_norm_le_euclidean
    (x : Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ) :
    ‖x‖ ≤ Real.sqrt (HGAS.normSq x) := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  have hi : (x i) ^ 2 ≤ HGAS.normSq x := by
    simpa only [HGAS.normSq, HGAS.dot, pow_two] using
      Finset.single_le_sum (fun k _ ↦ mul_self_nonneg (x k)) (Finset.mem_univ i)
  rw [Real.norm_eq_abs]
  nlinarith [Real.sq_sqrt (HGAS.normSq_nonneg x), Real.sqrt_nonneg (HGAS.normSq x),
    sq_abs (x i), abs_nonneg (x i)]

/-- Pairing two real coordinates costs at most a factor two, uniformly in
the number of detector blocks. -/
theorem detectorLinkedPoint_norm_le
    (x : Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ) (j : Fin vars) :
    ‖LinkedJacobiPolynomialCode.point
      ((FixedDetectorPolynomialCode.state x).base.base.source.linked j)‖ ≤
        2 * Real.sqrt (HGAS.normSq x) := by
  let e := linkedRealEmbedding (eqs := eqs) j
  have heq := linkedPointProjection_eq j x
  change ‖linkedPointProjection j x‖ ≤ _
  rw [heq]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hr := (norm_le_pi_norm x (e (ComplexCoordinates.realIndex i))).trans
    (detector_norm_le_euclidean x)
  have hi := (norm_le_pi_norm x (e (ComplexCoordinates.imagIndex i))).trans
    (detector_norm_le_euclidean x)
  have hb := Complex.norm_le_abs_re_add_abs_im
    (ComplexCoordinates.complexifyPoint (x ∘ e) i)
  exact hb.trans (by simpa [ComplexCoordinates.complexifyPoint, Real.norm_eq_abs,
    two_mul] using add_le_add hr hi)

/-- The actual Euclidean source growth bound passes to each linked block
at the same real exponent and the same ordinary-time horizons. -/
theorem detectorLinkedColumn_growth
    {x : ℝ → Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ}
    (hx : Continuous x) (j : Fin vars) {μ : ℝ} (hμ : 0 ≤ μ) (B : ℝ)
    (hgrowth : ∀ᶠ H : ℝ in atTop,
      H⁻¹ * (∫ t in (0 : ℝ)..H, (Real.sqrt (HGAS.normSq (x t))) ^ μ) ≤ B) :
    ∀ᶠ H : ℝ in atTop,
      H⁻¹ * (∫ t in (0 : ℝ)..H,
        ‖LinkedJacobiPolynomialCode.point (detectorLinkedColumn x j t)‖ ^ μ) ≤
          2 ^ μ * B := by
  have hpoint : Continuous (fun t ↦
      LinkedJacobiPolynomialCode.point (detectorLinkedColumn x j t)) :=
    (continuous_linkedPointProjection j).comp hx
  have hnormSq : Continuous (fun t ↦ HGAS.normSq (x t)) := by
    unfold HGAS.normSq HGAS.dot
    fun_prop
  have hsource := (Real.continuous_rpow_const hμ).comp hnormSq.sqrt
  have hlinked := (Real.continuous_rpow_const hμ).comp hpoint.norm
  filter_upwards [hgrowth, eventually_gt_atTop (0 : ℝ)] with H hH hpos
  have hbound : (∫ t in (0 : ℝ)..H,
      ‖LinkedJacobiPolynomialCode.point (detectorLinkedColumn x j t)‖ ^ μ) ≤
      (∫ t in (0 : ℝ)..H, (2 : ℝ) ^ μ * (Real.sqrt (HGAS.normSq (x t))) ^ μ) := by
    apply intervalIntegral.integral_mono_on hpos.le (hlinked.intervalIntegrable _ _)
      ((continuous_const.mul hsource).intervalIntegrable _ _)
    intro t _
    have h := Real.rpow_le_rpow (norm_nonneg _) (detectorLinkedPoint_norm_le (x t) j) hμ
    simpa only [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg _)] using h
  rw [intervalIntegral.integral_const_mul] at hbound
  calc
    _ ≤ H⁻¹ * ((2 : ℝ) ^ μ * ∫ t in (0 : ℝ)..H,
        (Real.sqrt (HGAS.normSq (x t))) ^ μ) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hpos.le)
    _ = (2 : ℝ) ^ μ * (H⁻¹ * ∫ t in (0 : ℝ)..H,
        (Real.sqrt (HGAS.normSq (x t))) ^ μ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hH (Real.rpow_nonneg (by norm_num) _)

end Stability.Selection
