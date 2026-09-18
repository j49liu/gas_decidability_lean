import HGAS.Clocks.ControllerPhaseProductSphereFlow
import HGAS.Modular.TwoControllerLinkedJacobiMixedCompactSourceCode
import Mathlib.Tactic

/-!
# Clock projection of the faithful mixed linked-Jacobi compactification

The preferred mixed source keeps the first eight coordinates as four
literal unit circles and compactifies only the twenty-eight linked
coordinates.  This file turns that geometric statement into an exact
continuous map from the compact mixed base to the canonical two-clock
product sphere.

The proof does not assume the circle equations separately.  It derives
them from membership in the mixed source product of spheres, identifies
the four compact blocks with the two controller/phase pairs, and proves
that the underlying eight-coordinate map is exactly the first controller
block of the uncompactified source.
-/

noncomputable section

namespace HGAS.Modular.TwoControllerLinkedJacobiMixedClockProjection

open HGAS

/-- Compact mixed-central base before adjoining the accumulator sphere. -/
abbrev BaseSpace :=
  CompactAccumulatorPipelineCode.BaseSpace
    TwoControllerLinkedJacobiMixedCompactSourceCode.layout

/-- Recover the thirty-six old source coordinates from a compact base
point. -/
def oldPoint (y : BaseSpace) :
    Fin TwoControllerLinkedJacobiMixedCompactSourceCode.sourceDimension → ℝ :=
  fun j ↦
    y.1 (MixedCentralPolynomialCode.xIndex
      (k :=
        TwoControllerLinkedJacobiMixedCompactSourceCode.affineBlockCount) j)

/-- The literal first eight (controller--phase) source coordinates,
regrouped with the canonical finite-product convention. -/
def clockRawPoint
    (y : BaseSpace) :
    Fin
      (HGAS.Clocks.ControllerPhaseProductPolynomialCode.dimension 2) → ℝ :=
  fun i ↦
    oldPoint y
      (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding i)

theorem productBlockEmbedding_zero
    (i : Fin HGAS.Clocks.ControllerPolynomialCode.dimension) :
    HGAS.Clocks.ControllerPhaseProductPolynomialCode.blockEmbedding
        (0 : Fin 2) i =
      TwoControllerLinkedJacobiPolynomialCode.omegaControllerEmbedding i := by
  apply Fin.ext
  fin_cases i <;> rfl

theorem productBlockEmbedding_one
    (i : Fin HGAS.Clocks.ControllerPolynomialCode.dimension) :
    HGAS.Clocks.ControllerPhaseProductPolynomialCode.blockEmbedding
        (1 : Fin 2) i =
      TwoControllerLinkedJacobiPolynomialCode.numberControllerEmbedding i := by
  apply Fin.ext
  fin_cases i <;> rfl

/-- The product-sphere property of the mixed base supplies all four
already-compact circle equations. -/
theorem compactBlockNormSq_eq_one
    (y : BaseSpace) :
    ∀ c,
      MixedCentralPolynomialCode.compactBlockNormSq
        TwoControllerLinkedJacobiMixedCompactSourceCode.layout
        (oldPoint y) c = 1 := by
  let w :
      Fin
        TwoControllerLinkedJacobiMixedCompactSourceCode.affineBlockCount →
          ℝ :=
    fun b ↦
      y.1 (MixedCentralPolynomialCode.wIndex
        (n :=
          TwoControllerLinkedJacobiMixedCompactSourceCode.sourceDimension)
        b)
  have hy :
      MixedCentralPolynomialCode.chartPoint (oldPoint y) w =
        y.1 :=
    MixedCentralPolynomialCode.chartPoint_decompose y.1
  have hspheres := y.2
  rw [← hy] at hspheres
  exact
    (MixedCentralPolynomialCode.onSourceProductSpheres_targetBlock_iff
      TwoControllerLinkedJacobiMixedCompactSourceCode.layout
      (oldPoint y) w).mp hspheres |>.2

theorem compactBlockDot_self
    (x :
      Fin
        TwoControllerLinkedJacobiMixedCompactSourceCode.sourceDimension →
          ℝ)
    (c :
      Fin
        TwoControllerLinkedJacobiMixedCompactSourceCode.compactBlockCount) :
    MixedCentralPolynomialCode.compactBlockDot
        TwoControllerLinkedJacobiMixedCompactSourceCode.layout x x c =
      MixedCentralPolynomialCode.compactBlockNormSq
        TwoControllerLinkedJacobiMixedCompactSourceCode.layout x c := by
  simp [MixedCentralPolynomialCode.compactBlockDot,
    MixedCentralPolynomialCode.compactBlockNormSq, pow_two]

theorem omegaController_radiusSq
    (y : BaseSpace) :
    HGAS.Clocks.Controller.controllerRadiusSq
        (HGAS.Clocks.ControllerPhaseProductPolynomialCode.state
          (clockRawPoint y) 0).controller = 1 := by
  have h :=
    compactBlockNormSq_eq_one y
      (finSumFinEquiv
        (Sum.inl
          (0 :
            Fin
              TwoControllerLinkedJacobiMixedCompactSourceCode.localCircleCount) :
          Fin
              TwoControllerLinkedJacobiMixedCompactSourceCode.localCircleCount ⊕
            Fin
              TwoControllerLinkedJacobiMixedCompactSourceCode.localCircleCount))
  rw [← compactBlockDot_self] at h
  rw [
    TwoControllerLinkedJacobiMixedCompactSourceCode.compactBlockDot_omega,
    TwoControllerLinkedJacobiMixedCompactSourceCode.localCircleDot_controller]
    at h
  simpa [HGAS.Clocks.Controller.controllerRadiusSq,
    HGAS.Clocks.ControllerPhaseProductPolynomialCode.state,
    HGAS.Clocks.ControllerPolynomialCode.state,
    PolynomialFiniteProductCode.unflattenPoint,
    clockRawPoint, productBlockEmbedding_zero, pow_two] using h

theorem omegaPhase_radiusSq
    (y : BaseSpace) :
    HGAS.Clocks.Controller.phaseRadiusSq
        (HGAS.Clocks.ControllerPhaseProductPolynomialCode.state
          (clockRawPoint y) 0).phase = 1 := by
  have h :=
    compactBlockNormSq_eq_one y
      (finSumFinEquiv
        (Sum.inl
          (1 :
            Fin
              TwoControllerLinkedJacobiMixedCompactSourceCode.localCircleCount) :
          Fin
              TwoControllerLinkedJacobiMixedCompactSourceCode.localCircleCount ⊕
            Fin
              TwoControllerLinkedJacobiMixedCompactSourceCode.localCircleCount))
  rw [← compactBlockDot_self] at h
  rw [
    TwoControllerLinkedJacobiMixedCompactSourceCode.compactBlockDot_omega,
    TwoControllerLinkedJacobiMixedCompactSourceCode.localCircleDot_phase]
    at h
  simpa [HGAS.Clocks.Controller.phaseRadiusSq,
    HGAS.Clocks.ControllerPhaseProductPolynomialCode.state,
    HGAS.Clocks.ControllerPolynomialCode.state,
    PolynomialFiniteProductCode.unflattenPoint,
    clockRawPoint, productBlockEmbedding_zero, pow_two] using h

theorem numberController_radiusSq
    (y : BaseSpace) :
    HGAS.Clocks.Controller.controllerRadiusSq
        (HGAS.Clocks.ControllerPhaseProductPolynomialCode.state
          (clockRawPoint y) 1).controller = 1 := by
  have h :=
    compactBlockNormSq_eq_one y
      (finSumFinEquiv
        (Sum.inr
          (0 :
            Fin
              TwoControllerLinkedJacobiMixedCompactSourceCode.localCircleCount) :
          Fin
              TwoControllerLinkedJacobiMixedCompactSourceCode.localCircleCount ⊕
            Fin
              TwoControllerLinkedJacobiMixedCompactSourceCode.localCircleCount))
  rw [← compactBlockDot_self] at h
  rw [
    TwoControllerLinkedJacobiMixedCompactSourceCode.compactBlockDot_number,
    TwoControllerLinkedJacobiMixedCompactSourceCode.localCircleDot_controller]
    at h
  simpa [HGAS.Clocks.Controller.controllerRadiusSq,
    HGAS.Clocks.ControllerPhaseProductPolynomialCode.state,
    HGAS.Clocks.ControllerPolynomialCode.state,
    PolynomialFiniteProductCode.unflattenPoint,
    clockRawPoint, productBlockEmbedding_one, pow_two] using h

theorem numberPhase_radiusSq
    (y : BaseSpace) :
    HGAS.Clocks.Controller.phaseRadiusSq
        (HGAS.Clocks.ControllerPhaseProductPolynomialCode.state
          (clockRawPoint y) 1).phase = 1 := by
  have h :=
    compactBlockNormSq_eq_one y
      (finSumFinEquiv
        (Sum.inr
          (1 :
            Fin
              TwoControllerLinkedJacobiMixedCompactSourceCode.localCircleCount) :
          Fin
              TwoControllerLinkedJacobiMixedCompactSourceCode.localCircleCount ⊕
            Fin
              TwoControllerLinkedJacobiMixedCompactSourceCode.localCircleCount))
  rw [← compactBlockDot_self] at h
  rw [
    TwoControllerLinkedJacobiMixedCompactSourceCode.compactBlockDot_number,
    TwoControllerLinkedJacobiMixedCompactSourceCode.localCircleDot_phase]
    at h
  simpa [HGAS.Clocks.Controller.phaseRadiusSq,
    HGAS.Clocks.ControllerPhaseProductPolynomialCode.state,
    HGAS.Clocks.ControllerPolynomialCode.state,
    PolynomialFiniteProductCode.unflattenPoint,
    clockRawPoint, productBlockEmbedding_one, pow_two] using h

theorem onClockCircles_clockRawPoint
    (y : BaseSpace) :
    HGAS.Clocks.ControllerPhaseProductSphereFlow.OnClockCircles
      (clockRawPoint y) := by
  intro a
  fin_cases a
  · exact ⟨omegaController_radiusSq y,
      omegaPhase_radiusSq y⟩
  · exact ⟨numberController_radiusSq y,
      numberPhase_radiusSq y⟩

/-- Continuous observation of the two literal clock blocks. -/
def clockProjection
    (y : BaseSpace) :
    HGAS.Clocks.ControllerPhaseProductSphereFlow.ClockProductSphere 2 :=
  ⟨clockRawPoint y, onClockCircles_clockRawPoint y⟩

@[simp]
theorem clockProjection_val
    (y : BaseSpace) :
    (clockProjection y).1 = clockRawPoint y :=
  rfl

theorem continuous_clockRawPoint :
    Continuous clockRawPoint := by
  apply continuous_pi
  intro i
  exact
    (continuous_apply
      (MixedCentralPolynomialCode.xIndex
        (k :=
          TwoControllerLinkedJacobiMixedCompactSourceCode.affineBlockCount)
        (TwoControllerLinkedJacobiPolynomialCode.controllersEmbedding i))).comp
      continuous_subtype_val

theorem continuous_clockProjection :
    Continuous clockProjection :=
  continuous_clockRawPoint.subtype_mk _

end HGAS.Modular.TwoControllerLinkedJacobiMixedClockProjection
