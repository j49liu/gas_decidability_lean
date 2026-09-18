import HGAS.Arithmetic.NormalizedCorrectedCanonicalFixedDetectorCentralChart
import HGAS.Compiler.AllAffinePositiveCentralTrajectory
import Mathlib.Tactic

/-!
# The canonical detector orbit is the canonical compact-base orbit

The explicit detector formulas are written in ordinary affine time,
whereas the denominator-cleared compact polynomial field runs in the
slower projective time.  This file applies the reusable all-affine forward
trajectory theorem and makes that change of clock explicit.

Let `z(t)` be the fully aligned canonical detector trajectory and let

```text
                 a(z) = (1 + ‖z‖²)⁻ᴷ,
          R(t) = ∫₀ᵗ a(z(s))⁻¹ ds.
```

Here `K` is the normalized source degree bound.  Since `a ≤ 1`, the
reciprocal clock speed is at least one, so `R` is a global order
isomorphism of the real line.  If `B=R⁻¹`, then the positive central lift
of `z(B(τ))` solves the literal compact base field.  ODE uniqueness
therefore identifies it with the compiler's named `baseFlow`.
-/

namespace HGAS.NormalizedCorrectedCanonicalCompactTrajectory

open HGAS
open HGAS.Clocks
open HGAS.CompactAccumulatorPipelineCode
open
  HGAS.CompactAccumulatorPipelineCode.AllAffinePositiveCentralTrajectory

noncomputable section

variable {eqs vars : ℕ}

/-- The fully aligned canonical affine detector curve. -/
abbrev canonicalAffineCurve
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ) :
    ℝ →
      (Fin
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
          eqs vars) → ℝ) :=
  NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalAffinePoint
    parameters I controller

/-- The canonical affine curve solves the literal uncompactified detector
polynomial ODE. -/
theorem canonicalAffineCurve_isIntegralCurve
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i)) :
    IsIntegralCurve
      (canonicalAffineCurve parameters I controller)
      (fun _ z ↦
        PolynomialFieldCode.realize
          (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
            parameters I) z) := by
  simpa only [
    canonicalAffineCurve,
    NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalAffinePoint,
    CanonicalFixedDetectorRawOrbitBound.canonicalRawState,
    NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode] using
    (CanonicalFixedDetectorChart.canonicalFixedDetectorPath_point_isIntegralCurve
      parameters I controller
      LockedControllerPhaseTrajectory.onePhase
      (1 : Circle) hlock)

/-- The automatic global reciprocal clock for the canonical detector. -/
abbrev canonicalReciprocalClock
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i)) :=
  reciprocalAffineClock
    (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)
    (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
      parameters I)
    (canonicalAffineCurve_isIntegralCurve
      parameters I controller hlock)

/-- Physical affine time as a function of compact projective time. -/
def physicalTime
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (τ : ℝ) : ℝ :=
  (PositiveIntegralClock.orderIso
    (canonicalReciprocalClock parameters I controller hlock)).symm τ

@[simp]
theorem physicalTime_zero
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i)) :
    physicalTime parameters I controller hlock 0 = 0 := by
  exact PositiveIntegralClock.symm_zero _

/-- The explicit positive central lift in compact projective time. -/
def canonicalCompactCurve
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (τ : ℝ) :
    BaseSpace
      (NormalizedCorrectedFixedDetectorCompactSourceCode.layout
        (eqs := eqs) (vars := vars)) :=
  positiveBasePoint
    (canonicalAffineCurve parameters I controller
      (physicalTime parameters I controller hlock τ))

/-- The generic positive base point is definitionally the same central
chart point used by the canonical detector bound. -/
theorem positiveBasePoint_eq_canonicalCompactBasePoint
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) :
    positiveBasePoint
        (canonicalAffineCurve parameters I controller t) =
      NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalCompactBasePoint
        parameters I controller t := by
  apply Subtype.ext
  funext q
  obtain ⟨j | b, rfl⟩ := finSumFinEquiv.surjective q
  · simp only [positiveBasePoint_finSum_inl]
    simp [NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalCompactBasePoint,
      NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalCentralChartPoint,
      MixedCentralPolynomialCode.chartPoint,
      MultiCentralPolynomialCode.chartPoint]
  · have hb : b = 0 := Subsingleton.elim _ _
    subst b
    simp only [positiveBasePoint_finSum_inr]
    simp [NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalCompactBasePoint,
      NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalCentralChartPoint,
      MixedCentralPolynomialCode.chartPoint,
      MultiCentralPolynomialCode.chartPoint]

/-- The explicit compact curve is the positive central chart point above
the canonical affine state at the inverse-clock physical time. -/
theorem canonicalCompactCurve_eq_canonicalCompactBasePoint
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (τ : ℝ) :
    canonicalCompactCurve parameters I controller hlock τ =
      NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalCompactBasePoint
        parameters I controller
        (physicalTime parameters I controller hlock τ) := by
  exact
    positiveBasePoint_eq_canonicalCompactBasePoint
      parameters I controller _

/-- The explicit compact lift solves the literal normalized base field. -/
theorem canonicalCompactCurve_isIntegralCurve
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i)) :
    IsIntegralCurve
      (fun τ ↦
        (canonicalCompactCurve parameters I controller hlock τ).1)
      (fun _ y ↦
        PolynomialFieldCode.realize
          (CompactAccumulatorPipelineCode.baseFieldCode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.layout
              (eqs := eqs) (vars := vars))
            (NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent
              I)
            (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
              parameters I)) y) := by
  simpa only [
    canonicalCompactCurve,
    physicalTime,
    canonicalAffineCurve,
    NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent] using
    (positiveBaseCurve_isIntegralCurve
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
        parameters I)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode_termsAffineBlockDegreeLE
        parameters I)
      (canonicalAffineCurve_isIntegralCurve
        parameters I controller hlock))

/-- **Canonical orbit identity.**  The explicitly compactified detector
trajectory is exactly the compiler's named compact base flow through its
positive seed. -/
theorem canonicalCompactCurve_eq_baseFlow
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hlock :
      ∀ i,
        Controller.IsControllerEquilibrium
          (RationalCode.decode (parameters i) : ℝ)
          (controller i))
    (τ : ℝ) :
    canonicalCompactCurve parameters I controller hlock τ =
      baseFlow
        (NormalizedCorrectedFixedDetectorCompactSourceCode.layout
          (eqs := eqs) (vars := vars))
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent I)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
          parameters I)
        τ
        (NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalCompactBasePoint
          parameters I controller 0) := by
  have h :=
    positiveBaseCurve_eq_baseFlow
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
        parameters I)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode_termsAffineBlockDegreeLE
        parameters I)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode_termsDegreeLE
        parameters I)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.baseCompactTangency
        parameters I)
      (canonicalAffineCurve_isIntegralCurve
        parameters I controller hlock)
      τ
  rw [← positiveBasePoint_eq_canonicalCompactBasePoint
    parameters I controller 0]
  simpa only [
    canonicalCompactCurve,
    physicalTime,
    canonicalAffineCurve,
    NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent]
    using h

end

end HGAS.NormalizedCorrectedCanonicalCompactTrajectory
