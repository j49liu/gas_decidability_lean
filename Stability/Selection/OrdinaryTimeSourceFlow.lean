import Stability.Selection.OrdinaryTimeSourceGraph
import HGAS.Arithmetic.CanonicalFixedDetectorFundamentalPhase
import HGAS.Arithmetic.FixedDetectorPrivateFrequency
import HGAS.Clocks.ControllerPhaseProductTorusObservation

/-!
# Physical translation of the literal source graph

The fundamental phase frequencies are angular velocities divided by `2π`.
The graph identity uses the actual canonical source trajectory at every
initial phase, including its gauge and both reciprocal signs.
-/

noncomputable section

open scoped BigOperators

namespace Stability.Selection

open HGAS HGAS.Analysis HGAS.Modular HGAS.Clocks
open CanonicalFixedDetectorTrajectory CanonicalFixedDetectorFundamentalPhase

variable {eqs vars : ℕ}

theorem sourcePhaseGraph_eq_circle (x : UnitAddTorus (Fin (vars + eqs)))
    (i : Fin (vars + eqs)) :
    sourcePhaseGraph x i = PhaseClockFlow.circlePhaseState (AddCircle.toCircle (x i)) := by
  simp only [sourcePhaseGraph, UnitAddTorus.mFourier_single, fourier_one,
    PhaseClockFlow.circlePhaseState]

theorem sourcePhaseGraph_radiusSq (x : UnitAddTorus (Fin (vars + eqs)))
    (i : Fin (vars + eqs)) : Controller.phaseRadiusSq (sourcePhaseGraph x i) = 1 := by
  rw [sourcePhaseGraph_eq_circle]
  have h := Circle.norm_coe (AddCircle.toCircle (x i))
  have hs := congrArg (fun r : ℝ ↦ r ^ 2) h
  dsimp only at hs
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hs
  simpa only [PhaseClockFlow.circlePhaseState, Controller.phaseRadiusSq, pow_two, one_mul]
    using hs

/-- Compiled signed powers are exactly the Fourier characters on the
literal phase graph. -/
theorem characterValue_sourcePhaseGraph
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (x : UnitAddTorus (Fin (vars + eqs))) (a : Fin (vars + eqs) → ℤ) :
    ControllerPhaseProductCharacterCode.characterValue a
      (fun i ↦ { controller := controller i, phase := sourcePhaseGraph x i }) =
        UnitAddTorus.mFourier a x := by
  let z := fun y : UnitAddTorus (Fin (vars + eqs)) ↦
    fun i ↦ ControllerPhaseState.mk (controller i) (sourcePhaseGraph y i)
  have hp : ∀ y i, Controller.phaseRadiusSq (z y i).phase = 1 := sourcePhaseGraph_radiusSq
  have he : ControllerPhaseProductTorusObservation.phase z hp x = x := by
    funext i
    apply PhaseClockFlow.unitAddCircleHomeomorph.injective
    rw [ControllerPhaseProductTorusObservation.phase,
      PhaseClockFlow.unitAddCircleHomeomorph.apply_symm_apply,
      PhaseClockFlow.unitAddCircleHomeomorph_apply]
    apply Subtype.ext
    rw [ControllerPhaseProductTorusObservation.phaseCircle_coe]
    change Complex.mk (sourcePhaseGraph x i).c (sourcePhaseGraph x i).d = _
    rw [sourcePhaseGraph_eq_circle]
    rfl
  simpa only [he] using
    (ControllerPhaseProductTorusObservation.mFourier_phase z hp x a).symm

theorem sourcePhaseGraph_flow
    (parameters : Fin (vars + eqs) → RationalCode)
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (x : UnitAddTorus (Fin (vars + eqs))) (t : ℝ) (i : Fin (vars + eqs)) :
    sourcePhaseGraph (RadicalClock.torusTranslationFlow
      (turnsFrequency parameters controller) t x) i =
      LockedControllerPhaseTrajectory.phasePath
        (LockedControllerPhaseTrajectory.angularVelocity parameters controller i)
        (AddCircle.toCircle (x i)) t := by
  rw [sourcePhaseGraph_eq_circle]
  have h := PhaseClockFlow.unitAddCircleHomeomorph_semiconj
    (LockedControllerPhaseTrajectory.angularVelocity parameters controller i) t (x i)
  simpa only [PhaseClockFlow.unitAddCircleHomeomorph_apply,
    PhaseClockFlow.turnTranslationFlow_apply, PhaseClockFlow.radiansToTurnsFrequency,
    RadicalClock.torusTranslationFlow_apply, Pi.add_apply, RadicalClock.torusDisplacement,
    turnsFrequency, LockedControllerPhaseTrajectory.phasePath] using
    congrArg PhaseClockFlow.circlePhaseState h

/-- Real lifts of the affine physical translation. -/
theorem torusTranslationFlow_realLift (ω : Fin (vars + eqs) → ℝ)
    (x : Fin (vars + eqs) → ℝ) (t : ℝ) :
    RadicalClock.torusTranslationFlow ω t (fun i ↦ (x i : UnitAddCircle)) =
      fun i ↦ ((x i + t * ω i : ℝ) : UnitAddCircle) := by
  funext i
  simp [RadicalClock.torusTranslationFlow_apply, RadicalClock.torusDisplacement]

private theorem numberFrequency_eq_sum
    (parameters : Fin (vars + eqs) → RationalCode) (I : DQLSystem eqs vars)
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ) (j : Fin vars) :
    numberFrequency parameters I controller j = 4 * ∑ row,
      (I.linear row j : ℝ) * LockedControllerPhaseTrajectory.angularVelocity
        parameters controller (finSumFinEquiv (Sum.inr row)) := by
  rw [CanonicalFixedDetectorFourierCrosswalk.numberFrequency_eq_characterFrequency]
  unfold LockedControllerPhaseTrajectory.characterFrequency
    DetectorCharacterCode.flattenCharacter
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [finSumFinEquiv.symm_apply_apply, DetectorCharacterCode.linearCharacter,
    Int.cast_mul, Int.cast_ofNat, Int.cast_zero, mul_zero, zero_mul, Finset.sum_const_zero,
    zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro row _
  ring

/-- The elliptic argument on a real phase lift, including the half-period. -/
def sourceEllipticParameter (I : DQLSystem eqs vars) (j : Fin vars)
    (x : Fin (vars + eqs) → ℝ) : ℂ :=
  4 * ((∑ row, (I.linear row j : ℝ) * x (finSumFinEquiv (Sum.inr row)) : ℝ) : ℂ) +
    (1 + (fundamentalThetaParameter (finSumFinEquiv (Sum.inl j)) x : ℂ)) / 2

theorem fundamentalThetaParameter_flow
    (parameters : Fin (vars + eqs) → RationalCode)
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (x : Fin (vars + eqs) → ℝ) (t : ℝ) (j : Fin vars) :
    fundamentalThetaParameter (finSumFinEquiv (Sum.inl j))
        (fun i ↦ x i + t * turnsFrequency parameters controller i) =
      modularPath (fundamentalThetaParameter (finSumFinEquiv (Sum.inl j)) x)
        (omegaFrequency parameters controller j) t := by
  apply UpperHalfPlane.ext
  rw [FixedDetectorPrivateFrequency.omegaFrequency_eq_four_mul_privateAngularVelocity]
  dsimp [fundamentalThetaParameter, modularPath, turnsFrequency,
    FixedDetectorPrivateFrequency.privateClockIndex]
  push_cast
  field_simp [Real.pi_ne_zero]
  ring

theorem sourceEllipticParameter_flow
    (parameters : Fin (vars + eqs) → RationalCode) (I : DQLSystem eqs vars)
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (x : Fin (vars + eqs) → ℝ) (t : ℝ) (j : Fin vars) :
    sourceEllipticParameter I j (fun i ↦ x i + t * turnsFrequency parameters controller i) =
      ellipticPath (sourceEllipticParameter I j x)
        (omegaFrequency parameters controller j) (numberFrequency parameters I controller j) t := by
  rw [sourceEllipticParameter, fundamentalThetaParameter_flow,
    FixedDetectorPrivateFrequency.omegaFrequency_eq_four_mul_privateAngularVelocity,
    numberFrequency_eq_sum]
  dsimp [sourceEllipticParameter, ellipticPath, modularPath, turnsFrequency,
    FixedDetectorPrivateFrequency.privateClockIndex]
  simp only [mul_add, Finset.sum_add_distrib]
  have hs : (∑ row, (I.linear row j : ℝ) *
      (t * (LockedControllerPhaseTrajectory.angularVelocity parameters controller
        (finSumFinEquiv (Sum.inr row)) / (2 * Real.pi)))) =
      (t / (2 * Real.pi)) * ∑ row, (I.linear row j : ℝ) *
        LockedControllerPhaseTrajectory.angularVelocity parameters controller
          (finSumFinEquiv (Sum.inr row)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro row _
    ring
  dsimp only [finSumFinEquiv, Equiv.coe_fn_mk, Sum.elim_inr] at hs
  rw [hs]
  push_cast
  field_simp [Real.pi_ne_zero]
  ring

/-- A Fourier character packaged as a unit-circle initial phase. -/
def sourceCharacterCircle (a : Fin (vars + eqs) → ℤ)
    (x : UnitAddTorus (Fin (vars + eqs))) : Circle :=
  ⟨UnitAddTorus.mFourier a x, mem_sphere_zero_iff_norm.mpr (norm_mFourier_apply a x)⟩

private theorem characterCircle_flow
    (parameters : Fin (vars + eqs) → RationalCode)
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (a : Fin (vars + eqs) → ℤ) (x : UnitAddTorus (Fin (vars + eqs))) (t : ℝ) :
    sourceCharacterCircle a (RadicalClock.torusTranslationFlow
        (turnsFrequency parameters controller) t x) =
      PhaseClockFlow.phaseRotationFlow
        (LockedControllerPhaseTrajectory.characterFrequency parameters controller a) t
        (sourceCharacterCircle a x) := by
  apply Subtype.ext
  change UnitAddTorus.mFourier a _ = _
  rw [RadicalClock.torusTranslationFlow_apply, RadicalClock.mFourier_add_point,
    RadicalClock.mFourier_torusDisplacement, PhaseClockFlow.phaseRotationFlow_apply,
    Circle.coe_mul, Circle.coe_exp]
  have hp : RadicalClock.frequencyPairing a (turnsFrequency parameters controller) =
      LockedControllerPhaseTrajectory.characterFrequency parameters controller a /
        (2 * Real.pi) := by
    unfold RadicalClock.frequencyPairing turnsFrequency
      LockedControllerPhaseTrajectory.characterFrequency
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hp, mul_comm (UnitAddTorus.mFourier a x)]
  congr 2
  push_cast
  field_simp [Real.pi_ne_zero]

private theorem graphClock_eq_clockPath
    (parameters : Fin (vars + eqs) → RationalCode)
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (x : UnitAddTorus (Fin (vars + eqs))) (t : ℝ) :
    (fun i ↦ ControllerPhaseState.mk (controller i)
      (sourcePhaseGraph (RadicalClock.torusTranslationFlow
        (turnsFrequency parameters controller) t x) i)) =
      clockPath parameters controller (fun i ↦ AddCircle.toCircle (x i)) t := by
  funext i
  rw [sourcePhaseGraph_flow]
  rfl

private theorem graphReciprocal_eq
    (I : DQLSystem eqs vars) (x : UnitAddTorus (Fin (vars + eqs)))
    (k : Fin (DetectorPoissonReciprocalCode.reciprocalCount vars)) :
    poissonReciprocalGraph I (finProdFinEquiv.symm k).1
        (if (finProdFinEquiv.symm k).2 = 0 then 1 else -1) x =
      (1 - (1 / 2 : ℂ) * UnitAddTorus.mFourier
        (DetectorPoissonReciprocalCode.reciprocalExponent I k) x)⁻¹ := by
  obtain ⟨⟨j, s⟩, rfl⟩ := finProdFinEquiv.surjective k
  fin_cases s <;>
    simp [poissonReciprocalGraph, DetectorPoissonReciprocalCode.reciprocalExponent,
      DetectorPoissonReciprocalCode.poissonExponent]

private theorem linkedGraph_flow_eq
    (parameters : Fin (vars + eqs) → RationalCode) (I : DQLSystem eqs vars)
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (x : Fin (vars + eqs) → ℝ) (t : ℝ) (j : Fin vars) :
    sourceLinkedThetaGraph I j (RadicalClock.torusTranslationFlow
      (turnsFrequency parameters controller) t (fun i ↦ (x i : UnitAddCircle))) =
      { unary := canonicalUnaryTheta (modularPath
          (fundamentalThetaParameter (finSumFinEquiv (Sum.inl j)) x)
          (omegaFrequency parameters controller j) t)
        jacobi := canonicalJacobiThetaState (ellipticPath (sourceEllipticParameter I j x)
          (omegaFrequency parameters controller j) (numberFrequency parameters I controller j) t)
          (modularPath (fundamentalThetaParameter (finSumFinEquiv (Sum.inl j)) x)
            (omegaFrequency parameters controller j) t) } := by
  rw [torusTranslationFlow_realLift]
  have h := sourceLinkedThetaGraph_eq_canonical I j
    (fun i ↦ x i + t * turnsFrequency parameters controller i)
  change sourceLinkedThetaGraph I j _ =
    { unary := canonicalUnaryTheta (fundamentalThetaParameter (finSumFinEquiv (Sum.inl j))
        (fun i ↦ x i + t * turnsFrequency parameters controller i))
      jacobi := canonicalJacobiThetaState (sourceEllipticParameter I j
        (fun i ↦ x i + t * turnsFrequency parameters controller i))
        (fundamentalThetaParameter (finSumFinEquiv (Sum.inl j))
          (fun i ↦ x i + t * turnsFrequency parameters controller i)) } at h
  rw [fundamentalThetaParameter_flow, sourceEllipticParameter_flow] at h
  exact h

/-- Exact identification with the canonical trajectory, for every real
initial lift and without a controller-equilibrium assumption. -/
theorem intendedSourceStateGraph_flow_eq_canonical
    (parameters : Fin (vars + eqs) → RationalCode) (I : DQLSystem eqs vars)
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (x : Fin (vars + eqs) → ℝ) (t : ℝ) :
    intendedSourceStateGraph I controller (RadicalClock.torusTranslationFlow
      (turnsFrequency parameters controller) t (fun i ↦ (x i : UnitAddCircle))) =
      fixedDetectorPath parameters I controller
        (fun i ↦ AddCircle.toCircle (x i : UnitAddCircle))
        (fun j ↦ sourceEllipticParameter I j x)
        (fun j ↦ fundamentalThetaParameter (finSumFinEquiv (Sum.inl j)) x)
        (sourceCharacterCircle (DetectorCharacterCode.flattenCharacter
          (DetectorCharacterCode.rhsCharacter I)) (fun i ↦ (x i : UnitAddCircle))) t := by
  have hc := graphClock_eq_clockPath parameters controller (fun i ↦ (x i : UnitAddCircle)) t
  have hchar (a : Fin (vars + eqs) → ℤ) := characterValue_sourcePhaseGraph controller
    (RadicalClock.torusTranslationFlow (turnsFrequency parameters controller) t
      (fun i ↦ (x i : UnitAddCircle))) a
  rw [hc] at hchar
  apply FixedDetectorPolynomialCode.State.ext
  · apply DetectorPoissonReciprocalCode.State.ext
    · apply ControllerProductLinkedJacobiGaugeFamilyState.ext
      · apply ControllerProductLinkedJacobiFamilyState.ext
        · exact hc
        · funext j
          exact linkedGraph_flow_eq parameters I controller x t j
      · funext j
        change (1 / 4 : ℂ) * UnitAddTorus.mFourier _ _ = gaugePath _ _ _ _ _ _
        rw [gaugePath, hchar]
        norm_num
    · funext k
      change poissonReciprocalGraph I _ _ _ = poissonReciprocalPath _ _ _ _ _ _
      rw [graphReciprocal_eq, poissonReciprocalPath, poissonCharacterPath, hchar]
      norm_num
  · have hr := characterCircle_flow parameters controller
      (DetectorCharacterCode.flattenCharacter (DetectorCharacterCode.rhsCharacter I))
      (fun i ↦ (x i : UnitAddCircle)) t
    rw [CanonicalFixedDetectorFourierCrosswalk.rhsCharacterFrequency_eq] at hr
    exact congrArg PhaseClockFlow.circlePhaseState hr

/-- The whole literal graph solves the exact compiled source field.
The reciprocal chart is proved from its actual inverse graph. -/
theorem intendedSourceGraph_isIntegralCurve
    (parameters : Fin (vars + eqs) → RationalCode) (I : DQLSystem eqs vars)
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (hlock : ∀ i, Controller.IsControllerEquilibrium
      ((parameters i).decode : ℝ) (controller i))
    (x : UnitAddTorus (Fin (vars + eqs))) :
    IsIntegralCurve (fun t ↦ intendedSourceGraph I controller
      (RadicalClock.torusTranslationFlow (turnsFrequency parameters controller) t x))
      (fun _ y ↦ PolynomialFieldCode.realize
        (FixedDetectorPolynomialCode.fieldCode parameters I) y) := by
  obtain ⟨v, rfl⟩ : ∃ v : Fin (vars + eqs) → ℝ, (fun i ↦ (v i : UnitAddCircle)) = x := by
    choose v hv using fun i ↦ QuotientAddGroup.mk_surjective (x i)
    exact ⟨v, funext hv⟩
  simp_rw [intendedSourceGraph, intendedSourceStateGraph_flow_eq_canonical]
  apply fixedDetectorPath_point_isIntegralCurve _ _ _ _ _ _ _ hlock
  intro j t
  rw [← sourceEllipticParameter_flow, ← fundamentalThetaParameter_flow]
  have ht := halfPeriodThetaGraph_eq_jacobiTheta1 I j
    (fun i ↦ v i + t * turnsFrequency parameters controller i)
  change halfPeriodThetaGraph I j _ = _ at ht
  intro hz
  exact left_ne_zero_of_mul_eq_one (thetaReciprocalGraph_identity I j _) (ht.trans hz)

end Stability.Selection
