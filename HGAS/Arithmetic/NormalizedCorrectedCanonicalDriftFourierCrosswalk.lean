import HGAS.Analysis.NormalizedCorrectedCanonicalDriftFourierFamily
import Mathlib.Tactic

/-!
# Exact canonical crosswalk for the complete normalized drift

This file identifies the literal normalized polynomial drift on the
canonical detector path with the complete realified Fourier family.

The validity coordinate deserves special care.  Its vanishing uses:

1. the linked-Jacobi, gauge, and reciprocal graph identities;
2. unit radius of every locked controller;
3. unit radius of every driven phase; and
4. unit radius of the final right-hand-side oscillator.

The last equality is stated separately below, so the terminal oscillator
cannot disappear behind a dimension count or an implicit normalization
convention.
-/

noncomputable section

namespace HGAS.NormalizedCorrectedCanonicalDriftFourierCrosswalk

open HGAS
open HGAS.Analysis
open HGAS.Analysis.NormalizedCorrectedCanonicalDriftFourierFamily
open HGAS.Analysis.CanonicalSelectorMomentSupportedCrosswalk
open HGAS.Analysis.CanonicalDetectorNoInstanceAggregatedFamily
open HGAS.Clocks
open HGAS.Modular

variable {eqs vars : ℕ}

/-- The final right-hand-side oscillator in the canonical state has
exactly unit squared radius. -/
theorem canonicalState_rhsRadiusSq_eq_one
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) :
    Controller.phaseRadiusSq
        (CorrectedCanonicalFixedDetectorMomentFourierCrosswalk.canonicalState
          parameters I controller t).rhs =
      1 := by
  unfold
    CorrectedCanonicalFixedDetectorMomentFourierCrosswalk.canonicalState
  exact
    NormalizedCorrectedCanonicalFixedDetectorGraph.fixedDetectorPath_rhsRadiusSq
      parameters I controller
      LockedControllerPhaseTrajectory.onePhase
      (fun _ ↦
        CanonicalFixedDetectorChart.halfPeriodInitialElliptic
          0 thetaGaugeBasePoint)
      (fun _ ↦ thetaGaugeBasePoint)
      (1 : Circle) t

/-- The complete normalization energy vanishes on the canonical state.
The proof supplies the final RHS radius equality explicitly as the third
component of the normalization zero-set characterization. -/
theorem canonicalState_normalizationEnergyValue_eq_zero
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (t : ℝ) :
    NormalizedCorrectedFixedDetectorValidityCode.normalizationEnergyValue
        (CorrectedCanonicalFixedDetectorMomentFourierCrosswalk.canonicalState
          parameters I controller t) =
      0 := by
  apply
    (NormalizedCorrectedFixedDetectorValidityCode.normalizationEnergyValue_eq_zero_iff
      _).2
  constructor
  · intro i
    unfold
      CorrectedCanonicalFixedDetectorMomentFourierCrosswalk.canonicalState
    exact
      NormalizedCorrectedCanonicalFixedDetectorGraph.fixedDetectorPath_controllerRadiusSq
        parameters I controller
        LockedControllerPhaseTrajectory.onePhase
        (fun _ ↦
          CanonicalFixedDetectorChart.halfPeriodInitialElliptic
            0 thetaGaugeBasePoint)
        (fun _ ↦ thetaGaugeBasePoint)
        (1 : Circle) hcontroller t i
  constructor
  · intro i
    unfold
      CorrectedCanonicalFixedDetectorMomentFourierCrosswalk.canonicalState
    exact
      NormalizedCorrectedCanonicalFixedDetectorGraph.fixedDetectorPath_phaseRadiusSq
        parameters I controller
        LockedControllerPhaseTrajectory.onePhase
        (fun _ ↦
          CanonicalFixedDetectorChart.halfPeriodInitialElliptic
            0 thetaGaugeBasePoint)
        (fun _ ↦ thetaGaugeBasePoint)
        (1 : Circle) t i
  · exact canonicalState_rhsRadiusSq_eq_one
      parameters I controller t

/-- The first normalized drift coordinate is exactly zero.  Here the
graph part and normalization part are rewritten separately. -/
theorem canonicalState_normalizedValidityEnergyValue_eq_zero
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (t : ℝ) :
    NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
        (CorrectedCanonicalFixedDetectorMomentFourierCrosswalk.canonicalState
          parameters I controller t) =
      0 := by
  unfold
    NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue
    NormalizedCorrectedFixedDetectorValidityCode.totalNormalizedValidityEnergyValue
  change
    FixedDetectorDriftCode.validityEnergyValue I
        (CorrectedCanonicalFixedDetectorMomentFourierCrosswalk.canonicalState
          parameters I controller t) +
      NormalizedCorrectedFixedDetectorValidityCode.normalizationEnergyValue
        (CorrectedCanonicalFixedDetectorMomentFourierCrosswalk.canonicalState
          parameters I controller t) =
      0
  rw [canonicalState_normalizationEnergyValue_eq_zero
    parameters I controller hcontroller t, add_zero]
  unfold
    CorrectedCanonicalFixedDetectorMomentFourierCrosswalk.canonicalState
  exact
    CanonicalFixedDetectorChart.canonicalFixedDetectorPath_validityEnergyValue_eq_zero
      parameters I controller
      LockedControllerPhaseTrajectory.onePhase
      (1 : Circle) t

/-- Semantic real drift coordinate before flattening the nested block
label to `Fin`. -/
def semanticAtLabel
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    Label vars → ℝ
  | Sum.inl _ =>
      NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I z
  | Sum.inr (Sum.inl k) =>
      CorrectedFixedDetectorMomentCode.scalarMomentValue I z k
  | Sum.inr (Sum.inr b) =>
      ![(NormalizedCorrectedFixedDetectorDriftCode.detectorValue z).re,
        (NormalizedCorrectedFixedDetectorDriftCode.detectorValue z).im] b

/-- Fourier real coordinate before flattening the label. -/
def fourierAtLabel
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable)
    (L : Label vars)
    (phase : UnitAddTorus (Fin (vars + eqs))) : ℝ :=
  (torusFourierSeries
    (coefficientAtLabel I hnot L)
    (exponentAtLabel I hnot L) phase).re

/-- The compiler's flattened semantic vector is exactly the nested-label
semantic vector transported by `label`. -/
theorem driftValue_eq_semanticAtLabel
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars)
    (q : Fin (driftCount vars)) :
    NormalizedCorrectedFixedDetectorDriftCode.driftValue I z q =
      semanticAtLabel I z (label q) := by
  obtain ⟨a | r, rfl⟩ := finSumFinEquiv.surjective q
  · fin_cases a
    simp [NormalizedCorrectedFixedDetectorDriftCode.driftValue,
      semanticAtLabel, label]
  · obtain ⟨k | b, rfl⟩ := finSumFinEquiv.surjective r
    · simp [NormalizedCorrectedFixedDetectorDriftCode.driftValue,
        semanticAtLabel, label]
    · simp [NormalizedCorrectedFixedDetectorDriftCode.driftValue,
        semanticAtLabel, label]

/-- The complete canonical nested-label semantics equals the selected
Fourier family at the fundamental physical clock phase. -/
theorem semanticAtLabel_canonical_eq_fourierAtLabel
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hnot : ¬ I.Solvable)
    (t : ℝ)
    (L : Label vars) :
    semanticAtLabel I
        (CorrectedCanonicalFixedDetectorMomentFourierCrosswalk.canonicalState
          parameters I controller t) L =
      fourierAtLabel I hnot L
        (CanonicalFixedDetectorFundamentalPhase.fundamentalPhasePath
          parameters controller t) := by
  rcases L with a | k | b
  · have ha : a = 0 := Subsingleton.elim _ _
    subst a
    rw [show
      semanticAtLabel I
          (CorrectedCanonicalFixedDetectorMomentFourierCrosswalk.canonicalState
            parameters I controller t) (Sum.inl 0) =
        NormalizedCorrectedFixedDetectorDriftCode.validityEnergyValue I
          (CorrectedCanonicalFixedDetectorMomentFourierCrosswalk.canonicalState
            parameters I controller t) from rfl]
    rw [canonicalState_normalizedValidityEnergyValue_eq_zero
      parameters I controller hcontroller t]
    simp [fourierAtLabel, coefficientAtLabel, exponentAtLabel,
      indexAtLabel, torusFourierSeries, torusSeriesTerm]
  · let kb := finProdFinEquiv.symm k
    have hmoment :=
      momentValue_eq_supportedSeries
        parameters I controller t kb.1
    have hreal :=
      re_torusFourierSeries_realifiedCoefficient kb.2
        (momentFamily I kb.1).supportedCoefficient
        (momentFamily I kb.1).supportedExponent
        (CanonicalFixedDetectorFundamentalPhase.fundamentalPhasePath
          parameters controller t)
    change
      ![
        (CorrectedFixedDetectorMomentCode.momentValue I
          (CorrectedCanonicalFixedDetectorMomentFourierCrosswalk.canonicalState
            parameters I controller t) kb.1).re,
        (CorrectedFixedDetectorMomentCode.momentValue I
          (CorrectedCanonicalFixedDetectorMomentFourierCrosswalk.canonicalState
            parameters I controller t) kb.1).im] kb.2 =
      (torusFourierSeries
        (realifiedCoefficient kb.2
          (momentFamily I kb.1).supportedCoefficient)
        (momentFamily I kb.1).supportedExponent
        (CanonicalFixedDetectorFundamentalPhase.fundamentalPhasePath
          parameters controller t)).re
    rw [hmoment]
    exact hreal.symm
  · have hdetector :
        NormalizedCorrectedFixedDetectorDriftCode.detectorValue
            (CorrectedCanonicalFixedDetectorMomentFourierCrosswalk.canonicalState
              parameters I controller t) =
          torusFourierSeries
            (detector I hnot).supportedCoefficient
            (detector I hnot).supportedExponent
            (CanonicalFixedDetectorFundamentalPhase.fundamentalPhasePath
              parameters controller t) := by
      calc
        NormalizedCorrectedFixedDetectorDriftCode.detectorValue
            (CorrectedCanonicalFixedDetectorMomentFourierCrosswalk.canonicalState
              parameters I controller t) =
            ControllerPhaseProductCharacterCode.evalPair
              (FixedDetectorPolynomialCode.detectorCode
                (eqs := eqs) (vars := vars))
              (FixedDetectorPolynomialCode.point
                (CorrectedCanonicalFixedDetectorMomentFourierCrosswalk.canonicalState
                  parameters I controller t)) := by
            exact
              (FixedDetectorDriftCode.evalPair_detectorCode_eq_detectorValue
                _).symm
        _ =
          torusFourierSeries
            (detector I hnot).supportedCoefficient
            (detector I hnot).supportedExponent
            (CanonicalFixedDetectorFundamentalPhase.fundamentalPhasePath
              parameters controller t) :=
            evalPair_detectorCode_canonical_eq_supportedSeries
              parameters controller I hnot t
    have hreal :=
      re_torusFourierSeries_realifiedCoefficient b
        (detector I hnot).supportedCoefficient
        (detector I hnot).supportedExponent
        (CanonicalFixedDetectorFundamentalPhase.fundamentalPhasePath
          parameters controller t)
    change
      ![
        (NormalizedCorrectedFixedDetectorDriftCode.detectorValue
          (CorrectedCanonicalFixedDetectorMomentFourierCrosswalk.canonicalState
            parameters I controller t)).re,
        (NormalizedCorrectedFixedDetectorDriftCode.detectorValue
          (CorrectedCanonicalFixedDetectorMomentFourierCrosswalk.canonicalState
            parameters I controller t)).im] b =
      (torusFourierSeries
        (realifiedCoefficient b
          (detector I hnot).supportedCoefficient)
        (detector I hnot).supportedExponent
        (CanonicalFixedDetectorFundamentalPhase.fundamentalPhasePath
          parameters controller t)).re
    rw [hdetector]
    exact hreal.symm

/-- Final vector identity in exactly the type and coordinate order needed
by the normalized compiler. -/
theorem canonical_driftValue_eq_realTorusFourierVector
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (hnot : ¬ I.Solvable)
    (t : ℝ) :
    NormalizedCorrectedFixedDetectorDriftCode.driftValue I
        (CorrectedCanonicalFixedDetectorMomentFourierCrosswalk.canonicalState
          parameters I controller t) =
      realTorusFourierVector
        (Index I hnot)
        (coefficient I hnot)
        (exponent I hnot)
        (CanonicalFixedDetectorFundamentalPhase.fundamentalPhasePath
          parameters controller t) := by
  funext q
  rw [driftValue_eq_semanticAtLabel]
  exact
    semanticAtLabel_canonical_eq_fourierAtLabel
      parameters I controller hcontroller hnot t (label q)

end HGAS.NormalizedCorrectedCanonicalDriftFourierCrosswalk
