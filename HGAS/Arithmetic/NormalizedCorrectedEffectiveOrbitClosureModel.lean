import HGAS.Arithmetic.NormalizedCorrectedCanonicalOrbitClosureModel
import HGAS.Arithmetic.NormalizedCorrectedEffectiveCompilerInput
import HGAS.Clocks.ExplicitPositiveControllerEquilibrium
import Mathlib.Tactic

/-!
# Effective prime specialization of the canonical orbit-closure model

The effective compiler assigns the `i`-th prime to the `i`-th fundamental
clock.  We select a concrete unit equilibrium of each corresponding cubic
controller field using the normalized positive eigendirection from
`ExplicitPositiveControllerEquilibrium`.

Every locked prime controller has one of the two signed square-root
frequencies.  Thus a single sign vector identifies the fundamental phase
frequency with the standard scaled prime-radical frequency

```text
                  (1 / (2π)) · (±√pᵢ).
```

This file specializes the generic canonical component model to exactly
the parameters and gain occurring in the effective compiler input.
-/

noncomputable section

namespace HGAS.NormalizedCorrectedEffectiveOrbitClosureModel

open HGAS
open HGAS.Analysis
open HGAS.Analysis.NormalizedCorrectedCanonicalDriftFourierFamily
open HGAS.Clocks
open HGAS.NormalizedCorrectedCanonicalOrbitClosureChart
open HGAS.NormalizedCorrectedEffectiveCompilerInput

variable {eqs vars : ℕ}

/-- The explicit equilibrium controller chosen for each effective prime
clock. -/
def controller (eqs vars : ℕ) :
    Fin (vars + eqs) → Controller.ControllerState ℝ :=
  fun i ↦
    ExplicitPositiveControllerEquilibrium.state
      (primeRadicand (vars + eqs) i : ℝ)

theorem controller_radiusSq (eqs vars : ℕ) :
    ∀ i, Controller.controllerRadiusSq (controller eqs vars i) = 1 := by
  intro i
  exact
    ExplicitPositiveControllerEquilibrium.state_radiusSq
      (primeRadicand (vars + eqs) i : ℝ)

theorem controller_equilibrium (eqs vars : ℕ) :
    ∀ i,
      Controller.IsControllerEquilibrium
        (RationalCode.decode (controllerParameters eqs vars i) : ℝ)
        (controller eqs vars i) := by
  intro i
  have hp :
      (1 : ℝ) < (primeRadicand (vars + eqs) i : ℕ) := by
    exact_mod_cast (primeRadicand_prime (vars + eqs) i).one_lt
  simpa [controllerParameters,
    ObservedTimeChangedControllerPhaseHaar.decode_primeClockCodes] using
      (ExplicitPositiveControllerEquilibrium.state_isControllerEquilibrium
        (primeRadicand (vars + eqs) i : ℝ) hp)

/-- The selected effective controller family has a common signed-radical
turn-frequency representation. -/
theorem exists_sign_turnsFrequency (eqs vars : ℕ) :
    ∃ sign : Fin (vars + eqs) → ℤ,
      (∀ i, sign i = 1 ∨ sign i = -1) ∧
      CanonicalFixedDetectorFundamentalPhase.turnsFrequency
          (controllerParameters eqs vars)
          (controller eqs vars) =
        ScaledRadicalClock.scaledSignedPrimeSqrtFrequency
          (1 / (2 * Real.pi))
          (primeRadicand (vars + eqs))
          sign := by
  obtain ⟨sign, hsign, hlocked⟩ :=
    RadicalClock.exists_signs_for_primeControllerEquilibria
      (primeRadicand (vars + eqs))
      (controller eqs vars)
      (controller_radiusSq eqs vars)
      (fun i ↦ by
        have h :=
          controller_equilibrium eqs vars i
        simpa [controllerParameters,
          ObservedTimeChangedControllerPhaseHaar.decode_primeClockCodes]
          using h)
  refine ⟨sign, hsign, ?_⟩
  simpa only [controllerParameters] using
    (CanonicalFixedDetectorFundamentalPhase.turnsFrequency_primeClockCodes_eq_scaledRadical
      (primeRadicand (vars + eqs))
      (controller eqs vars)
      sign hlocked)

/-- Exact effective canonical model, with the sign branch exposed for the
prime-radical small-divisor theorem. -/
theorem exists_model
    (I : DQLSystem eqs vars)
    (hnot : ¬ I.Solvable) :
    Nonempty
      (Σ sign : Fin (vars + eqs) → ℤ,
        PLift (∀ i, sign i = 1 ∨ sign i = -1) ×
        RadicalTimeChangedTorusFourierComponent.Model
        (layout eqs vars)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent I)
        (NormalizedCorrectedCanonicalEffectivePrimitiveGain.effectiveAccumulatorScaleCode
          I (primeRadicand (vars + eqs)))
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode
          (controllerParameters eqs vars) I)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDriftCode I)
        (Index I hnot)
        (1 / (2 * Real.pi))
        (primeRadicand (vars + eqs))
        sign
        (scaledRealCoefficient
          (RationalCode.decode
            (NormalizedCorrectedCanonicalEffectivePrimitiveGain.effectiveAccumulatorScaleCode
              I (primeRadicand (vars + eqs))) : ℝ)
          (coefficient I hnot))
        (exponent I hnot)) := by
  obtain ⟨sign, hsign, hfrequency⟩ :=
    exists_sign_turnsFrequency eqs vars
  refine ⟨⟨sign, ⟨hsign⟩, ?_⟩⟩
  exact
      NormalizedCorrectedCanonicalOrbitClosureModel.model
        (NormalizedCorrectedCanonicalEffectivePrimitiveGain.effectiveAccumulatorScaleCode
          I (primeRadicand (vars + eqs)))
        (controllerParameters eqs vars)
        I
        (controller eqs vars)
        (controller_radiusSq eqs vars)
        (controller_equilibrium eqs vars)
        hnot
        (1 / (2 * Real.pi))
        (primeRadicand (vars + eqs))
        sign
        hfrequency

end HGAS.NormalizedCorrectedEffectiveOrbitClosureModel
