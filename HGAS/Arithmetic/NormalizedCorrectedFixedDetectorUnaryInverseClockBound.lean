import HGAS.Arithmetic.FixedDetectorUnaryCoordinateNorm
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
import HGAS.Compiler.AllAffineCompactSourceReverseRecurrence
import HGAS.Dynamics.GenericUnboundedClockContradiction
import Mathlib.Tactic

/-!
# A detector unary coordinate is bounded by reciprocal physical speed

For a selected two-sided validity orbit, physical time is obtained by
inverting the compact-time clock

```text
  w(t) = (1 + ‖x(t)‖²)⁻ᴷ.
```

Every linked unary `C` coordinate is part of the full affine detector
point.  The structured norm estimate therefore gives

```text
  ‖Cⱼ(τ)‖^(2K)
    ≤ (1 + ‖physicalPoint(τ)‖²)^K
    = 1 / w(clock⁻¹(τ)).
```

The final expression is exactly `inverseClockReciprocal O.clock τ`.
This module is purely a compiler/clock bridge and is independent of all
modular classification hypotheses.
-/

namespace HGAS.NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit

open HGAS
open Filter Topology
open CompactAccumulatorPipelineCode.AllAffineCompactSourceChart
open CompactAccumulatorPipelineCode.AllAffineCompactSourceClock
open CompactAccumulatorPipelineCode.AllAffineCompactSourceTwoSidedClock
open CompactAccumulatorPipelineCode.AllAffineCompactSourceReverseRecurrence

noncomputable section

variable {eqs vars : ℕ}
variable
  {u :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      eqs vars}

namespace SelectedTwoSidedValidityOrbit

variable
  (O : SelectedTwoSidedValidityOrbit u)

/-- Every unary `C` coordinate on the selected physical orbit is
dominated, at the compactification-matching even power, by reciprocal
physical clock speed. -/
theorem unaryC_evenPower_le_inverseClockReciprocal
    (j : Fin vars) (τ : ℝ) :
    ‖((O.physicalState τ).base.base.source.linked j).unary.C‖ ^
          (2 * speedExponent
            (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)) ≤
      HGAS.Dynamics.inverseClockReciprocal O.clock τ := by
  let K : ℕ :=
    speedExponent
      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
  have hsq :
      ‖((O.physicalState τ).base.base.source.linked j).unary.C‖ ^ 2 ≤
        normSq (O.physicalPoint τ) := by
    rw [← O.point_physicalState τ]
    exact fixedDetector_unaryC_norm_sq_le
      (O.physicalState τ) j
  have hbound :=
    evenPower_le_inverse_affineSpeed
      (K := K)
      (a :=
        ‖((O.physicalState τ).base.base.source.linked j).unary.C‖)
      (x := O.physicalPoint τ)
      (norm_nonneg _) hsq
  simpa only [K, HGAS.Dynamics.inverseClockReciprocal_apply,
    twoSidedClockWeight, physicalPoint] using hbound

/-- The speed-genericity field stored in the selected orbit is precisely
the positive-integer-horizon mean of its integral clock. -/
theorem clock_positiveIntegerMean :
    Tendsto
      (fun n : ℕ ↦
        (positiveIntegerHorizon n)⁻¹ *
          integralClock
            (twoSidedClockWeight
              (speedExponent
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
              (affineCurve u O.point))
            (positiveIntegerHorizon n))
      atTop (𝓝 O.speedMean) := by
  have heq :
      (fun n : ℕ ↦
        Dynamics.integerOrbitAverageObservable
          ((compactFlow u).restrict (finiteInvariant u))
          (affineSpeedBCF
            (speedExponent
              (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)))
          (n + 1) O.point) =
        fun n : ℕ ↦
          (positiveIntegerHorizon n)⁻¹ *
            integralClock
              (twoSidedClockWeight
                (speedExponent
                  (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
                (affineCurve u O.point))
              (positiveIntegerHorizon n) := by
    funext n
    rw [Dynamics.integerOrbitAverageObservable_apply]
    simp only [positiveIntegerHorizon,
      Nat.cast_add, Nat.cast_one]
    congr 1
  rw [← heq]
  exact O.speed_generic

/-- The reversed clock has the reverse generic speed mean stored in the
selected two-sided orbit. -/
theorem reverseClock_positiveIntegerMean :
    Tendsto
      (fun n : ℕ ↦
        (positiveIntegerHorizon n)⁻¹ *
          integralClock
            (fun t ↦
              twoSidedClockWeight
                (speedExponent
                  (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
                (affineCurve u O.point) (-t))
            (positiveIntegerHorizon n))
      atTop (𝓝 O.speedMean) := by
  have heq :
      (fun n : ℕ ↦
        Dynamics.integerOrbitAverageObservable
          ((compactFlow u).restrict (finiteInvariant u)).reverse
          (affineSpeedBCF
            (speedExponent
              (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)))
          (n + 1) O.point) =
        fun n : ℕ ↦
          (positiveIntegerHorizon n)⁻¹ *
            integralClock
              (fun t ↦
                twoSidedClockWeight
                  (speedExponent
                    (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
                  (affineCurve u O.point) (-t))
              (positiveIntegerHorizon n) := by
    funext n
    rw [Dynamics.integerOrbitAverageObservable_apply]
    simp only [positiveIntegerHorizon,
      Nat.cast_add, Nat.cast_one]
    rfl
  rw [← heq]
  exact O.speed_generic_reverse

/-- Reciprocal speed for the reversed clock at time `τ` is the original
reciprocal speed at time `-τ`. -/
theorem inverseClockReciprocal_reverseClock
    (τ : ℝ) :
    HGAS.Dynamics.inverseClockReciprocal
        (reverseClock O.clock) τ =
      HGAS.Dynamics.inverseClockReciprocal O.clock (-τ) := by
  simp only [HGAS.Dynamics.inverseClockReciprocal_apply,
    twoSidedClockWeight]
  exact
    congrArg
      (fun t : ℝ ↦
        (affineSpeed
          (speedExponent
            (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
          (affineCurve u O.point t))⁻¹)
      (neg_reverseClock_symm O.clock τ)

end SelectedTwoSidedValidityOrbit

end

end HGAS.NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
