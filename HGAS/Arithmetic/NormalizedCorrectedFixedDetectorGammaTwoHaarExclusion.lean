import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorUnaryInverseClockBound
import HGAS.Modular.GammaTwoScaledH4SquareCompactTests
import HGAS.Modular.RealFrameHorocycleUnaryAmplitude
import Mathlib.Tactic

/-!
# Haar exclusion for a selected detector unary frame branch

This module joins the three independent ingredients of the nonperiodic
modular argument:

1. the exact real-frame identity
   `scaled H₄² observable = ‖C‖^(2K)`;
2. the compiler estimate
   `‖C‖^(2K) ≤ reciprocal clock speed`;
3. the explicit Haar cusp marginal, converted to arbitrarily large
   compactly supported continuous tests.

The first theorem exposes the resulting orbitwise bound.  The second is
the contradiction endpoint: if the frame orbit were Haar generic, its
positive-mean compactification clock would force the averages of those
compact tests both to become arbitrarily large and to remain uniformly
bounded.

No periodic-orbit statement is used here.  The hypotheses describe the
literal nonperiodic real-frame branch returned by the recurrent unary lift
classification.
-/

namespace HGAS.NormalizedCorrectedFixedDetectorGammaTwoHaarExclusion

open HGAS
open Filter Topology
open HGAS.Modular
open HGAS.NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
open UpperHalfPlane hiding I

noncomputable section

variable {eqs vars : ℕ}
variable
  {u :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      eqs vars}

namespace SelectedTwoSidedValidityOrbit

variable
  (O : HGAS.NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit.SelectedTwoSidedValidityOrbit u)

private abbrev unaryTrajectory (j : Fin vars) :
    ℝ → UnaryModularState ℂ :=
  fun τ ↦
    ((O.physicalState τ).base.base.source.linked j).unary

/-- The speed-normalized `H₄²` observable is bounded by reciprocal
physical clock speed along every exact real-frame unary branch. -/
theorem scaledH4Square_orbitBound
    (j : Fin vars)
    (hz :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock
        (unaryTrajectory O j))
    (hB :
      ∀ τ,
        UnaryModularState.B (unaryTrajectory O j τ) ≠ 0)
    (T : ℝ → ℍ)
    (hlambda :
      ∀ τ,
        UnaryModularState.lambdaCoordinate
            (unaryTrajectory O j τ) =
          canonicalLambda (T τ))
    (g : RealModularFrame) (s : ℝ)
    (hframe :
      ∀ τ,
        T τ =
          realModularFrameBasePoint
            (g * upperUnipotent (s * τ)))
    (τ : ℝ) :
    gammaTwoScaledH4SquareNormPower
        (horocycleSpeedNorm s)
        (speedExponent
          (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
        (scaledGammaTwoHorocycleFlow s τ
          (gammaTwoFrameQuotientMk g)) ≤
      HGAS.Dynamics.inverseClockReciprocal O.clock τ := by
  rw [
    gammaTwoScaledH4SquareNormPower_eq_unaryC_norm_pow
      hz hB hlambda g s hframe
      (speedExponent
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      τ]
  exact O.unaryC_evenPower_le_inverseClockReciprocal j τ

/-- A selected exact real-frame unary branch cannot be Haar generic when
the compactification exponent is at least one. -/
theorem not_haarGeneric_of_exactRealFrameBranch
    (j : Fin vars)
    (hz :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock
        (unaryTrajectory O j))
    (hB :
      ∀ τ,
        UnaryModularState.B (unaryTrajectory O j τ) ≠ 0)
    (T : ℝ → ℍ)
    (hlambda :
      ∀ τ,
        UnaryModularState.lambdaCoordinate
            (unaryTrajectory O j τ) =
          canonicalLambda (T τ))
    (g : RealModularFrame) (s : ℝ) (hs : s ≠ 0)
    (hframe :
      ∀ τ,
        T τ =
          realModularFrameBasePoint
            (g * upperUnipotent (s * τ)))
    (hK :
      1 ≤ speedExponent
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
    (hgeneric :
      IsForwardGenericFor
        (scaledGammaTwoHorocycleFlow s)
        gammaTwoFrameHaarProbability
        (gammaTwoFrameQuotientMk g)) :
    False := by
  exact
    not_gammaTwoHaarGeneric_of_positiveMeanClock_and_scaledH4Square_orbitBound
      (scaledGammaTwoHorocycleFlow s)
      hgeneric O.clock O.speedMean_pos O.clock_positiveIntegerMean
      (horocycleSpeedNorm s)
      (horocycleSpeedNorm_ne_zero hs)
      (speedExponent
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u))
      hK
      (scaledH4Square_orbitBound O
        j hz hB T hlambda g s hframe)

end SelectedTwoSidedValidityOrbit

end

end HGAS.NormalizedCorrectedFixedDetectorGammaTwoHaarExclusion
