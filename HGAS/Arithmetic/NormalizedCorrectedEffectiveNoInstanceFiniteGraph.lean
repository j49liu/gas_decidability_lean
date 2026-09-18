import HGAS.Arithmetic.NormalizedCorrectedEffectiveOrbitClosureModel
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorExplicitFiniteGraphGap
import Mathlib.Tactic

/-!
# Effective finite graph for every no-instance

This module discharges the complete no-instance side of the effective
normalized compiler.

For a nonsolvable Diophantine quadratic--linear system we use:

* the explicit prime-controller orbit-closure model;
* the complete normalized drift Fourier family;
* its zero-mode, ordinary summability, and radical-height weighted
  summability theorems;
* the effective rational accumulator gain; and
* the uniform positive lower bound for the canonical central chart.

The result is an invariant probability whose reward average has the
explicit positive gap required by the compiler.
-/

noncomputable section

open Function MeasureTheory
open scoped BigOperators BoundedContinuousFunction

namespace HGAS.NormalizedCorrectedEffectiveNoInstanceFiniteGraph

open HGAS
open HGAS.Analysis
open HGAS.Analysis.NormalizedCorrectedCanonicalDriftFourierFamily
open HGAS.Clocks
open HGAS.CompactAccumulatorPipelineCode
open HGAS.NormalizedCorrectedCanonicalOrbitClosureChart
open HGAS.NormalizedCorrectedCanonicalEffectivePrimitiveGain
open HGAS.NormalizedCorrectedEffectiveCompilerInput
open HGAS.NormalizedCorrectedEffectiveOrbitClosureModel
open HGAS.NormalizedCorrectedFixedDetectorCompactSourceCode

variable {eqs vars : ℕ}

/-- The effective central lower bound used in the no-instance graph. -/
abbrev centralLower (eqs vars : ℕ) : ℝ :=
  NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalCentralWeightSqLowerBound
    eqs vars

/-- Every nonsolvable input has an invariant finite graph with the
explicit positive canonical reward gap. -/
theorem finite_graph
    (I : DQLSystem eqs vars) :
    ¬ I.Solvable →
      ∃ μ :
          Dynamics.InvariantProbabilityMeasure
            (sourceFlow
              layout
              (sourceDegreeBound
                (system
                  (NormalizedCorrectedEffectiveCompilerInput.compilerInput I)))
              (clearingExponent
                (system
                  (NormalizedCorrectedEffectiveCompilerInput.compilerInput I)))
              (accumulatorScale
                (NormalizedCorrectedEffectiveCompilerInput.compilerInput I))
              (sourceFieldCode
                (parameters
                  (NormalizedCorrectedEffectiveCompilerInput.compilerInput I))
                (system
                  (NormalizedCorrectedEffectiveCompilerInput.compilerInput I)))
              (sourceDriftCode
                (system
                  (NormalizedCorrectedEffectiveCompilerInput.compilerInput I)))
              (rewardMargin
                (NormalizedCorrectedEffectiveCompilerInput.compilerInput I))),
        explicitFiniteGraphDelta (centralLower eqs vars) ≤
          Dynamics.observableAverage
            (UnitSpherePolynomialWrapper.sourceRewardBCF
              (sourceBlock
                (m := driftDimension vars) layout)
              (rewardCode
                (n :=
                  NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
                    eqs vars)
                (k := affineBlockCount)
                (m := driftDimension vars)
                (rewardMargin
                  (NormalizedCorrectedEffectiveCompilerInput.compilerInput I))))
            μ.measure := by
  intro hnot
  let hex :=
    NormalizedCorrectedEffectiveOrbitClosureModel.exists_sign_turnsFrequency
      eqs vars
  let sign : Fin (vars + eqs) → ℤ :=
    hex.choose
  have hsign : ∀ i, sign i = 1 ∨ sign i = -1 := by
    exact hex.choose_spec.1
  have hfrequency :
      CanonicalFixedDetectorFundamentalPhase.turnsFrequency
          (controllerParameters eqs vars)
          (NormalizedCorrectedEffectiveOrbitClosureModel.controller
            eqs vars) =
        ScaledRadicalClock.scaledSignedPrimeSqrtFrequency
          (1 / (2 * Real.pi))
          (primeRadicand (vars + eqs))
          sign := by
    exact hex.choose_spec.2
  let G :
      ¬(system
          (NormalizedCorrectedEffectiveCompilerInput.compilerInput I)).Solvable →
        RadicalTimeChangedTorusFourierComponent.Model
          layout
          (sourceDegreeBound
            (system
              (NormalizedCorrectedEffectiveCompilerInput.compilerInput I)))
          (clearingExponent
            (system
              (NormalizedCorrectedEffectiveCompilerInput.compilerInput I)))
          (accumulatorScale
            (NormalizedCorrectedEffectiveCompilerInput.compilerInput I))
          (sourceFieldCode
            (parameters
              (NormalizedCorrectedEffectiveCompilerInput.compilerInput I))
            (system
              (NormalizedCorrectedEffectiveCompilerInput.compilerInput I)))
          (sourceDriftCode
            (system
              (NormalizedCorrectedEffectiveCompilerInput.compilerInput I)))
          (Index I hnot)
          (1 / (2 * Real.pi))
          (primeRadicand (vars + eqs))
          sign
          (scaledRealCoefficient
            (RationalCode.decode
              (accumulatorScale
                (NormalizedCorrectedEffectiveCompilerInput.compilerInput I)) :
              ℝ)
            (coefficient I hnot))
          (exponent I hnot) :=
    fun _ ↦
      NormalizedCorrectedCanonicalOrbitClosureModel.model
        (NormalizedCorrectedCanonicalEffectivePrimitiveGain.effectiveAccumulatorScaleCode
          I (primeRadicand (vars + eqs)))
        (controllerParameters eqs vars)
        I
        (NormalizedCorrectedEffectiveOrbitClosureModel.controller eqs vars)
        (controller_radiusSq eqs vars)
        (controller_equilibrium eqs vars)
        hnot
        (1 / (2 * Real.pi))
        (primeRadicand (vars + eqs))
        sign
        hfrequency
  have hzero :
      ∀ _hnot :
          ¬(system
            (NormalizedCorrectedEffectiveCompilerInput.compilerInput I)).Solvable,
        ∀ q j,
          exponent I hnot q j = 0 →
            scaledRealCoefficient
                (RationalCode.decode
                  (accumulatorScale
                    (NormalizedCorrectedEffectiveCompilerInput.compilerInput I)) :
                  ℝ)
                (coefficient I hnot) q j =
              0 := by
    intro _hnot
    exact
      scaledRealCoefficient_zeroMode
        (RationalCode.decode
          (accumulatorScale
            (NormalizedCorrectedEffectiveCompilerInput.compilerInput I)) : ℝ)
        (coefficient I hnot)
        (exponent I hnot)
        (zeroMode I hnot)
  have hcoefficient :
      ∀ q,
        Summable fun j ↦
          ‖scaledRealCoefficient
            (RationalCode.decode
              (accumulatorScale
                (NormalizedCorrectedEffectiveCompilerInput.compilerInput I)) :
              ℝ)
            (coefficient I hnot) q j‖ := by
    exact
      summable_norm_scaledRealCoefficient
        (RationalCode.decode
          (accumulatorScale
            (NormalizedCorrectedEffectiveCompilerInput.compilerInput I)) : ℝ)
        (coefficient I hnot)
        (coefficient_summable I hnot)
  have hweighted :
      ∀ q,
        Summable fun j ↦
          ‖scaledRealCoefficient
              (RationalCode.decode
                (accumulatorScale
                  (NormalizedCorrectedEffectiveCompilerInput.compilerInput I)) :
                ℝ)
              (coefficient I hnot) q j‖ *
            RadicalSmallDivisor.radicalConjugateHeight
                (primeRadicand (vars + eqs))
                (exponent I hnot q j) ^
              (RadicalSmallDivisor.radicalDegree
                (primeRadicand (vars + eqs)) - 1) := by
    exact
      summable_norm_scaledRealCoefficient_mul_weight
        (RationalCode.decode
          (accumulatorScale
            (NormalizedCorrectedEffectiveCompilerInput.compilerInput I)) : ℝ)
        (coefficient I hnot)
        (fun q j ↦
          RadicalSmallDivisor.radicalConjugateHeight
              (primeRadicand (vars + eqs))
              (exponent I hnot q j) ^
            (RadicalSmallDivisor.radicalDegree
              (primeRadicand (vars + eqs)) - 1))
        (coefficient_weighted_summable
          I hnot
          (primeRadicand (vars + eqs))
          (RadicalSmallDivisor.radicalDegree
            (primeRadicand (vars + eqs)) - 1))
  have hprimitive :
      8 *
          (∑ q : Fin (driftDimension vars),
            (primitiveCoordinateBound
              (Index I hnot)
              (scaledRealCoefficient
                (RationalCode.decode
                  (accumulatorScale
                    (NormalizedCorrectedEffectiveCompilerInput.compilerInput I)) :
                  ℝ)
                (coefficient I hnot))
              (exponent I hnot)
              (RadicalTimeChangedTorusFourierComponent.frequency
                (1 / (2 * Real.pi))
                (primeRadicand (vars + eqs))
                sign) q) ^ 2) ≤
        centralLower eqs vars := by
    simpa [sign] using
      (NormalizedCorrectedCanonicalEffectivePrimitiveGain.effectiveAccumulatorScale_small
        I hnot
        (primeRadicand (vars + eqs))
        (primeRadicand_prime (vars + eqs))
        (primeRadicand_injective (vars + eqs))
        sign hsign)
  have hcentral :
      ∀ h :
          ¬(system
            (NormalizedCorrectedEffectiveCompilerInput.compilerInput I)).Solvable,
        ∀ b : (G h).ComponentSpace,
          centralLower eqs vars ≤ baseCentralWeightProduct layout b.1 := by
    intro h b
    simpa [G,
      NormalizedCorrectedCanonicalOrbitClosureChart.layout,
      NormalizedCorrectedFixedDetectorCompactSourceCode.layout] using
        (NormalizedCorrectedCanonicalOrbitClosureChart.centralLower_le
          (controllerParameters eqs vars)
          I
          (NormalizedCorrectedEffectiveOrbitClosureModel.controller eqs vars)
          (controller_radiusSq eqs vars)
          (controller_equilibrium eqs vars)
          b)
  have hmargin :
      (RationalCode.decode
          (rewardMargin
            (NormalizedCorrectedEffectiveCompilerInput.compilerInput I)) :
        ℝ) ≤
        3 * centralLower eqs vars / 8 := by
    calc
      (RationalCode.decode
          (rewardMargin
            (NormalizedCorrectedEffectiveCompilerInput.compilerInput I)) :
        ℝ) ≤
          3 *
              (1 /
                (1 +
                  (CanonicalRawOrbitEffectiveBudget.rawNormSqNatBudget
                    eqs vars : ℝ))) /
            8 := by
              simpa using
                decode_rewardMarginCode_le_effectiveGap eqs vars
      _ ≤ 3 * centralLower eqs vars / 8 := by
        gcongr
        exact
          effectiveCentralLower_le_canonicalCentralWeightSqLowerBound
            eqs vars
  exact
    (finite_graph_of_radicalTimeChangedTorus_explicitGap
      (NormalizedCorrectedEffectiveCompilerInput.compilerInput I)
      G
      (one_div_ne_zero
        (mul_ne_zero (by norm_num) Real.pi_ne_zero))
      (primeRadicand_prime (vars + eqs))
      (primeRadicand_injective (vars + eqs))
      hsign
      hzero
      hcoefficient
      hweighted
      (centralLower eqs vars)
      (NormalizedCorrectedCanonicalFixedDetectorCentralChart.canonicalCentralWeightSqLowerBound_pos)
      hprimitive
      hcentral
      hmargin)
      (by simpa using hnot)

end HGAS.NormalizedCorrectedEffectiveNoInstanceFiniteGraph
