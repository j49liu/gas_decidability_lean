import Stability.Selection.OrdinaryTimeConditionalBase
import Stability.Selection.OrdinaryTimeDetectorGainCode
import HGAS.Compiler.CompactAccumulatorPipelineNonempty

/-!
# The compact detector's negative reward bound

Ordinary-time extraction rules out zero conditional drift means for any
nonzero accumulator gain. The compact-accumulator theorem then gives the
exact upper bound `β ≤ -ε`, including the least-integer gain of Section 9.
No no-instance graph or alternative effective gain enters this argument.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Dynamics HGAS.CompactAccumulatorPipelineCode
open HGAS.NormalizedCorrectedFixedDetectorCompactSourceCode
open HGAS.Clocks.ObservedTimeChangedControllerPhaseHaar
open MeasureTheory
open scoped BoundedContinuousFunction

variable {eqs vars : ℕ}

/-- The actual product of source and accumulator spheres. -/
abbrev DetectorCompactSpace (eqs vars : ℕ) :=
  UnitSpherePolynomialWrapper.SourceProductSphere
    (sourceBlock (m := driftDimension vars) (layout (eqs := eqs) (vars := vars)))

local instance : Nonempty (DetectorCompactSpace eqs vars) := by
  simpa [NormalizedCorrectedFixedDetectorCompactSourceCode.layout] using
    nonempty_sourceProductSphere_oneBlockAllAffine
      (sourceDimension eqs vars) (driftDimension vars)

/-- The literal compiled compact flow, with both rational constants explicit. -/
def detectorCompactFlow (I : DQLSystem eqs vars) (p : Fin (vars + eqs) → ℕ)
    (κ ε : RationalCode) : Flow ℝ (DetectorCompactSpace eqs vars) :=
  sourceFlow layout (sourceDegreeBound I) (clearingExponent I) κ
    (sourceFieldCode (primeClockCodes p) I) (sourceDriftCode I) ε

/-- The literal reward `u₀ + 2w² - 1 - ε` on the actual compact source. -/
def detectorCompactReward (eqs vars : ℕ) (ε : RationalCode) : DetectorCompactSpace eqs vars →ᵇ ℝ :=
  UnitSpherePolynomialWrapper.sourceRewardBCF
    (sourceBlock (m := driftDimension vars) (layout (eqs := eqs) (vars := vars)))
    (rewardCode (n := sourceDimension eqs vars) (k := 1) (m := driftDimension vars) ε)

/-- Solvability forces a nonzero coordinate of the actual conditional
base drift, for every nonzero rational gain and every reward margin. -/
theorem detectorConditionalBase_nonzero_mean
    (I : DQLSystem eqs vars) (hcolumns : DQLNonzeroLinearAugmentation.HasNonzeroLinearColumn I)
    (p : Fin (vars + eqs) → ℕ) (hp : ∀ i, (p i).Prime) (hinjective : Function.Injective p)
    (κ ε : RationalCode) (hκ : (κ.decode : ℝ) ≠ 0) (hsolv : I.Solvable)
    (μ : InvariantProbabilityMeasure (detectorCompactFlow I p κ ε))
    (hμ : IsErgodicInvariantProbability (detectorCompactFlow I p κ ε) μ.measure)
    (hpos : (μ.measure : Measure (DetectorCompactSpace eqs vars))
      (sourceFiniteInteriorSet (m := driftDimension vars) layout) ≠ 0) :
    ∃ q, (∫ b, baseDriftBCF layout (clearingExponent I) κ (sourceDriftCode I) b q
      ∂((conditionalBaseProbability layout (sourceDegreeBound I) (clearingExponent I) κ
        (sourceFieldCode (primeClockCodes p) I)
        (sourceFieldCode_termsDegreeLE (primeClockCodes p) I)
        (sourceDriftCode I) (sourceDriftCode_termsDegreeLE I) ε
        (baseCompactTangency (primeClockCodes p) I) μ hpos).measure :
          Measure (BaseSpace (layout (eqs := eqs) (vars := vars))))) ≠ 0 := by
  by_contra! hzero
  let ν := conditionalBaseProbability layout (sourceDegreeBound I) (clearingExponent I) κ
    (sourceFieldCode (primeClockCodes p) I)
    (sourceFieldCode_termsDegreeLE (primeClockCodes p) I)
    (sourceDriftCode I) (sourceDriftCode_termsDegreeLE I) ε
    (baseCompactTangency (primeClockCodes p) I) μ hpos
  have hν := ordinaryConditionalBase_ergodic (sourceDegreeBound I) (clearingExponent I) κ
    (sourceFieldCode (primeClockCodes p) I)
    (sourceFieldCode_termsDegreeLE (primeClockCodes p) I)
    (sourceDriftCode I) (sourceDriftCode_termsDegreeLE I) ε
    (baseCompactTangency (primeClockCodes p) I) μ hpos hμ
  have hfull := ordinaryConditionalBase_finiteInterior_full
    (sourceDegreeBound I) (clearingExponent I) κ
    (sourceFieldCode (primeClockCodes p) I)
    (sourceFieldCode_termsDegreeLE (primeClockCodes p) I)
    (sourceDriftCode I) (sourceDriftCode_termsDegreeLE I) ε
    (baseCompactTangency (primeClockCodes p) I) μ hpos
  apply not_solvable_of_ergodic_compactBase_zero p hp hinjective I hcolumns ν hν hfull _ hsolv
  intro q
  exact compactBase_mean_zero_of_scaled (clearingExponent I) κ hκ (sourceDriftCode I)
    (ν.measure : Measure (BaseSpace (layout (eqs := eqs) (vars := vars)))) q (hzero q)

/-- Quantitative negative branch for the actual compact field. No
positivity hypothesis on the margin is needed for this upper bound. -/
theorem detectorCompactMaximum_le_neg_margin
    (I : DQLSystem eqs vars) (hcolumns : DQLNonzeroLinearAugmentation.HasNonzeroLinearColumn I)
    (p : Fin (vars + eqs) → ℕ) (hp : ∀ i, (p i).Prime) (hinjective : Function.Injective p)
    (κ ε : RationalCode) (hκ : (κ.decode : ℝ) ≠ 0) (hsolv : I.Solvable) :
    maximalInvariantAverage (detectorCompactFlow I p κ ε)
      (detectorCompactReward eqs vars ε) ≤ -(ε.decode : ℝ) := by
  let hP := sourceFieldCode_termsDegreeLE (primeClockCodes p) I
  let hh := sourceDriftCode_termsDegreeLE I
  let ht := baseCompactTangency (primeClockCodes p) I
  apply maximalInvariantAverage_le_neg_epsilon_of_compactAccumulator
    (measurableSet_sourceFiniteInteriorSet (m := driftDimension vars) layout)
    (canonicalFiniteInteriorInvariant layout (sourceDegreeBound I) (clearingExponent I) κ
      (sourceFieldCode (primeClockCodes p) I) hP (sourceDriftCode I) hh ε ht)
    (restrictedBaseProjection layout) (continuous_restrictedBaseProjection layout)
    (canonicalRestrictedBaseProjection_semiconj layout (sourceDegreeBound I) (clearingExponent I) κ
      (sourceFieldCode (primeClockCodes p) I) hP (sourceDriftCode I) hh ε ht)
    (finiteAccumulatorProjection layout) (continuous_finiteAccumulatorProjection layout)
    (baseDriftBCF layout (clearingExponent I) κ (sourceDriftCode I))
    (canonicalFiniteAccumulator_u_hasDerivAt layout (sourceDegreeBound I) (clearingExponent I) κ
      (sourceFieldCode (primeClockCodes p) I) hP (sourceDriftCode I) hh ε ht)
    (canonicalFiniteAccumulator_w_hasDerivAt layout (sourceDegreeBound I) (clearingExponent I) κ
      (sourceFieldCode (primeClockCodes p) I) hP (sourceDriftCode I) hh ε ht)
  · intro μ hμ hpos
    simpa only [conditionalBaseProbability] using
      detectorConditionalBase_nonzero_mean I hcolumns p hp hinjective κ ε hκ hsolv μ hμ hpos
  · exact sourceRewardBCF_le_neg_epsilon_of_not_mem_finiteInterior layout ε

/-- The exact least-integer gain and margin satisfy the printed negative
branch, with no identification with the preserved alternative compiler. -/
theorem detectorGraphGain_maximum_le_neg_margin
    (I : DQLSystem eqs vars) (hcolumns : DQLNonzeroLinearAugmentation.HasNonzeroLinearColumn I)
    (p : Fin (vars + eqs) → ℕ) (hp : ∀ i, (p i).Prime) (hinjective : Function.Injective p)
    (hsolv : I.Solvable) :
    maximalInvariantAverage
      (detectorCompactFlow I p (rhsGraphGainCode I p I.rhs)
        (RationalCode.encode (detectorGraphMargin eqs vars)))
      (detectorCompactReward eqs vars (RationalCode.encode (detectorGraphMargin eqs vars))) ≤
      -(detectorGraphMargin eqs vars : ℝ) := by
  have hκ : ((rhsGraphGainCode I p I.rhs).decode : ℝ) ≠ 0 := by
    rw [decode_rhsGraphGainCode]
    exact_mod_cast (detectorGraphGain_pos I p).ne'
  simpa only [RationalCode.decode_encode] using
    detectorCompactMaximum_le_neg_margin I hcolumns p hp hinjective
      (rhsGraphGainCode I p I.rhs)
      (RationalCode.encode (detectorGraphMargin eqs vars)) hκ hsolv

end Stability.Selection
