import Stability.Selection.OrdinaryTimeAccumulatorGap
import HGAS.Arithmetic.NormalizedCorrectedAugmentedFamilyFromGap

/-!
# The fixed universal family from ordinary-time selection

The existing computable DQL augmentation supplies nonzero linear columns.
The compact gaps proved from forward ordinary-time selection then feed
the fixed-resource polynomial wrapper. The underlying finite compiler is
unchanged, including its effective alternative gain and reward margin.
-/

noncomputable section

namespace Stability.Selection

open HGAS
open HGAS.NormalizedCorrectedAugmentedUniversalResources

/-- The actual computable universal source family, using the new
ordinary-time obstruction for its yes-instance semantics. -/
def ordinaryTimeUniversalFamily :
    Compiler.FixedUniversalDQLCompactSignSourceFamily
      NormalizedCorrectedAugmentedFamilyFromGap.system sourceBlock wrapperDegree :=
  NormalizedCorrectedAugmentedFamilyFromGap.familyOfGaps fun input ↦
    effectiveDetectorAccumulatorGap (UniversalHalting.augmentedUniversalHaltingFixedDQL input)
      (UniversalHalting.augmentedUniversalHaltingFixedDQL_hasNonzeroLinearColumn input)

/-- The emitted code is the literal existing fixed-resource compiler,
not a choice made from any semantic certificate. -/
theorem ordinaryTimeUniversalFamily_output_eq :
    ordinaryTimeUniversalFamily.outputCode =
      Compiler.wrappedCompactSignSourceOutputCode sourceBlock wrapperDegree sourceCode := rfl

theorem ordinaryTimeUniversalFamily_output_computable :
    Computable ordinaryTimeUniversalFamily.outputCode :=
  ordinaryTimeUniversalFamily.outputCode_computable

/-- Fixed state dimension of the homogeneous wrapped family. -/
abbrev ordinaryTimeFixedDimension : ℕ := compactSourceDimension + 1

/-- Fixed odd homogeneous degree of the wrapped family. -/
abbrev ordinaryTimeFixedDegree : ℕ :=
  Compiler.FixedUniversalDQLCompactSignSourceFamily.outputDegree sourceSphereCount wrapperDegree

/-- Exact many-one correctness for the actual emitted polynomial codes. -/
theorem ordinaryTimeUniversalFamily_hgas_iff (input : ℕ) :
    HGASQ ordinaryTimeFixedDimension ordinaryTimeFixedDegree
      (ordinaryTimeUniversalFamily.outputCode input) ↔ UniversalHalting.Predicate input :=
  ordinaryTimeUniversalFamily.hgasQ_output_iff_predicate input

/-- Fixed-pair completeness obtained through ordinary-time source
selection and the actual compact accumulator, with no selector premise. -/
theorem ordinaryTime_fixedPair_sigmaOneComplete :
    SigmaOneComplete (HGASQ ordinaryTimeFixedDimension ordinaryTimeFixedDegree) :=
  ordinaryTimeUniversalFamily.fixedPair_sigmaOneComplete

/-- The common dimension threshold after the existing effective cubic
lift; it is independent of the input code. -/
abbrev ordinaryTimeCofinalDimensionThreshold : ℕ :=
  Veronese.cubicLiftCodeDimension ordinaryTimeFixedDimension
    (Compiler.FixedUniversalDQLCompactSignSourceFamily.outputHalfDegree
      sourceSphereCount wrapperDegree)

/-- The same completed family gives all sufficiently large dimensions
and every odd degree at least three via the existing effective lifts. -/
theorem ordinaryTime_cofinal_sigmaOneComplete
    (N d : ℕ) (hN : ordinaryTimeCofinalDimensionThreshold ≤ N)
    (hd : Odd d) (hthree : 3 ≤ d) :
    SigmaOneComplete (HGASQ N d) :=
  ordinaryTimeUniversalFamily.cofinal_sigmaOneComplete N d hN hd hthree

end Stability.Selection
