import HGAS.Arithmetic.NormalizedCorrectedAugmentedFamilyFromGap
import HGAS.Arithmetic.NormalizedCorrectedEffectiveCanonicalThetaOutputs
import HGAS.Arithmetic.NormalizedCorrectedEffectiveGapFromCanonicalTheta
import Mathlib.Tactic

/-!
# The completed repaired universal compact-sign family

The universal DQL preprocessing appends one linear equality for every
variable.  It preserves solvability and ensures that every detector
column is nonzero.  The effective canonical-theta theorem therefore
supplies the yes-instance half of the semantic gap for every repaired
universal input.  The orbit-closure Fourier theorem supplies the
no-instance half.

This file assembles those results into the single computable,
fixed-resource compact-sign source family consumed by the
recursion-theoretic reduction.
-/

noncomputable section

namespace HGAS.NormalizedCorrectedAugmentedEffectiveFamily

open HGAS

/-- The one fixed state dimension produced before optional cubic
dimension padding. -/
abbrev fixedDimension : ℕ :=
  NormalizedCorrectedAugmentedUniversalResources.compactSourceDimension + 1

/-- The fixed output dimension is nonzero. -/
theorem fixedDimension_pos : 0 < fixedDimension := by
  simp only [fixedDimension]
  omega

/-- The one fixed odd homogeneous degree produced by the compact-sign
wrapper. -/
abbrev fixedDegree : ℕ :=
  Compiler.FixedUniversalDQLCompactSignSourceFamily.outputDegree
    NormalizedCorrectedAugmentedUniversalResources.sourceSphereCount
    NormalizedCorrectedAugmentedUniversalResources.wrapperDegree

/-- The complete semantic gap of one augmented universal-halting
instance. -/
def gap (input : ℕ) :
    NormalizedCorrectedAugmentedFamilyFromGap.Gap input := by
  let D :=
    UniversalHalting.augmentedUniversalHaltingFixedDQL input
  exact
    NormalizedCorrectedEffectiveGapFromCanonicalTheta.gapOfCanonicalThetaOutputs
      D
      (fun O ↦
        NormalizedCorrectedEffectiveCanonicalThetaOutputs.hasCanonicalThetaOutputs
          D O
          (UniversalHalting.augmentedUniversalHaltingFixedDQL_hasNonzeroLinearColumn
            input))

/-- The completed fixed-dimension, fixed-degree, computable source
family. -/
def family :
    Compiler.FixedUniversalDQLCompactSignSourceFamily
      NormalizedCorrectedAugmentedFamilyFromGap.system
      NormalizedCorrectedAugmentedUniversalResources.sourceBlock
      NormalizedCorrectedAugmentedUniversalResources.wrapperDegree :=
  NormalizedCorrectedAugmentedFamilyFromGap.familyOfGaps gap

/-- Fixed-pair `Σ⁰₁`-completeness for the repaired universal family. -/
theorem fixedPair_sigmaOneComplete :
    SigmaOneComplete (HGASQ fixedDimension fixedDegree) := by
  exact
    Compiler.FixedUniversalDQLCompactSignSourceFamily.fixedPair_sigmaOneComplete
      family

/-- The fixed output degree is odd. -/
theorem fixedDegree_odd : Odd fixedDegree :=
  Nat.odd_iff.mpr
    (Compiler.FixedUniversalDQLCompactSignSourceFamily.outputDegree_odd
      family)

/-- The fixed output degree is at least three. -/
theorem fixedDegree_ge_three : 3 ≤ fixedDegree :=
  Compiler.FixedUniversalDQLCompactSignSourceFamily.three_le_outputDegree
    family

/-- In particular, membership in this single fixed-dimension,
fixed-degree homogeneous GAS language is undecidable. -/
theorem fixedPair_not_computable :
    ¬ComputablePred (HGASQ fixedDimension fixedDegree) :=
  fixedPair_sigmaOneComplete.not_computable

/-- The complement of the fixed-pair language is not computably
enumerable. -/
theorem fixedPair_complement_not_re :
    ¬REPred (fun code ↦ ¬HGASQ fixedDimension fixedDegree code) :=
  fixedPair_sigmaOneComplete.complement_not_re

/-- Half-degree used by the effective cubicization of the fixed source
family. -/
abbrev fixedOutputHalfDegree : ℕ :=
  Compiler.FixedUniversalDQLCompactSignSourceFamily.outputHalfDegree
    NormalizedCorrectedAugmentedUniversalResources.sourceSphereCount
    NormalizedCorrectedAugmentedUniversalResources.wrapperDegree

/-- Explicit threshold after cubicization.  Every larger dimension is
obtained by effective degree/dimension padding. -/
abbrev cofinalDimensionThreshold : ℕ :=
  Veronese.cubicLiftCodeDimension
    fixedDimension fixedOutputHalfDegree

/-- **Cofinal fixed-pair theorem.**  For every dimension beyond the
single displayed threshold and every odd degree at least three, rational
homogeneous polynomial GAS is `Σ⁰₁`-complete. -/
theorem cofinal_sigmaOneComplete
    (N d : ℕ)
    (hN : cofinalDimensionThreshold ≤ N)
    (hd : Odd d)
    (hthree : 3 ≤ d) :
    SigmaOneComplete (HGASQ N d) :=
  Compiler.FixedUniversalDQLCompactSignSourceFamily.cofinal_sigmaOneComplete
    family N d hN hd hthree

/-- In particular, cubic homogeneous GAS is `Σ⁰₁`-complete in every
dimension beyond the explicit fixed threshold. -/
theorem cubic_sigmaOneComplete
    (N : ℕ)
    (hN : cofinalDimensionThreshold ≤ N) :
    SigmaOneComplete (HGASQ N 3) :=
  cofinal_sigmaOneComplete N 3 hN (by norm_num) (by norm_num)

/-- Hence cubic homogeneous GAS is undecidable in every sufficiently
large fixed dimension. -/
theorem cubic_not_computable
    (N : ℕ)
    (hN : cofinalDimensionThreshold ≤ N) :
    ¬ComputablePred (HGASQ N 3) :=
  (cubic_sigmaOneComplete N hN).not_computable

/-- The complement of every sufficiently-large fixed-dimensional cubic
language is not computably enumerable. -/
theorem cubic_complement_not_re
    (N : ℕ)
    (hN : cofinalDimensionThreshold ≤ N) :
    ¬REPred (fun code ↦ ¬HGASQ N 3 code) :=
  (cubic_sigmaOneComplete N hN).complement_not_re

end HGAS.NormalizedCorrectedAugmentedEffectiveFamily
