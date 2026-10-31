import Stability.Selection.OrdinaryTimeDetectorCompiler
import HGAS.Arithmetic.NormalizedCorrectedAugmentedUniversalResources
import HGAS.Compiler.FixedUniversalDQLCompactSignSourceFamily

/-!
# The universal detector with the least-integer gain

The augmented fixed DQL template supplies nonzero linear columns. Only
its RHS varies, so the raw gain compiler is computable in the input and
the existing resource bounds give one dimension and one odd degree.
-/

noncomputable section

namespace Stability.Selection

open HGAS
open HGAS.NormalizedCorrectedAugmentedUniversalResources
open HGAS.NormalizedCorrectedEffectiveCompilerInput (primeRadicand primeRadicand_prime
  primeRadicand_injective)

private theorem system_eq_reference_rhs (input : ℕ) :
    UniversalHalting.augmentedUniversalHaltingFixedDQL input =
      { UniversalHalting.augmentedReferenceDQL with
        rhs := (UniversalHalting.augmentedUniversalHaltingFixedDQL input).rhs } := by
  have h := UniversalHalting.augmentedUniversalHaltingFixedDQL_sameCharacterData input
  generalize UniversalHalting.augmentedUniversalHaltingFixedDQL input = I at h ⊢
  generalize UniversalHalting.augmentedReferenceDQL = J at h ⊢
  rcases I with ⟨A, B, c⟩
  rcases J with ⟨A', B', c'⟩
  rcases h with ⟨rfl, rfl⟩
  rfl

/-- The literal compact field/reward code emitted with the computable
least-integer gain. -/
def universalDetectorSourceCode (input : ℕ) :
    PolynomialFieldCode compactSourceDimension × PolynomialCode compactSourceDimension :=
  NormalizedCorrectedFixedDetectorCompactSourceCode.compile
    (detectorCompilerInput (UniversalHalting.augmentedUniversalHaltingFixedDQL input)
      (primeRadicand (variableCount + equationCount)))

theorem universalDetectorSourceCode_computable : Computable universalDetectorSourceCode := by
  have hr : Primrec (fun I : DQLSystem equationCount variableCount ↦ I.rhs) := by
    rw [Primrec.fin_curry]
    apply Primrec₂.swap
    rw [Primrec.fin_curry₁]
    exact DetectorCharacterCode.rhsEntry_primrec
  have h := (detectorCompiledSourceCode_rhs_computable UniversalHalting.augmentedReferenceDQL
    (primeRadicand (variableCount + equationCount))).comp
      (hr.to_comp.comp UniversalHalting.augmentedUniversalHaltingFixedDQL_computable)
  apply h.of_eq
  intro input
  rw [universalDetectorSourceCode, system_eq_reference_rhs input]

/-- One semantic certificate for each actual universal detector code. -/
def universalDetectorCertificate (input : ℕ) :
    Compiler.CompactSignSourceCertificate sourceBlock
      (UniversalHalting.augmentedUniversalHaltingFixedDQL input) :=
  detectorSignCertificate (UniversalHalting.augmentedUniversalHaltingFixedDQL input)
    (UniversalHalting.augmentedUniversalHaltingFixedDQL_hasNonzeroLinearColumn input)
    (primeRadicand (variableCount + equationCount)) (primeRadicand_prime _)
    (primeRadicand_injective _)

theorem universalDetectorCertificate_degree (input : ℕ) :
    (universalDetectorCertificate input).degree = wrapperDegree :=
  instance_wrapperDegree_eq input

theorem universalDetectorSourceCode_eq_certificate (input : ℕ) :
    universalDetectorSourceCode input =
      ((universalDetectorCertificate input).fieldCode,
        (universalDetectorCertificate input).rewardCode) := rfl

/-- A complete fixed-resource family for the actual least-integer-gain
detector and its homogeneous wrapper. -/
def universalDetectorFamily : Compiler.FixedUniversalDQLCompactSignSourceFamily
    UniversalHalting.augmentedUniversalHaltingFixedDQL sourceBlock wrapperDegree :=
  Compiler.FixedUniversalDQLCompactSignSourceFamily.ofComputableSourceCodes
    UniversalHalting.augmentedUniversalHaltingFixedDQL_solvable_iff
    wrapperDegree wrapperDegree_ge_three wrapperDegree_odd
    universalDetectorCertificate universalDetectorCertificate_degree
    universalDetectorSourceCode universalDetectorSourceCode_computable
    universalDetectorSourceCode_eq_certificate

/-- The output is the direct syntactic wrapper, independent of the proofs
carried by the semantic certificates. -/
theorem universalDetectorFamily_output_eq :
    universalDetectorFamily.outputCode = Compiler.wrappedCompactSignSourceOutputCode
      sourceBlock wrapperDegree universalDetectorSourceCode := rfl

/-- The universal output is also the proof-independent per-instance
field code of the exact detector compiler. -/
theorem universalDetectorFamily_output_eq_wrappedField (input : ℕ) :
    universalDetectorFamily.outputCode input =
      detectorWrappedFieldCode (UniversalHalting.augmentedUniversalHaltingFixedDQL input)
        (primeRadicand (variableCount + equationCount)) := by
  rw [universalDetectorFamily.outputCode_eq]
  rfl

theorem universalDetectorFamily_output_computable : Computable universalDetectorFamily.outputCode :=
  universalDetectorFamily.outputCode_computable

abbrev universalDetectorFixedDimension : ℕ := compactSourceDimension + 1

abbrev universalDetectorFixedDegree : ℕ :=
  Compiler.FixedUniversalDQLCompactSignSourceFamily.outputDegree sourceSphereCount wrapperDegree

theorem universalDetectorFamily_hgas_iff (input : ℕ) :
    HGASQ universalDetectorFixedDimension universalDetectorFixedDegree
      (universalDetectorFamily.outputCode input) ↔ UniversalHalting.Predicate input :=
  universalDetectorFamily.hgasQ_output_iff_predicate input

theorem universalDetector_fixedPair_sigmaOneComplete :
    SigmaOneComplete (HGASQ universalDetectorFixedDimension universalDetectorFixedDegree) :=
  universalDetectorFamily.fixedPair_sigmaOneComplete

abbrev universalDetectorCofinalDimensionThreshold : ℕ :=
  Veronese.cubicLiftCodeDimension universalDetectorFixedDimension
    (Compiler.FixedUniversalDQLCompactSignSourceFamily.outputHalfDegree
      sourceSphereCount wrapperDegree)

theorem universalDetector_cofinal_sigmaOneComplete
    (N d : ℕ) (hN : universalDetectorCofinalDimensionThreshold ≤ N)
    (hd : Odd d) (hthree : 3 ≤ d) : SigmaOneComplete (HGASQ N d) :=
  universalDetectorFamily.cofinal_sigmaOneComplete N d hN hd hthree

end Stability.Selection
