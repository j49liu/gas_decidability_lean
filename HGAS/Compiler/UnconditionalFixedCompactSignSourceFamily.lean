import HGAS.Arithmetic.UnconditionalFixedDQL
import HGAS.Compiler.CompactSignSourceWrapper
import HGAS.Computability.HGASLanguage
import HGAS.Wrapper.UnitSphereWrapperComputability

/-!
# Fixed-resource compact-sign source families

This is the faithful fixed-resource endpoint for the paper's lower-bound
compiler.  The source layout and wrapper degree are fixed once and for
all.  For every unary universal-halting input, the family supplies:

* a `CompactSignSourceCertificate` for the corresponding fixed-arity DQL
  system;
* the literal finite source field/reward codes used by that certificate;
* one computable map producing the final homogeneous field code.

The semantic certificate may use modular functions, invariant measures,
and compactness in its proof.  The output map cannot: its computability is
obtained solely by composing finite sparse-code compilers.  This separation
is the formal effectivity firewall.

The older unaugmented specialized structure below deliberately carries no
unconditional existence theorem.  The outside-closure module
`NormalizedCorrectedUnconditionalFamilyFromGap` can construct an inhabitant
conditionally from a gap certificate for every input, but the public
endpoint neither supplies that old premise nor uses the resulting
specialization.  Instead it first applies the nonzero-column DQL
augmentation and inhabits the distinct generic structure
`FixedUniversalDQLCompactSignSourceFamily` in
`NormalizedCorrectedAugmentedEffectiveFamily`.
-/

namespace HGAS

noncomputable section

namespace Compiler

variable {n k : ℕ}

/-- Pointwise application of the verified homogeneous wrapper. -/
def wrappedCompactSignSourceOutputCode
    (sourceBlock : Fin n → Fin k) (wrapperDegree : ℕ)
    (sourceCode :
      ℕ → PolynomialFieldCode n × PolynomialCode n) :
    ℕ → PolynomialFieldCode (n + 1) :=
  fun input ↦
    UnitSpherePolynomialWrapper.finalFieldCode
      sourceBlock wrapperDegree
      (sourceCode input).1 (sourceCode input).2

theorem wrappedCompactSignSourceOutputCode_computable
    (sourceBlock : Fin n → Fin k) (wrapperDegree : ℕ)
    (sourceCode :
      ℕ → PolynomialFieldCode n × PolynomialCode n)
    (hsourceCode : Computable sourceCode) :
    Computable
      (wrappedCompactSignSourceOutputCode
        sourceBlock wrapperDegree sourceCode) :=
  (UnitSpherePolynomialWrapper.finalFieldCode_computable
    sourceBlock wrapperDegree).comp hsourceCode

/-- One effective fixed-resource family implementing the compact sign
dichotomy for the universal fixed-DQL family. -/
structure FixedUniversalCompactSignSourceFamily
    (sourceBlock : Fin n → Fin k)
    [Nonempty
      (UnitSpherePolynomialWrapper.SourceProductSphere sourceBlock)]
    (wrapperDegree : ℕ) where
  wrapperDegree_ge_three : 3 ≤ wrapperDegree
  wrapperDegree_odd : wrapperDegree % 2 = 1
  certificate :
    ∀ input : ℕ,
      CompactSignSourceCertificate sourceBlock
        (UniversalHalting.unconditionalUniversalHaltingFixedDQL input)
  certificate_degree :
    ∀ input, (certificate input).degree = wrapperDegree
  outputCode : ℕ → PolynomialFieldCode (n + 1)
  outputCode_eq :
    ∀ input, outputCode input = (certificate input).finalFieldCode
  outputCode_computable : Computable outputCode

namespace FixedUniversalCompactSignSourceFamily

/-- Canonical family constructor from computable source field/reward
syntax and semantically matching certificates. -/
def ofComputableSourceCodes
    {sourceBlock : Fin n → Fin k}
    [Nonempty
      (UnitSpherePolynomialWrapper.SourceProductSphere sourceBlock)]
    (wrapperDegree : ℕ)
    (wrapperDegree_ge_three : 3 ≤ wrapperDegree)
    (wrapperDegree_odd : wrapperDegree % 2 = 1)
    (certificate :
      ∀ input : ℕ,
        CompactSignSourceCertificate sourceBlock
          (UniversalHalting.unconditionalUniversalHaltingFixedDQL input))
    (certificate_degree :
      ∀ input, (certificate input).degree = wrapperDegree)
    (sourceCode :
      ℕ → PolynomialFieldCode n × PolynomialCode n)
    (sourceCode_computable : Computable sourceCode)
    (sourceCode_eq_certificate :
      ∀ input,
        sourceCode input =
          ((certificate input).fieldCode,
            (certificate input).rewardCode)) :
    FixedUniversalCompactSignSourceFamily
      sourceBlock wrapperDegree where
  wrapperDegree_ge_three := wrapperDegree_ge_three
  wrapperDegree_odd := wrapperDegree_odd
  certificate := certificate
  certificate_degree := certificate_degree
  outputCode :=
    wrappedCompactSignSourceOutputCode
      sourceBlock wrapperDegree sourceCode
  outputCode_eq := by
    intro input
    simp only [wrappedCompactSignSourceOutputCode,
      sourceCode_eq_certificate input,
      CompactSignSourceCertificate.finalFieldCode,
      certificate_degree input]
  outputCode_computable :=
    wrappedCompactSignSourceOutputCode_computable
      sourceBlock wrapperDegree sourceCode sourceCode_computable

variable
    {sourceBlock : Fin n → Fin k}
    [Nonempty
      (UnitSpherePolynomialWrapper.SourceProductSphere sourceBlock)]
    {wrapperDegree : ℕ}
    (family :
      FixedUniversalCompactSignSourceFamily
        sourceBlock wrapperDegree)

/-- Common homogeneous output degree. -/
abbrev outputDegree (k wrapperDegree : ℕ) : ℕ :=
  UnitSpherePolynomialWrapper.targetDegree k wrapperDegree

theorem outputDegree_odd
    (family :
      FixedUniversalCompactSignSourceFamily
        sourceBlock wrapperDegree) :
    outputDegree k wrapperDegree % 2 = 1 :=
  UnitSpherePolynomialWrapper.targetDegree_odd
    wrapperDegree family.wrapperDegree_odd

/-- Every emitted coordinate is homogeneous at the one fixed advertised
degree. -/
theorem outputCode_isHomogeneous
    (input : ℕ) :
    ∀ j : Fin (n + 1),
      (PolynomialCode.decode (family.outputCode input j)).IsHomogeneous
        (outputDegree k wrapperDegree) := by
  rw [family.outputCode_eq input]
  simpa only [CompactSignSourceCertificate.finalFieldCode,
    outputDegree, family.certificate_degree input] using
    UnitSpherePolynomialWrapper.finalFieldCode_isHomogeneous_of_degreeBounds
        sourceBlock (family.certificate input).degree
        (family.certificate input).degree_ge_three
        (family.certificate input).degree_odd
        (family.certificate input).fieldCode
        (family.certificate input).field_degree
        (family.certificate input).rewardCode
        (family.certificate input).reward_degree

theorem outputCode_homogeneous
    (input : ℕ) :
    PolynomialFieldCode.homogeneous
        (outputDegree k wrapperDegree)
        (family.outputCode input) = true :=
  (PolynomialFieldCode.homogeneous_eq_true_iff
    (outputDegree k wrapperDegree)
    (family.outputCode input)).2
      (family.outputCode_isHomogeneous input)

/-- Exact fixed-pair correctness. -/
theorem hgasQ_output_iff_predicate
    (input : ℕ) :
    HGASQ (n + 1) (outputDegree k wrapperDegree)
        (family.outputCode input) ↔
      UniversalHalting.Predicate input := by
  rw [hgasQ_iff_of_homogeneous
    (family.outputCode input)
    (family.outputCode_homogeneous input)]
  rw [family.outputCode_eq input]
  exact
    (CompactSignSourceCertificate.finalField_gas_iff_solvable
      (family.certificate input)).trans
        (UniversalHalting.unconditionalUniversalHaltingFixedDQL_solvable_iff
            input)

/-- The executable output is a many-one reduction from the selected unary
universal-halting predicate. -/
theorem predicate_manyOneReducible_hgasQ
    (family :
      FixedUniversalCompactSignSourceFamily
        sourceBlock wrapperDegree) :
    UniversalHalting.Predicate ≤₀
      HGASQ (n + 1) (outputDegree k wrapperDegree) := by
  refine
    ⟨family.outputCode, family.outputCode_computable, ?_⟩
  intro input
  exact (family.hgasQ_output_iff_predicate input).symm

/-- Mathlib's standard universal partial-recursive-code halting language
reduces to the same fixed HGAS language. -/
theorem universalHalts_manyOneReducible_hgasQ
    (family :
      FixedUniversalCompactSignSourceFamily
        sourceBlock wrapperDegree) :
    UniversalHalts ≤₀
      HGASQ (n + 1) (outputDegree k wrapperDegree) :=
  (UniversalHalting.re_manyOneReducible_predicate
      universalHalts_re).trans
    family.predicate_manyOneReducible_hgasQ

end FixedUniversalCompactSignSourceFamily

end Compiler

end

end HGAS
