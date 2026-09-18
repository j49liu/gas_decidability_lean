import HGAS.Arithmetic.UnconditionalMRDP
import HGAS.Compiler.UnconditionalFixedCompactSignSourceFamily
import HGAS.Computability.HGASLanguage
import HGAS.Propagation.CofinalSigmaOne
import HGAS.Wrapper.UnitSphereWrapperComputability
import Mathlib.Tactic

/-!
# Reusable fixed-DQL compact-sign source families

Unlike the older endpoint specialized to one particular DQL presentation,
this structure accepts any fixed-arity DQL family together with a proof
that its solvability is the chosen unary universal-halting predicate.
This small abstraction is what lets a semantics-preserving preprocessing
(such as the nonzero-linear-column augmentation) pass through the final
recursion-theoretic layer without identifying two different DQL systems.
-/

namespace HGAS.Compiler

open HGAS

noncomputable section

variable {eqs vars n k : ℕ}

/-- One effective fixed-resource compact-sign source family for an
arbitrary fixed-arity DQL presentation of universal halting. -/
structure FixedUniversalDQLCompactSignSourceFamily
    (system : ℕ → DQLSystem eqs vars)
    (sourceBlock : Fin n → Fin k)
    [Nonempty
      (UnitSpherePolynomialWrapper.SourceProductSphere sourceBlock)]
    (wrapperDegree : ℕ) where
  system_solvable_iff :
    ∀ input, (system input).Solvable ↔ UniversalHalting.Predicate input
  wrapperDegree_ge_three : 3 ≤ wrapperDegree
  wrapperDegree_odd : wrapperDegree % 2 = 1
  certificate :
    ∀ input : ℕ,
      CompactSignSourceCertificate sourceBlock (system input)
  certificate_degree :
    ∀ input, (certificate input).degree = wrapperDegree
  outputCode : ℕ → PolynomialFieldCode (n + 1)
  outputCode_eq :
    ∀ input, outputCode input = (certificate input).finalFieldCode
  outputCode_computable : Computable outputCode

namespace FixedUniversalDQLCompactSignSourceFamily

variable
    {system : ℕ → DQLSystem eqs vars}
    {sourceBlock : Fin n → Fin k}
    [Nonempty
      (UnitSpherePolynomialWrapper.SourceProductSphere sourceBlock)]
    {wrapperDegree : ℕ}

/-- Canonical constructor from computable finite source syntax. -/
def ofComputableSourceCodes
    (system_solvable_iff :
      ∀ input, (system input).Solvable ↔ UniversalHalting.Predicate input)
    (wrapperDegree : ℕ)
    (wrapperDegree_ge_three : 3 ≤ wrapperDegree)
    (wrapperDegree_odd : wrapperDegree % 2 = 1)
    (certificate :
      ∀ input : ℕ,
        CompactSignSourceCertificate sourceBlock (system input))
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
    FixedUniversalDQLCompactSignSourceFamily
      system sourceBlock wrapperDegree where
  system_solvable_iff := system_solvable_iff
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
    (family :
      FixedUniversalDQLCompactSignSourceFamily
        system sourceBlock wrapperDegree)

include family

/-- Common homogeneous output degree. -/
abbrev outputDegree (k wrapperDegree : ℕ) : ℕ :=
  UnitSpherePolynomialWrapper.targetDegree k wrapperDegree

theorem outputDegree_odd :
    outputDegree k wrapperDegree % 2 = 1 :=
  UnitSpherePolynomialWrapper.targetDegree_odd
    wrapperDegree
    (FixedUniversalDQLCompactSignSourceFamily.wrapperDegree_odd family)

theorem outputCode_isHomogeneous
    (input : ℕ) :
    ∀ j : Fin (n + 1),
      (PolynomialCode.decode
        (FixedUniversalDQLCompactSignSourceFamily.outputCode family input j)
        ).IsHomogeneous
        (outputDegree k wrapperDegree) := by
  rw [FixedUniversalDQLCompactSignSourceFamily.outputCode_eq family input]
  simpa only [CompactSignSourceCertificate.finalFieldCode,
    outputDegree,
    FixedUniversalDQLCompactSignSourceFamily.certificate_degree family input]
    using
    UnitSpherePolynomialWrapper.finalFieldCode_isHomogeneous_of_degreeBounds
        sourceBlock
        (FixedUniversalDQLCompactSignSourceFamily.certificate family input).degree
        (FixedUniversalDQLCompactSignSourceFamily.certificate family input
          ).degree_ge_three
        (FixedUniversalDQLCompactSignSourceFamily.certificate family input
          ).degree_odd
        (FixedUniversalDQLCompactSignSourceFamily.certificate family input
          ).fieldCode
        (FixedUniversalDQLCompactSignSourceFamily.certificate family input
          ).field_degree
        (FixedUniversalDQLCompactSignSourceFamily.certificate family input
          ).rewardCode
        (FixedUniversalDQLCompactSignSourceFamily.certificate family input
          ).reward_degree

theorem outputCode_homogeneous
    (input : ℕ) :
    PolynomialFieldCode.homogeneous
        (outputDegree k wrapperDegree)
        (FixedUniversalDQLCompactSignSourceFamily.outputCode family input) =
      true :=
  (PolynomialFieldCode.homogeneous_eq_true_iff
    (outputDegree k wrapperDegree)
    (FixedUniversalDQLCompactSignSourceFamily.outputCode family input)).2
      (outputCode_isHomogeneous family input)

/-- Exact fixed-pair correctness for the supplied DQL presentation. -/
theorem hgasQ_output_iff_predicate
    (input : ℕ) :
    HGASQ (n + 1) (outputDegree k wrapperDegree)
        (FixedUniversalDQLCompactSignSourceFamily.outputCode family input) ↔
      UniversalHalting.Predicate input := by
  rw [hgasQ_iff_of_homogeneous
    (FixedUniversalDQLCompactSignSourceFamily.outputCode family input)
    (outputCode_homogeneous family input)]
  rw [FixedUniversalDQLCompactSignSourceFamily.outputCode_eq family input]
  exact
    (CompactSignSourceCertificate.finalField_gas_iff_solvable
      (FixedUniversalDQLCompactSignSourceFamily.certificate family input)).trans
        (FixedUniversalDQLCompactSignSourceFamily.system_solvable_iff
          family input)

theorem predicate_manyOneReducible_hgasQ :
    UniversalHalting.Predicate ≤₀
      HGASQ (n + 1) (outputDegree k wrapperDegree) := by
  refine
    ⟨FixedUniversalDQLCompactSignSourceFamily.outputCode family,
      FixedUniversalDQLCompactSignSourceFamily.outputCode_computable family,
      ?_⟩
  intro input
  exact (hgasQ_output_iff_predicate family input).symm

theorem universalHalts_manyOneReducible_hgasQ :
    UniversalHalts ≤₀
      HGASQ (n + 1) (outputDegree k wrapperDegree) :=
  (UniversalHalting.re_manyOneReducible_predicate
      universalHalts_re).trans
    (predicate_manyOneReducible_hgasQ family)

/-- One completed repaired family yields fixed-pair
`Σ⁰₁`-completeness. -/
theorem fixedPair_sigmaOneComplete :
    SigmaOneComplete
      (HGASQ (n + 1) (outputDegree k wrapperDegree)) :=
  sigmaOneComplete_of_universalHalts_reduction
    (hgasQ_re_of_oddDegree
      (n + 1) (outputDegree k wrapperDegree)
      (Nat.odd_iff.mpr (outputDegree_odd family)))
    (universalHalts_manyOneReducible_hgasQ family)

theorem three_le_outputDegree :
    3 ≤ outputDegree k wrapperDegree := by
  have hdegree :=
    FixedUniversalDQLCompactSignSourceFamily.wrapperDegree_ge_three family
  unfold outputDegree
  unfold UnitSpherePolynomialWrapper.targetDegree
  omega

/-- Half-degree parameter used by the effective cubic lift. -/
def outputHalfDegree
    (k wrapperDegree : ℕ) : ℕ :=
  (outputDegree k wrapperDegree - 1) / 2

theorem outputDegree_eq_two_mul_outputHalfDegree_add_one :
    outputDegree k wrapperDegree =
      2 * outputHalfDegree k wrapperDegree + 1 := by
  have hodd :
      Odd (outputDegree k wrapperDegree) :=
    Nat.odd_iff.mpr (outputDegree_odd family)
  obtain ⟨r, hr⟩ := hodd
  unfold outputHalfDegree
  omega

theorem one_le_outputHalfDegree :
    1 ≤ outputHalfDegree k wrapperDegree := by
  have hthree := three_le_outputDegree family
  rw [outputDegree_eq_two_mul_outputHalfDegree_add_one family]
    at hthree
  omega

/-- Cofinal fixed-pair completeness for every sufficiently large
dimension and every odd degree at least three. -/
theorem cofinal_sigmaOneComplete
    (N d : ℕ)
    (hN :
      Veronese.cubicLiftCodeDimension
          (n + 1) (outputHalfDegree k wrapperDegree) ≤ N)
    (hd : Odd d) (hthree : 3 ≤ d) :
    SigmaOneComplete (HGASQ N d) := by
  have hsource :
      UniversalHalts ≤₀
        HGASQ (n + 1)
          (2 * outputHalfDegree k wrapperDegree + 1) := by
    simpa only [
      ← outputDegree_eq_two_mul_outputHalfDegree_add_one family] using
        (universalHalts_manyOneReducible_hgasQ family)
  exact
    HGAS.Propagation.sigmaOneComplete_cofinalFixedPair_of_universalHalts_reduction
        (n + 1) (outputHalfDegree k wrapperDegree) N d
        (by omega)
        (one_le_outputHalfDegree family)
        hsource hN hd hthree

end FixedUniversalDQLCompactSignSourceFamily

end

end HGAS.Compiler
