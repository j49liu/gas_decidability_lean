import HGAS.Compiler.DetectorSourceWrapper
import HGAS.Arithmetic.UnconditionalFixedDQL
import HGAS.Computability.HGASLanguage
import HGAS.Wrapper.UnitSphereWrapperComputability

/-!
# Fixed-resource composition of the detector source and homogeneous wrapper

This file isolates the exact *uniformity* statement needed to turn the
single-instance theorem in `DetectorSourceWrapper` into one fixed-dimension,
fixed-degree many-one reduction.

Fix once and for all:

* an ambient source dimension `n`;
* a number `k` of sphere blocks;
* the assignment `sourceBlock : Fin n → Fin k`; and
* one odd source/wrapper degree `D ≥ 3`.

A `FixedUniversalDetectorSourceFamily sourceBlock D` contains a
`DetectorSourceCertificate` for every member of the already-constructed
fixed-arity universal DQL family.  It also contains one computable map from
the natural-number input to the *final* wrapped sparse polynomial code.
The equality field says that this executable output is exactly the field
whose dynamics are justified by the corresponding semantic certificate.

This is deliberately a certificate interface, not an existence theorem.
In particular, an inhabitant must supply:

* every source vector field, reward, compact flow, detector factor, and
  invariant-measure statement required by `DetectorSourceCertificate`;
* a proof that the same degree `D` is used for every input; and
* a genuinely computable final-code map together with its exactness proof.

Thus none of the missing source-compilation work is hidden behind a choice
operator.  Once an inhabitant is constructed, however, all remaining
composition is automatic: every output is homogeneous at the one advertised
degree, and membership in the corresponding `HGASQ` language is equivalent
to universal halting.
-/

namespace HGAS

open Function

noncomputable section

namespace Compiler

variable {n k : ℕ}

/-- Apply the verified homogeneous wrapper pointwise to a family of source
field/reward codes.  This is the canonical executable output map used by
the constructor below. -/
def wrappedSourceOutputCode
    (sourceBlock : Fin n → Fin k) (wrapperDegree : ℕ)
    (sourceCode :
      ℕ → PolynomialFieldCode n × PolynomialCode n) :
    ℕ → PolynomialFieldCode (n + 1) :=
  fun input ↦
    UnitSpherePolynomialWrapper.finalFieldCode sourceBlock wrapperDegree
      (sourceCode input).1 (sourceCode input).2

/-- A computable source-code family remains computable after the verified
homogeneous wrapper is applied. -/
theorem wrappedSourceOutputCode_computable
    (sourceBlock : Fin n → Fin k) (wrapperDegree : ℕ)
    (sourceCode :
      ℕ → PolynomialFieldCode n × PolynomialCode n)
    (hsourceCode : Computable sourceCode) :
    Computable
      (wrappedSourceOutputCode sourceBlock wrapperDegree sourceCode) :=
  (UnitSpherePolynomialWrapper.finalFieldCode_computable
    sourceBlock wrapperDegree).comp hsourceCode

/-- A fixed-resource, effective family of detector-source certificates for
the unconditional universal-halting DQL family.

The source layout and degree are parameters of the structure, hence are
literally independent of `input`.  The family does not claim to exist:
constructing an inhabitant is precisely the remaining uniform polynomial
source-compiler problem. -/
structure FixedUniversalDetectorSourceFamily
    (sourceBlock : Fin n → Fin k)
    [Nonempty (UnitSpherePolynomialWrapper.SourceProductSphere sourceBlock)]
    (wrapperDegree : ℕ) where
  /-- The fixed source degree meets the wrapper's lower bound. -/
  wrapperDegree_ge_three : 3 ≤ wrapperDegree
  /-- The fixed source degree has the parity required by the wrapper. -/
  wrapperDegree_odd : wrapperDegree % 2 = 1
  /-- A complete semantic source certificate for every universal input. -/
  certificate :
    ∀ input : ℕ,
      DetectorSourceCertificate sourceBlock
        (UniversalHalting.unconditionalUniversalHaltingFixedDQL input)
  /-- Every certificate uses the same advertised source degree. -/
  certificate_degree :
    ∀ input : ℕ, (certificate input).degree = wrapperDegree
  /-- The actual finite-code compiler output. -/
  outputCode : ℕ → PolynomialFieldCode (n + 1)
  /-- The executable output is exactly the semantically certified wrapper
  output, not merely a dynamically equivalent field. -/
  outputCode_eq :
    ∀ input : ℕ,
      outputCode input = (certificate input).finalFieldCode
  /-- The final sparse-code map is computable uniformly in the input. -/
  outputCode_computable : Computable outputCode

namespace FixedUniversalDetectorSourceFamily

/-- Canonical constructor from a computable family of source field/reward
codes.

The equality hypothesis is intentionally literal.  It prevents the
semantic certificates from naming one source field while the executable
compiler silently emits another.  The final output map and its computability
proof are then obtained by direct composition with the already-verified
wrapper compiler. -/
def ofComputableSourceCodes
    {sourceBlock : Fin n → Fin k}
    [Nonempty (UnitSpherePolynomialWrapper.SourceProductSphere sourceBlock)]
    (wrapperDegree : ℕ)
    (wrapperDegree_ge_three : 3 ≤ wrapperDegree)
    (wrapperDegree_odd : wrapperDegree % 2 = 1)
    (certificate :
      ∀ input : ℕ,
        DetectorSourceCertificate sourceBlock
          (UniversalHalting.unconditionalUniversalHaltingFixedDQL input))
    (certificate_degree :
      ∀ input : ℕ, (certificate input).degree = wrapperDegree)
    (sourceCode :
      ℕ → PolynomialFieldCode n × PolynomialCode n)
    (sourceCode_computable : Computable sourceCode)
    (sourceCode_eq_certificate :
      ∀ input : ℕ,
        sourceCode input =
          ((certificate input).fieldCode,
            (certificate input).rewardCode)) :
    FixedUniversalDetectorSourceFamily sourceBlock wrapperDegree where
  wrapperDegree_ge_three := wrapperDegree_ge_three
  wrapperDegree_odd := wrapperDegree_odd
  certificate := certificate
  certificate_degree := certificate_degree
  outputCode :=
    wrappedSourceOutputCode sourceBlock wrapperDegree sourceCode
  outputCode_eq := by
    intro input
    simp only [wrappedSourceOutputCode,
      sourceCode_eq_certificate input,
      DetectorSourceCertificate.finalFieldCode,
      certificate_degree input]
  outputCode_computable :=
    wrappedSourceOutputCode_computable sourceBlock wrapperDegree
      sourceCode sourceCode_computable

variable
    {sourceBlock : Fin n → Fin k}
    [Nonempty (UnitSpherePolynomialWrapper.SourceProductSphere sourceBlock)]
    {wrapperDegree : ℕ}
    (family :
      FixedUniversalDetectorSourceFamily sourceBlock wrapperDegree)

/-- The single homogeneous degree advertised for every compiled output. -/
abbrev outputDegree (k wrapperDegree : ℕ) : ℕ :=
  UnitSpherePolynomialWrapper.targetDegree k wrapperDegree

/-- The advertised output degree is odd.  This is useful when the resulting
fixed language is propagated through degree-raising constructions. -/
theorem outputDegree_odd
    (family :
      FixedUniversalDetectorSourceFamily sourceBlock wrapperDegree) :
    outputDegree k wrapperDegree % 2 = 1 :=
  UnitSpherePolynomialWrapper.targetDegree_odd
    wrapperDegree family.wrapperDegree_odd

/-- Every coordinate of every compiled field is homogeneous at the same
fixed degree.

The proof applies the concrete wrapper's syntactic degree theorem to the
certificate for `input`; `certificate_degree` then identifies that
certificate's degree with the one fixed family degree. -/
theorem outputCode_isHomogeneous
    (input : ℕ) :
    ∀ j : Fin (n + 1),
      (PolynomialCode.decode (family.outputCode input j)).IsHomogeneous
        (outputDegree k wrapperDegree) := by
  rw [family.outputCode_eq input]
  simpa only [DetectorSourceCertificate.finalFieldCode, outputDegree,
    family.certificate_degree input] using
    UnitSpherePolynomialWrapper.finalFieldCode_isHomogeneous_of_degreeBounds
      sourceBlock (family.certificate input).degree
      (family.certificate input).degree_ge_three
      (family.certificate input).degree_odd
      (family.certificate input).fieldCode
      (family.certificate input).field_degree
      (family.certificate input).rewardCode
      (family.certificate input).reward_degree

/-- Boolean homogeneity validation accepts every emitted code.  This is the
exact syntactic validity conjunct appearing in the raw-code language
`HGASQ`; it is not inferred merely from the realized vector field. -/
theorem outputCode_homogeneous
    (input : ℕ) :
    PolynomialFieldCode.homogeneous (outputDegree k wrapperDegree)
        (family.outputCode input) =
      true :=
  (PolynomialFieldCode.homogeneous_eq_true_iff
    (outputDegree k wrapperDegree) (family.outputCode input)).2
      (family.outputCode_isHomogeneous input)

/-- End-to-end correctness for the fixed resource pair.

The first step discharges `HGASQ`'s Boolean syntax check.  The source-wrapper
composition theorem then converts GAS of the emitted field to solvability of
the fixed DQL instance, and the unconditional arithmetic construction
converts that solvability statement to universal halting. -/
theorem hgasQ_output_iff_predicate
    (input : ℕ) :
    HGASQ (n + 1) (outputDegree k wrapperDegree)
        (family.outputCode input) ↔
      UniversalHalting.Predicate input := by
  rw [hgasQ_iff_of_homogeneous
    (family.outputCode input) (family.outputCode_homogeneous input)]
  rw [family.outputCode_eq input]
  exact
    (DetectorSourceCertificate.finalField_gas_iff_solvable
      (family.certificate input)).trans
        (UniversalHalting.unconditionalUniversalHaltingFixedDQL_solvable_iff
          input)

/-- The executable output map is a many-one reduction from the unary
universal-halting predicate to one fixed `HGASQ` language. -/
theorem predicate_manyOneReducible_hgasQ
    (family :
      FixedUniversalDetectorSourceFamily sourceBlock wrapperDegree) :
    UniversalHalting.Predicate ≤₀
      HGASQ (n + 1) (outputDegree k wrapperDegree) := by
  refine ⟨family.outputCode, family.outputCode_computable, ?_⟩
  intro input
  exact (family.hgasQ_output_iff_predicate input).symm

/-- Mathlib's standard universal partial-recursive-code halting language
also reduces to the same fixed `HGASQ` language. -/
theorem universalHalts_manyOneReducible_hgasQ
    (family :
      FixedUniversalDetectorSourceFamily sourceBlock wrapperDegree) :
    UniversalHalts ≤₀
      HGASQ (n + 1) (outputDegree k wrapperDegree) :=
  (UniversalHalting.re_manyOneReducible_predicate universalHalts_re).trans
    family.predicate_manyOneReducible_hgasQ

end FixedUniversalDetectorSourceFamily

end Compiler

end

end HGAS
