# Formalization ledger

Current status: **the unconditional augmented fixed-pair theorem and its
cofinal cubic consequence are complete and kernel checked**.

This ledger records the public theorem chain in the current worktree.  It
supersedes the early-development checklist that described the
modular/Jacobi-to-compiler integration as open.

The mathematical language is

```lean
HGASQ n d : PolynomialFieldCode n → Prop
```

from `HGAS/Computability/HGASLanguage.lean`.  Its inputs are finite rational
codes for polynomial vector fields on `ℝⁿ`, and syntactic homogeneity of
the requested degree is part of the language definition.

## Headline theorems

The final endpoint is
`HGAS/Arithmetic/NormalizedCorrectedAugmentedEffectiveFamily.lean`, which is
imported by the public root `HGAS.lean`.

It defines three fixed natural-number expressions:

```lean
HGAS.NormalizedCorrectedAugmentedEffectiveFamily.fixedDimension
HGAS.NormalizedCorrectedAugmentedEffectiveFamily.fixedDegree
HGAS.NormalizedCorrectedAugmentedEffectiveFamily.cofinalDimensionThreshold
```

and proves:

```lean
fixedPair_sigmaOneComplete :
  SigmaOneComplete (HGASQ fixedDimension fixedDegree)

fixedPair_not_computable :
  ¬ ComputablePred (HGASQ fixedDimension fixedDegree)

fixedPair_complement_not_re :
  ¬ REPred (fun code ↦ ¬ HGASQ fixedDimension fixedDegree code)

fixedDimension_pos :
  0 < fixedDimension

fixedDegree_odd :
  Odd fixedDegree

fixedDegree_ge_three :
  3 ≤ fixedDegree

cofinal_sigmaOneComplete
    (N d : ℕ)
    (hN : cofinalDimensionThreshold ≤ N)
    (hd : Odd d)
    (hthree : 3 ≤ d) :
  SigmaOneComplete (HGASQ N d)

cubic_sigmaOneComplete
    (N : ℕ)
    (hN : cofinalDimensionThreshold ≤ N) :
  SigmaOneComplete (HGASQ N 3)

cubic_not_computable
    (N : ℕ)
    (hN : cofinalDimensionThreshold ≤ N) :
  ¬ ComputablePred (HGASQ N 3)

cubic_complement_not_re
    (N : ℕ)
    (hN : cofinalDimensionThreshold ≤ N) :
  ¬ REPred (fun code ↦ ¬ HGASQ N 3 code)
```

Thus the formalization proves:

1. `Σ⁰₁`-completeness, and hence undecidability, for one fixed dimension
   and one fixed odd degree;
2. `Σ⁰₁`-completeness for every fixed odd degree at least three in every
   dimension beyond one fixed threshold; and
3. in particular, `Σ⁰₁`-completeness of cubic homogeneous GAS in every
   sufficiently large fixed dimension.

These are unconditional Lean theorems: the endpoint takes no unproved
classification proposition, compiler certificate, or semantic gap as a
hypothesis.

## What is not claimed

The present result does **not** settle `HGASQ 3 3`.

In particular:

- `fixedDimension` is not proved equal to `3`;
- `fixedDegree` is proved odd and at least three, but is not proved equal
  to `3`;
- `cubic_sigmaOneComplete` requires
  `cofinalDimensionThreshold ≤ N`; and
- there is no theorem establishing
  `cofinalDimensionThreshold ≤ 3`.

Consequently, this development proves neither decidability nor
`Σ⁰₁`-hardness for the specific three-dimensional cubic language
`HGASQ 3 3`.  That low-dimensional problem remains separate from the
completed cofinal theorem.

The word “cofinal” is important: the cubic result applies to every
*sufficiently large* fixed dimension, not to every positive dimension.

## Trust and build status

The project is pinned to Lean/Mathlib 4.30.0 and uses:

```toml
warningAsError = true
```

The authoritative full build is:

```bash
lake build
```

It currently succeeds, including the root `HGAS.lean` import and the
completed endpoint.

The source audit

```bash
rg -n '(^|[^A-Za-z])(sorry|admit)\b|^\s*axiom\b|^\s*unsafe\b' \
  HGAS HGAS.lean --glob '*.lean'
```

finds no proof placeholder, project axiom declaration, or unsafe
declaration.  Incidental English words such as “admit” or “axiom-free” in
module comments are not declarations.

Direct `#print axioms` checks on

```text
NormalizedCorrectedAugmentedEffectiveFamily.gap
NormalizedCorrectedAugmentedEffectiveFamily.family
NormalizedCorrectedAugmentedEffectiveFamily.fixedPair_sigmaOneComplete
NormalizedCorrectedAugmentedEffectiveFamily.fixedPair_not_computable
NormalizedCorrectedAugmentedEffectiveFamily.fixedPair_complement_not_re
NormalizedCorrectedAugmentedEffectiveFamily.cofinal_sigmaOneComplete
NormalizedCorrectedAugmentedEffectiveFamily.cubic_sigmaOneComplete
NormalizedCorrectedAugmentedEffectiveFamily.cubic_not_computable
NormalizedCorrectedAugmentedEffectiveFamily.cubic_complement_not_re
```

report only:

```text
propext
Classical.choice
Quot.sound
```

These are the ordinary Lean/Mathlib logical foundations used by the
development.  No project-defined axiom appears in the dependency closure
of the headline result.

## Fixed constants and the meaning of computability

The fixed universal Diophantine representation is selected from a proved
MRDP existence theorem.  In particular,
`UniversalHalting.unconditionalUniversalHaltingRepresentation` is a
`noncomputable def`: classical choice selects one finite representative
once and for all.

As a consequence, the following are fixed closed natural-number
expressions in Lean but are not currently reducible numerical literals:

- the universal DQL equation and variable counts;
- the augmented source dimension;
- the fixed wrapper and output degrees; and
- the cofinal cubic dimension threshold.

The formalization proves `Computable` for the specialization and source-code
maps in Mathlib's recursion-theoretic sense.  This is exactly the
effectivity required for a many-one reduction: there exists a Turing
computation of the finite output code, uniformly in the input, after the
once-and-for-all fixed representation has been selected.

It does **not** follow that Lean can presently evaluate

```lean
#eval HGAS.NormalizedCorrectedAugmentedUniversalResources.sourceCode 0
```

to a concrete printed list.  The current definitions retain the classical
choice of the universal polynomial and its dimensions, so that expression
depends on noncomputable constants.  No numerical value for
`fixedDimension`, `fixedDegree`, or `cofinalDimensionThreshold` is claimed.
This extraction caveat does not weaken the proved `Computable` maps or the
many-one reductions.

## End-to-end theorem/module crosswalk

Every row below is complete (`[x]`) on the dependency path of the headline
theorem.

| Stage | Principal declaration | Module | Status |
|---|---|---|---|
| Rational fixed-pair GAS language | `HGASQ` | `HGAS/Computability/HGASLanguage.lean` | `[x]` |
| Homogeneous angular characterization | `globallyAsymptoticallyStable_iff_maximalAngularAverage_neg` | `HGAS/Wrapper/AngularAverageGAS.lean` | `[x]` |
| Odd-degree c.e. upper bound | `hgasQ_re_of_oddDegree` | `HGAS/Lyapunov/RationalHomogeneousConverse.lean` | `[x]` |
| Primitive-recursive MRDP closure | `UniversalHalting.binaryPrimitiveRecursiveRelationsAreDiophantine` | `HGAS/Arithmetic/UnconditionalMRDP.lean` | `[x]` |
| Fixed-arity DQL source | `UniversalHalting.unconditionalUniversalHaltingFixedDQL_solvable_iff` | `HGAS/Arithmetic/UnconditionalFixedDQL.lean` | `[x]` |
| Fixed-DQL `Σ⁰₁`-completeness | `UniversalHalting.unconditionalFixedDQLSolvability_sigmaOneComplete` | `HGAS/Arithmetic/UnconditionalFixedDQL.lean` | `[x]` |
| Solvability-preserving linear-column repair | `DQLNonzeroLinearAugmentation.augment_solvable_iff` | `HGAS/Arithmetic/DQLNonzeroLinearAugmentation.lean` | `[x]` |
| Nonzero linear column in every augmented variable | `DQLNonzeroLinearAugmentation.augment_hasNonzeroLinearColumn` | `HGAS/Arithmetic/DQLNonzeroLinearAugmentation.lean` | `[x]` |
| Effective augmentation | `DQLNonzeroLinearAugmentation.augment_computable` | `HGAS/Arithmetic/DQLNonzeroLinearAugmentation.lean` | `[x]` |
| Augmented universal semantics | `UniversalHalting.augmentedUniversalHaltingFixedDQL_solvable_iff` | `HGAS/Arithmetic/NormalizedCorrectedAugmentedUniversalResources.lean` | `[x]` |
| Fixed augmented dimensions and degrees | `NormalizedCorrectedAugmentedUniversalResources.instance_wrapperDegree_eq` | `HGAS/Arithmetic/NormalizedCorrectedAugmentedUniversalResources.lean` | `[x]` |
| Computable normalized source syntax | `NormalizedCorrectedAugmentedUniversalResources.sourceCode_computable` | `HGAS/Arithmetic/NormalizedCorrectedAugmentedUniversalResources.lean` | `[x]` |
| Canonical theta output on every selected orbit | `NormalizedCorrectedEffectiveCanonicalThetaOutputs.hasCanonicalThetaOutputs` | `HGAS/Arithmetic/NormalizedCorrectedEffectiveCanonicalThetaOutputs.lean` | `[x]` |
| No-instance positive finite graph | `NormalizedCorrectedEffectiveNoInstanceFiniteGraph.finite_graph` | `HGAS/Arithmetic/NormalizedCorrectedEffectiveNoInstanceFiniteGraph.lean` | `[x]` |
| Solvable-instance nonzero drift mean | `NormalizedCorrectedEffectiveNonzeroMeanFromTheta.not_conditionalBaseDriftZero_of_solvable` | `HGAS/Arithmetic/NormalizedCorrectedEffectiveNonzeroMeanFromTheta.lean` | `[x]` |
| Two-sided semantic gap | `NormalizedCorrectedEffectiveGapFromCanonicalTheta.gapOfCanonicalThetaOutputs` | `HGAS/Arithmetic/NormalizedCorrectedEffectiveGapFromCanonicalTheta.lean` | `[x]` |
| Literal source-code/certificate equality | `NormalizedCorrectedAugmentedFamilyFromGap.sourceCode_eq_certificateOfGap` | `HGAS/Arithmetic/NormalizedCorrectedAugmentedFamilyFromGap.lean` | `[x]` |
| Fixed-resource family from gaps | `NormalizedCorrectedAugmentedFamilyFromGap.familyOfGaps` | `HGAS/Arithmetic/NormalizedCorrectedAugmentedFamilyFromGap.lean` | `[x]` |
| Exact compiled correctness | `Compiler.FixedUniversalDQLCompactSignSourceFamily.hgasQ_output_iff_predicate` | `HGAS/Compiler/FixedUniversalDQLCompactSignSourceFamily.lean` | `[x]` |
| Generic fixed-pair completeness | `Compiler.FixedUniversalDQLCompactSignSourceFamily.fixedPair_sigmaOneComplete` | `HGAS/Compiler/FixedUniversalDQLCompactSignSourceFamily.lean` | `[x]` |
| Generic cofinal propagation | `Compiler.FixedUniversalDQLCompactSignSourceFamily.cofinal_sigmaOneComplete` | `HGAS/Compiler/FixedUniversalDQLCompactSignSourceFamily.lean` | `[x]` |
| Unconditional semantic gap | `NormalizedCorrectedAugmentedEffectiveFamily.gap` | `HGAS/Arithmetic/NormalizedCorrectedAugmentedEffectiveFamily.lean` | `[x]` |
| Unconditional computable family | `NormalizedCorrectedAugmentedEffectiveFamily.family` | `HGAS/Arithmetic/NormalizedCorrectedAugmentedEffectiveFamily.lean` | `[x]` |
| Final fixed-pair theorem | `NormalizedCorrectedAugmentedEffectiveFamily.fixedPair_sigmaOneComplete` | `HGAS/Arithmetic/NormalizedCorrectedAugmentedEffectiveFamily.lean` | `[x]` |
| Fixed-pair complement is not c.e. | `NormalizedCorrectedAugmentedEffectiveFamily.fixedPair_complement_not_re` | `HGAS/Arithmetic/NormalizedCorrectedAugmentedEffectiveFamily.lean` | `[x]` |
| Final cofinal odd-degree theorem | `NormalizedCorrectedAugmentedEffectiveFamily.cofinal_sigmaOneComplete` | `HGAS/Arithmetic/NormalizedCorrectedAugmentedEffectiveFamily.lean` | `[x]` |
| Final sufficiently-large-dimension cubic theorem | `NormalizedCorrectedAugmentedEffectiveFamily.cubic_sigmaOneComplete` | `HGAS/Arithmetic/NormalizedCorrectedAugmentedEffectiveFamily.lean` | `[x]` |
| Cofinal cubic complement is not c.e. | `NormalizedCorrectedAugmentedEffectiveFamily.cubic_complement_not_re` | `HGAS/Arithmetic/NormalizedCorrectedAugmentedEffectiveFamily.lean` | `[x]` |

## Mathematical dependency chain

### 1. The c.e. upper bound

`HGASQ n d` checks syntactic homogeneity and asks whether the realized
rational polynomial field is globally asymptotically stable at the origin.
For odd `d`,
`HGAS/Lyapunov/RationalHomogeneousConverse.lean` proves
`hgasQ_re_of_oddDegree`: the language is recursively enumerable.  This is
the upper half of every `SigmaOneComplete` endpoint.

The reusable dynamics behind this layer include homogeneous scaling,
forward completeness, invariant measures, uniform negative orbit blocks,
and the maximal invariant angular average.  Their public synthesis is
`globallyAsymptoticallyStable_iff_maximalAngularAverage_neg`.

### 2. Universal halting to one fixed DQL type

`HGAS/Arithmetic/UnconditionalMRDP.lean` closes the formerly parameterized
MRDP interface with
`binaryPrimitiveRecursiveRelationsAreDiophantine`.  The resulting fixed
universal polynomial is compiled to a fixed-row, fixed-variable
quadratic-linear Diophantine system in
`HGAS/Arithmetic/UnconditionalFixedDQL.lean`.

The detector requires every variable to occur in a nonzero linear column.
`DQLNonzeroLinearAugmentation.augment` duplicates every variable and adds
the equations

```text
x_j - y_j = 0.
```

The transformation preserves and reflects integer solvability, makes both
the old and duplicate columns visibly nonzero, and is primitive recursive.
The augmented universal family therefore still represents the same unary
universal-halting predicate with fixed arities.

### 3. Canonical normalized detector

The normalized-corrected compiler combines:

- prime-radical controller clocks;
- physical detector phases;
- canonical theta coefficients;
- a three-moment rigidity argument;
- the DQL detector Fourier series;
- compact source charts; and
- an accumulator drift and reward.

The all-orbit endpoint
`NormalizedCorrectedEffectiveCanonicalThetaOutputs.hasCanonicalThetaOutputs`
uses the nonzero-linear-column property delivered by the augmentation.  It
identifies the selected drift outputs with the required canonical theta
series on every selected bidirectional validity orbit.

The main reusable modules immediately upstream include:

- `HGAS/Arithmetic/NormalizedCorrectedEffectiveColumnFrequencyIrrational.lean`;
- `HGAS/Arithmetic/CanonicalDetectorThetaQuadraticGeometric.lean`;
- `HGAS/Arithmetic/NormalizedCorrectedFixedDetectorThreeMomentTargetOutput.lean`;
- `HGAS/Modular/JacobiThreeMomentTargetRigidity.lean`; and
- `HGAS/Modular/QuadraticGeometricSequence.lean`.

### 4. The two semantic sides of the gap

For a nonsolvable DQL instance,
`NormalizedCorrectedEffectiveNoInstanceFiniteGraph.finite_graph` constructs
an invariant finite graph with a uniform positive reward gap.  Its proof
uses the explicit prime-controller orbit-closure model, the full normalized
drift Fourier expansion, radical small-divisor bounds, the effective
primitive gain, and a positive lower bound for the canonical central chart.

For a solvable instance,
`NormalizedCorrectedEffectiveNonzeroMeanFromTheta.not_conditionalBaseDriftZero_of_solvable`
shows that an ergodic invariant measure with positive finite-interior mass
cannot have every conditional base-drift mean equal to zero.  Otherwise
recurrence supplies a selected bidirectional validity orbit, and its
canonical theta output contradicts the solvable detector mean theorem.

`NormalizedCorrectedEffectiveGapFromCanonicalTheta.gapOfCanonicalThetaOutputs`
joins these branches into the exact
`CanonicalCompactAccumulatorGap` required by the compact accumulator
wrapper.

### 5. The effectivity firewall and homogeneous wrapper

The semantic certificate may contain classically selected invariant
measures and orbit data.  The emitted program must not compute from those
objects.

`NormalizedCorrectedAugmentedFamilyFromGap.familyOfGaps` enforces that
separation:

- semantic certificates prove the GAS equivalence;
- `NormalizedCorrectedAugmentedUniversalResources.sourceCode` supplies the
  finite field and reward syntax;
- `sourceCode_computable` proves the syntax map computable; and
- `sourceCode_eq_certificateOfGap` proves, definitionally, that the emitted
  syntax is exactly the syntax stored in the certificate.

The reusable structure
`Compiler.FixedUniversalDQLCompactSignSourceFamily` then applies the
product-of-spheres homogeneous wrapper and proves
`hgasQ_output_iff_predicate`.  The output is homogeneous at one fixed odd
degree, its code map is computable, and its GAS semantics are exactly the
universal-halting predicate.

### 6. Fixed-pair completeness and cubic propagation

`NormalizedCorrectedAugmentedEffectiveFamily.gap` instantiates the gap for
every augmented universal input.  `family` packages these instances into
the completed fixed-resource family.  The fixed-pair lower bound is
combined with `hgasQ_re_of_oddDegree`, yielding
`fixedPair_sigmaOneComplete`.

The effective Veronese cubic lift and odd-degree/dimension padding are
implemented principally in:

- `HGAS/Computability/CubicLiftEffectiveGain.lean`;
- `HGAS/Computability/CubicLiftCodeCompiler.lean`;
- `HGAS/Propagation/DegreePaddingGAS.lean`;
- `HGAS/Propagation/DegreePaddingCode.lean`;
- `HGAS/Propagation/CofinalFixedPairReduction.lean`; and
- `HGAS/Propagation/CofinalSigmaOne.lean`.

They preserve GAS exactly, preserve finite-code computability, and turn the
one fixed-pair reduction into `cofinal_sigmaOneComplete`.  Specializing the
target degree to `3` gives `cubic_sigmaOneComplete`.

## Historical interfaces retained in the tree

The development deliberately retains several structures and conditional
theorems that were useful while the proof was assembled.  Examples include
the generic `CanonicalCompactAccumulatorGap`, the older
`FixedUniversalCompactSignSourceFamily`, and named classification
propositions in the modular dynamics directories.

Historically, the first ledger treated inhabitants of these interfaces as
future obligations.  That status is now obsolete for the headline theorem:

- `NormalizedCorrectedAugmentedEffectiveFamily.gap` supplies the required
  semantic gaps unconditionally;
- `NormalizedCorrectedAugmentedEffectiveFamily.family` supplies the actual
  fixed-resource family; and
- the final endpoint's `#print axioms` closure contains no such proposition
  as an assumption.

The old interfaces remain useful abstractions and alternate proof routes;
their continued presence must not be read as an open hypothesis of the
completed augmented endpoint.

## Reproducibility checklist

From the `lean/` directory:

```bash
# Full warning-as-error project build
lake build

# Narrow endpoint build
lake build HGAS.Arithmetic.NormalizedCorrectedAugmentedEffectiveFamily

# Placeholder/project-axiom scan
rg -n '(^|[^A-Za-z])(sorry|admit)\b|^\s*axiom\b|^\s*unsafe\b' \
  HGAS HGAS.lean --glob '*.lean'
```

For trust auditing, import
`HGAS.Arithmetic.NormalizedCorrectedAugmentedEffectiveFamily` in a temporary
Lean file and run `#print axioms` on the seven headline declarations listed
under “Trust and build status”.

Independent audit notes are kept under `../audits/`, including:

- `lean_augmented_fixed_resource_audit_2026-07-24.md`;
- the endpoint audits for the normalized-corrected family; and
- the module-specific analytic, arithmetic, compiler, and wrapper audits
  accumulated during development.
