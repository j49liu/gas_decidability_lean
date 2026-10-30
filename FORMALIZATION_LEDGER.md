# Formalization ledger

Last updated: 2026-10-08

Current status: **the unconditional augmented fixed-pair GAS theorem, its
cofinal cubic consequence, and the fixed-parameter GAS/HLS cubicization
theorems are complete and kernel checked**. The cofinal HLS hardness and
undecidability endpoints are conditional transfer theorems: their external
source result remains an explicit hypothesis.

This ledger records the public theorem chain in the current worktree.  It
supersedes the early-development checklist that described the
modular/Jacobi-to-compiler integration as open.

This ledger uses four status labels:

- **Exact**: the Lean declaration has the intended coded input language,
  hypotheses, and conclusion.
- **Equivalent or alternative**: Lean proves a result sufficient for the
  dependency chain through a norm-equivalent, representation-equivalent, or
  different fixed-resource formulation.
- **Conditional**: the declaration exposes an unformalized literature input
  as a hypothesis.
- **Not formalized**: the repository makes no claim that Lean verifies the
  stated result.

The preserved GAS companion is
`docs/hgas_sigma1_complete_formalization_companion.tex`. It records the
preceding 824-module formalization. The additive HLS and shadowing extension
is documented in `docs/cubicization_hls_formalization_companion.tex`. This
ledger, rather than either companion alone, is the authoritative coverage
record for the combined 837-module repository.

The mathematical language is

```lean
HGASQ n d : PolynomialFieldCode n → Prop
```

from `HGAS/Computability/HGASLanguage.lean`.  Its inputs are finite rational
codes for polynomial vector fields on `ℝⁿ`, and syntactic homogeneity of
the requested degree is part of the language definition.

The corresponding homogeneous Lyapunov-stability language is

```lean
HLSQ n d : PolynomialFieldCode n → Prop
```

from `HGAS/Stability/KordaLyapunov.lean`. Invalid homogeneity codes are
negative instances for both languages.

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

## HLS and common cubicization theorems

The additive endpoint is
`HGAS/Propagation/CofinalLyapunovReduction.lean`, supported by the new
stability, Veronese, and computability modules listed below. For fixed
`n >= 2` and `k >= 1`, it proves:

```lean
hlsQ_manyOneReducible_cubic :
  HLSQ n (2 * k + 1) ≤₀
    HLSQ (cubicLiftCodeDimension n k) 3

exists_computable_cubicization :
  ∃ f, Computable f ∧
    ∀ F,
      (HGASQ n (2 * k + 1) F ↔
        HGASQ (cubicLiftCodeDimension n k) 3 (f F)) ∧
      (HLSQ n (2 * k + 1) F ↔
        HLSQ (cubicLiftCodeDimension n k) 3 (f F))
```

Thus one fixed-parameter code map preserves both properties. The theorem
`hlsQ_manyOneReducible_cofinalFixedPair` composes this map with dimension
and odd-degree padding to obtain

```lean
HLSQ n (2 * k + 1) ≤₀ HLSQ N d
```

whenever `cubicLiftCodeDimension n k <= N`, `Odd d`, and `3 <= d`.

The semantic core is unconditional. In particular, the extension proves

```lean
sourceLS_iff_stabilizedCubicLS
```

for every homogeneous source field of degree `2*k+1` with `k >= 1`. The
raw-code compiler's additional `n >= 2` hypothesis is needed only for its
explicit malformed-code fallback.

The exported cofinal HLS consequences have two deliberately separate
forms:

- `hlsQ_manyOneHard_cofinal_of_source` transfers `ManyOneHard` from a fixed
  source language and derives target hardness, undecidability, and a
  non-c.e. complement; and
- `hlsQ_not_computable_cofinal_of_source` transfers noncomputability alone.

Both theorems are **conditional**. Korda's source theorem is represented by
the explicit hypothesis `hsource`; the repository does not formalize his
register-machine reduction.

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

The repository also does not claim:

- a common raw-code GAS/HLS compiler in source dimension `n = 1`;
- one cubic compiler computable uniformly while `(n,k)` varies;
- an evaluable numerical value for the chosen shadow gain or cofinal
  threshold;
- a maximal-solution API theorem equating the paper's wording with Lean's
  global-forward-trajectory representation;
- a verbatim `Q`-norm version of the printed finite-horizon shadowing
  proposition;
- an unconditional Lean proof of Korda's source hardness theorem; or
- formalizations of the manuscript's variable-resource corollary, normal
  forms (iii) and (iv), the even-degree and linear-field lemmas, or the
  Korda GAS/forward-completeness corollary.

The GAS-only cubic compiler covers every positive source dimension. The
semantic HLS preservation theorem also has no `n >= 2` restriction; only
the bundled raw-code theorem has that restriction.

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
completed endpoints. The source tree has 837 modules: 796 in the public
closure and 41 independently elaborated modules outside it.

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
HGAS.lyapunovStableWithExistence_iff_uniformLinearTrajectoryBound
HGAS.lyapunovStableWithExistence_iff_boundedEuclideanAngularCocycle
HGAS.Veronese.exists_finiteHorizonOrbitShadowing
HGAS.Veronese.exists_finiteHorizonShadowing
HGAS.Veronese.sourceLS_iff_stabilizedCubicLS
HGAS.Veronese.effectiveCubicLSReductionCode_hgasQ_iff
HGAS.Propagation.effectiveCubicLSReductionCode_hlsQ_iff
HGAS.Propagation.exists_computable_cubicization
HGAS.Propagation.hlsQ_manyOneHard_cofinal_of_source
HGAS.Propagation.hlsQ_not_computable_cofinal_of_source
```

report only:

```text
propext
Classical.choice
Quot.sound
```

These are the ordinary Lean/Mathlib logical foundations used by the
development. No project-defined axiom appears in the dependency closure of
the headline GAS or HLS results. The occurrence of `Classical.choice`
records nonconstructive existence choices; it is not a project axiom.

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

The shadow-gain compiler has a parallel fixed-parameter qualification. For
each fixed `(n,k)`, `fixedCubicShadowGainParameters` selects a natural gain
by classical choice, and `effectiveCubicLSReductionCode_primrec` proves that
the resulting map is primitive recursive in the input field code. Lean
therefore proves existence of a computable reduction for each fixed pair.
It does not provide one algorithm uniform in varying `(n,k)`, and the
selected gain need not reduce to a printed numeral.

## End-to-end theorem/module crosswalk

Every row in the first table is complete (`[x]`) on the dependency path of
the headline GAS theorem.

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

The HLS extension is a strict additive layer. All 13 modules in the next
table lie in the public import closure; every preceding `HGAS/` module is
unchanged.

| Stage | Principal declaration or role | Module | Status |
|---|---|---|---|
| Nonvacuous HLS predicate and code language | `LyapunovStableWithExistence`, `HLSQ` | `HGAS/Stability/KordaLyapunov.lean` | `[x]` |
| Uniform linear bound | `lyapunovStableWithExistence_iff_uniformLinearTrajectoryBound` | `HGAS/Stability/KordaLyapunov.lean` | `[x]` |
| Euclidean angular criterion | `lyapunovStableWithExistence_iff_boundedEuclideanAngularCocycle` | `HGAS/Stability/AngularLyapunov.lean` | `[x]` |
| Angular-field congruence | `lyapunovStableWithExistence_iff_of_eqOn_sphere` | `HGAS/Stability/AngularCongruence.lean` | `[x]` |
| Linear conjugacy | `lyapunovStableWithExistence_conjugateField_iff` | `HGAS/Stability/LinearConjugacyLyapunov.lean` | `[x]` |
| HLS product, dimension, and degree padding | `degreeDimensionPadCode_hlsQ_iff_of_homogeneous` | `HGAS/Stability/PaddingLyapunov.lean` | `[x]` |
| Source and weighted angular criteria | `lyapunovStableWithExistence_iff_boundedWeightedAngularCocycle` | `HGAS/Veronese/LyapunovAngularCriteria.lean` | `[x]` |
| Distance to the Veronese cone | `exists_coneDistanceSq_le_energy` | `HGAS/Veronese/ConeDistance.lean` | `[x]` |
| Decay and Lipschitz preliminaries | shadowing estimates and cone invariance | `HGAS/Veronese/ShadowingPrelims.lean` | `[x]` |
| Shadowing parameter package | `CubicLiftShadowingBounds` | `HGAS/Veronese/CubicLiftShadowingBounds.lean` | `[x]` |
| Finite-horizon shadowing and semantic HLS preservation | `exists_finiteHorizonOrbitShadowing`, `exists_finiteHorizonShadowing`, `sourceLS_iff_stabilizedCubicLS` | `HGAS/Veronese/CubicLiftLyapunovConjugacy.lean` | `[x]` |
| Generic hardness transfers | `ManyOneHard` and its consequences | `HGAS/Computability/ManyOneHard.lean` | `[x]` |
| Fixed-parameter effective gain and common compiler | `effectiveCubicLSReductionCode_primrec`, code-level GAS/HLS correctness | `HGAS/Computability/CubicLiftEffectiveShadowGain.lean` | `[x]` |
| Cubic/cofinal HLS reductions | `exists_computable_cubicization`, `hlsQ_manyOneReducible_cofinalFixedPair` | `HGAS/Propagation/CofinalLyapunovReduction.lean` | `[x]` |

## Paper-to-Lean scope matrix

This table records what the repository verifies literally. It avoids the
stronger and inaccurate claim that every printed intermediate lemma is
formalized verbatim.

| Manuscript result or ingredient | Status | Qualification |
|---|---|---|
| Main cofinal and fixed-pair GAS theorems | **Exact** | Unconditional statements about raw rational field codes |
| Cubic GAS consequence | **Exact** | Every dimension beyond the symbolic fixed threshold |
| GAS angular criterion | **Exact for the Euclidean form** | Negativity of the maximal invariant angular average on the Euclidean unit sphere |
| Odd-degree c.e. upper bound | **Exact statement; alternative proof** | The printed endpoint is proved through finite-grid certificates rather than Tarski elimination |
| Required MRDP input | **Equivalent or alternative** | The universal-halting case needed by the reduction, not the printed arbitrary-r.e.-set theorem verbatim |
| Fixed-resource DQL construction | **Equivalent or alternative** | Exact fixed arities and semantics, but not the paper's affine-right-hand-side form verbatim |
| Korda scaling lemma for HLS | **Equivalent or alternative** | Uses the repository's global-forward-trajectory representation |
| Korda angular HLS criterion | **Equivalent or alternative** | Uses a bounded-cocycle witness rather than the paper's named optimum |
| GAS cubicization | **Exact** | Code reduction for positive source dimension; fixed-parameter computability |
| Common GAS/HLS cubicization | **Exact** | One raw-code compiler for `n >= 2`, `k >= 1`; fixed-parameter computability |
| Finite-horizon shadowing | **Equivalent or alternative** | Split orbit/cocycle statements in a norm equivalent to the paper's `Q`-norm formulation |
| GAS and HLS degree/dimension padding | **Exact** | Exact code-level equivalences under their stated homogeneity hypotheses |
| HLS cofinal fixed-pair transfer | **Exact** | Source dimension at least two for the raw-code compiler |
| Korda HLS hardness and undecidability consequences | **Conditional** | Korda's source theorem is the explicit `hsource` hypothesis |
| Theta, selector, drift, compactification, and wrapper chain | **Equivalent or alternative** | Distributed formal analogues sufficient for the GAS endpoint |
| Compiler uniformity in varying `(n,k)` | **Not formalized** | The proved code maps are computable separately for fixed `(n,k)` |
| Maximal-solution/global-trajectory bridge | **Not formalized** | Polynomial regularity and uniqueness support the representation, but no standalone API theorem is exported |
| Variable-resource corollary and normal forms (iii),(iv) | **Not formalized** | No Lean coverage claimed |
| Even-degree, linear-field, and Korda GAS/forward-completeness results | **Not formalized** | No Lean coverage claimed |

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

### 7. Homogeneous Lyapunov stability and shadowing

`HGAS/Stability/KordaLyapunov.lean` prevents the trajectory-only stability
predicate from becoming vacuous when solutions blow up. Its
`LyapunovStableWithExistence` predicate requires existence of a global
forward trajectory from every sufficiently small initial state and bounds
every global forward trajectory from that state. Homogeneous scaling gives
`lyapunovStableWithExistence_iff_uniformLinearTrajectoryBound`.

`HGAS/Stability/AngularLyapunov.lean` converts this linear trajectory bound
to boundedness of the Euclidean angular radial cocycle. The Veronese layer
transfers that criterion to the source and weighted target geometries.

The stabilized cubic field contracts the toric penalty away from the
Veronese cone. `exists_finiteHorizonOrbitShadowing` compares each finite
target orbit segment with an orbit on the invariant cone, and
`exists_finiteHorizonShadowing` derives the corresponding radial-cocycle
bound. Together with exact conjugacy on the cone, these estimates prove
`sourceLS_iff_stabilizedCubicLS`.

The exported finite-horizon results are a split, norm-equivalent formal
analogue of the manuscript's one displayed `Q`-norm proposition. They are
the actual results used by the Lean proof; this ledger does not claim that
the printed proposition is exported verbatim.

### 8. Effective common compiler and conditional HLS transfer

`HGAS/Computability/CubicLiftEffectiveShadowGain.lean` selects a sufficient
shadow gain for each fixed `(n,k)` and proves the resulting field-code map
primitive recursive in the input code. Valid codes use the stabilized
cubic lift. Invalid codes map to an explicit unstable homogeneous cubic
field, making the compiler total and preserving negative instances.

`HGAS/Propagation/CofinalLyapunovReduction.lean` instantiates the semantic
theorem rather than assuming it. The resulting
`exists_computable_cubicization` declaration uses the same map for GAS and
HLS. HLS padding then yields the exact cofinal fixed-pair reduction.

The last step separates formal and external evidence. The generic
`ManyOneHard` lemmas are proved in Lean, but Korda's source hardness theorem
is not. Consequently, the final HLS propagation theorems take that source
claim as `hsource`. No unconditional HLS classification is inferred inside
Lean without this hypothesis.

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

The source history is similarly explicit. The HLS release retains all 824
preceding `HGAS/` modules byte for byte and adds 13 public-closure modules.
The original GAS companion is preserved rather than silently rewritten; the
new companion documents the additive layer.

## Reproducibility checklist

From the `lean/` directory:

```bash
# Full warning-as-error project build
lake build

# Narrow endpoint build
lake build HGAS.Arithmetic.NormalizedCorrectedAugmentedEffectiveFamily
lake build HGAS.Propagation.CofinalLyapunovReduction

# Import-closure and legacy-catalog check
python3 scripts/check_import_closure.py

# Placeholder/project-axiom scan
rg -n '(^|[^A-Za-z])(sorry|admit)\b|^\s*axiom\b|^\s*unsafe\b' \
  HGAS HGAS.lean --glob '*.lean'
```

For trust auditing, run

```bash
lake env lean -DwarningAsError=true scripts/ReleaseAxiomAudit.lean
```

and inspect every `#print axioms` result. The expected dependency list for
each audited endpoint is `[propext, Classical.choice, Quot.sound]`. This is
an inspection audit: Lean checks that every named declaration elaborates,
but the command does not itself reject an unexpected additional axiom.

A release check should also elaborate each of the 41 paths in
`LEGACY_MODULES.md` directly with `-DwarningAsError=true`. The closure script
checks their exact catalog membership; direct elaboration checks that the
files remain valid even though `HGAS.lean` does not import them.
