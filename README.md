# Lean formalization of homogeneous stability and decidability

This repository is the canonical Lean source for two related developments:

1. the unconditional fixed-pair and cofinal
   `Σ⁰₁`-completeness theorems for homogeneous global asymptotic
   stability (HGAS); and
2. the additive formalization of homogeneous Lyapunov stability (HLS),
   finite-horizon shadowing, and one fixed-parameter cubic compiler that
   preserves both GAS and HLS.

The published HLS development adds 13 modules without changing any of the
824 modules in the preceding GAS release. These 837 modules and their
public root, `HGAS.lean`, remain unchanged. The further results below use
the separate public root `Stability.lean` in the same source tree.

The accompanying paper is
[Global asymptotic stability of homogeneous polynomial vector fields is undecidable](https://arxiv.org/abs/2610.12434)
by Ivan O. Shevchenko, Jun Liu, and Xinzhi Liu (arXiv:2610.12434).

The formalization proves
the headline coded-language endpoints and formal analogues sufficient for
their Lean dependency chains. Some printed intermediate results are exposed
in equivalent or alternative forms rather than copied verbatim.

## Further stability results

The `Stability` library adds general polynomial GAS/LAS hardness, uniform
dimension-and-odd-degree-input semidecision, and the broader ordinary-time trajectory selector
with its compact-measure application. Build it with `lake build Stability`; the published
`HGAS` sources and pinned environment are unchanged.

Beyond the core GAS proof, the new library formalizes the halting-to-HLS
construction from [Korda's written proof](https://arxiv.org/abs/2609.22058v2),
without copying or porting his earlier
[Lean implementation](https://homepages.laas.fr/mkorda/arnold_lean.zip).
It derives the computational source from Mathlib's universal evaluator
and discharges the source-hardness assumption: `Stability/Computability/UniversalStabilityReduction.lean`
proves unconditional HLS hardness for a fixed cubic dimension and every
larger dimension and odd degree at least three. This is a hardness result,
not an assertion that HLS is recursively enumerable.

Proof explanations are in `docs/stability_formalization_companion.tex`
and its PDF; exact coverage is recorded in `FORMALIZATION_LEDGER.md`.
Use `scripts/StabilityAxiomAudit.lean` and `scripts/StabilityRegression.lean`
for the additional checks.

## Companion documents and coverage ledger

The repository keeps two preserved companions with distinct scopes,
alongside the stability companion described above:

- `docs/hgas_sigma1_complete_formalization_companion.tex` is the preserved
  companion to the original 824-module GAS formalization. Its rendered PDF
  is `docs/hgas_sigma1_complete_formalization_companion.pdf`.
- `docs/cubicization_hls_formalization_companion.tex` documents the 13-module
  HLS and shadowing extension. Its rendered PDF is
  `docs/cubicization_hls_formalization_companion.pdf`.

`FORMALIZATION_LEDGER.md` is the authoritative current crosswalk. It labels
paper-to-Lean correspondences as exact, equivalent or alternative,
conditional, or not formalized. `LEGACY_MODULES.md` separately catalogs the
41 source modules outside the `HGAS.lean` import closure; two of these
are dependencies of `Stability.lean`.

## Build

The project is pinned to Lean and Mathlib 4.30.0.

```bash
lake build HGAS Stability
```

During development,
`lake env lean -DwarningAsError=true HGAS/Path/To/File.lean` checks one
module. The repository excludes `.lake/`, compiled artifacts, and
exploratory `Scratch*.lean` files. A fresh clone reconstructs all
dependencies from `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`.

## Unconditional GAS endpoints

The final GAS theorem module is
`HGAS/Arithmetic/NormalizedCorrectedAugmentedEffectiveFamily.lean`. It
proves:

- `fixedPair_sigmaOneComplete`: one fixed positive dimension and one fixed
  odd degree at least three already give a `SigmaOneComplete` rational HGAS
  language;
- `cofinal_sigmaOneComplete`: every sufficiently large fixed dimension and
  every fixed odd degree at least three give a `SigmaOneComplete` HGAS
  language;
- `cubic_sigmaOneComplete`: cubic HGAS is `SigmaOneComplete` in every
  sufficiently large fixed dimension; and
- the corresponding undecidability and non-c.e.-complement consequences.

The fixed dimensions, degrees, and cofinal threshold are closed symbolic
Lean terms. They ultimately use a finite Diophantine representation chosen
by classical choice, so the development does not currently evaluate them
to numerical literals. In particular, it does not determine the separate
low-dimensional language `HGASQ 3 3`.

## HLS and common cubicization endpoints

`HGAS/Stability/KordaLyapunov.lean` defines
`LyapunovStableWithExistence` and the rational code language `HLSQ`. This is
the nonvacuous stability notion in which nearby initial states admit global
forward trajectories and every such trajectory stays nearby. The extension
then proves:

- Korda's uniform-linear-trajectory-bound characterization in
  `HGAS/Stability/KordaLyapunov.lean`;
- the bounded-angular-cocycle criterion in
  `HGAS/Stability/AngularLyapunov.lean`;
- dimension and odd-degree padding for HLS in
  `HGAS/Stability/PaddingLyapunov.lean`;
- finite-horizon orbit and radial-cocycle shadowing and semantic HLS
  preservation by the stabilized cubic Veronese lift in
  `HGAS/Veronese/CubicLiftLyapunovConjugacy.lean`;
- a primitive-recursive code compiler for each fixed pair `(n,k)` in
  `HGAS/Computability/CubicLiftEffectiveShadowGain.lean`; and
- exact cubic and cofinal fixed-pair HLS reductions in
  `HGAS/Propagation/CofinalLyapunovReduction.lean`.

For every fixed `n >= 2` and `k >= 1`, the declaration
`exists_computable_cubicization` supplies one map that preserves both
`HGASQ n (2*k+1)` and `HLSQ n (2*k+1)` under cubicization. The older
GAS-only compiler covers positive source dimensions, including `n = 1`.
The `n >= 2` hypothesis for the bundled raw-code compiler comes from its
explicit two-coordinate unstable fallback for malformed inputs, not from
the semantic HLS conjugacy theorem.

The computability statement is fixed-parameter: Lean proves a computable
input-code map separately for each fixed `(n,k)`. The chosen shadow gain is
selected noncomputably once the pair is fixed. The repository does not
claim one compiler computable uniformly in varying `(n,k)`, nor does it
claim that the selected multiplier is currently evaluable.

The preserved cofinal HLS declarations are conditional transfer theorems:
their source hardness appears as an explicit hypothesis named `hsource`,
not a project axiom. The new `Stability` library proves that source result
and applies these unchanged transfer theorems to obtain unconditional HLS
hardness, as described above.

## Trust policy

Public endpoints must not depend on project-defined `axiom` declarations,
`sorry`, `admit`, `unsafe` proof shortcuts, or hidden substitutes for an
external result. An external theorem not formalized in this repository must
instead remain an explicit hypothesis of the exported conditional theorem.

Run the source audit with:

```bash
rg -n \
  -e '^[[:space:]]*((private|protected)[[:space:]]+)?axiom[[:space:]]' \
  -e '^[[:space:]]*((private|protected)[[:space:]]+)?unsafe[[:space:]]' \
  -e '^[[:space:]]*(sorry|admit)\b' \
  -e ':=[[:space:]]*(by[[:space:]]+)?(sorry|admit)\b' \
  HGAS HGAS.lean Stability Stability.lean
```

The audited headline endpoints report only `propext`, `Classical.choice`,
and `Quot.sound` under `#print axioms`. The exact declarations and their
scope are listed in `FORMALIZATION_LEDGER.md`.

Reproduce the kernel-axiom inspection with:

```bash
lake env lean -DwarningAsError=true scripts/ReleaseAxiomAudit.lean
```

This command prints the dependencies for manual inspection; it does not
automatically reject an unexpected additional axiom.

## Source coverage

The directory `Stability/` contains 251 Lean modules, all in the transitive
import closure of `Stability.lean`.

The preserved directory `HGAS/` contains 837 Lean modules. The transitive import
closure of `HGAS.lean` contains 796 of them. The remaining 41 historical,
alternative, or audit modules are catalogued in `LEGACY_MODULES.md`; all 41
also elaborate independently with warnings treated as errors.

Check the import graph and catalog with:

```bash
python3 scripts/check_import_closure.py
```

The expected result is:

```text
HGAS source modules: 837
Public import closure: 796
Outside public closure: 41
LEGACY_MODULES.md exact-set check: PASS
Stability source modules: 251
Stability modules in Stability.lean closure: 251
Stability modules outside Stability.lean closure: 0
Catalogued HGAS modules in Stability.lean closure: 2
  HGAS/Modular/GammaTwoHorocycleOrientationReversal.lean
  HGAS/Modular/GammaTwoScaledPointwiseEquidistribution.lean
Stability import-closure check: PASS
```

## Copyright and license

Copyright (c) 2026 Jun Liu and Ivan O. Shevchenko. This project is licensed
under the Apache License, Version 2.0; see `LICENSE`.
