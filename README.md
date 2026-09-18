# Lean formalization of homogeneous-GAS completeness

This directory contains the completed formalization of the repaired
homogeneous-GAS completeness proof.  The human-readable proof that follows
the final Lean dependency chain is
`docs/hgas_sigma1_complete_formalization_companion.tex`.  The research
manuscript is maintained separately; this repository contains the complete
Lean source, its pinned environment, and the formalization companion.  The
final endpoint uses the nonzero-linear-column augmentation described in the
companion.

The formalization has two simultaneous goals:

1. track the mathematical proof closely enough that a reader can move
   between the paper and Lean declarations without reverse engineering the
   code; and
2. isolate reusable mathematics—homogeneous dynamics, invariant averages,
   polynomial encodings, cocycle compactification, and Veronese lifts—from
   the manuscript-specific reduction.

## Build

The project is pinned to Lean and Mathlib 4.30.0.

```bash
lake update
lake build HGAS
```

During development, `lake env lean HGAS/Path/To/File.lean` checks one module.

The repository intentionally excludes `.lake/`, compiled artifacts, and
the exploratory `Scratch*.lean` files.  A fresh clone reconstructs all
dependencies from `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`.

## Headline endpoint

The public root is `HGAS.lean`.  Its final theorem module is
`HGAS/Arithmetic/NormalizedCorrectedAugmentedEffectiveFamily.lean`.  The
module proves:

- `fixedPair_sigmaOneComplete`: one fixed positive dimension and one fixed
  odd degree at least three already give a `SigmaOneComplete` rational HGAS
  language;
- `cofinal_sigmaOneComplete`: every sufficiently large fixed dimension and
  every fixed odd degree at least three give a `SigmaOneComplete` language;
- `cubic_sigmaOneComplete`: in particular, cubic HGAS is
  `SigmaOneComplete` in every sufficiently large fixed dimension; and
- the corresponding undecidability and non-c.e.-complement consequences.

The development does not determine the separate low-dimensional language
`HGASQ 3 3`.

## Trust policy

The finished theorem must not depend on project-defined `axiom`
declarations, `sorry`, `admit`, or `unsafe` proof shortcuts. External
published inputs used by the paper are formalization obligations, not
permanent axioms. Temporary interfaces, if introduced while work is in
progress, live in explicitly named staging modules and may not be imported
by the final theorem.

Run the placeholder audit with:

```bash
rg -n \
  -e '^[[:space:]]*((private|protected)[[:space:]]+)?axiom[[:space:]]' \
  -e '^[[:space:]]*((private|protected)[[:space:]]+)?unsafe[[:space:]]' \
  -e '^[[:space:]]*(sorry|admit)\b' \
  -e ':=[[:space:]]*(by[[:space:]]+)?(sorry|admit)\b' \
  HGAS HGAS.lean
```

The exact theorem-to-module ledger is maintained in
`FORMALIZATION_LEDGER.md`.

## Source coverage

The directory `HGAS/` contains 824 Lean modules.  The transitive import
closure of `HGAS.lean` contains 783 of them.  The remaining 41 historical,
alternative, or audit modules are catalogued in `LEGACY_MODULES.md`; all 41
also elaborate independently with warnings treated as errors.

Check the import graph and catalog with:

```bash
python3 scripts/check_import_closure.py
```

The expected result is:

```text
HGAS source modules: 824
Public import closure: 783
Outside public closure: 41
LEGACY_MODULES.md exact-set check: PASS
```
