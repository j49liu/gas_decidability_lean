# Stability and undecidability in Lean

This repository contains machine-checked proofs about the limits of deciding
stability for polynomial differential equations. The central result is that
global asymptotic stability (GAS) is undecidable even for homogeneous cubic
vector fields with rational coefficients in a sufficiently large fixed
dimension.

The accompanying paper is
[Global asymptotic stability of homogeneous polynomial vector fields is undecidable](https://arxiv.org/abs/2610.12434)
by Ivan O. Shevchenko, Jun Liu, and Xinzhi Liu.

## What is proved

For every sufficiently large fixed dimension and every fixed odd degree
at least three, homogeneous GAS is **Σ⁰₁-complete**. In practical terms,
there is a search procedure that eventually recognizes exactly the positive
instance, but no algorithm that always terminates and correctly decides
both positive and negative instances.

The repository also proves **many-one hardness for homogeneous Lyapunov
stability (HLS)**, again in sufficiently large fixed dimensions and every odd
degree at least three. Its reduction from the halting problem is fully
formalized. This is a hardness result, not a claim that Lyapunov stability
is recursively enumerable.

Beyond the core GAS proof, we formalize the halting-to-Lyapunov-stability
construction from [Korda's written proof](https://arxiv.org/abs/2609.22058v2).
The development starts from Mathlib's universal evaluator and does not
copy or port his earlier
[Lean implementation](https://homepages.laas.fr/mkorda/arnold_lean.zip).

Further results include GAS completeness for explicitly defined languages
with odd degree, or dimension and odd degree, supplied as input. They also
include hardness of GAS and local asymptotic stability for general
polynomial fields in sufficiently large fixed dimensions and with degree
bound at least three. Recursive enumerability is not claimed for these
general polynomial stability problems.

The dimension thresholds are symbolic: this development does not compute
numerical bounds or settle the three-dimensional cubic GAS or Lyapunov
stability problems. Nor is every statement in the paper formalized
verbatim. In particular, coverage of its variable-resource corollary is
partial: separate fixed-degree, dimension-input theorems and an
identification with the paper's unrestricted all-degree language are not
provided. The [formalization ledger](FORMALIZATION_LEDGER.md) records the
precise statements, hypotheses, and limitations.

## Reading the proofs

The companions explain the mathematics and connect it to the Lean code:

- [GAS completeness](docs/hgas_sigma1_complete_formalization_companion.pdf):
  the original fixed-dimension, fixed-degree reduction and its cubic and
  higher-degree consequences.
- [Cubicization and Lyapunov stability](docs/cubicization_hls_formalization_companion.pdf):
  the stability criteria, shadowing estimates, and reduction to cubic fields.
- [Further stability results](docs/stability_formalization_companion.pdf):
  the broader trajectory selector, Fourier estimates, effective GAS
  construction, and full halting-to-Lyapunov-stability reduction.

The first two companions are preserved accounts of earlier releases.
For current coverage, including results added since those releases, use
the [ledger](FORMALIZATION_LEDGER.md). TeX sources and a guide to the
documents are available in [docs/](docs/README.md).

## Build and check

The project uses Lean and Mathlib **4.30.0**, pinned by the files in this
repository. From the repository root, build both libraries with:

```bash
lake build HGAS Stability
```

Both names matter: plain `lake build` builds only `HGAS`.

To check the imports, inspect axiom dependencies, and run the regression
examples:

```bash
python3 scripts/check_import_closure.py
lake env lean -DwarningAsError=true scripts/ReleaseAxiomAudit.lean
lake env lean -DwarningAsError=true scripts/StabilityAxiomAudit.lean
lake env lean -DwarningAsError=true scripts/StabilityRegression.lean
```

The proofs contain no `sorry`, `admit`, or project-defined axioms.
The audited declarations depend only on the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`. The audit scripts print
these dependencies for inspection; the Stability audit also rejects
project-namespaced axiom declarations. See the
[release checklist](RELEASE_CHECKLIST.md) for the full verification procedure.

## Finding your way in the code

[HGAS/](HGAS/) contains the original GAS proof, cubicization, and
shadowing arguments. [Stability/](Stability/) adds the later results
without changing the published `HGAS` sources. Their public entry points
are [HGAS.lean](HGAS.lean) and [Stability.lean](Stability.lean).

Useful places to start are the
[main GAS theorems](HGAS/Arithmetic/NormalizedCorrectedAugmentedEffectiveFamily.lean),
the [halting-to-HLS reduction](Stability/Computability/UniversalStabilityReduction.lean),
and the [GAS construction matching the paper](Stability/Selection/OrdinaryTimeUniversalDetector.lean).
The ledger links the intermediate results to their modules.

Historical alternatives and audit modules are described in the
[legacy-module catalog](LEGACY_MODULES.md); release history is summarized
in the [release notes](RELEASE_NOTES.md).

Licensed under the [Apache License, Version 2.0](LICENSE).
