# Lean Formalization of Undecidability of Stability for Homogeneous Polynomial Vector Fields

This repository contains Lean proofs that global asymptotic stability is
undecidable for homogeneous polynomial vector fields with rational
coefficients, even in a sufficiently large fixed dimension and at degree
three. The origin is globally asymptotically stable (GAS) if every trajectory
approaches it and trajectories starting close to it remain close for all
forward time.

The accompanying paper is
[Global asymptotic stability of homogeneous polynomial vector fields is undecidable](https://arxiv.org/abs/2610.12434)
by Ivan O. Shevchenko, Jun Liu, and Xinzhi Liu.

## What is proved

Write HGAS(n, d) for the set of codes of homogeneous polynomial vector
fields with rational coefficients in dimension n and of degree d whose
origin is GAS. There is an integer N such that, for every fixed n ≥ N and
every fixed odd d ≥ 3,
HGAS(n, d) is **many-one complete for the recursively enumerable sets**
(equivalently, Σ⁰₁-complete). Thus a search procedure can eventually recognize
exactly the GAS instances, and every recursively enumerable decision problem
can be reduced to this one. No algorithm can always terminate and correctly
decide whether the origin is GAS.

While the main focus of our work is homogeneous global asymptotic stability
(HGAS), we also obtain sharper results for homogeneous Lyapunov stability
(HLS), building on [Korda's recent undecidability result](https://arxiv.org/abs/2609.22058v2).
Our reduction to degree three gives **many-one hardness for HLS** in every
sufficiently large fixed dimension and every fixed odd degree at least
three. This does not establish that HLS is recursively enumerable.

To make the formalization of these HLS results self-contained, we also
formalize the reduction from the halting problem to Lyapunov stability in
Korda's proof. A
[Lean formalization of Korda's original write-up](https://homepages.laas.fr/mkorda/arnold_lean.zip)
is also available.

Further completeness results concern sets of codes with odd degree, or
both dimension and odd degree, supplied as input. We also prove many-one
hardness of GAS and local asymptotic stability for polynomial vector fields
without the homogeneity restriction, in every sufficiently large fixed
dimension and with any fixed degree bound at least three. We do not claim
recursive enumerability for these non-homogeneous problems.

The bounds on dimension are not evaluated numerically, and neither
HGAS(3, 3) nor HLS(3, 3) is settled here. Not every statement in the paper
is formalized verbatim. Coverage of the results with dimension or degree
supplied as input is partial: there are no separate theorems with degree
fixed and dimension supplied as input, nor an identification with the
paper's set of codes allowing all positive dimensions and degrees.
The [formalization ledger](FORMALIZATION_LEDGER.md) records the precise
statements, hypotheses, and differences from the paper.

## How the proof works

The proof has the two main parts described in Section 2 of the paper:

1. **Reduction to degree three.** A homogeneous polynomial vector field of
   odd degree at least three is lifted to one of degree three in a possibly
   larger dimension, preserving both GAS and Lyapunov stability. Adding variables and
   increasing the odd degree then gives the results in every sufficiently
   large dimension and every odd degree at least three.
2. **One fixed dimension and degree.** The halting problem is reduced to
   solvability of a Diophantine equation, then to a nonzero constant Fourier
   coefficient. A polynomial system relates this coefficient to time
   averages along its intended trajectories. Finite polynomial tests control
   the recurrent trajectories relevant to the proof. A compactification and
   the angular criterion for GAS then give a homogeneous vector field whose
   origin is GAS exactly when the computation halts, with dimension and
   degree independent of the input.

Together with recursive enumerability of HGAS(n, d) for these odd degrees,
these two parts prove many-one completeness. The Lean development proves
the required results, but some intermediate arguments differ from those
in the paper; the ledger describes these differences.

## Reading the proofs

The companions explain the mathematics and connect it to the Lean code:

- [GAS completeness](docs/hgas_sigma1_complete_formalization_companion.pdf):
  the reduction from the halting problem to GAS at one fixed dimension and
  degree, and the consequences for degree three and higher odd degrees.
- [Reduction to degree three and Lyapunov stability](docs/cubicization_hls_formalization_companion.pdf):
  the angular criteria for stability and the proof that the reduction
  preserves GAS and Lyapunov stability.
- [Further stability results](docs/stability_formalization_companion.pdf):
  the intended trajectories and their time averages, the construction of
  the homogeneous vector field, and the reduction from the halting problem
  to Lyapunov stability.

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

[HGAS/](HGAS/) contains the original GAS proof and the reduction to degree
three preserving GAS and Lyapunov stability. [Stability/](Stability/) adds
proofs corresponding to the paper's revised statements and the further
stability results, without changing the published `HGAS` sources. Import
[HGAS.lean](HGAS.lean) and [Stability.lean](Stability.lean) to use the two
libraries.

Useful places to start are the
[main GAS theorems](HGAS/Arithmetic/NormalizedCorrectedAugmentedEffectiveFamily.lean),
the [reduction from the halting problem to HLS](Stability/Computability/UniversalStabilityReduction.lean),
and the [fixed-dimension, fixed-degree GAS construction](Stability/Selection/OrdinaryTimeUniversalDetector.lean).
The ledger links the intermediate results to their modules.

Historical alternatives and audit modules are described in the
[legacy-module catalog](LEGACY_MODULES.md); release history is summarized
in the [release notes](RELEASE_NOTES.md).

Licensed under the [Apache License, Version 2.0](LICENSE).
