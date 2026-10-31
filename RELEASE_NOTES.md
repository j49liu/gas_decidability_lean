# Release notes

## Stability extension

Prepared on 2026-10-31, based on published commit `81276ab`.

The separate `Stability` library adds 251 modules while preserving all
837 published `HGAS` modules and the pinned Lean/Mathlib 4.30.0 environment.
The additions formalize:

- the broader ordinary-time trajectory selector and explicit Fourier bounds;
- the printed-gain compact graph, invariant-average gap, and effective GAS family;
- degree-input and joint dimension-and-odd-degree-input GAS completeness;
- bounded-degree polynomial GAS and LAS hardness; and
- the halting-to-HLS source reduction and unconditional cubic/cofinal HLS
  hardness, undecidability, and non-r.e.-complement consequences.

The existing conditional HLS transfer theorems remain unchanged; the new
library proves their source hypothesis. HLS recursive enumerability is not
claimed. Coverage of the paper's full variable-resource corollary is partial:
fixed-degree dimension-input theorems and identification with its unrestricted
all-degree language are not formalized.

The new companion is `docs/stability_formalization_companion.tex` and its
rendered PDF. The axiom audit covers 454 declarations using only standard
Lean axioms and rejects project-namespaced axiom declarations. The regression
script checks mathematical and coding boundary cases.

## Merged GAS and Lyapunov-stability formalization

Release candidate prepared on 2026-10-08.

This release extends the original homogeneous-GAS completeness artifact with
the Lyapunov-stability half of the cubicization argument.  The extension is
additive: all 824 modules from the GAS-only snapshot are unchanged byte for
byte, and 13 new modules are imported by `HGAS.lean`.

The new modules formalize:

- Lyapunov stability with existence of forward trajectories;
- the uniform-linear-bound and angular-cocycle criteria;
- finite-horizon shadowing for the stabilized Veronese cubic lift;
- preservation of Lyapunov stability by that lift;
- a fixed-parameter primitive-recursive compiler which preserves both GAS
  and Lyapunov stability for source dimension at least two; and
- degree/dimension padding and conditional transfer of Lyapunov-stability
  hardness and undecidability.

In that release, source hardness was an external input to the Lean transfer
theorems. The `Stability` extension above now proves that source result.
The cubicization compiler is computable after `(n,k)` are fixed; the
development does not prove one compiler computable uniformly in varying `(n,k)`.

The preceding GAS-only artifact is the root commit
`d837330957a1ef12ab1bcca6fc7867f9c308ca63`.  It contains the fixed-pair and
cofinal homogeneous-GAS completeness theorem and remains available in Git
history at that commit. The proposed signed tag `gas-completeness-v1` has
not been created.

## Documentation

- `docs/hgas_sigma1_complete_formalization_companion.tex` follows the
  fixed-pair and cofinal GAS-completeness dependency chain.
- `docs/cubicization_hls_formalization_companion.tex` follows the added
  cubicization and Lyapunov-stability dependency chain; its checked rendering
  is `docs/cubicization_hls_formalization_companion.pdf`.
- `docs/stability_formalization_companion.tex` follows the new selector,
  Fourier, effective GAS, and halting-to-HLS proofs; its checked rendering
  is `docs/stability_formalization_companion.pdf`.
- `FORMALIZATION_LEDGER.md` is the authoritative statement-to-module
  crosswalk and records which correspondences are exact, equivalent,
  conditional, or intentionally absent.

## Verification

From the repository root, run:

```bash
lake build HGAS Stability
python3 scripts/check_import_closure.py
lake env lean -DwarningAsError=true scripts/ReleaseAxiomAudit.lean
lake env lean -DwarningAsError=true scripts/StabilityAxiomAudit.lean
lake env lean -DwarningAsError=true scripts/StabilityRegression.lean
```

The expected source counts are 837 modules under `HGAS/`, 796 modules in the
`HGAS.lean` import closure, and 41 modules outside that root. All 251
`Stability` modules belong to the `Stability.lean` closure, which also uses
two of the 41 catalogued HGAS modules. The catalog remains relative to
`HGAS.lean`; its 41 files should also be elaborated before publication.
