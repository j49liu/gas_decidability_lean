# Release notes

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

The source theorem from Korda's work is not formalized.  The Lean transfer
theorems take its hardness or undecidability conclusion as an explicit
hypothesis.  The cubicization compiler is computable after `(n,k)` are fixed;
the development does not prove one compiler computable uniformly in varying
`(n,k)`.

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
- `FORMALIZATION_LEDGER.md` is the authoritative statement-to-module
  crosswalk and records which correspondences are exact, equivalent,
  conditional, or intentionally absent.

## Verification

From the repository root, run:

```bash
lake build HGAS
python3 scripts/check_import_closure.py
lake env lean -DwarningAsError=true scripts/ReleaseAxiomAudit.lean
```

The expected source counts are 837 modules under `HGAS/`, 796 modules in the
public import closure, and 41 modules outside it.  The last 41 modules are
catalogued in `LEGACY_MODULES.md` and should also be elaborated before a
release is published.
