# Release checklist

This file records the checks for publishing both libraries and
optional follow-up steps for citation metadata and signed releases.

## Completed for the merged release (2026-10-08)

- [x] Base the release branch on GitHub `main` commit
  `d837330957a1ef12ab1bcca6fc7867f9c308ca63`.
- [x] Retain all 824 GAS-only modules byte for byte.
- [x] Add the 13 audited HLS, shadowing, and propagation modules.
- [x] Import the added modules from `HGAS.lean`.
- [x] Update the README, coverage ledger, legacy catalog, and import checker.
- [x] Add a separate HLS/cubicization companion source.
- [x] Render and visually inspect the 15-page HLS/cubicization companion PDF.
- [x] Add a reproducible release axiom audit.
- [x] Verify the public root and the 837/796/41 import counts.
- [x] Elaborate all 41 outside-closure modules directly with
  `-DwarningAsError=true`.
- [x] Verify the repository-local author identity is
  `Jun Liu <23146644+j49liu@users.noreply.github.com>`, matching the
  canonical remote commit.
- [x] Identify the copyright holders as Jun Liu and Ivan O. Shevchenko.
- [x] License the formalization under the Apache License, Version 2.0.
- [x] Link the accompanying paper, arXiv:2610.12434, from the README.

## Stability extension

- [x] Preserve the 837 published `HGAS` modules and pinned dependencies.
- [x] Import all 251 added modules from `Stability.lean`.
- [x] Add and render `docs/stability_formalization_companion.tex`.
- [x] Record exact coverage and limitations in `FORMALIZATION_LEDGER.md`.
- [x] Add `scripts/StabilityAxiomAudit.lean` and
  `scripts/StabilityRegression.lean`.
- [x] Extend the import checker to both roots and report shared legacy dependencies.
- [x] Build both libraries and run both axiom audits and the Stability regressions.

## Optional follow-up requiring an author decision or credential

- [ ] Add `CITATION.cff` using the paper metadata linked in the README and
  the approved formalization author list.
- [ ] Register the existing ED25519 public key with GitHub as an SSH
  signing key, start an `ssh-agent`, and unlock the private key.
- [ ] Configure Git to sign commits and tags with that key.
- [ ] Create a signed annotated historical tag, proposed name
  `gas-completeness-v1`, on commit `d837330957a1ef12ab1bcca6fc7867f9c308ca63`.
- [ ] For a future signed release, review the diff and create a signed commit.
- [ ] Create a signed release tag, proposed name
  `paper-formalization-v1`, on the reviewed commit.

Signing and tags are not prerequisites for a normal source-code push.

## Final verification before a push

Run the following commands from the repository root:

```bash
git fetch origin
lake build HGAS Stability
python3 scripts/check_import_closure.py
while IFS= read -r legacy_module; do
  lake env lean -DwarningAsError=true "$legacy_module" || exit 1
done < <(sed -n 's/^[0-9][0-9]*\. `\(HGAS\/[^`]*\.lean\)`$/\1/p' LEGACY_MODULES.md)
lake env lean -DwarningAsError=true scripts/ReleaseAxiomAudit.lean
lake env lean -DwarningAsError=true scripts/StabilityAxiomAudit.lean
lake env lean -DwarningAsError=true scripts/StabilityRegression.lean
git diff --check origin/main...HEAD
git diff --check
git status --porcelain
git merge-base --is-ancestor origin/main HEAD
git rev-list --left-right --count origin/main...HEAD
git config --get user.name
git config --get user.email
```

Both library targets are explicit because plain `lake build` defaults to
`HGAS` only. Inspect both axiom-audit outputs for dependencies outside
`propext`, `Classical.choice`, and `Quot.sound`.

After the reviewed changes have been committed, the status output must be
empty, and the revision count must begin with `0`,
which shows that the release commit is a fast-forward descendant of the
current remote branch. The two identity commands must print the reviewed name
and email above. Build against the committed `lake-manifest.json`; dependency
updates should be reviewed separately. If signed tags have been created,
review them and the commit signatures with:

```bash
git tag --list --format='%(refname:short) %(objectname)'
git verify-tag gas-completeness-v1
git verify-tag paper-formalization-v1
git log --show-signature --decorate --oneline origin/main..HEAD
```

Push the reviewed branch only after these checks pass. Push signed tags
only after separate author approval and successful signature verification.
