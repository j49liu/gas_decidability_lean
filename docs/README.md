# Formalization companions and technical notes

The repository has three companion documents. The first two preserve the
published GAS and cubicization developments; the third documents the
`Stability` library.

## GAS completeness

`hgas_sigma1_complete_formalization_companion.tex` explains the fixed-pair
and cofinal \(\Sigma^0_1\)-completeness proof for homogeneous global
asymptotic stability.  Its PDF is
`hgas_sigma1_complete_formalization_companion.pdf`.

This document follows the dependency chain already present in the original
824-module GAS-only release.  Those modules remain unchanged in the merged
repository.

## Cubicization and Lyapunov stability

`cubicization_hls_formalization_companion.tex` explains the 13-module
extension: Lyapunov stability with forward existence, angular cocycles,
finite-horizon shadowing, the common GAS/HLS cubic compiler, padding, and
conditional transfer of source hardness. Its rendered PDF is
`cubicization_hls_formalization_companion.pdf`.

The document states the formal scope explicitly.  In particular, the bundled
raw-code GAS/HLS compiler assumes source dimension at least two, and its
computability is fixed-parameter rather than uniform in varying `(n,k)`.
The conditional transfer theorems are preserved; the `Stability` library
now supplies their source-hardness hypothesis.

## Further stability results

`stability_formalization_companion.tex` explains the broader ordinary-time
selector, explicit Fourier bounds and printed-gain GAS construction,
degree-input and joint dimension-and-odd-degree-input languages, polynomial
GAS/LAS hardness, and the full halting-to-HLS reduction. Its rendered PDF is
`stability_formalization_companion.pdf`.

The HLS source reduction and its cubic/cofinal hardness consequences are
unconditional; they do not assert recursive enumerability of HLS. The
variable-resource results cover the stated raw languages, not every part
of the paper's variable-resource corollary.

## Authoritative coverage record

`../FORMALIZATION_LEDGER.md` is the authoritative crosswalk between the
research manuscript and Lean.  It distinguishes exact theorem statements
from equivalent formulations, alternative formal routes, conditional
transfer results, and results that are not formalized.

`hgas_formalization_companion.tex` is an earlier predecessor retained for
historical context. The three documents named above are the release
companions.

The remaining Markdown and TeX files in this directory record focused
audits or intermediate mathematical components.  They are not substitutes
for the coverage ledger.
