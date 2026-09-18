# Canonical modular lambda: global covering completed

Date: 24 July 2026

The boundary recorded in `canonical_lambda_covering_boundary.md` is now
closed without axioms.

The proof factors canonical lambda as

\[
\mathbb H \xrightarrow{q} \mathbb H/\Gamma(2)
 \xrightarrow{\bar\lambda} \mathbb C\setminus\{0,1\}.
\]

The Lean development proves:

1. `q` is a covering map;
2. `\bar\lambda` is a proper local homeomorphism with finite fibers;
3. `\bar\lambda` is surjective, hence a covering map; and
4. a covering map followed by a covering with finite outer fibers is again
   a covering.

The fourth item is isolated as the reusable theorem

```lean
HGAS.Covering.IsCoveringMap.comp_of_finite_fibers
```

in `HGAS/Topology/FiniteOuterCoveringComposition.lean`.  Unlike the
application, the theorem does not assume that the inner map is surjective;
empty inner fibers are handled explicitly.

The resulting global theorem is

```lean
canonicalLambdaPunctured_isCoveringMap_global :
  CanonicalLambdaIsCovering
```

in `HGAS/Modular/CanonicalLambdaQuotient.lean`.  The same file exposes
unconditional path-lifting corollaries:

```lean
canonicalLambdaPunctured_existsUnique_continuous_lift_global
canonicalLambdaPunctured_exists_lift_with_derivatives_global
```

Thus modular-trajectory reconstruction no longer carries the classical
uniformization theorem as an explicit hypothesis.

Validation:

- `lake build HGAS` succeeds;
- the strict scan finds no `sorry`, `admit`, project `axiom`, `unsafe`
  declaration, or equivalent placeholder;
- `#print axioms` for the composition theorem and global covering theorem
  reports only `propext`, `Classical.choice`, and `Quot.sound`.
