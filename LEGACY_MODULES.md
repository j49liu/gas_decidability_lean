# Modules outside the public `HGAS` import closure

Import closures last verified: 2026-10-31

The transitive import closure of `HGAS.lean` contains 796 of the 837
modules under `HGAS/`. The 41 modules below are outside that closure.
They are retained as historical alternatives, intermediate experiments,
or audit/query modules; none is a dependency of an endpoint exported by
`HGAS.lean`. Items 33 and 35, `GammaTwoHorocycleOrientationReversal.lean`
and `GammaTwoScaledPointwiseEquidistribution.lean`, are dependencies of
`Stability.lean` through `Stability/Selection/LinearThetaCuspExclusion.lean`.
They remain outside the `HGAS` root, so the catalog below is unchanged.

The 13 modules added for Lyapunov stability, shadowing, and the common
GAS/HLS cubic compiler all belong to the public closure. Consequently, the
outside set below is unchanged from the preceding 824-module GAS release.

Outside the public closure does **not** mean that a file fails to
elaborate or that every declaration in it is false. All 41 files were
directly elaborated in the pinned Lean 4.30.0/Mathlib v4.30.0 environment
with:

```text
lake env lean -DwarningAsError=true <module>
```

All 41 returned exit status zero. Together with the 796-module public
closure, this gives direct verification coverage of all 837 source
modules at this snapshot.

The exact closure and catalog equality can be reproduced from the
repository root with:

```text
python3 scripts/check_import_closure.py
```

## Exact list

1. `HGAS/Analysis/RadicalAggregatedFourierComponent.lean`
2. `HGAS/Analysis/RadicalTorusComponentFiniteGraph.lean`
3. `HGAS/Arithmetic/ClosedHorocycleFullCoreNormalizedSeed.lean`
4. `HGAS/Arithmetic/ClosedHorocycleFullCoreNormalizedSeedAxiomAudit.lean`
5. `HGAS/Arithmetic/CorrectedFixedDetectorExplicitFiniteGraphGap.lean`
6. `HGAS/Arithmetic/CorrectedFixedDetectorFiniteGraphBridge.lean`
7. `HGAS/Arithmetic/CorrectedFixedDetectorForwardStructuredOrbit.lean`
8. `HGAS/Arithmetic/CorrectedFixedDetectorPhysicalMomentAverages.lean`
9. `HGAS/Arithmetic/CorrectedFixedDetectorRHSZeroObstruction.lean`
10. `HGAS/Arithmetic/CorrectedFixedDetectorValidityOrbit.lean`
11. `HGAS/Arithmetic/FixedDetectorArbitraryPhaseClassifiedSeries.lean`
12. `HGAS/Arithmetic/FixedDetectorForwardArbitraryPhaseClassifiedSeries.lean`
13. `HGAS/Arithmetic/FixedDetectorForwardTrajectoryReverseAxiomAudit.lean`
14. `HGAS/Arithmetic/FixedDetectorNormalizedForwardBlochColumnAxiomAudit.lean`
15. `HGAS/Arithmetic/NormalizedCorrectedAugmentedFamilyFromTheta.lean`
16. `HGAS/Arithmetic/NormalizedCorrectedFixedDetectorControllerLocking.lean`
17. `HGAS/Arithmetic/NormalizedCorrectedFixedDetectorDifferentiableClosedChartAxiomAudit.lean`
18. `HGAS/Arithmetic/NormalizedCorrectedFixedDetectorForwardStructuredOrbit.lean`
19. `HGAS/Arithmetic/NormalizedCorrectedFixedDetectorGammaTwoHaarExclusion.lean`
20. `HGAS/Arithmetic/NormalizedCorrectedFixedDetectorPhysicalMomentAverages.lean`
21. `HGAS/Arithmetic/NormalizedCorrectedFixedDetectorStandardizedExactFrameExclusion.lean`
22. `HGAS/Arithmetic/NormalizedCorrectedFixedDetectorStandardizedHaarExclusionAxiomAudit.lean`
23. `HGAS/Arithmetic/NormalizedCorrectedFixedDetectorValidityOrbit.lean`
24. `HGAS/Arithmetic/NormalizedCorrectedUnconditionalCompactResources.lean`
25. `HGAS/Arithmetic/NormalizedCorrectedUnconditionalFamilyFromGap.lean`
26. `HGAS/Arithmetic/NormalizedCorrectedUnconditionalFixedDetectorDegree.lean`
27. `HGAS/Compiler/AllAffineConditionalGenericZeroOrbit.lean`
28. `HGAS/Compiler/AllAffineErgodicPhysicalZeroOrbit.lean`
29. `HGAS/Compiler/AllAffinePhysicalDriftAverages.lean`
30. `HGAS/Modular/ExplicitGammaTwoHaarCompactTestsAxiomAudit.lean`
31. `HGAS/Modular/GammaTwoGenericPointAlternative.lean`
32. `HGAS/Modular/GammaTwoH4SquareCompactTests.lean`
33. `HGAS/Modular/GammaTwoHorocycleOrientationReversal.lean`
34. `HGAS/Modular/GammaTwoOccupationInputsUnconditionalAxiomAudit.lean`
35. `HGAS/Modular/GammaTwoScaledPointwiseEquidistribution.lean`
36. `HGAS/Modular/GammaTwoScaledPointwiseEquidistributionAxiomAudit.lean`
37. `HGAS/Modular/GammaTwoStateMarginalClosed.lean`
38. `HGAS/Modular/GammaTwoUniformNonescapeAxiomAudit.lean`
39. `HGAS/Modular/HorizontalThetaHeightSelector.lean`
40. `HGAS/Modular/JacobiThreeMomentRigidity.lean`
41. `HGAS/Modular/ZeroLinearJacobiSelectorRigidity.lean`

## Routing cautions

- `JacobiThreeMomentRigidity.lean` and
  `ZeroLinearJacobiSelectorRigidity.lean` contain valid conditional
  algebraic statements, but their old zero-ratio narrative is not the
  selector used by the theorem. The manuscript gives a counterexample to
  the attempted general zero-ratio inference. The live endpoint uses
  `Modular/JacobiThreeMomentTargetRigidity.lean` with an irrational-ratio
  hypothesis and proves that hypothesis after nonzero-column augmentation.
- `NormalizedCorrectedUnconditionalFamilyFromGap.lean` is the older
  unaugmented conditional route. The completed family is
  `Arithmetic/NormalizedCorrectedAugmentedEffectiveFamily.lean`.
- Files with `AxiomAudit` in their names are diagnostic `#print axioms`
  modules. They do not introduce project axioms.

Two related modules remain in the public closure but are not confused
with the final routing:

- `Arithmetic/CorrectedJacobiSelectorCentering.lean` is live coefficient
  infrastructure, although its zero-column branch is unreachable after
  augmentation.
- `Modular/RecurrentMeasureClassification.lean` is a valid generic
  conditional interface. Its base classification theorem also feeds the
  alternative `GammaTwoStateMarginalClosed.lean` module; the endpoint does
  not use its finite-permutation-cover specializations and follows a
  different unconditional pointwise route.

The `HGAS` root should not import the 41 files merely to make a coverage
count look simpler. Keeping the endpoint closure narrow makes the theorem
dependency graph auditable.
