import HGAS.Arithmetic.ClosedHorocycleFullCoreNormalizedSeed

set_option linter.hashCommand false
set_option linter.style.longLine false

/-!
# Axiom audit for closed-horocycle full-core normalization

These commands expose the transitive assumptions of the primitive-row
completion, the finite level-two cusp normalization, the exact affine
chart, and the final conversion to the normalized forward detector seed.
-/

#print axioms HGAS.Modular.exists_primitiveRowHorizontalization_of_isPeriodicHorocyclePoint

#print axioms HGAS.Modular.PrimitiveRowHorizontalization.basePath_scaled_eq_horizontal

#print axioms HGAS.Modular.completionGammaTwoFactor_mem

#print axioms HGAS.Modular.reduce_cuspNormalizedCompletion

#print axioms HGAS.Modular.PrimitiveRowHorizontalization.exists_cuspNormalized

#print axioms HGAS.Modular.cuspNormalizedGammaTwoFactor_mem

#print axioms HGAS.ClosedHorocycleFullCoreNormalizedSeed.ClosedHorocycleAffineChart.tau_eq_completed_scaledOrbit

#print axioms HGAS.ClosedHorocycleFullCoreNormalizedSeed.ClosedHorocycleFullCoreNormalization.toNormalizedSeed

#print axioms HGAS.ClosedHorocycleFullCoreNormalizedSeed.ClosedHorocycleFullCoreNormalization.matchesCompiledGaugedBlochPhaseAt
