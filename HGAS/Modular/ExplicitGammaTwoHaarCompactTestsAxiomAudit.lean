import HGAS.Modular.ExplicitGammaTwoHaarCompactTests

set_option linter.hashCommand false

/-!
# Axiom audit for the Γ(2) compact-cusp-test bridge

These commands expose the transitive trust boundary of the reusable
Radon--Urysohn approximation theorem and its modular clock-contradiction
endpoint.
-/

#print axioms
  HGAS.Dynamics.exists_compactlySupportedContinuous_minorant_integral_gt

#print axioms
  HGAS.Modular.exists_explicitGammaTwoHaar_compactMinorant_integral_gt

#print axioms
  HGAS.Modular.exists_gammaTwoHaar_compactMinorant_integral_gt

#print axioms
  HGAS.Modular.gammaTwoHaar_largeCompactTests_of_cuspLowerBound

#print axioms
  HGAS.Modular.not_gammaTwoHaarGeneric_of_positiveMeanClock_and_cuspLowerBound
