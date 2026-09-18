import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorStandardizedExactFrameExclusion

set_option linter.style.longLine false

/-!
# Axiom audit for standardized exact-frame Haar exclusion

This file is intentionally limited to `#print axioms` commands.  It
checks the reusable analytic bridge, the orientation-free detector
endpoint, and its direct exact-frame composition theorem.
-/

open
  HGAS.NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit.SelectedTwoSidedValidityOrbit
open
  HGAS.NormalizedCorrectedFixedDetectorStandardizedHaarExclusion.SelectedBidirectionalValidityOrbit
open
  HGAS.NormalizedCorrectedFixedDetectorStandardizedExactFrameExclusion.SelectedBidirectionalValidityOrbit
open
  HGAS.NormalizedFixedDetectorUnitSpeedHaarExclusion.SelectedBidirectionalValidityOrbit

#print axioms
  HGAS.Modular.gammaTwoHaar_largeCompactTests_of_positiveMultiple_scaledH4Square_orbitBound

#print axioms
  HGAS.Modular.gammaTwoScaledH4SquareNormPower_eq_unaryC_norm_pow

#print axioms
  unaryC_evenPower_le_inverseClockReciprocal

#print axioms
  not_haarGeneric_of_standardizedExactFrameBranch

#print axioms
  standardizedUnaryColumn_hasHorizontalOrExactNonHaarFrameLift

#print axioms
  standardizedUnaryColumn_hasHorizontalOrPeriodicExactFrameLift

#print axioms
  HGAS.NormalizedCorrectedFixedDetectorStandardizedExactFrameExclusion.gammaTwoSignedNonzeroOrbitEquidistribution_unconditional

#print axioms
  standardizedUnaryColumn_hasHorizontalOrPeriodicFrame_viaSignedDS

#print axioms
  not_unitSpeedHaarGeneric_of_standardizedExactFrameBranch

#print axioms
  periodic_of_standardizedExactFrameBranch

#print axioms
  scaledPeriodic_of_standardizedExactFrameBranch

#print axioms
  standardizedUnaryColumn_hasHorizontalOrPeriodicExactFrameLift_unconditional
