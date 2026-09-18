import HGAS.Modular.GammaTwoScaledPointwiseEquidistribution

/-!
# Axiom audit for signed pointwise horocycle equidistribution

This file keeps the trust report for the orientation-reversal and signed
rescaling bridge separate from its mathematical implementation.
-/

set_option linter.hashCommand false

#print axioms
  HGAS.Modular.gammaTwoFrameOrientationReversal_scaledHorocycleFlow

#print axioms
  HGAS.Modular.IsRightInvariantFrameProbability.orientationReversal_map_eq

#print axioms
  HGAS.Modular.IsForwardGenericFor.tendsto_forwardContinuousOrbitAverageAt

#print axioms
  HGAS.Modular.IsForwardGenericFor.scaledGammaTwoHorocycleFlow_mul_pos

#print axioms
  HGAS.Modular.gammaTwoPointwiseScaledHorocycleEquidistribution_unconditional
