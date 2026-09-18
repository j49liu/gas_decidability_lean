import HGAS.Arithmetic.FixedDetectorForwardArbitraryPhaseClassifiedSeries

/-!
# Axiom audit for the forward detector reverse crosswalk

This file is intentionally limited to `#print axioms` commands for the
main forward-time reverse and series endpoints.
-/

open HGAS
open HGAS.ComplexGaugeFamilyPolynomialCode
open HGAS.Modular.ControllerProductLinkedJacobiFamilyPolynomialCode
open HGAS.FixedDetectorForwardTrajectoryReverseCrosswalk
open HGAS.FixedDetectorForwardArbitraryPhaseClassifiedSeries

#print axioms base_hasDerivAt_of_pointAt

#print axioms gauge_hasDerivAt_of_pointAt

#print axioms linkedPoint_hasDerivAt_of_pointAt

#print axioms isStructuredAt_of_hasDerivAt

#print axioms isForwardStructuredTrajectory_of_isForwardTrajectory

#print axioms compactSourcePhysicalPoint_isForwardStructuredTrajectory

#print axioms HGAS.ForwardRecurrentAt.congr_of_eqOn_Ici

#print axioms conclusion_of_hypotheses
