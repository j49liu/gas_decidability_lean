import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorDifferentiableClosedChart

set_option linter.style.longLine false

/-!
# Axiom audit for automatic differentiable closed charts

This file is intentionally limited to `#print axioms` commands.
-/

open
  HGAS.NormalizedCorrectedFixedDetectorDifferentiableClosedChart.SelectedBidirectionalValidityOrbit

#print axioms
  HGAS.Modular.horizontalBaseFrame_isPeriodic

#print axioms
  HGAS.Modular.exists_closedUnaryHorocycleChart_of_horizontalLine

#print axioms
  HGAS.Modular.recurrentGenericUnaryTrajectory_exists_differentiable_horizontal_or_exactFrame

#print axioms
  standardizedUnaryColumn_exists_differentiable_closedChart

#print axioms
  standardizedUnaryColumn_exists_selectedFiniteClosedChart

#print axioms
  standardizedUnaryColumn_exists_finiteClosedSelectionData
