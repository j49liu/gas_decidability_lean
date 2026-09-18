import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorTwoSidedStructuredOrbit
import HGAS.Arithmetic.FixedDetectorReverseTrajectoryCrosswalk
import Mathlib.Tactic

/-!
# Complete semantic structure of the normalized corrected selected orbit

The two-sided physical clock produces a complete ordinary-time solution of
the literal fixed-detector polynomial field.  Applying the reverse compiler
therefore recovers every nested semantic equation for all real times.

This is stronger than the positive-ray interface used by the older compact
source argument.  In particular it permits a reversal of physical time when
the signed modular controller frequency is negative.
-/

namespace HGAS.NormalizedCorrectedFixedDetectorTwoSidedCompleteStructure

open HGAS
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit

noncomputable section

variable {eqs vars : ℕ}
variable
  {u :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      eqs vars}

namespace SelectedTwoSidedValidityOrbit

variable
  (O : SelectedTwoSidedValidityOrbit u)

/-- The selected physical detector orbit satisfies all nested compiler
equations on the whole real line. -/
theorem physicalPoint_isStructuredTrajectory :
    FixedDetectorReverseTrajectoryCrosswalk.IsStructuredTrajectory
      (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
      O.physicalPoint := by
  apply
    FixedDetectorReverseTrajectoryCrosswalk.isStructuredTrajectory_of_isIntegralCurve
  simpa only [
    NormalizedCorrectedFixedDetectorCompactSourceCode.sourceFieldCode] using
    O.physicalPoint_isIntegralCurve

end SelectedTwoSidedValidityOrbit

end

end HGAS.NormalizedCorrectedFixedDetectorTwoSidedCompleteStructure
