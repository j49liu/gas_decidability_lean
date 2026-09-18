import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorCompactSourceCode
import HGAS.Arithmetic.UnconditionalFixedDetectorDegree
import Mathlib.Tactic

/-!
# Fixed resource bounds for the normalized corrected universal family

The normalized correction changes only coefficients and adds degree-four
radius penalties below the pre-existing validity bound.  Its declared
source, clearing, and compiler degree functions are therefore
definitionally the same degree ledgers as in the original fixed-template
compiler.

This module transports the already proved fixed-template resource theorem
to the normalized corrected compiler used by the final reduction.  The
resulting natural numbers depend on the once-and-for-all DPRM polynomial,
but not on the universal-machine input.
-/

namespace HGAS.UniversalHalting

/-- One input-independent affine-source degree for the normalized
corrected detector. -/
noncomputable abbrev
    unconditionalNormalizedCorrectedDetectorSourceDegree : ℕ :=
  NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound
    unconditionalReferenceDQL

/-- One input-independent denominator-clearing exponent for the
normalized corrected detector. -/
noncomputable abbrev
    unconditionalNormalizedCorrectedDetectorClearingExponent : ℕ :=
  NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent
    unconditionalReferenceDQL

/-- One input-independent degree for the complete normalized corrected
compact field/reward compiler. -/
noncomputable abbrev
    unconditionalNormalizedCorrectedDetectorCompilerDegree : ℕ :=
  NormalizedCorrectedFixedDetectorCompactSourceCode.compilerDegree
    unconditionalReferenceDQL

/-- The normalized corrected affine-source degree is the same for every
encoded input. -/
theorem
    unconditionalUniversalHaltingFixedDQL_normalizedCorrected_sourceDegreeBound_eq
    (input : ℕ) :
    NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDegreeBound
        (unconditionalUniversalHaltingFixedDQL input) =
      unconditionalNormalizedCorrectedDetectorSourceDegree := by
  exact
    unconditionalUniversalHaltingFixedDQL_sourceDegreeBound_eq input

/-- The normalized corrected clearing exponent is the same for every
encoded input. -/
theorem
    unconditionalUniversalHaltingFixedDQL_normalizedCorrected_clearingExponent_eq
    (input : ℕ) :
    NormalizedCorrectedFixedDetectorCompactSourceCode.clearingExponent
        (unconditionalUniversalHaltingFixedDQL input) =
      unconditionalNormalizedCorrectedDetectorClearingExponent := by
  exact
    unconditionalUniversalHaltingFixedDQL_clearingExponent_eq input

/-- The normalized corrected complete compiler degree is the same for
every encoded input. -/
theorem
    unconditionalUniversalHaltingFixedDQL_normalizedCorrected_compilerDegree_eq
    (input : ℕ) :
    NormalizedCorrectedFixedDetectorCompactSourceCode.compilerDegree
        (unconditionalUniversalHaltingFixedDQL input) =
      unconditionalNormalizedCorrectedDetectorCompilerDegree := by
  exact
    unconditionalUniversalHaltingFixedDQL_compilerDegree_eq input

end HGAS.UniversalHalting
