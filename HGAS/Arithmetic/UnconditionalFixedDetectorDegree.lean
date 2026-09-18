import HGAS.Arithmetic.FixedTemplateDetectorDegree
import HGAS.Arithmetic.UnconditionalFixedDQL

/-!
# One detector degree for the unconditional universal-halting family

The universal-halting reduction uses one fixed sparse Diophantine
polynomial.  An input changes only the one parameter substituted into that
polynomial.  `FixedTemplateDetectorDegree` proves that such a specialization
does not change any character exponent and therefore does not change the
degree of the compact detector compiler.

This file names the resulting literal constants for the unconditional DPRM
specialization.  These are noncomputable natural numbers because Mathlib's
DPRM theorem supplies the universal polynomial classically; crucially, they
are independent of the machine input.
-/

namespace HGAS

namespace UniversalHalting

open FixedTemplateDetectorDegree

/-- The fixed sparse polynomial selected by the proved DPRM closure
theorem. -/
noncomputable abbrev unconditionalUniversalPolynomial :=
  (fixedUniversalRepresentation
    binaryPrimitiveRecursiveRelationsAreDiophantine).polynomial

/-- A canonical zero-parameter DQL instance used to name all common
detector resource bounds. -/
noncomputable abbrev unconditionalReferenceDQL :
    DQLSystem unconditionalFixedDQLEquationCount
      unconditionalFixedDQLVariableCount :=
  referenceDQL unconditionalUniversalPolynomial

/-- One input-independent degree bound for the affine detector source. -/
noncomputable abbrev unconditionalDetectorSourceDegree : ℕ :=
  FixedDetectorCompactSourceCode.sourceDegreeBound
    unconditionalReferenceDQL

/-- One input-independent denominator-clearing exponent. -/
noncomputable abbrev unconditionalDetectorClearingExponent : ℕ :=
  FixedDetectorCompactSourceCode.clearingExponent
    unconditionalReferenceDQL

/-- One input-independent degree for the complete compact detector
field/reward compiler. -/
noncomputable abbrev unconditionalDetectorCompilerDegree : ℕ :=
  FixedDetectorCompactSourceCode.compilerDegree
    unconditionalReferenceDQL

/-- The affine detector degree is literally the same for every encoded
universal-machine input. -/
theorem
    unconditionalUniversalHaltingFixedDQL_sourceDegreeBound_eq
    (input : ℕ) :
    FixedDetectorCompactSourceCode.sourceDegreeBound
        (unconditionalUniversalHaltingFixedDQL input) =
      unconditionalDetectorSourceDegree := by
  exact
    sourceDegreeBound_fixedTemplateDQL
      unconditionalUniversalPolynomial (unaryVector input)

/-- The clearing exponent is literally the same for every input. -/
theorem
    unconditionalUniversalHaltingFixedDQL_clearingExponent_eq
    (input : ℕ) :
    FixedDetectorCompactSourceCode.clearingExponent
        (unconditionalUniversalHaltingFixedDQL input) =
      unconditionalDetectorClearingExponent := by
  exact
    clearingExponent_fixedTemplateDQL
      unconditionalUniversalPolynomial (unaryVector input)

/-- **Fixed-degree endpoint for the detector compiler.**

Every member of the unconditional universal-halting family lands in the
same state dimension and has the same raw polynomial degree bound. -/
theorem
    unconditionalUniversalHaltingFixedDQL_compilerDegree_eq
    (input : ℕ) :
    FixedDetectorCompactSourceCode.compilerDegree
        (unconditionalUniversalHaltingFixedDQL input) =
      unconditionalDetectorCompilerDegree := by
  exact
    compilerDegree_fixedTemplateDQL
      unconditionalUniversalPolynomial (unaryVector input)

end UniversalHalting

end HGAS
