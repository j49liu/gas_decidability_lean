import HGAS.Arithmetic.FixedDetectorCompactSourceCode
import HGAS.Arithmetic.FixedTemplatePolynomialDQL
import Mathlib.Tactic

/-!
# A fixed detector degree for a fixed Diophantine template

The fixed-template DQL compiler stores every specialized numerical
coefficient in a newly appended right-hand-side row.  Its quadratic and
linear tables are independent of the parameter tuple.  This matters for
the detector compiler: all Laurent-character degrees depend only on those
two tables, while the varying right-hand side is handled by the terminal
fixed-degree oscillator.

This module records that separation explicitly.  The endpoint says that
the complete compact-source degree and clearing exponent are constant over
all specializations of one sparse Diophantine template.
-/

namespace HGAS

namespace FixedTemplateDetectorDegree

open Clocks.ControllerPhaseProductCharacterCode

variable {eqs vars : ℕ}

/-- Two DQL systems have the same finite character data when their
quadratic and linear coefficient tables agree.  Their right-hand sides
may differ. -/
structure SameCharacterData
    (I J : DQLSystem eqs vars) : Prop where
  quadratic : I.quadratic = J.quadratic
  linear : I.linear = J.linear

namespace SameCharacterData

variable {I J : DQLSystem eqs vars}

theorem quadraticCharacter_eq
    (h : SameCharacterData I J) (j : Fin vars) :
    DetectorCharacterCode.quadraticCharacter I j =
      DetectorCharacterCode.quadraticCharacter J j := by
  funext phase
  cases phase with
  | inl k =>
      rfl
  | inr row =>
      exact congrFun (congrFun h.quadratic row) j

theorem linearCharacter_eq
    (h : SameCharacterData I J) (j : Fin vars) :
    DetectorCharacterCode.linearCharacter I j =
      DetectorCharacterCode.linearCharacter J j := by
  funext phase
  cases phase with
  | inl k =>
      rfl
  | inr row =>
      exact congrFun (congrFun h.linear row) j

theorem poissonArgumentCharacter_eq
    (h : SameCharacterData I J) (j : Fin vars) :
    DetectorCharacterCode.poissonArgumentCharacter I j =
      DetectorCharacterCode.poissonArgumentCharacter J j := by
  unfold DetectorCharacterCode.poissonArgumentCharacter
  rw [h.quadraticCharacter_eq j]

theorem poissonExponent_eq
    (h : SameCharacterData I J) (j : Fin vars) :
    DetectorPoissonReciprocalCode.poissonExponent I j =
      DetectorPoissonReciprocalCode.poissonExponent J j := by
  unfold DetectorPoissonReciprocalCode.poissonExponent
  rw [h.poissonArgumentCharacter_eq j]

theorem reciprocalExponent_eq
    (h : SameCharacterData I J)
    (k : Fin (DetectorPoissonReciprocalCode.reciprocalCount vars)) :
    DetectorPoissonReciprocalCode.reciprocalExponent I k =
      DetectorPoissonReciprocalCode.reciprocalExponent J k := by
  unfold DetectorPoissonReciprocalCode.reciprocalExponent
  let js := finProdFinEquiv.symm k
  change
    (![DetectorPoissonReciprocalCode.poissonExponent I js.1,
        fun i ↦ -DetectorPoissonReciprocalCode.poissonExponent I js.1 i]
        js.2) =
      (![DetectorPoissonReciprocalCode.poissonExponent J js.1,
        fun i ↦ -DetectorPoissonReciprocalCode.poissonExponent J js.1 i]
        js.2)
  rw [h.poissonExponent_eq js.1]

theorem gaugeExponents_eq
    (h : SameCharacterData I J) (j : Fin vars) :
    DetectorJacobiGaugeData.gaugeExponents I j =
      DetectorJacobiGaugeData.gaugeExponents J j := by
  unfold DetectorJacobiGaugeData.gaugeExponents
    DetectorJacobiGaugeData.gaugeCharacter
  rw [h.linearCharacter_eq j]

theorem linearExponent_eq
    (h : SameCharacterData I J) (j : Fin vars) :
    FixedDetectorMomentCode.linearExponent I j =
      FixedDetectorMomentCode.linearExponent J j := by
  unfold FixedDetectorMomentCode.linearExponent
  rw [h.linearCharacter_eq j]

theorem jacobiPlusExponent_eq
    (h : SameCharacterData I J) (j : Fin vars) :
    FixedDetectorMomentCode.jacobiPlusExponent I j =
      FixedDetectorMomentCode.jacobiPlusExponent J j := by
  unfold FixedDetectorMomentCode.jacobiPlusExponent
  rw [h.linearExponent_eq j]

theorem jacobiMinusExponent_eq
    (h : SameCharacterData I J) (j : Fin vars) :
    FixedDetectorMomentCode.jacobiMinusExponent I j =
      FixedDetectorMomentCode.jacobiMinusExponent J j := by
  unfold FixedDetectorMomentCode.jacobiMinusExponent
  rw [h.linearExponent_eq j]

theorem reciprocalExponentEnergySum_eq
    (h : SameCharacterData I J) :
    FixedDetectorPolynomialCode.reciprocalExponentEnergySum I =
      FixedDetectorPolynomialCode.reciprocalExponentEnergySum J := by
  unfold FixedDetectorPolynomialCode.reciprocalExponentEnergySum
  apply Finset.sum_congr rfl
  intro k _
  rw [h.reciprocalExponent_eq k]

theorem gaugeExponentEnergySum_eq
    (h : SameCharacterData I J) :
    FixedDetectorPolynomialCode.gaugeExponentEnergySum I =
      FixedDetectorPolynomialCode.gaugeExponentEnergySum J := by
  unfold FixedDetectorPolynomialCode.gaugeExponentEnergySum
  apply Finset.sum_congr rfl
  intro j _
  rw [h.gaugeExponents_eq j]

theorem momentCharacterEnergySum_eq
    (h : SameCharacterData I J) :
    FixedDetectorMomentCode.momentCharacterEnergySum I =
      FixedDetectorMomentCode.momentCharacterEnergySum J := by
  unfold FixedDetectorMomentCode.momentCharacterEnergySum
  apply Finset.sum_congr rfl
  intro j _
  rw [h.jacobiPlusExponent_eq j,
    h.jacobiMinusExponent_eq j]

theorem fieldDegree_eq
    (h : SameCharacterData I J) :
    FixedDetectorPolynomialCode.fieldDegree I =
      FixedDetectorPolynomialCode.fieldDegree J := by
  unfold FixedDetectorPolynomialCode.fieldDegree
  rw [h.reciprocalExponentEnergySum_eq]

theorem validityDegree_eq
    (h : SameCharacterData I J) :
    FixedDetectorValidityEnergyCode.validityDegree I =
      FixedDetectorValidityEnergyCode.validityDegree J := by
  unfold FixedDetectorValidityEnergyCode.validityDegree
    FixedDetectorValidityEnergyCode.gaugeResidualEnergyDegree
    FixedDetectorValidityEnergyCode.reciprocalResidualEnergyDegree
  rw [h.gaugeExponentEnergySum_eq,
    h.reciprocalExponentEnergySum_eq]

theorem momentDegree_eq
    (h : SameCharacterData I J) :
    FixedDetectorMomentCode.momentDegree I =
      FixedDetectorMomentCode.momentDegree J := by
  unfold FixedDetectorMomentCode.momentDegree
  rw [h.momentCharacterEnergySum_eq]

theorem driftDegree_eq
    (h : SameCharacterData I J) :
    FixedDetectorDriftCode.driftDegree I =
      FixedDetectorDriftCode.driftDegree J := by
  unfold FixedDetectorDriftCode.driftDegree
  rw [h.validityDegree_eq, h.momentDegree_eq]

theorem sourceDegreeBound_eq
    (h : SameCharacterData I J) :
    FixedDetectorCompactSourceCode.sourceDegreeBound I =
      FixedDetectorCompactSourceCode.sourceDegreeBound J := by
  unfold FixedDetectorCompactSourceCode.sourceDegreeBound
  rw [h.fieldDegree_eq, h.driftDegree_eq]

theorem clearingExponent_eq
    (h : SameCharacterData I J) :
    FixedDetectorCompactSourceCode.clearingExponent I =
      FixedDetectorCompactSourceCode.clearingExponent J := by
  unfold FixedDetectorCompactSourceCode.clearingExponent
  rw [h.sourceDegreeBound_eq]

theorem compactFieldDegree_eq
    (h : SameCharacterData I J) :
    FixedDetectorCompactSourceCode.compactFieldDegree I =
      FixedDetectorCompactSourceCode.compactFieldDegree J := by
  unfold FixedDetectorCompactSourceCode.compactFieldDegree
  rw [h.sourceDegreeBound_eq, h.clearingExponent_eq]

theorem compilerDegree_eq
    (h : SameCharacterData I J) :
    FixedDetectorCompactSourceCode.compilerDegree I =
      FixedDetectorCompactSourceCode.compilerDegree J := by
  unfold FixedDetectorCompactSourceCode.compilerDegree
  rw [h.compactFieldDegree_eq]

end SameCharacterData

/-! ## Specialization to a single sparse polynomial template -/

variable {m k : ℕ}

/-- Parameter specialization changes only right-hand-side values. -/
theorem fixedTemplateDQL_sameCharacterData
    (polynomial : IntegerPolynomialCode (m + k))
    (a b : Fin m → ℕ) :
    SameCharacterData
      (FixedTemplatePolynomialDQL.fixedTemplateDQL polynomial a)
      (FixedTemplatePolynomialDQL.fixedTemplateDQL polynomial b) := by
  constructor
  · rfl
  · rfl

/-- A canonical reference specialization, used only to name the common
degree of one fixed template. -/
def referenceDQL
    (polynomial : IntegerPolynomialCode (m + k)) :
    DQLSystem
      (FixedTemplatePolynomialDQL.templateEquationCount polynomial)
      (FixedTemplatePolynomialDQL.templateVariableCount polynomial) :=
  FixedTemplatePolynomialDQL.fixedTemplateDQL polynomial
    (fun _ ↦ 0)

/-- The raw affine detector degree is constant over all parameter
specializations of one fixed template. -/
theorem sourceDegreeBound_fixedTemplateDQL
    (polynomial : IntegerPolynomialCode (m + k))
    (parameters : Fin m → ℕ) :
    FixedDetectorCompactSourceCode.sourceDegreeBound
        (FixedTemplatePolynomialDQL.fixedTemplateDQL
          polynomial parameters) =
      FixedDetectorCompactSourceCode.sourceDegreeBound
        (referenceDQL polynomial) :=
  (fixedTemplateDQL_sameCharacterData polynomial parameters
    (fun _ ↦ 0)).sourceDegreeBound_eq

/-- The denominator-clearing exponent is likewise one literal constant. -/
theorem clearingExponent_fixedTemplateDQL
    (polynomial : IntegerPolynomialCode (m + k))
    (parameters : Fin m → ℕ) :
    FixedDetectorCompactSourceCode.clearingExponent
        (FixedTemplatePolynomialDQL.fixedTemplateDQL
          polynomial parameters) =
      FixedDetectorCompactSourceCode.clearingExponent
        (referenceDQL polynomial) :=
  (fixedTemplateDQL_sameCharacterData polynomial parameters
    (fun _ ↦ 0)).clearingExponent_eq

/-- Endpoint: the complete compact field/reward compiler has a single
parameter-independent raw degree bound for a fixed template. -/
theorem compilerDegree_fixedTemplateDQL
    (polynomial : IntegerPolynomialCode (m + k))
    (parameters : Fin m → ℕ) :
    FixedDetectorCompactSourceCode.compilerDegree
        (FixedTemplatePolynomialDQL.fixedTemplateDQL
          polynomial parameters) =
      FixedDetectorCompactSourceCode.compilerDegree
        (referenceDQL polynomial) :=
  (fixedTemplateDQL_sameCharacterData polynomial parameters
    (fun _ ↦ 0)).compilerDegree_eq

end FixedTemplateDetectorDegree

end HGAS
