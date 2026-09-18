import HGAS.Compactification.AllAffinePolynomialCode
import HGAS.Compiler.CompactAccumulatorPipelineComputability
import HGAS.Compiler.CompactAccumulatorPipelineGapCertificate
import HGAS.Modular.LinkedJacobiPolynomialComputability
import HGAS.Modular.LinkedJacobiPolynomialDegrees
import HGAS.Modular.TwoControllerLinkedJacobiPolynomialComputability
import HGAS.Modular.TwoControllerLinkedJacobiPolynomialDegrees
import Mathlib.Tactic

/-!
# The dynamic two-controller linked-Jacobi source in the compact pipeline

This module turns the concrete thirty-six-real-coordinate source into one
literal input of the mixed-central compactification and accumulator
pipeline.

All source coordinates are placed in one affine block; there are no
already compact source blocks.  The source field has ordinary raw degree
at most nine.  We choose the even clearing exponent ten, which both
dominates that degree and is convenient for the later homogeneous
construction.

The twenty linked residual coordinates are not recomputed.  They are
transported from the rightmost twenty-eight-variable linked block into the
full thirty-six-variable space by the generic injective variable
embedding.  Their exact semantics and their simultaneous-vanishing
criterion are proved both on structured states and at arbitrary ambient
points.

The final pipeline field has

```
  (36 + 1) + (20 + 1) = 58
```

real coordinates: one central weight for the affine source block and
twenty residual accumulators plus their common affine coordinate.
-/

namespace HGAS.Modular

open HGAS

namespace TwoControllerLinkedJacobiCompactSourceCode

abbrev sourceDimension : ℕ :=
  TwoControllerLinkedJacobiPolynomialCode.dimension
abbrev residualDimension : ℕ := 10 + 10
abbrev affineBlockCount : ℕ := 1
abbrev compactBlockCount : ℕ := 0

/-- Sharp ordinary degree bound for the coupled source field. -/
abbrev sourceDegreeBound : ℕ := 9

/-- Sharp ordinary degree bound for the transported validity residuals. -/
abbrev residualDegreeBound : ℕ := 4

/-- Even denominator-clearing exponent for the unique affine block. -/
abbrev clearingExponent : ℕ := 10

/-- Dimension of the emitted compactified field and accumulator block. -/
abbrev finalDimension : ℕ :=
  (sourceDimension + affineBlockCount) + (residualDimension + 1)

theorem sourceDimension_eq_thirty_six :
    sourceDimension = 36 :=
  TwoControllerLinkedJacobiPolynomialCode.dimension_eq_thirty_six

theorem residualDimension_eq_twenty :
    residualDimension = 20 := by
  norm_num [residualDimension]

theorem clearingExponent_even :
    clearingExponent % 2 = 0 := by
  norm_num [clearingExponent]

theorem sourceDegree_lt_clearingExponent :
    sourceDegreeBound < clearingExponent := by
  norm_num [sourceDegreeBound, clearingExponent]

/-- Exact requested dimension identity. -/
theorem finalDimension_eq_fifty_eight :
    finalDimension = (36 + 1) + (20 + 1) ∧
      finalDimension = 58 := by
  constructor <;>
    norm_num [finalDimension, sourceDimension,
      affineBlockCount, residualDimension,
      TwoControllerLinkedJacobiPolynomialCode.dimension,
      TwoControllerLinkedJacobiPolynomialCode.controllerPairDimension,
      TwoControllerLinkedJacobiPolynomialCode.ControllerCode.dimension,
      TwoControllerLinkedJacobiPolynomialCode.linkedRealDimension,
      LinkedJacobiPolynomialCode.dimension,
      LinkedJacobiPolynomialCode.unaryDimension,
      LinkedJacobiPolynomialCode.jacobiDimension,
      HGAS.Clocks.ControllerPolynomialCode.dimension,
      UnaryPolynomialCode.modularDimension,
      JacobiPolynomialCode.dimension]

/-- One affine block and no pre-existing compact block. -/
def layout :
    Fin sourceDimension →
      Fin affineBlockCount ⊕ Fin compactBlockCount :=
  MixedCentralPolynomialCode.oneBlockAllAffineLayout sourceDimension

/-- Exact dynamically coupled source field on thirty-six real
coordinates. -/
def sourceFieldCode
    (pΩ pN : RationalCode) :
    PolynomialFieldCode sourceDimension :=
  TwoControllerLinkedJacobiPolynomialCode.fieldCode pΩ pN

/-- Lift the twenty linked real residuals through the right
`28`-coordinate block embedding into all thirty-six variables. -/
def residualCode
    (i : Fin residualDimension) :
    PolynomialCode sourceDimension :=
  PolynomialBlockCode.right
    (m :=
      TwoControllerLinkedJacobiPolynomialCode.controllerPairDimension)
    (LinkedJacobiPolynomialCode.realResidualCode i)

/-! ## Exact source and residual semantics -/

/-- Exact ambient semantics of the uncompactified source field. -/
@[simp]
theorem realize_sourceFieldCode
    (pΩ pN : RationalCode)
    (x : Fin sourceDimension → ℝ) :
    PolynomialFieldCode.realize
        (sourceFieldCode pΩ pN) x =
      TwoControllerLinkedJacobiPolynomialCode.point
        (TwoControllerLinkedJacobiPolynomialCode.vectorField
          (RationalCode.decode pΩ)
          (RationalCode.decode pN)
          (TwoControllerLinkedJacobiPolynomialCode.state x)) :=
  TwoControllerLinkedJacobiPolynomialCode.realize_fieldCode_arbitrary
    pΩ pN x

/-- A lifted scalar residual ignores the controller coordinates and
evaluates exactly as its original linked-block code. -/
@[simp]
theorem eval_residualCode
    (z : TwoControllerLinkedJacobiState)
    (i : Fin residualDimension) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (TwoControllerLinkedJacobiPolynomialCode.point z)
        (PolynomialCode.decode (residualCode i)) =
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (ComplexCoordinates.realifyPoint
          (LinkedJacobiPolynomialCode.point z.linked))
        (PolynomialCode.decode
          (LinkedJacobiPolynomialCode.realResidualCode i)) := by
  rw [residualCode,
    TwoControllerLinkedJacobiPolynomialCode.point,
    PolynomialBlockCode.eval₂Hom_right]

/-- Reassembling the twenty lifted scalar evaluations gives exactly the
ten named complex linked-Jacobi residuals. -/
@[simp]
theorem complexifyPoint_eval_residualCode
    (z : TwoControllerLinkedJacobiState) :
    ComplexCoordinates.complexifyPoint
        (fun q ↦
          MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
            (TwoControllerLinkedJacobiPolynomialCode.point z)
            (PolynomialCode.decode (residualCode q))) =
      fun i ↦
        linkedJacobiResidual
          (LinkedJacobiPolynomialCode.residualIndex i) z.linked := by
  simpa only [eval_residualCode] using
    LinkedJacobiPolynomialCode.complexifyPoint_eval_realResidualCode
      z.linked

/-- Ambient form of the residual semantics theorem. -/
@[simp]
theorem complexifyPoint_eval_residualCode_arbitrary
    (x : Fin sourceDimension → ℝ) :
    ComplexCoordinates.complexifyPoint
        (fun q ↦
          MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
            (PolynomialCode.decode (residualCode q))) =
      fun i ↦
        linkedJacobiResidual
          (LinkedJacobiPolynomialCode.residualIndex i)
          (TwoControllerLinkedJacobiPolynomialCode.state x).linked := by
  have h :=
    complexifyPoint_eval_residualCode
      (TwoControllerLinkedJacobiPolynomialCode.state x)
  simpa using h

/-- Simultaneous vanishing of all lifted scalar residuals is equivalent to
vanishing of every named linked-Jacobi residual. -/
theorem forall_eval_residualCode_eq_zero_iff
    (z : TwoControllerLinkedJacobiState) :
    (∀ q,
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (TwoControllerLinkedJacobiPolynomialCode.point z)
        (PolynomialCode.decode (residualCode q)) = 0) ↔
      ∀ r : LinkedJacobiResidualIndex,
        linkedJacobiResidual r z.linked = 0 := by
  simpa only [eval_residualCode] using
    LinkedJacobiPolynomialCode.forall_eval_realResidualCode_eq_zero_iff
      z.linked

/-- Ambient form of the simultaneous-vanishing criterion. -/
theorem forall_eval_residualCode_eq_zero_iff_arbitrary
    (x : Fin sourceDimension → ℝ) :
    (∀ q,
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (residualCode q)) = 0) ↔
      ∀ r : LinkedJacobiResidualIndex,
        linkedJacobiResidual r
          (TwoControllerLinkedJacobiPolynomialCode.state x).linked = 0 := by
  have h :=
    forall_eval_residualCode_eq_zero_iff
      (TwoControllerLinkedJacobiPolynomialCode.state x)
  simpa using h

/-! ## Total-degree and affine-block ledgers -/

/-- Sharp degree-nine bound for every source-field component. -/
theorem sourceFieldCode_termsDegreeLE
    (pΩ pN : RationalCode) :
    ∀ j, PolynomialCode.TermsDegreeLE sourceDegreeBound
      (sourceFieldCode pΩ pN j) :=
  TwoControllerLinkedJacobiPolynomialCode.fieldCode_termsDegreeLE pΩ pN

/-- Transport preserves the sharp degree-four residual bound. -/
theorem residualCode_termsDegreeLE :
    ∀ i, PolynomialCode.TermsDegreeLE residualDegreeBound
      (residualCode i) := by
  intro i
  exact
    PolynomialCode.termsDegreeLE_injectVariables _
      (LinkedJacobiPolynomialCode.realResidualCode_termsDegreeLE i)

/-- The sharp degree-nine source bound supplies the degree-ten
denominator-clearing premise in the one affine block. -/
theorem sourceFieldCode_termsAffineBlockDegreeLE
    (pΩ pN : RationalCode) :
    ∀ j,
      MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
        layout clearingExponent
        (sourceFieldCode pΩ pN j) := by
  intro j
  apply
    MixedCentralPolynomialCode.termsAffineBlockDegreeLE_oneBlockAllAffineLayout
  exact
    (sourceFieldCode_termsDegreeLE pΩ pN j).promote
      (by
        norm_num [sourceDegreeBound, clearingExponent])

/-- The transported residuals also satisfy the degree-ten clearing
premise. -/
theorem residualCode_termsAffineBlockDegreeLE :
    ∀ i,
      MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
        layout clearingExponent (residualCode i) := by
  intro i
  apply
    MixedCentralPolynomialCode.termsAffineBlockDegreeLE_oneBlockAllAffineLayout
  exact
    (residualCode_termsDegreeLE i).promote
      (by
        norm_num [residualDegreeBound, clearingExponent])

/-- With zero precompact blocks, the base compact-tangency premise is
vacuous. -/
theorem baseCompactTangency
    (pΩ pN : RationalCode) :
    CompactAccumulatorPipelineCode.BaseCompactTangency
      layout clearingExponent
      (sourceFieldCode pΩ pN) := by
  intro y
  dsimp
  intro c
  exact Fin.elim0 c

/-! ## One primitive-recursive call to the compact accumulator pipeline -/

/-- Runtime data, in order: `pΩ`, `pN`, accumulator scale `kappa`, and
strict-sign margin `epsilon`. -/
abbrev CompilerInput :=
  ((RationalCode × RationalCode) × RationalCode) × RationalCode

/-- Convert the concrete four-parameter input to the generic pipeline
input. -/
def toPipelineInput
    (u : CompilerInput) :
    CompactAccumulatorPipelineCode.CompilerInput
      sourceDimension residualDimension :=
  (((u.1.2,
      sourceFieldCode u.1.1.1 u.1.1.2),
    residualCode),
    u.2)

/-- Complete compactified field and reward code.  Its field component is
typed over exactly `Fin 58`. -/
def compile
    (u : CompilerInput) :
    PolynomialFieldCode finalDimension ×
      PolynomialCode finalDimension :=
  CompactAccumulatorPipelineCode.compile
    layout clearingExponent (toPipelineInput u)

/-- The fixed transported residual family is primitive recursive in its
finite index. -/
theorem residualCode_primrec :
    Primrec residualCode :=
  PolynomialBlockCode.right_primrec.comp
    LinkedJacobiPolynomialCode.realResidualCode_primrec

/-- Formation of the generic pipeline input is primitive recursive in all
four packed rational-code parameters. -/
theorem toPipelineInput_primrec :
    Primrec toPipelineInput := by
  have hparameters :
      Primrec (fun u : CompilerInput ↦ u.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hsource :
      Primrec
        (fun u : CompilerInput ↦
          sourceFieldCode u.1.1.1 u.1.1.2) :=
    TwoControllerLinkedJacobiPolynomialCode.fieldCode_primrec.comp
      (Primrec.fst.comp hparameters)
      (Primrec.snd.comp hparameters)
  have hscale :
      Primrec (fun u : CompilerInput ↦ u.1.2) :=
    Primrec.snd.comp Primrec.fst
  exact
    Primrec.pair
      (Primrec.pair
        (Primrec.pair hscale hsource)
        (Primrec.const residualCode))
      Primrec.snd

/-- The complete four-parameter compactification/accumulator compiler is
primitive recursive. -/
theorem compile_primrec :
    Primrec compile :=
  (CompactAccumulatorPipelineCode.compile_primrec
    (m := residualDimension)
    layout clearingExponent).comp
      toPipelineInput_primrec

theorem compile_computable :
    Computable compile :=
  compile_primrec.to_comp

end TwoControllerLinkedJacobiCompactSourceCode

end HGAS.Modular
