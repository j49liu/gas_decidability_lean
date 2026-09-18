import HGAS.Clocks.ControllerPhaseProductCircleLayout
import HGAS.Compactification.RightAffineLeftCompactLayout
import HGAS.Compiler.CompactAccumulatorPipelineComputability
import HGAS.Compiler.CompactAccumulatorPipelineGapCertificate
import HGAS.Modular.ControllerProductLinkedJacobiPolynomialComputability
import HGAS.Modular.ControllerProductLinkedJacobiPolynomialDegrees
import HGAS.Modular.LinkedJacobiPolynomialComputability
import HGAS.Modular.LinkedJacobiPolynomialDegrees
import Mathlib.Tactic

/-!
# A mixed compact source for a finite controller product and one linked Jacobi block

Fix `q` controller--phase clocks.  Their `4q` real coordinates already
come in `2q` invariant circles:

```
        (r_a,s_a)      and      (c_a,d_a),       a : Fin q.
```

The remaining twenty-eight real coordinates form one linked
unary--Jacobi block.  They are affine and are centrally compactified by
one new chart coordinate.  Thus the canonical layout has

* `2q` inherited compact circle blocks on the left; and
* one affine block on the right.

Three rational tuples are runtime parameters.  The first tuple specifies
the controller fields; the second and third specify the two rational
linear frequency readouts used by the linked Jacobi block.  The source
field has controller/linked bidegree at most `(3,8)` and ordinary degree
at most nine.  Consequently the even clearing exponent eight is enough.

The validity observable consists of the twenty real coordinates of the
ten complex linked-Jacobi residuals.  This file proves their exact
semantics, exact source semantics at arbitrary ambient points, and global
tangency to every inherited circle before and after denominator
clearing.  It then packages the construction into the reusable compact
accumulator compiler.

The proof of compact tangency is worth emphasizing.  Every output
coordinate belonging to an inherited circle has right-affine degree
zero.  Hence compact-support homogenization multiplies that coordinate
by the common slowdown even at the affine equator.  Since the original
finite clock-product field is algebraically tangent at every ambient
point, the cleared field remains tangent globally; no division by a
chart coordinate and no circle equation is used.
-/

namespace HGAS.Modular

open HGAS

namespace ControllerProductLinkedJacobiMixedCompactSourceCode

open HGAS.Clocks

variable {q : ℕ}

/-- Dimension `4q+28` of the uncompactified coupled source. -/
abbrev sourceDimension (q : ℕ) : ℕ :=
  ControllerProductLinkedJacobiPolynomialCode.dimension q

/-- The ten complex residuals are represented by twenty real
coordinates. -/
abbrev residualDimension : ℕ := 10 + 10

/-- The linked block is the unique affine block. -/
abbrev affineBlockCount : ℕ := 1

/-- Each of the `q` controller--phase clocks contributes two circles. -/
abbrev compactBlockCount (q : ℕ) : ℕ :=
  ControllerPhaseProductCircleLayout.circleCount q

/-- Number of left controller coordinates. -/
abbrev controllerDimension (q : ℕ) : ℕ :=
  ControllerProductLinkedJacobiPolynomialCode.controllerDimension q

/-- Number of right linked coordinates. -/
abbrev linkedDimension : ℕ :=
  ControllerProductLinkedJacobiPolynomialCode.linkedRealDimension

/-- Sharp degree bound in the unique affine linked block. -/
abbrev affineDegreeBound : ℕ := 8

/-- Even denominator-clearing exponent. -/
abbrev clearingExponent : ℕ := 8

/-- Dimension after adjoining one affine chart coordinate and the
twenty-dimensional accumulator sphere. -/
abbrev finalDimension (q : ℕ) : ℕ :=
  (sourceDimension q + affineBlockCount) + (residualDimension + 1)

theorem sourceDimension_eq
    (q : ℕ) :
    sourceDimension q = q * 4 + 28 := by
  norm_num [sourceDimension,
    ControllerProductLinkedJacobiPolynomialCode.dimension,
    ControllerProductLinkedJacobiPolynomialCode.controllerDimension,
    ControllerProductLinkedJacobiPolynomialCode.linkedRealDimension,
    ControllerPhaseProductPolynomialCode.dimension,
    ControllerPolynomialCode.dimension,
    LinkedJacobiPolynomialCode.dimension,
    LinkedJacobiPolynomialCode.unaryDimension,
    LinkedJacobiPolynomialCode.jacobiDimension,
    UnaryPolynomialCode.modularDimension,
    JacobiPolynomialCode.dimension]

theorem residualDimension_eq_twenty :
    residualDimension = 20 := by
  norm_num [residualDimension]

theorem compactBlockCount_eq
    (q : ℕ) :
    compactBlockCount q = 2 * q := by
  simp [compactBlockCount,
    ControllerPhaseProductCircleLayout.circleCount,
    ControllerPhaseProductCircleLayout.localCircleCount,
    Nat.mul_comm]

theorem clearingExponent_even :
    clearingExponent % 2 = 0 := by
  norm_num [clearingExponent]

theorem finalDimension_eq
    (q : ℕ) :
    finalDimension q = q * 4 + 50 := by
  rw [finalDimension, sourceDimension_eq]
  norm_num [affineBlockCount, residualDimension]

/-! ## Layout and finite source codes -/

/-- Keep the `2q` clock circles compact and put the complete linked block
in the unique right affine block. -/
def layout (q : ℕ) :
    Fin (sourceDimension q) →
      Fin affineBlockCount ⊕ Fin (compactBlockCount q) :=
  RightAffineLeftCompactLayout.layout
    ControllerPhaseProductCircleLayout.circleBlock

/-- Exact coupled source field with one controller tuple and two
frequency-weight tuples. -/
def sourceFieldCode
    (parameters omegaWeights numberWeights :
      Fin q → RationalCode) :
    PolynomialFieldCode (sourceDimension q) :=
  ControllerProductLinkedJacobiPolynomialCode.fieldCode
    parameters omegaWeights numberWeights

/-- The twenty real validity residuals depend only on the right linked
block. -/
def residualCode
    (q : ℕ) (i : Fin residualDimension) :
    PolynomialCode (sourceDimension q) :=
  PolynomialBlockCode.right
    (m := controllerDimension q)
    (LinkedJacobiPolynomialCode.realResidualCode i)

/-! ## Exact source semantics -/

@[simp]
theorem realize_sourceFieldCode
    (parameters omegaWeights numberWeights :
      Fin q → RationalCode)
    (x : Fin (sourceDimension q) → ℝ) :
    PolynomialFieldCode.realize
        (sourceFieldCode parameters omegaWeights numberWeights) x =
      ControllerProductLinkedJacobiPolynomialCode.point
        (ControllerProductLinkedJacobiPolynomialCode.vectorField
          (fun i ↦
            (RationalCode.decode (parameters i) : ℝ))
          (fun i ↦
            (RationalCode.decode (omegaWeights i) : ℝ))
          (fun i ↦
            (RationalCode.decode (numberWeights i) : ℝ))
          (ControllerProductLinkedJacobiPolynomialCode.state x)) :=
  ControllerProductLinkedJacobiPolynomialCode.realize_fieldCode_arbitrary
    parameters omegaWeights numberWeights x

/-! ## Exact validity-residual semantics -/

/-- A lifted residual ignores all controller coordinates. -/
@[simp]
theorem eval_residualCode
    (z : ControllerProductLinkedJacobiState q)
    (i : Fin residualDimension) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (ControllerProductLinkedJacobiPolynomialCode.point z)
        (PolynomialCode.decode (residualCode q i)) =
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (ComplexCoordinates.realifyPoint
          (LinkedJacobiPolynomialCode.point z.linked))
        (PolynomialCode.decode
          (LinkedJacobiPolynomialCode.realResidualCode i)) := by
  rw [residualCode,
    ControllerProductLinkedJacobiPolynomialCode.point,
    PolynomialBlockCode.eval₂Hom_right]

/-- Reassembling the twenty scalar evaluations gives the ten named
complex linked-Jacobi residuals. -/
@[simp]
theorem complexifyPoint_eval_residualCode
    (z : ControllerProductLinkedJacobiState q) :
    ComplexCoordinates.complexifyPoint
        (fun i ↦
          MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
            (ControllerProductLinkedJacobiPolynomialCode.point z)
            (PolynomialCode.decode (residualCode q i))) =
      fun i ↦
        linkedJacobiResidual
          (LinkedJacobiPolynomialCode.residualIndex i) z.linked := by
  simpa only [eval_residualCode] using
    LinkedJacobiPolynomialCode.complexifyPoint_eval_realResidualCode
      z.linked

/-- Ambient version of the residual semantics theorem. -/
@[simp]
theorem complexifyPoint_eval_residualCode_arbitrary
    (x : Fin (sourceDimension q) → ℝ) :
    ComplexCoordinates.complexifyPoint
        (fun i ↦
          MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
            (PolynomialCode.decode (residualCode q i))) =
      fun i ↦
        linkedJacobiResidual
          (LinkedJacobiPolynomialCode.residualIndex i)
          (ControllerProductLinkedJacobiPolynomialCode.state x).linked := by
  have h :=
    complexifyPoint_eval_residualCode
      (ControllerProductLinkedJacobiPolynomialCode.state x)
  simpa using h

/-- Simultaneous scalar vanishing is exactly validity of every named
linked-Jacobi residual. -/
theorem forall_eval_residualCode_eq_zero_iff
    (z : ControllerProductLinkedJacobiState q) :
    (∀ i,
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (ControllerProductLinkedJacobiPolynomialCode.point z)
        (PolynomialCode.decode (residualCode q i)) = 0) ↔
      ∀ r : LinkedJacobiResidualIndex,
        linkedJacobiResidual r z.linked = 0 := by
  simpa only [eval_residualCode] using
    LinkedJacobiPolynomialCode.forall_eval_realResidualCode_eq_zero_iff
      z.linked

/-- Ambient form of the simultaneous-vanishing criterion. -/
theorem forall_eval_residualCode_eq_zero_iff_arbitrary
    (x : Fin (sourceDimension q) → ℝ) :
    (∀ i,
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (residualCode q i)) = 0) ↔
      ∀ r : LinkedJacobiResidualIndex,
        linkedJacobiResidual r
          (ControllerProductLinkedJacobiPolynomialCode.state x).linked = 0 := by
  have h :=
    forall_eval_residualCode_eq_zero_iff
      (ControllerProductLinkedJacobiPolynomialCode.state x)
  simpa using h

/-! ## Circle geometry and original-field tangency -/

/-- The compact-block dot product of the mixed layout is exactly the
canonical circle dot product on the left controller coordinates. -/
theorem compactBlockDot_layout
    {R : Type*} [CommRing R]
    (x v : Fin (sourceDimension q) → R)
    (c : Fin (compactBlockCount q)) :
    MixedCentralPolynomialCode.compactBlockDot (layout q) x v c =
      ControllerPhaseProductCircleLayout.circleDot
        (x ∘
          ControllerProductLinkedJacobiPolynomialCode.controllersEmbedding)
        (v ∘
          ControllerProductLinkedJacobiPolynomialCode.controllersEmbedding)
        c := by
  unfold layout
  rw [RightAffineLeftCompactLayout.compactBlockDot_layout]
  rfl

/-- Restricting the complete coupled source velocity to controller
coordinates recovers the block-diagonal controller-product velocity. -/
theorem sourceVelocity_controllers
    (parameters omegaWeights numberWeights :
      Fin q → RationalCode)
    (x : Fin (sourceDimension q) → ℝ) :
    (PolynomialFieldCode.realize
        (sourceFieldCode parameters omegaWeights numberWeights) x) ∘
        ControllerProductLinkedJacobiPolynomialCode.controllersEmbedding =
      PolynomialFieldCode.realize
        (ControllerProductLinkedJacobiPolynomialCode.controllerFieldCode
          parameters)
        (x ∘
          ControllerProductLinkedJacobiPolynomialCode.controllersEmbedding) := by
  funext i
  change
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode
          (sourceFieldCode parameters omegaWeights numberWeights
            (ControllerProductLinkedJacobiPolynomialCode.controllersEmbedding
              i))) =
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (x ∘
          ControllerProductLinkedJacobiPolynomialCode.controllersEmbedding)
        (PolynomialCode.decode
          (ControllerProductLinkedJacobiPolynomialCode.controllerFieldCode
            parameters i))
  rw [sourceFieldCode,
    ControllerProductLinkedJacobiPolynomialCode.fieldCode_controllersEmbedding,
    PolynomialBlockCode.left,
    PolynomialCode.eval₂Hom_decode_injectVariables]
  rfl

/-- Exact original-field tangency to each of the `2q` inherited circle
blocks at every ambient point. -/
theorem sourceFieldCode_compactBlockDot
    (parameters omegaWeights numberWeights :
      Fin q → RationalCode)
    (x : Fin (sourceDimension q) → ℝ) :
    ∀ c,
      MixedCentralPolynomialCode.compactBlockDot (layout q) x
        (PolynomialFieldCode.realize
          (sourceFieldCode parameters omegaWeights numberWeights) x) c = 0 := by
  intro c
  rw [compactBlockDot_layout, sourceVelocity_controllers]
  exact
    ControllerPhaseProductCircleLayout.fieldCode_circleDot_arbitrary
      parameters
      (x ∘
        ControllerProductLinkedJacobiPolynomialCode.controllersEmbedding)
      c

/-! ## Structural degree ledger -/

/-- The source has controller/right-linked bidegree at most `(3,8)`. -/
theorem sourceFieldCode_termsBidegreeLE
    (parameters omegaWeights numberWeights :
      Fin q → RationalCode) :
    ∀ j, PolynomialBlockCode.TermsBidegreeLE 3 8
      (sourceFieldCode parameters omegaWeights numberWeights j) :=
  ControllerProductLinkedJacobiPolynomialCode.fieldCode_termsBidegreeLE
    parameters omegaWeights numberWeights

/-- The ordinary total degree is at most nine, independently of `q`. -/
theorem sourceFieldCode_termsDegreeLE
    (parameters omegaWeights numberWeights :
      Fin q → RationalCode) :
    ∀ j, PolynomialCode.TermsDegreeLE 9
      (sourceFieldCode parameters omegaWeights numberWeights j) :=
  ControllerProductLinkedJacobiPolynomialCode.fieldCode_termsDegreeLE
    parameters omegaWeights numberWeights

/-- Controller outputs use no right linked variable. -/
theorem sourceFieldCode_controller_termsBidegreeLE
    (parameters omegaWeights numberWeights :
      Fin q → RationalCode)
    (i : Fin (controllerDimension q)) :
    PolynomialBlockCode.TermsBidegreeLE 3 0
      (sourceFieldCode parameters omegaWeights numberWeights
        (ControllerProductLinkedJacobiPolynomialCode.controllersEmbedding i)) := by
  rw [sourceFieldCode,
    ControllerProductLinkedJacobiPolynomialCode.fieldCode_controllersEmbedding]
  exact
    PolynomialBlockCode.termsBidegreeLE_left
      (ControllerProductLinkedJacobiPolynomialCode.controllerFieldCode_termsDegreeLE
        parameters i)

/-- Every source component satisfies the sharp affine clearing bound
`M=8`. -/
theorem sourceFieldCode_termsAffineBlockDegreeLE
    (parameters omegaWeights numberWeights :
      Fin q → RationalCode) :
    ∀ j,
      MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
        (layout q) clearingExponent
        (sourceFieldCode parameters omegaWeights numberWeights j) := by
  intro j
  unfold layout
  exact
    RightAffineLeftCompactLayout.termsAffineBlockDegreeLE_of_termsBidegreeLE
      ControllerPhaseProductCircleLayout.circleBlock
      (sourceFieldCode_termsBidegreeLE
        parameters omegaWeights numberWeights j)

/-- The transported residuals have bidegree `(0,4)`. -/
theorem residualCode_termsBidegreeLE :
    ∀ i, PolynomialBlockCode.TermsBidegreeLE 0 4
      (residualCode q i) := by
  intro i
  exact
    PolynomialBlockCode.termsBidegreeLE_right
      (LinkedJacobiPolynomialCode.realResidualCode_termsDegreeLE i)

/-- Every residual satisfies the common affine clearing bound `M=8`. -/
theorem residualCode_termsAffineBlockDegreeLE :
    ∀ i,
      MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
        (layout q) clearingExponent (residualCode q i) := by
  intro i
  unfold layout
  exact
    RightAffineLeftCompactLayout.termsAffineBlockDegreeLE_of_termsBidegreeLE_of_le
      ControllerPhaseProductCircleLayout.circleBlock
      (residualCode_termsBidegreeLE i)
      (by norm_num [clearingExponent])

/-- Any output coordinate selected by a compact layout block uses no
affine variable. -/
theorem sourceFieldCode_termsAffineDegreeZero_of_compact
    (parameters omegaWeights numberWeights :
      Fin q → RationalCode)
    (j : Fin (sourceDimension q))
    (c : Fin (compactBlockCount q))
    (hj : layout q j = Sum.inr c) :
    MixedCentralPolynomialCode.TermsAffineDegreeZero
      (layout q)
      (sourceFieldCode parameters omegaWeights numberWeights j) := by
  obtain ⟨i | r, rfl⟩ := finSumFinEquiv.surjective j
  · unfold layout
    exact
      RightAffineLeftCompactLayout.termsAffineDegreeZero_of_termsBidegreeLE
        ControllerPhaseProductCircleLayout.circleBlock
        (sourceFieldCode_controller_termsBidegreeLE
          parameters omegaWeights numberWeights i)
  · have hright :
        layout q
            (finSumFinEquiv
              (Sum.inr r :
                Fin (controllerDimension q) ⊕ Fin linkedDimension)) =
          Sum.inl (0 : Fin affineBlockCount) := by
      simp [layout, RightAffineLeftCompactLayout.layout]
    rw [hright] at hj
    exact (Sum.inl_ne_inr hj).elim

/-! ## Global tangency after denominator clearing -/

/-- The denominator-cleared source velocity remains tangent to every
inherited circle, including at the affine equator `w=0`. -/
theorem clearedSourceVelocity_compactBlockDot
    (parameters omegaWeights numberWeights :
      Fin q → RationalCode)
    (x : Fin (sourceDimension q) → ℝ)
    (w : Fin affineBlockCount → ℝ) :
    ∀ c,
      MixedCentralPolynomialCode.compactBlockDot (layout q) x
        (MixedCentralPolynomialCode.clearedSourceVelocity
          (layout q) clearingExponent
          (sourceFieldCode parameters omegaWeights numberWeights)
          (MixedCentralPolynomialCode.chartPoint x w)) c = 0 := by
  intro c
  exact
    MixedCentralPolynomialCode.compactBlockDot_clearedSourceVelocity_eq_zero
      (layout q) clearingExponent
      (sourceFieldCode parameters omegaWeights numberWeights)
      x w c
      (fun j hj ↦
        sourceFieldCode_termsAffineDegreeZero_of_compact
          parameters omegaWeights numberWeights j c hj)
      (sourceFieldCode_compactBlockDot
        parameters omegaWeights numberWeights x c)

/-- The exact source-specific compact-tangency premise required by the
compact accumulator pipeline. -/
theorem baseCompactTangency
    (parameters omegaWeights numberWeights :
      Fin q → RationalCode) :
    CompactAccumulatorPipelineCode.BaseCompactTangency
      (layout q) clearingExponent
      (sourceFieldCode parameters omegaWeights numberWeights) := by
  intro y
  dsimp
  intro c
  let x : Fin (sourceDimension q) → ℝ :=
    fun j ↦
      y.1 (MixedCentralPolynomialCode.xIndex
        (k := affineBlockCount) j)
  let w : Fin affineBlockCount → ℝ :=
    fun b ↦
      y.1 (MixedCentralPolynomialCode.wIndex
        (n := sourceDimension q) b)
  have hy :
      MixedCentralPolynomialCode.chartPoint x w = y.1 :=
    MixedCentralPolynomialCode.chartPoint_decompose y.1
  rw [← hy]
  simpa only [MixedCentralPolynomialCode.chartPoint_xIndex] using
    clearedSourceVelocity_compactBlockDot
      parameters omegaWeights numberWeights x w c

/-! ## Primitive-recursive compactification--accumulator pipeline -/

/-- Runtime data consists of the three source tuples, the accumulator
scale `kappa`, and the strict-sign margin `epsilon`. -/
abbrev CompilerInput (q : ℕ) :=
  (ControllerProductLinkedJacobiPolynomialCode.CompilerInput q ×
      RationalCode) × RationalCode

def toPipelineInput
    (u : CompilerInput q) :
    CompactAccumulatorPipelineCode.CompilerInput
      (sourceDimension q) residualDimension :=
  (((u.1.2,
      sourceFieldCode u.1.1.1.1 u.1.1.1.2 u.1.1.2),
    residualCode q),
    u.2)

/-- Complete mixed compactification and accumulator compiler. -/
def compile
    (u : CompilerInput q) :
    PolynomialFieldCode (finalDimension q) ×
      PolynomialCode (finalDimension q) :=
  CompactAccumulatorPipelineCode.compile
    (layout q) clearingExponent (toPipelineInput u)

theorem residualCode_primrec :
    Primrec (residualCode q) :=
  PolynomialBlockCode.right_primrec.comp
    LinkedJacobiPolynomialCode.realResidualCode_primrec

set_option maxHeartbeats 800000 in
-- Nested finite-function encodings make this composition expensive.
theorem toPipelineInput_primrec :
    Primrec (toPipelineInput (q := q)) := by
  have hsourceInput :
      Primrec
        (fun u : CompilerInput q ↦ u.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hsource :
      Primrec
        (fun u : CompilerInput q ↦
          sourceFieldCode u.1.1.1.1 u.1.1.1.2 u.1.1.2) :=
    ControllerProductLinkedJacobiPolynomialCode.fieldCode_primrec.comp
      hsourceInput
  have hscale :
      Primrec (fun u : CompilerInput q ↦ u.1.2) :=
    Primrec.snd.comp Primrec.fst
  exact
    Primrec.pair
      (Primrec.pair
        (Primrec.pair hscale hsource)
        (Primrec.const (residualCode q)))
      Primrec.snd

set_option maxHeartbeats 800000 in
-- The pipeline compiler traverses finite sparse syntax.
theorem compile_primrec :
    Primrec (compile (q := q)) :=
  (CompactAccumulatorPipelineCode.compile_primrec
    (m := residualDimension)
    (layout q) clearingExponent).comp
      toPipelineInput_primrec

theorem compile_computable :
    Computable (compile (q := q)) :=
  compile_primrec.to_comp

/-- The mixed source has `2q+1` base sphere blocks, and the accumulator
adds one more sphere. -/
theorem sphereBlockCounts
    (q : ℕ) :
    affineBlockCount + compactBlockCount q = 2 * q + 1 ∧
      (affineBlockCount + compactBlockCount q) + 1 =
        2 * q + 2 := by
  simp [affineBlockCount, compactBlockCount_eq q]
  omega

end ControllerProductLinkedJacobiMixedCompactSourceCode

end HGAS.Modular
