import HGAS.Clocks.ControllerPhaseProductCircleLayout
import HGAS.Compactification.RightAffineLeftCompactLayout
import HGAS.Compiler.CompactAccumulatorPipelineComputability
import HGAS.Compiler.CompactAccumulatorPipelineGapCertificate
import HGAS.Modular.ControllerProductLinkedJacobiFamilyPolynomialComputability
import HGAS.Modular.ControllerProductLinkedJacobiFamilyPolynomialDegrees
import HGAS.Modular.ControllerProductLinkedJacobiFamilyResidualCode
import HGAS.Modular.ControllerProductLinkedJacobiFamilyResidualEnergyCode
import Mathlib.Tactic

/-!
# A mixed compact source for a common controller product and finitely many Jacobi blocks

Fix `q` controller--phase clocks and `b` linked unary--Jacobi blocks.  The
clocks are shared: every Jacobi frequency is a rational linear readout of
the same controller product.  The uncompactified state therefore has the
canonical split

```
             4q controller coordinates  |  28b linked coordinates.
```

The controller coordinates already come in `2q` invariant circles, two
per clock.  We keep those circles as literal compact blocks.  All `28b`
linked coordinates are placed in one affine block and centrally
compactified with one new chart coordinate.  This choice is important:
the number of Jacobi blocks changes the dimension, but it does not change
the affine degree.  Every source component has controller/linked
bidegree at most `(3,8)`, so the single even clearing exponent eight works
uniformly in both `q` and `b`.

Each linked block has ten complex algebraic validity residuals.  Splitting
them into real and imaginary parts gives `20b` scalar residual
polynomials, which this module retains as an exact algebraic interface.
Those signed coordinates are not used directly as drift observables:
their invariant averages could cancel.  Instead, the canonical compact
accumulator uses the `10b` nonnegative polynomials

```
                         (Re R)² + (Im R)².
```

The `10b` individual energies remain available for local auditing.  The
selector-facing compiler sums them into one aggregate nonnegative
validity coordinate and therefore appends a two-dimensional accumulator
sphere.  This sum vanishes exactly when every complex validity residual
vanishes.

This file records the complete interface needed by that pipeline:

* exact source semantics at arbitrary ambient points;
* exact scalar-residual and nonnegative residual-energy semantics;
* the source, scalar-residual, and energy degree ledgers;
* tangency to every inherited controller circle before and after
  denominator clearing, including at the affine equator; and
* primitive-recursive, hence computable, compilation from the rational
  controller parameters and both finite families of frequency weights.

The statements include the degenerate cases `q = 0` and `b = 0`.  If
`q = 0`, there are no inherited compact circles.  If `b = 0`, the affine
coordinate, scalar-residual, and energy families are empty, but the generic
one-chart compactification and accumulator compiler still have their
usual chart and accumulator coordinates; all residual assertions are
then vacuous.
-/

namespace HGAS.Modular

open HGAS

namespace ControllerProductLinkedJacobiFamilyMixedCompactSourceCode

open HGAS.Clocks
open ControllerProductLinkedJacobiFamilyResidualEnergyCode

variable {q b : ℕ}

/-- Dimension `4q+28b` of the uncompactified coupled source. -/
abbrev sourceDimension (q b : ℕ) : ℕ :=
  ControllerProductLinkedJacobiFamilyPolynomialCode.dimension q b

/-- Twenty signed real residual coordinates for each linked Jacobi block.
These are retained for exact algebraic semantics. -/
abbrev scalarResidualDimension (b : ℕ) : ℕ :=
  ControllerProductLinkedJacobiFamilyResidualCode.residualDimension b

/-- Ten nonnegative squared complex-residual norms for each linked block.
These remain exposed for local auditing. -/
abbrev residualEnergyDimension (b : ℕ) : ℕ :=
  ControllerProductLinkedJacobiFamilyResidualEnergyCode.energyDimension b

/-- The canonical accumulator uses one aggregate nonnegative validity
coordinate. -/
abbrev accumulatorResidualDimension : ℕ := 1

/-- All linked coordinates form one (possibly empty) affine block. -/
abbrev affineBlockCount : ℕ := 1

/-- Each controller--phase clock contributes two compact circles. -/
abbrev compactBlockCount (q : ℕ) : ℕ :=
  ControllerPhaseProductCircleLayout.circleCount q

/-- Number of left controller coordinates. -/
abbrev controllerDimension (q : ℕ) : ℕ :=
  ControllerProductLinkedJacobiFamilyPolynomialCode.controllerDimension q

/-- Number of right linked-family coordinates. -/
abbrev linkedFamilyDimension (b : ℕ) : ℕ :=
  ControllerProductLinkedJacobiFamilyPolynomialCode.linkedFamilyDimension b

/-- Sharp degree bound in the unique affine linked-family block. -/
abbrev affineDegreeBound : ℕ := 8

/-- Even denominator-clearing exponent used by the central chart. -/
abbrev clearingExponent : ℕ := 8

/-- Dimension after adjoining the affine chart coordinate and the
two-dimensional aggregate-energy accumulator sphere. -/
abbrev finalDimension (q b : ℕ) : ℕ :=
  (sourceDimension q b + affineBlockCount) +
    (accumulatorResidualDimension + 1)

theorem sourceDimension_eq
    (q b : ℕ) :
    sourceDimension q b = q * 4 + b * 28 := by
  norm_num [sourceDimension,
    ControllerProductLinkedJacobiFamilyPolynomialCode.dimension,
    ControllerProductLinkedJacobiFamilyPolynomialCode.controllerDimension,
    ControllerProductLinkedJacobiFamilyPolynomialCode.linkedFamilyDimension,
    ControllerProductLinkedJacobiFamilyPolynomialCode.localLinkedRealDimension,
    ControllerPhaseProductPolynomialCode.dimension,
    ControllerPolynomialCode.dimension,
    LinkedJacobiPolynomialCode.dimension,
    LinkedJacobiPolynomialCode.unaryDimension,
    LinkedJacobiPolynomialCode.jacobiDimension,
    UnaryPolynomialCode.modularDimension,
    JacobiPolynomialCode.dimension]

theorem scalarResidualDimension_eq
    (b : ℕ) :
    scalarResidualDimension b = b * 20 := by
  norm_num [scalarResidualDimension,
    ControllerProductLinkedJacobiFamilyResidualCode.residualDimension,
    ControllerProductLinkedJacobiFamilyResidualCode.localResidualDimension]

theorem residualEnergyDimension_eq
    (b : ℕ) :
    residualEnergyDimension b = b * 10 := by
  norm_num [residualEnergyDimension,
    ControllerProductLinkedJacobiFamilyResidualEnergyCode.energyDimension,
    ControllerProductLinkedJacobiFamilyResidualEnergyCode.localEnergyDimension]

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
    (q b : ℕ) :
    finalDimension q b = q * 4 + b * 28 + 3 := by
  rw [finalDimension, sourceDimension_eq]
  norm_num [affineBlockCount, accumulatorResidualDimension]

/-! ## Layout and finite polynomial sources -/

/-- Keep all `2q` clock circles compact and place the complete flattened
linked family in the unique right affine block. -/
def layout (q b : ℕ) :
    Fin (sourceDimension q b) →
      Fin affineBlockCount ⊕ Fin (compactBlockCount q) :=
  RightAffineLeftCompactLayout.layout
    ControllerPhaseProductCircleLayout.circleBlock

/-- Exact common-controller finite-family source field. -/
def sourceFieldCode
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode) :
    PolynomialFieldCode (sourceDimension q b) :=
  ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode
    parameters omegaWeights numberWeights

/-- All `20b` real validity residuals, lifted into the complete source
coordinate family. -/
def residualCode
    (q b : ℕ) :
    Fin (scalarResidualDimension b) →
      PolynomialCode (sourceDimension q b) :=
  ControllerProductLinkedJacobiFamilyResidualCode.residualCode q b

/-- The preferred accumulator observables: one nonnegative squared
complex-residual norm for every named residual in every linked block. -/
def residualEnergyCode
    (q b : ℕ) :
    Fin (residualEnergyDimension b) →
      PolynomialCode (sourceDimension q b) :=
  ControllerProductLinkedJacobiFamilyResidualEnergyCode.residualEnergyCode q b

/-- The single aggregate nonnegative validity polynomial. -/
def totalResidualEnergyCode
    (q b : ℕ) :
    PolynomialCode (sourceDimension q b) :=
  ControllerProductLinkedJacobiFamilyResidualEnergyCode.totalResidualEnergyCode
    q b

/-- The one-coordinate family consumed by the canonical accumulator. -/
def accumulatorResidualCode
    (q b : ℕ) :
    Fin accumulatorResidualDimension →
      PolynomialCode (sourceDimension q b) :=
  fun _ ↦ totalResidualEnergyCode q b

/-! ## Exact source semantics -/

/-- The literal rational compiler realizes the intended coupled vector
field at every ambient point.  No circle or residual equation is used. -/
@[simp]
theorem realize_sourceFieldCode
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (x : Fin (sourceDimension q b) → ℝ) :
    PolynomialFieldCode.realize
        (sourceFieldCode parameters omegaWeights numberWeights) x =
      ControllerProductLinkedJacobiFamilyPolynomialCode.point
        (ControllerProductLinkedJacobiFamilyPolynomialCode.vectorField
          (fun i ↦
            (RationalCode.decode (parameters i) : ℝ))
          (fun a i ↦
            (RationalCode.decode (omegaWeights a i) : ℝ))
          (fun a i ↦
            (RationalCode.decode (numberWeights a i) : ℝ))
          (ControllerProductLinkedJacobiFamilyPolynomialCode.state x)) :=
  ControllerProductLinkedJacobiFamilyPolynomialCode.realize_fieldCode_arbitrary
    parameters omegaWeights numberWeights x

/-! ## Exact validity-residual semantics -/

/-- The residual coordinate indexed by `(a,i)` sees exactly residual
coordinate `i` of linked block `a`. -/
@[simp]
theorem eval_residualCode_residualBlockEmbedding
    (z : ControllerProductLinkedJacobiFamilyState q b)
    (a : Fin b)
    (i :
      Fin
        ControllerProductLinkedJacobiFamilyResidualCode.localResidualDimension) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (ControllerProductLinkedJacobiFamilyPolynomialCode.point z)
        (PolynomialCode.decode
          (residualCode q b
            (ControllerProductLinkedJacobiFamilyResidualCode.residualBlockEmbedding
              a i))) =
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (ComplexCoordinates.realifyPoint
          (LinkedJacobiPolynomialCode.point (z.linked a)))
        (PolynomialCode.decode
          (LinkedJacobiPolynomialCode.realResidualCode i)) :=
  ControllerProductLinkedJacobiFamilyResidualCode.eval_residualCode_residualBlockEmbedding
    z a i

/-- Ambient version of the preceding scalar evaluation theorem. -/
@[simp]
theorem eval_residualCode_residualBlockEmbedding_arbitrary
    (x : Fin (sourceDimension q b) → ℝ)
    (a : Fin b)
    (i :
      Fin
        ControllerProductLinkedJacobiFamilyResidualCode.localResidualDimension) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode
          (residualCode q b
            (ControllerProductLinkedJacobiFamilyResidualCode.residualBlockEmbedding
              a i))) =
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (ComplexCoordinates.realifyPoint
          (LinkedJacobiPolynomialCode.point
            ((ControllerProductLinkedJacobiFamilyPolynomialCode.state x).linked
              a)))
        (PolynomialCode.decode
          (LinkedJacobiPolynomialCode.realResidualCode i)) := by
  have h :=
    eval_residualCode_residualBlockEmbedding
      (ControllerProductLinkedJacobiFamilyPolynomialCode.state x) a i
  simpa using h

/-- Reassembling the twenty scalar coordinates belonging to block `a`
recovers its ten named complex residuals. -/
@[simp]
theorem complexifyPoint_eval_residualBlock
    (z : ControllerProductLinkedJacobiFamilyState q b)
    (a : Fin b) :
    ComplexCoordinates.complexifyPoint
        (fun i ↦
          MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
            (ControllerProductLinkedJacobiFamilyPolynomialCode.point z)
            (PolynomialCode.decode
              (residualCode q b
                (ControllerProductLinkedJacobiFamilyResidualCode.residualBlockEmbedding
                  a i)))) =
      fun i ↦
        linkedJacobiResidual
          (LinkedJacobiPolynomialCode.residualIndex i)
          (z.linked a) :=
  ControllerProductLinkedJacobiFamilyResidualCode.complexifyPoint_eval_residualBlock
    z a

/-- Ambient pointwise form of the named complex-residual semantics. -/
@[simp]
theorem complexifyPoint_eval_residualBlock_arbitrary
    (x : Fin (sourceDimension q b) → ℝ)
    (a : Fin b) :
    ComplexCoordinates.complexifyPoint
        (fun i ↦
          MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
            (PolynomialCode.decode
              (residualCode q b
                (ControllerProductLinkedJacobiFamilyResidualCode.residualBlockEmbedding
                  a i)))) =
      fun i ↦
        linkedJacobiResidual
          (LinkedJacobiPolynomialCode.residualIndex i)
          ((ControllerProductLinkedJacobiFamilyPolynomialCode.state x).linked
            a) := by
  have h :=
    complexifyPoint_eval_residualBlock
      (ControllerProductLinkedJacobiFamilyPolynomialCode.state x) a
  simpa using h

/-- All scalar residual coordinates vanish exactly when every named
complex residual vanishes in every linked block. -/
theorem forall_eval_residualCode_eq_zero_iff
    (z : ControllerProductLinkedJacobiFamilyState q b) :
    (∀ k,
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (ControllerProductLinkedJacobiFamilyPolynomialCode.point z)
        (PolynomialCode.decode (residualCode q b k)) = 0) ↔
      ∀ a (r : LinkedJacobiResidualIndex),
        linkedJacobiResidual r (z.linked a) = 0 :=
  ControllerProductLinkedJacobiFamilyResidualCode.forall_eval_residualCode_eq_zero_iff
    z

/-- Ambient form of the simultaneous-vanishing criterion. -/
theorem forall_eval_residualCode_eq_zero_iff_arbitrary
    (x : Fin (sourceDimension q b) → ℝ) :
    (∀ k,
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (residualCode q b k)) = 0) ↔
      ∀ a (r : LinkedJacobiResidualIndex),
        linkedJacobiResidual r
          ((ControllerProductLinkedJacobiFamilyPolynomialCode.state x).linked
            a) = 0 :=
  ControllerProductLinkedJacobiFamilyResidualCode.forall_eval_residualCode_eq_zero_iff_arbitrary
    x

/-! ### Preferred nonnegative residual energies -/

/-- Exact evaluation of one residual energy in one linked block. -/
@[simp]
theorem eval_residualEnergyCode_energyBlockEmbedding
    (z : ControllerProductLinkedJacobiFamilyState q b)
    (a : Fin b)
    (i :
      Fin
        ControllerProductLinkedJacobiFamilyResidualEnergyCode.localEnergyDimension) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (ControllerProductLinkedJacobiFamilyPolynomialCode.point z)
        (PolynomialCode.decode
          (residualEnergyCode q b
            (ControllerProductLinkedJacobiFamilyResidualEnergyCode.energyBlockEmbedding
              a i))) =
      Complex.normSq
        (linkedJacobiResidual
          (LinkedJacobiPolynomialCode.residualIndex i)
          (z.linked a)) :=
  ControllerProductLinkedJacobiFamilyResidualEnergyCode.eval_residualEnergyCode_energyBlockEmbedding
    z a i

/-- Ambient form of exact residual-energy evaluation. -/
@[simp]
theorem eval_residualEnergyCode_energyBlockEmbedding_arbitrary
    (x : Fin (sourceDimension q b) → ℝ)
    (a : Fin b)
    (i :
      Fin
        ControllerProductLinkedJacobiFamilyResidualEnergyCode.localEnergyDimension) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode
          (residualEnergyCode q b
            (ControllerProductLinkedJacobiFamilyResidualEnergyCode.energyBlockEmbedding
              a i))) =
      Complex.normSq
        (linkedJacobiResidual
          (LinkedJacobiPolynomialCode.residualIndex i)
          ((ControllerProductLinkedJacobiFamilyPolynomialCode.state x).linked
            a)) := by
  have h :=
    eval_residualEnergyCode_energyBlockEmbedding
      (ControllerProductLinkedJacobiFamilyPolynomialCode.state x) a i
  simpa using h

/-- Every preferred accumulator observable is nonnegative at every
ambient source point. -/
theorem eval_residualEnergyCode_nonneg_arbitrary
    (x : Fin (sourceDimension q b) → ℝ)
    (k : Fin (residualEnergyDimension b)) :
    0 ≤
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (residualEnergyCode q b k)) := by
  have h :=
    ControllerProductLinkedJacobiFamilyResidualEnergyCode.eval_residualEnergyCode_nonneg
        (ControllerProductLinkedJacobiFamilyPolynomialCode.state x) k
  simpa using h

/-- Simultaneous vanishing of all nonnegative energies is exactly
validity of every linked Jacobi block. -/
theorem forall_eval_residualEnergyCode_eq_zero_iff
    (z : ControllerProductLinkedJacobiFamilyState q b) :
    (∀ k,
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (ControllerProductLinkedJacobiFamilyPolynomialCode.point z)
        (PolynomialCode.decode (residualEnergyCode q b k)) = 0) ↔
      ∀ a (r : LinkedJacobiResidualIndex),
        linkedJacobiResidual r (z.linked a) = 0 :=
  ControllerProductLinkedJacobiFamilyResidualEnergyCode.forall_eval_residualEnergyCode_eq_zero_iff
    z

/-- Ambient simultaneous-vanishing semantics for the preferred
nonnegative energy family. -/
theorem forall_eval_residualEnergies_eq_zero_iff_arbitrary
    (x : Fin (sourceDimension q b) → ℝ) :
    (∀ k,
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (residualEnergyCode q b k)) = 0) ↔
      ∀ a (r : LinkedJacobiResidualIndex),
        linkedJacobiResidual r
          ((ControllerProductLinkedJacobiFamilyPolynomialCode.state x).linked
            a) = 0 :=
  forall_eval_residualEnergyCode_eq_zero_iff_arbitrary x

/-! ### Aggregate validity energy used by the accumulator -/

/-- Exact semantics of the single aggregate validity coordinate. -/
@[simp]
theorem eval_totalResidualEnergyCode
    (z : ControllerProductLinkedJacobiFamilyState q b) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (ControllerProductLinkedJacobiFamilyPolynomialCode.point z)
        (PolynomialCode.decode (totalResidualEnergyCode q b)) =
      ∑ k : Fin (residualEnergyDimension b),
        Complex.normSq
          (linkedJacobiResidual
            (LinkedJacobiPolynomialCode.residualIndex
              (finProdFinEquiv.symm k).2)
            (z.linked (finProdFinEquiv.symm k).1)) :=
  ControllerProductLinkedJacobiFamilyResidualEnergyCode.eval_totalResidualEnergyCode
    z

/-- Ambient exact semantics of the aggregate validity coordinate. -/
@[simp]
theorem eval_totalResidualEnergyCode_arbitrary
    (x : Fin (sourceDimension q b) → ℝ) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (totalResidualEnergyCode q b)) =
      ∑ k : Fin (residualEnergyDimension b),
        Complex.normSq
          (linkedJacobiResidual
            (LinkedJacobiPolynomialCode.residualIndex
              (finProdFinEquiv.symm k).2)
            ((ControllerProductLinkedJacobiFamilyPolynomialCode.state x).linked
              (finProdFinEquiv.symm k).1)) := by
  have h :=
    eval_totalResidualEnergyCode
      (ControllerProductLinkedJacobiFamilyPolynomialCode.state x)
  simpa using h

/-- The aggregate validity coordinate is nonnegative at every ambient
point. -/
theorem eval_totalResidualEnergyCode_nonneg_arbitrary
    (x : Fin (sourceDimension q b) → ℝ) :
    0 ≤
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (totalResidualEnergyCode q b)) := by
  have h :=
    ControllerProductLinkedJacobiFamilyResidualEnergyCode.eval_totalResidualEnergyCode_nonneg
        (ControllerProductLinkedJacobiFamilyPolynomialCode.state x)
  rw [ControllerProductLinkedJacobiFamilyPolynomialCode.point_state] at h
  exact h

/-- The aggregate validity coordinate vanishes exactly when every named
linked-Jacobi residual vanishes. -/
theorem eval_totalResidualEnergyCode_eq_zero_iff_arbitrary
    (x : Fin (sourceDimension q b) → ℝ) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (totalResidualEnergyCode q b)) = 0 ↔
      ∀ a (r : LinkedJacobiResidualIndex),
        linkedJacobiResidual r
          ((ControllerProductLinkedJacobiFamilyPolynomialCode.state x).linked
            a) = 0 := by
  have h :=
    ControllerProductLinkedJacobiFamilyResidualEnergyCode.eval_totalResidualEnergyCode_eq_zero_iff
        (ControllerProductLinkedJacobiFamilyPolynomialCode.state x)
  rw [ControllerProductLinkedJacobiFamilyPolynomialCode.point_state] at h
  exact h

/-- Simultaneous vanishing semantics in the exact one-coordinate family
shape expected by the generic accumulator. -/
theorem forall_eval_accumulatorResidualCode_eq_zero_iff_arbitrary
    (x : Fin (sourceDimension q b) → ℝ) :
    (∀ i,
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (accumulatorResidualCode q b i)) = 0) ↔
      ∀ a (r : LinkedJacobiResidualIndex),
        linkedJacobiResidual r
          ((ControllerProductLinkedJacobiFamilyPolynomialCode.state x).linked
            a) = 0 := by
  constructor
  · intro h
    exact
      (eval_totalResidualEnergyCode_eq_zero_iff_arbitrary x).1
        (h 0)
  · intro h i
    exact
      (eval_totalResidualEnergyCode_eq_zero_iff_arbitrary x).2 h

/-! ## Circle geometry and original-field tangency -/

/-- The compact-block dot product of the mixed layout is exactly the
canonical circle dot product on the common controller coordinates. -/
theorem compactBlockDot_layout
    {R : Type*} [CommRing R]
    (x v : Fin (sourceDimension q b) → R)
    (c : Fin (compactBlockCount q)) :
    MixedCentralPolynomialCode.compactBlockDot (layout q b) x v c =
      ControllerPhaseProductCircleLayout.circleDot
        (x ∘
          ControllerProductLinkedJacobiFamilyPolynomialCode.controllersEmbedding)
        (v ∘
          ControllerProductLinkedJacobiFamilyPolynomialCode.controllersEmbedding)
        c := by
  unfold layout
  rw [RightAffineLeftCompactLayout.compactBlockDot_layout]
  rfl

/-- Restricting the coupled source velocity to the common controller
coordinates recovers the block-diagonal controller-product velocity. -/
theorem sourceVelocity_controllers
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (x : Fin (sourceDimension q b) → ℝ) :
    (PolynomialFieldCode.realize
        (sourceFieldCode parameters omegaWeights numberWeights) x) ∘
        ControllerProductLinkedJacobiFamilyPolynomialCode.controllersEmbedding =
      PolynomialFieldCode.realize
        (ControllerProductLinkedJacobiFamilyPolynomialCode.controllerFieldCode
          parameters)
        (x ∘
          ControllerProductLinkedJacobiFamilyPolynomialCode.controllersEmbedding) := by
  funext i
  change
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode
          (sourceFieldCode parameters omegaWeights numberWeights
            (ControllerProductLinkedJacobiFamilyPolynomialCode.controllersEmbedding
              i))) =
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (x ∘
          ControllerProductLinkedJacobiFamilyPolynomialCode.controllersEmbedding)
        (PolynomialCode.decode
          (ControllerProductLinkedJacobiFamilyPolynomialCode.controllerFieldCode
            parameters i))
  rw [sourceFieldCode,
    ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode_controllersEmbedding,
    PolynomialBlockCode.left,
    PolynomialCode.eval₂Hom_decode_injectVariables]
  rfl

/-- Exact original-field tangency to each inherited controller circle at
every ambient point. -/
theorem sourceFieldCode_compactBlockDot
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (x : Fin (sourceDimension q b) → ℝ) :
    ∀ c,
      MixedCentralPolynomialCode.compactBlockDot (layout q b) x
        (PolynomialFieldCode.realize
          (sourceFieldCode parameters omegaWeights numberWeights) x) c = 0 := by
  intro c
  rw [compactBlockDot_layout, sourceVelocity_controllers]
  exact
    ControllerPhaseProductCircleLayout.fieldCode_circleDot_arbitrary
      parameters
      (x ∘
        ControllerProductLinkedJacobiFamilyPolynomialCode.controllersEmbedding)
      c

/-! ## Structural degree ledger -/

/-- The source has common-controller/linked-family bidegree at most
`(3,8)`, uniformly in `q` and `b`. -/
theorem sourceFieldCode_termsBidegreeLE
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode) :
    ∀ j, PolynomialBlockCode.TermsBidegreeLE 3 8
      (sourceFieldCode parameters omegaWeights numberWeights j) :=
  ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode_termsBidegreeLE
    parameters omegaWeights numberWeights

/-- The ordinary total degree is at most nine, uniformly in `q` and
`b`. -/
theorem sourceFieldCode_termsDegreeLE
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode) :
    ∀ j, PolynomialCode.TermsDegreeLE 9
      (sourceFieldCode parameters omegaWeights numberWeights j) :=
  ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode_termsDegreeLE
    parameters omegaWeights numberWeights

/-- Controller outputs use no linked-family variable. -/
theorem sourceFieldCode_controller_termsBidegreeLE
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (i : Fin (controllerDimension q)) :
    PolynomialBlockCode.TermsBidegreeLE 3 0
      (sourceFieldCode parameters omegaWeights numberWeights
        (ControllerProductLinkedJacobiFamilyPolynomialCode.controllersEmbedding
          i)) := by
  rw [sourceFieldCode,
    ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode_controllersEmbedding]
  exact
    PolynomialBlockCode.termsBidegreeLE_left
      (ControllerProductLinkedJacobiFamilyPolynomialCode.controllerFieldCode_termsDegreeLE
        parameters i)

/-- Every source component satisfies the sharp affine clearing bound
`M=8`. -/
theorem sourceFieldCode_termsAffineBlockDegreeLE
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode) :
    ∀ j,
      MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
        (layout q b) clearingExponent
        (sourceFieldCode parameters omegaWeights numberWeights j) := by
  intro j
  unfold layout
  exact
    RightAffineLeftCompactLayout.termsAffineBlockDegreeLE_of_termsBidegreeLE
        ControllerPhaseProductCircleLayout.circleBlock
        (sourceFieldCode_termsBidegreeLE
          parameters omegaWeights numberWeights j)

/-- The complete residual family has bidegree at most `(0,4)`. -/
theorem residualCode_termsBidegreeLE :
    ∀ k, PolynomialBlockCode.TermsBidegreeLE 0 4
      (residualCode q b k) :=
  ControllerProductLinkedJacobiFamilyResidualCode.residualCode_termsBidegreeLE

/-- Every family residual satisfies the common affine clearing bound
`M=8`. -/
theorem residualCode_termsAffineBlockDegreeLE :
    ∀ k,
      MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
        (layout q b) clearingExponent (residualCode q b k) := by
  intro k
  unfold layout
  exact
    RightAffineLeftCompactLayout.termsAffineBlockDegreeLE_of_termsBidegreeLE_of_le
        ControllerPhaseProductCircleLayout.circleBlock
        (residualCode_termsBidegreeLE k)
        (by norm_num [clearingExponent])

/-- Every preferred residual energy has bidegree at most `(0,8)`. -/
theorem residualEnergyCode_termsBidegreeLE :
    ∀ k, PolynomialBlockCode.TermsBidegreeLE 0 8
      (residualEnergyCode q b k) :=
  ControllerProductLinkedJacobiFamilyResidualEnergyCode.residualEnergyCode_termsBidegreeLE

/-- The preferred nonnegative energy observables satisfy the sharp
common affine clearing bound `M=8`. -/
theorem residualEnergyCode_termsAffineBlockDegreeLE :
    ∀ k,
      MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
        (layout q b) clearingExponent
        (residualEnergyCode q b k) := by
  intro k
  unfold layout
  exact
    RightAffineLeftCompactLayout.termsAffineBlockDegreeLE_of_termsBidegreeLE
      ControllerPhaseProductCircleLayout.circleBlock
      (residualEnergyCode_termsBidegreeLE k)

/-- Summing the individual energies preserves the right-block
bidegree `(0,8)`. -/
theorem totalResidualEnergyCode_termsBidegreeLE :
    PolynomialBlockCode.TermsBidegreeLE 0 8
      (totalResidualEnergyCode q b) := by
  have hsum :
      ∀ ps :
          List
            (PolynomialCode
              (controllerDimension q + linkedFamilyDimension b)),
        (∀ p ∈ ps,
          PolynomialBlockCode.TermsBidegreeLE 0 8 p) →
        PolynomialBlockCode.TermsBidegreeLE 0 8
          (PolynomialCode.sumCodes ps) := by
    intro ps hp
    induction ps with
    | nil =>
        exact PolynomialBlockCode.termsBidegreeLE_zero 0 8
    | cons p ps ih =>
        change
          PolynomialBlockCode.TermsBidegreeLE 0 8
            (PolynomialCode.add p (PolynomialCode.sumCodes ps))
        exact
          PolynomialBlockCode.termsBidegreeLE_add
            (hp p (by simp))
            (ih (fun r hr ↦ hp r (by simp [hr])))
  unfold totalResidualEnergyCode
  unfold
    ControllerProductLinkedJacobiFamilyResidualEnergyCode.totalResidualEnergyCode
  apply hsum
  intro p hp
  rw [List.mem_ofFn] at hp
  obtain ⟨k, rfl⟩ := hp
  exact residualEnergyCode_termsBidegreeLE k

/-- The aggregate validity coordinate has ordinary degree at most
eight. -/
theorem totalResidualEnergyCode_termsDegreeLE :
    PolynomialCode.TermsDegreeLE 8
      (totalResidualEnergyCode q b) :=
  ControllerProductLinkedJacobiFamilyResidualEnergyCode.totalResidualEnergyCode_termsDegreeLE

/-- The canonical one-coordinate residual family satisfies the sharp
affine clearing bound. -/
theorem accumulatorResidualCode_termsAffineBlockDegreeLE :
    ∀ i,
      MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
        (layout q b) clearingExponent
        (accumulatorResidualCode q b i) := by
  intro i
  unfold accumulatorResidualCode layout
  exact
    RightAffineLeftCompactLayout.termsAffineBlockDegreeLE_of_termsBidegreeLE
      ControllerPhaseProductCircleLayout.circleBlock
      totalResidualEnergyCode_termsBidegreeLE

/-- Any output coordinate belonging to a compact layout block uses no
affine linked-family variable. -/
theorem sourceFieldCode_termsAffineDegreeZero_of_compact
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (j : Fin (sourceDimension q b))
    (c : Fin (compactBlockCount q))
    (hj : layout q b j = Sum.inr c) :
    MixedCentralPolynomialCode.TermsAffineDegreeZero
      (layout q b)
      (sourceFieldCode parameters omegaWeights numberWeights j) := by
  obtain ⟨i | r, rfl⟩ := finSumFinEquiv.surjective j
  · unfold layout
    exact
      RightAffineLeftCompactLayout.termsAffineDegreeZero_of_termsBidegreeLE
          ControllerPhaseProductCircleLayout.circleBlock
          (sourceFieldCode_controller_termsBidegreeLE
            parameters omegaWeights numberWeights i)
  · have hright :
        layout q b
            (finSumFinEquiv
              (Sum.inr r :
                Fin (controllerDimension q) ⊕
                  Fin (linkedFamilyDimension b))) =
          Sum.inl (0 : Fin affineBlockCount) := by
      simp [layout, RightAffineLeftCompactLayout.layout]
    rw [hright] at hj
    exact (Sum.inl_ne_inr hj).elim

/-! ## Global tangency after denominator clearing -/

/-- The denominator-cleared source remains tangent to every inherited
circle, including at the affine equator `w=0`. -/
theorem clearedSourceVelocity_compactBlockDot
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (x : Fin (sourceDimension q b) → ℝ)
    (w : Fin affineBlockCount → ℝ) :
    ∀ c,
      MixedCentralPolynomialCode.compactBlockDot (layout q b) x
        (MixedCentralPolynomialCode.clearedSourceVelocity
          (layout q b) clearingExponent
          (sourceFieldCode parameters omegaWeights numberWeights)
          (MixedCentralPolynomialCode.chartPoint x w)) c = 0 := by
  intro c
  exact
    MixedCentralPolynomialCode.compactBlockDot_clearedSourceVelocity_eq_zero
        (layout q b) clearingExponent
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
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode) :
    CompactAccumulatorPipelineCode.BaseCompactTangency
      (layout q b) clearingExponent
      (sourceFieldCode parameters omegaWeights numberWeights) := by
  intro y
  dsimp
  intro c
  let x : Fin (sourceDimension q b) → ℝ :=
    fun j ↦
      y.1 (MixedCentralPolynomialCode.xIndex
        (k := affineBlockCount) j)
  let w : Fin affineBlockCount → ℝ :=
    fun a ↦
      y.1 (MixedCentralPolynomialCode.wIndex
        (n := sourceDimension q b) a)
  have hy :
      MixedCentralPolynomialCode.chartPoint x w = y.1 :=
    MixedCentralPolynomialCode.chartPoint_decompose y.1
  rw [← hy]
  simpa only [MixedCentralPolynomialCode.chartPoint_xIndex] using
    clearedSourceVelocity_compactBlockDot
      parameters omegaWeights numberWeights x w c

/-! ## Primitive-recursive compactification--accumulator pipeline -/

/-- Runtime data consists of the complete finite-family source input,
the accumulator scale `kappa`, and the strict-sign margin `epsilon`. -/
abbrev CompilerInput (q b : ℕ) :=
  (ControllerProductLinkedJacobiFamilyPolynomialCode.CompilerInput q b ×
      RationalCode) × RationalCode

/-- Repackage the family input for the generic compact accumulator
compiler.  The drift family is the nonnegative residual-energy family,
not the signed scalar residual coordinates.  More precisely, it is the
singleton family containing the total squared residual energy. -/
def toPipelineInput
    (u : CompilerInput q b) :
    CompactAccumulatorPipelineCode.CompilerInput
      (sourceDimension q b) accumulatorResidualDimension :=
  (((u.1.2,
      sourceFieldCode u.1.1.1.1 u.1.1.1.2 u.1.1.2),
    accumulatorResidualCode q b),
    u.2)

/-- Complete mixed compactification and accumulator compiler. -/
def compile
    (u : CompilerInput q b) :
    PolynomialFieldCode (finalDimension q b) ×
      PolynomialCode (finalDimension q b) :=
  CompactAccumulatorPipelineCode.compile
    (layout q b) clearingExponent (toPipelineInput u)

theorem residualCode_primrec :
    Primrec (residualCode q b) :=
  ControllerProductLinkedJacobiFamilyResidualCode.residualCode_primrec

/-- The preferred nonnegative residual-energy family is primitive
recursive. -/
theorem residualEnergyCode_primrec :
    Primrec (residualEnergyCode q b) :=
  ControllerProductLinkedJacobiFamilyResidualEnergyCode.residualEnergyCode_primrec

/-- Indexed access to the canonical singleton aggregate-energy family is
primitive recursive. -/
theorem accumulatorResidualCode_primrec :
    Primrec (accumulatorResidualCode q b) :=
  Primrec.dom_finite _

set_option maxHeartbeats 1600000 in
-- The runtime input contains two nested families of finite functions.
theorem toPipelineInput_primrec :
    Primrec (toPipelineInput (q := q) (b := b)) := by
  have hsourceInput :
      Primrec
        (fun u : CompilerInput q b ↦ u.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hsource :
      Primrec
        (fun u : CompilerInput q b ↦
          sourceFieldCode u.1.1.1.1 u.1.1.1.2 u.1.1.2) :=
    ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode_primrec.comp
      hsourceInput
  have hscale :
      Primrec (fun u : CompilerInput q b ↦ u.1.2) :=
    Primrec.snd.comp Primrec.fst
  exact
    Primrec.pair
      (Primrec.pair
        (Primrec.pair hscale hsource)
        (Primrec.const (accumulatorResidualCode q b)))
      Primrec.snd

set_option maxHeartbeats 1600000 in
-- The generic compiler traverses finite sparse polynomial syntax.
theorem compile_primrec :
    Primrec (compile (q := q) (b := b)) :=
  (CompactAccumulatorPipelineCode.compile_primrec
    (m := accumulatorResidualDimension)
    (layout q b) clearingExponent).comp
      toPipelineInput_primrec

theorem compile_computable :
    Computable (compile (q := q) (b := b)) :=
  compile_primrec.to_comp

/-- The mixed source has `2q+1` base sphere blocks: one central sphere
for the linked-family affine chart and `2q` inherited circles.  The
accumulator adds one further sphere. -/
theorem sphereBlockCounts
    (q : ℕ) :
    affineBlockCount + compactBlockCount q = 2 * q + 1 ∧
      (affineBlockCount + compactBlockCount q) + 1 =
        2 * q + 2 := by
  simp [affineBlockCount, compactBlockCount_eq q]
  omega

end ControllerProductLinkedJacobiFamilyMixedCompactSourceCode

end HGAS.Modular
