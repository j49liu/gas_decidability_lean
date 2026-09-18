import HGAS.Arithmetic.FixedDetectorDriftComputability
import HGAS.Arithmetic.FixedDetectorDriftDegrees
import HGAS.Compactification.AllAffinePolynomialCode
import HGAS.Compiler.CompactAccumulatorPipelineComputability
import HGAS.Compiler.CompactAccumulatorPipelineDegrees
import HGAS.Compiler.CompactAccumulatorPipelineGapCertificate
import Mathlib.Tactic

/-!
# The complete fixed detector as an all-affine compact source

This module makes one executable call to the generic central
compactification and vector-accumulator pipeline.

The uncompactified detector has

```
                    4 * eqs + 38 * vars + 2
```

real coordinates.  Every one of them is affine, so they form one central
block and there are no pre-existing compact blocks.  The accumulator has
one coordinate for the nonnegative validity energy, two real coordinates
for each selector moment, and two coordinates for the final detector.

The DQL coefficients can make Laurent-character degrees arbitrarily
large.  Consequently the denominator-clearing exponent must be computed
from the instance rather than fixed merely from `eqs` and `vars`.  We use
twice the maximum of the proved source-field and drift degree bounds.  It
is even, dominates both inputs, and remains primitive recursive.
-/

namespace HGAS

open _root_.MvPolynomial
open Clocks.ControllerPhaseProductCharacterCode

namespace FixedDetectorCompactSourceCode

variable {eqs vars : ℕ}

/-! ## Fixed finite layout and resources -/

abbrev sourceDimension (eqs vars : ℕ) : ℕ :=
  FixedDetectorPolynomialCode.dimension eqs vars

abbrev driftDimension (vars : ℕ) : ℕ :=
  FixedDetectorDriftCode.driftCount vars

abbrev affineBlockCount : ℕ := 1
abbrev compactBlockCount : ℕ := 0

/-- Dimension after adjoining the one central chart coordinate and the
complete stereographic vector accumulator. -/
abbrev finalDimension (eqs vars : ℕ) : ℕ :=
  (sourceDimension eqs vars + affineBlockCount) +
    (driftDimension vars + 1)

/-- All detector coordinates belong to one affine block. -/
def layout :
    Fin (sourceDimension eqs vars) →
      Fin affineBlockCount ⊕ Fin compactBlockCount :=
  MixedCentralPolynomialCode.oneBlockAllAffineLayout
    (sourceDimension eqs vars)

/-- The complete drift has `14 * vars + 3` real coordinates. -/
theorem driftDimension_eq :
    driftDimension vars = 14 * vars + 3 := by
  change 1 + ((vars * 7) * 2 + 2) = 14 * vars + 3
  omega

/-- Exact ambient size of the compact source plus accumulator. -/
theorem finalDimension_eq :
    finalDimension eqs vars = 4 * eqs + 52 * vars + 7 := by
  change
    (FixedDetectorPolynomialCode.dimension eqs vars + 1) +
        (FixedDetectorDriftCode.driftCount vars + 1) =
      4 * eqs + 52 * vars + 7
  rw [FixedDetectorPolynomialCode.dimension_eq]
  rw [show FixedDetectorDriftCode.driftCount vars =
      14 * vars + 3 from driftDimension_eq]
  omega

/-! ## Instance-dependent degree and clearing ledgers -/

/-- A common raw degree bound for the affine detector field and every
drift coordinate. -/
def sourceDegreeBound (I : DQLSystem eqs vars) : ℕ :=
  max (FixedDetectorPolynomialCode.fieldDegree I)
    (FixedDetectorDriftCode.driftDegree I)

/-- An even all-affine denominator-clearing exponent. -/
def clearingExponent (I : DQLSystem eqs vars) : ℕ :=
  2 * sourceDegreeBound I

/-- Raw degree bound for the compactified field with one affine block. -/
def compactFieldDegree (I : DQLSystem eqs vars) : ℕ :=
  sourceDegreeBound I + clearingExponent I + 3

/-- The strict-sign reward has raw degree two in the one-block layout. -/
abbrev compactRewardDegree : ℕ := 2

/-- One common raw bound for both components returned by `compile`. -/
def compilerDegree (I : DQLSystem eqs vars) : ℕ :=
  max (compactFieldDegree I) compactRewardDegree

theorem fieldDegree_le_sourceDegreeBound
    (I : DQLSystem eqs vars) :
    FixedDetectorPolynomialCode.fieldDegree I ≤ sourceDegreeBound I :=
  Nat.le_max_left _ _

theorem driftDegree_le_sourceDegreeBound
    (I : DQLSystem eqs vars) :
    FixedDetectorDriftCode.driftDegree I ≤ sourceDegreeBound I :=
  Nat.le_max_right _ _

theorem sourceDegreeBound_le_clearingExponent
    (I : DQLSystem eqs vars) :
    sourceDegreeBound I ≤ clearingExponent I := by
  unfold clearingExponent
  omega

theorem clearingExponent_even
    (I : DQLSystem eqs vars) :
    clearingExponent I % 2 = 0 := by
  simp [clearingExponent]

/-! ## Concrete affine source and drift -/

/-- The complete uncompactified fixed-detector polynomial field. -/
def sourceFieldCode
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars) :
    PolynomialFieldCode (sourceDimension eqs vars) :=
  FixedDetectorPolynomialCode.fieldCode parameters I

/-- The complete validity, selector, and detector drift vector. -/
def sourceDriftCode
    (I : DQLSystem eqs vars) :
    Fin (driftDimension vars) →
      PolynomialCode (sourceDimension eqs vars) :=
  FixedDetectorDriftCode.driftCode I

/-- Every affine source-field component satisfies the common raw bound. -/
theorem sourceFieldCode_termsDegreeLE
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars) :
    ∀ j,
      PolynomialCode.TermsDegreeLE (sourceDegreeBound I)
        (sourceFieldCode parameters I j) := by
  intro j
  exact
    (FixedDetectorPolynomialCode.fieldCode_termsDegreeLE
      parameters I j).promote
        (fieldDegree_le_sourceDegreeBound I)

/-- Every drift coordinate satisfies the same common raw bound. -/
theorem sourceDriftCode_termsDegreeLE
    (I : DQLSystem eqs vars) :
    ∀ i,
      PolynomialCode.TermsDegreeLE (sourceDegreeBound I)
        (sourceDriftCode I i) := by
  intro i
  exact
    (FixedDetectorDriftCode.driftCode_termsDegreeLE I i).promote
      (driftDegree_le_sourceDegreeBound I)

/-- Ordinary total degree gives the denominator-clearing premise for the
unique all-affine source block. -/
theorem sourceFieldCode_termsAffineBlockDegreeLE
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars) :
    ∀ j,
      MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
        layout (clearingExponent I)
        (sourceFieldCode parameters I j) := by
  intro j
  apply
    MixedCentralPolynomialCode.termsAffineBlockDegreeLE_oneBlockAllAffineLayout
  exact
    (sourceFieldCode_termsDegreeLE parameters I j).promote
      (sourceDegreeBound_le_clearingExponent I)

/-- The same clearing premise holds for every drift coordinate. -/
theorem sourceDriftCode_termsAffineBlockDegreeLE
    (I : DQLSystem eqs vars) :
    ∀ i,
      MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
        layout (clearingExponent I) (sourceDriftCode I i) := by
  intro i
  apply
    MixedCentralPolynomialCode.termsAffineBlockDegreeLE_oneBlockAllAffineLayout
  exact
    (sourceDriftCode_termsDegreeLE I i).promote
      (sourceDegreeBound_le_clearingExponent I)

/-- There is no pre-existing compact source block, so the corresponding
tangency premise is vacuous. -/
theorem baseCompactTangency
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars) :
    CompactAccumulatorPipelineCode.BaseCompactTangency
      layout (clearingExponent I)
      (sourceFieldCode parameters I) := by
  intro y
  dsimp
  intro c
  exact Fin.elim0 c

/-! ## Executable compact-source compiler -/

/-- Runtime input: controller parameters, the DQL table, accumulator
scale `κ`, and strict-sign margin `ε`. -/
abbrev CompilerInput (eqs vars : ℕ) :=
  (((Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode) ×
      DQLSystem eqs vars) × RationalCode) × RationalCode

def parameters
    (u : CompilerInput eqs vars) :
    Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
      RationalCode :=
  u.1.1.1

def system (u : CompilerInput eqs vars) :
    DQLSystem eqs vars :=
  u.1.1.2

def accumulatorScale (u : CompilerInput eqs vars) :
    RationalCode :=
  u.1.2

def rewardMargin (u : CompilerInput eqs vars) :
    RationalCode :=
  u.2

/-- The literal input expected by the generic compact accumulator
pipeline. -/
def toPipelineInput
    (u : CompilerInput eqs vars) :
    CompactAccumulatorPipelineCode.CompilerInput
      (sourceDimension eqs vars) (driftDimension vars) :=
  (((accumulatorScale u,
      sourceFieldCode (parameters u) (system u)),
    sourceDriftCode (system u)),
    rewardMargin u)

/-- Complete centrally compactified source field and strict-sign reward. -/
def compile
    (u : CompilerInput eqs vars) :
    PolynomialFieldCode (finalDimension eqs vars) ×
      PolynomialCode (finalDimension eqs vars) :=
  CompactAccumulatorPipelineCode.compile
    layout (clearingExponent (system u)) (toPipelineInput u)

/-! ## Raw output degrees -/

/-- Every coordinate of the emitted compact polynomial field satisfies the
explicit instance-dependent bound. -/
theorem compile_field_termsDegreeLE
    (u : CompilerInput eqs vars) :
    ∀ q,
      PolynomialCode.TermsDegreeLE
        (compactFieldDegree (system u))
        ((compile u).1 q) := by
  simpa [compile, toPipelineInput, compactFieldDegree,
    affineBlockCount] using
    (CompactAccumulatorPipelineCode.fieldCode_termsDegreeLE
      layout (clearingExponent (system u))
      (accumulatorScale u)
      (sourceFieldCode (parameters u) (system u))
      (sourceFieldCode_termsDegreeLE (parameters u) (system u))
      (sourceDriftCode (system u))
      (sourceDriftCode_termsDegreeLE (system u)))

/-- The emitted reward has raw degree at most two. -/
theorem compile_reward_termsDegreeLE
    (u : CompilerInput eqs vars) :
    PolynomialCode.TermsDegreeLE compactRewardDegree
      (compile u).2 := by
  simpa [compile, toPipelineInput, compactRewardDegree,
    affineBlockCount] using
    (CompactAccumulatorPipelineCode.rewardCode_termsDegreeLE
      (n := sourceDimension eqs vars)
      (k := affineBlockCount)
      (m := driftDimension vars)
      (rewardMargin u))

/-- One common raw bound for the field and reward output pair. -/
theorem compile_termsDegreeLE
    (u : CompilerInput eqs vars) :
    (∀ q,
      PolynomialCode.TermsDegreeLE
        (compilerDegree (system u)) ((compile u).1 q)) ∧
      PolynomialCode.TermsDegreeLE
        (compilerDegree (system u)) (compile u).2 := by
  constructor
  · intro q
    exact
      (compile_field_termsDegreeLE u q).promote
        (Nat.le_max_left _ _)
  · exact
      (compile_reward_termsDegreeLE u).promote
        (Nat.le_max_right _ _)

/-! ## Exact scaled-chart semantics -/

/-- The slowed accumulator forcing is exactly the decoded rational scale,
the central time slowdown, and the semantic detector drift. -/
@[simp]
theorem eval₂Hom_slowedDriftCode_scaledChart
    (u : CompilerInput eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars)
    (w : Fin affineBlockCount → ℝ)
    (i : Fin (driftDimension vars)) :
    eval₂Hom (algebraMap ℚ ℝ)
        (MixedCentralPolynomialCode.scaledChartPoint
          layout w (FixedDetectorPolynomialCode.point z))
        (PolynomialCode.decode
          (CompactAccumulatorPipelineCode.slowedDriftCode
            layout (clearingExponent (system u))
            (accumulatorScale u)
            (sourceDriftCode (system u)) i)) =
      (RationalCode.decode (accumulatorScale u) : ℝ) *
        MixedCentralPolynomialCode.slowdown
          (clearingExponent (system u)) w *
        FixedDetectorDriftCode.driftValue (system u) z i := by
  rw [
    CompactAccumulatorPipelineCode.eval₂Hom_slowedDriftCode_scaledChart
      layout (clearingExponent (system u))
      (accumulatorScale u) (sourceDriftCode (system u))
      (sourceDriftCode_termsAffineBlockDegreeLE (system u))
      i w (FixedDetectorPolynomialCode.point z)]
  simp [sourceDriftCode]

/-- The base coordinates of the compact source retain the exact centrally
compactified fixed-detector vector field. -/
@[simp]
theorem eval₂Hom_compile_base_scaledChart
    (u : CompilerInput eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars)
    (w : Fin affineBlockCount → ℝ)
    (a : Fin (driftDimension vars) → ℝ)
    (W : ℝ)
    (q : Fin (sourceDimension eqs vars + affineBlockCount)) :
    eval₂Hom (algebraMap ℚ ℝ)
        (AccumulatorPolynomialCode.combinedPoint
          (MixedCentralPolynomialCode.scaledChartPoint
            layout w (FixedDetectorPolynomialCode.point z))
          a W)
        (PolynomialCode.decode
          ((compile u).1
            (AccumulatorPolynomialCode.baseIndex
              (n := sourceDimension eqs vars + affineBlockCount)
              (m := driftDimension vars) q))) =
      MixedCentralPolynomialCode.mixedAmbientField
        layout
        (MixedCentralPolynomialCode.slowdown
          (clearingExponent (system u)) w)
        w
        (MixedCentralPolynomialCode.scaledSourcePoint
          layout w (FixedDetectorPolynomialCode.point z))
        (FixedDetectorPolynomialCode.point
          (FixedDetectorPolynomialCode.vectorField
            (parameters u) (system u) z)) q := by
  have h :=
    CompactAccumulatorPipelineCode.eval₂Hom_fieldCode_base_scaledChart
      layout (clearingExponent (system u))
      (accumulatorScale u)
      (sourceFieldCode (parameters u) (system u))
      (sourceFieldCode_termsAffineBlockDegreeLE
        (parameters u) (system u))
      (sourceDriftCode (system u)) q w
      (FixedDetectorPolynomialCode.point z) a W
  have hfield :=
    FixedDetectorPolynomialCode.realize_fieldCode
      (parameters u) (system u) z
  simpa [compile, toPipelineInput, sourceFieldCode] using
    h.trans (congrArg
      (fun v ↦
        MixedCentralPolynomialCode.mixedAmbientField
          layout
          (MixedCentralPolynomialCode.slowdown
            (clearingExponent (system u)) w)
          w
          (MixedCentralPolynomialCode.scaledSourcePoint
            layout w (FixedDetectorPolynomialCode.point z)) v q)
      hfield)

/-- Every accumulator-vector coordinate realizes the exact compactified
translation field driven by the semantic detector drift. -/
@[simp]
theorem eval₂Hom_compile_u_scaledChart
    (u : CompilerInput eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars)
    (w : Fin affineBlockCount → ℝ)
    (a : Fin (driftDimension vars) → ℝ)
    (W : ℝ) (i : Fin (driftDimension vars)) :
    eval₂Hom (algebraMap ℚ ℝ)
        (AccumulatorPolynomialCode.combinedPoint
          (MixedCentralPolynomialCode.scaledChartPoint
            layout w (FixedDetectorPolynomialCode.point z))
          a W)
        (PolynomialCode.decode
          ((compile u).1
            (AccumulatorPolynomialCode.uIndex
              (n := sourceDimension eqs vars + affineBlockCount) i))) =
      accumulatorUField a W
        (fun j ↦
          (RationalCode.decode (accumulatorScale u) : ℝ) *
            MixedCentralPolynomialCode.slowdown
              (clearingExponent (system u)) w *
            FixedDetectorDriftCode.driftValue (system u) z j) i := by
  simpa [compile, toPipelineInput, sourceDriftCode] using
    (CompactAccumulatorPipelineCode.eval₂Hom_fieldCode_u_scaledChart
      layout (clearingExponent (system u))
      (accumulatorScale u)
      (sourceFieldCode (parameters u) (system u))
      (sourceDriftCode (system u))
      (sourceDriftCode_termsAffineBlockDegreeLE (system u))
      w (FixedDetectorPolynomialCode.point z) a W i)

/-- The scalar accumulator coordinate realizes the matching compactified
translation equation. -/
@[simp]
theorem eval₂Hom_compile_w_scaledChart
    (u : CompilerInput eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars)
    (w : Fin affineBlockCount → ℝ)
    (a : Fin (driftDimension vars) → ℝ)
    (W : ℝ) :
    eval₂Hom (algebraMap ℚ ℝ)
        (AccumulatorPolynomialCode.combinedPoint
          (MixedCentralPolynomialCode.scaledChartPoint
            layout w (FixedDetectorPolynomialCode.point z))
          a W)
        (PolynomialCode.decode
          ((compile u).1
            (AccumulatorPolynomialCode.wIndex
              (sourceDimension eqs vars + affineBlockCount)
              (driftDimension vars)))) =
      accumulatorWField a W
        (fun j ↦
          (RationalCode.decode (accumulatorScale u) : ℝ) *
            MixedCentralPolynomialCode.slowdown
              (clearingExponent (system u)) w *
            FixedDetectorDriftCode.driftValue (system u) z j) := by
  simpa [compile, toPipelineInput, sourceDriftCode] using
    (CompactAccumulatorPipelineCode.eval₂Hom_fieldCode_w_scaledChart
      layout (clearingExponent (system u))
      (accumulatorScale u)
      (sourceFieldCode (parameters u) (system u))
      (sourceDriftCode (system u))
      (sourceDriftCode_termsAffineBlockDegreeLE (system u))
      w (FixedDetectorPolynomialCode.point z) a W)

/-- In the one-block layout the reward is literally
`W + 2 w₀² - 1 - ε`. -/
@[simp]
theorem eval₂Hom_compile_reward_scaledChart
    (u : CompilerInput eqs vars)
    (z : Fin (sourceDimension eqs vars) → ℝ)
    (w : Fin affineBlockCount → ℝ)
    (a : Fin (driftDimension vars) → ℝ)
    (W : ℝ) :
    eval₂Hom (algebraMap ℚ ℝ)
        (AccumulatorPolynomialCode.combinedPoint
          (MixedCentralPolynomialCode.scaledChartPoint layout w z)
          a W)
        (PolynomialCode.decode (compile u).2) =
      W + 2 * w 0 ^ 2 - 1 -
        (RationalCode.decode (rewardMargin u) : ℝ) := by
  simpa [compile, toPipelineInput, affineBlockCount] using
    (CompactAccumulatorPipelineCode.eval₂Hom_rewardCode
      (n := sourceDimension eqs vars)
      (k := affineBlockCount)
      (l := compactBlockCount)
      (m := driftDimension vars)
      (rewardMargin u) layout w z a W)

/-! ## Primitive-recursive degree selection -/

private theorem natListSum_primrec :
    Primrec (fun xs : List ℕ ↦ xs.sum) := by
  have hstep :
      Primrec₂
        (fun (_ : List ℕ) (p : ℕ × ℕ) ↦ p.1 + p.2) :=
    Primrec.nat_add.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.list_foldr Primrec.id (Primrec.const 0) hstep).of_eq
      (fun _ ↦ rfl)

private theorem finSumNat_primrec
    {α : Type*} [Primcodable α] {r : ℕ}
    (f : α → Fin r → ℕ)
    (hf : ∀ i, Primrec (fun a ↦ f a i)) :
    Primrec (fun a ↦ ∑ i, f a i) := by
  have hlist :
      Primrec (fun a ↦ List.ofFn fun i ↦ f a i) :=
    Primrec.list_ofFn hf
  exact
    (natListSum_primrec.comp hlist).of_eq
      (by
        intro a
        simp [List.sum_ofFn])

/-- Absolute exponent energy is primitive recursive on every fixed finite
integer tuple. -/
theorem exponentEnergy_primrec {q : ℕ} :
    Primrec
      (exponentEnergy :
        (Fin q → ℤ) → ℕ) := by
  have hlist :
      Primrec
        (fun e : Fin q → ℤ ↦
          List.ofFn fun i ↦ (e i).natAbs) :=
    Primrec.list_ofFn fun i ↦
      Clocks.ControllerPhaseProductCharacterCode.intNatAbs_primrec.comp
        (Primrec.fin_app.comp Primrec.id (Primrec.const i))
  exact
    (natListSum_primrec.comp hlist).of_eq
      (by
        intro e
        simp [exponentEnergy, List.sum_ofFn])

/-- The reciprocal-character energy ledger used by the detector field is
primitive recursive in the DQL table. -/
theorem reciprocalExponentEnergySum_primrec :
    Primrec
      (FixedDetectorPolynomialCode.reciprocalExponentEnergySum :
        DQLSystem eqs vars → ℕ) := by
  apply finSumNat_primrec
  intro k
  exact
    exponentEnergy_primrec.comp
      (DetectorPoissonReciprocalCode.reciprocalExponent_primrec k)

/-- The detector source-field degree bound is primitive recursive. -/
theorem fieldDegree_primrec :
    Primrec
      (FixedDetectorPolynomialCode.fieldDegree :
        DQLSystem eqs vars → ℕ) := by
  exact
    (Primrec.nat_max.comp
      (Primrec.const 9)
      (Primrec.nat_add.comp
        reciprocalExponentEnergySum_primrec
        (Primrec.const 3))).of_eq
      (fun _ ↦ rfl)

/-- The fourth-root gauge energy ledger is primitive recursive. -/
theorem gaugeExponentEnergySum_primrec :
    Primrec
      (FixedDetectorPolynomialCode.gaugeExponentEnergySum :
        DQLSystem eqs vars → ℕ) := by
  apply finSumNat_primrec
  intro j
  exact
    exponentEnergy_primrec.comp
      (DetectorJacobiGaugeData.gaugeExponents_primrec j)

/-- The validity-energy degree bound is primitive recursive. -/
theorem validityDegree_primrec :
    Primrec
      (FixedDetectorValidityEnergyCode.validityDegree :
        DQLSystem eqs vars → ℕ) := by
  have hgauge :
      Primrec
        (FixedDetectorValidityEnergyCode.gaugeResidualEnergyDegree :
          DQLSystem eqs vars → ℕ) :=
    (Primrec.nat_mul.comp
      (Primrec.const 2)
      (Primrec.nat_max.comp
        (Primrec.const 4)
        gaugeExponentEnergySum_primrec)).of_eq
      (fun _ ↦ rfl)
  have hreciprocal :
      Primrec
        (FixedDetectorValidityEnergyCode.reciprocalResidualEnergyDegree :
          DQLSystem eqs vars → ℕ) :=
    (Primrec.nat_mul.comp
      (Primrec.const 2)
      (Primrec.nat_add.comp
        reciprocalExponentEnergySum_primrec
        (Primrec.const 1))).of_eq
      (fun _ ↦ rfl)
  exact
    (Primrec.nat_max.comp
      (Primrec.const 8)
      (Primrec.nat_max.comp hgauge hreciprocal)).of_eq
      (fun _ ↦ rfl)

/-- The complete selector-moment character-energy ledger is primitive
recursive. -/
theorem momentCharacterEnergySum_primrec :
    Primrec
      (FixedDetectorMomentCode.momentCharacterEnergySum :
        DQLSystem eqs vars → ℕ) := by
  apply finSumNat_primrec
  intro j
  have hplus :
      Primrec
        (fun I : DQLSystem eqs vars ↦
          exponentEnergy
            (FixedDetectorMomentCode.jacobiPlusExponent I j)) :=
    exponentEnergy_primrec.comp
      (FixedDetectorMomentCode.jacobiPlusExponent_primrec j)
  have hminus :
      Primrec
        (fun I : DQLSystem eqs vars ↦
          exponentEnergy
            (FixedDetectorMomentCode.jacobiMinusExponent I j)) :=
    exponentEnergy_primrec.comp
      (FixedDetectorMomentCode.jacobiMinusExponent_primrec j)
  exact
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp
          (Primrec.const
            (exponentEnergy
              (FixedDetectorMomentCode.unaryFirstHarmonicExponent
                (eqs := eqs) j)))
          (Primrec.const
            (exponentEnergy
              (FixedDetectorMomentCode.rootHalfExponent
                (eqs := eqs) j))))
        hplus)
      hminus).of_eq
      (fun _ ↦ rfl)

/-- The selector-moment degree bound is primitive recursive. -/
theorem momentDegree_primrec :
    Primrec
      (FixedDetectorMomentCode.momentDegree :
        DQLSystem eqs vars → ℕ) :=
  (Primrec.nat_add.comp
    momentCharacterEnergySum_primrec
    (Primrec.const 2)).of_eq
    (fun _ ↦ rfl)

/-- The full drift degree bound is primitive recursive. -/
theorem driftDegree_primrec :
    Primrec
      (FixedDetectorDriftCode.driftDegree :
        DQLSystem eqs vars → ℕ) :=
  (Primrec.nat_max.comp
    validityDegree_primrec
    (Primrec.nat_max.comp
      momentDegree_primrec
      (Primrec.const (4 * vars + 1)))).of_eq
    (fun _ ↦ rfl)

/-- The common affine source/drift degree is primitive recursive. -/
theorem sourceDegreeBound_primrec :
    Primrec
      (sourceDegreeBound :
        DQLSystem eqs vars → ℕ) :=
  Primrec.nat_max.comp fieldDegree_primrec driftDegree_primrec

/-- The selected even denominator-clearing exponent is primitive
recursive in the DQL table. -/
theorem clearingExponent_primrec :
    Primrec
      (clearingExponent :
        DQLSystem eqs vars → ℕ) :=
  Primrec.nat_mul.comp
    (Primrec.const 2) sourceDegreeBound_primrec

/-! ## A reusable dynamic-exponent central compiler -/

/-- Unlike the generic fixed-exponent theorem, this lemma permits the
clearing exponent to be part of the runtime input. -/
theorem homogenize_withExponent_primrec
    {n k l : ℕ}
    (L : Fin n → Fin k ⊕ Fin l) :
    Primrec
      (fun input : ℕ × PolynomialCode n ↦
        MixedCentralPolynomialCode.homogenize
          L input.1 input.2) := by
  have hliftExponent :
      Primrec
        (fun input : ℕ × ExponentCode n ↦
          MixedCentralPolynomialCode.liftExponent
            L input.1 input.2) := by
    rw [Primrec.fin_curry]
    apply Primrec₂.swap
    rw [Primrec.fin_curry₁]
    intro q
    cases hq : finSumFinEquiv.symm q with
    | inl j =>
        exact
          (Primrec.fin_app.comp Primrec.snd
            (Primrec.const j)).of_eq
            (by
              intro input
              simp [MixedCentralPolynomialCode.liftExponent, hq])
    | inr b =>
        exact
          (Primrec.nat_sub.comp
            Primrec.fst
            ((MixedCentralPolynomialCode.affineBlockDegree_primrec
              L b).comp Primrec.snd)).of_eq
            (by
              intro input
              simp [MixedCentralPolynomialCode.liftExponent, hq])
  have hliftTerm :
      Primrec
        (fun input :
            ℕ × (ExponentCode n × RationalCode) ↦
          MixedCentralPolynomialCode.liftTerm
            L input.1 input.2) := by
    exact
      (Primrec.pair
        (hliftExponent.comp
          (Primrec.pair Primrec.fst
            (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp Primrec.snd)).of_eq
        (fun _ ↦ rfl)
  have hmap :
      Primrec₂
        (fun input : ℕ × PolynomialCode n ↦
          fun term ↦
            MixedCentralPolynomialCode.liftTerm
              L input.1 term) := by
    change
      Primrec
        (fun p :
            (ℕ × PolynomialCode n) ×
              (ExponentCode n × RationalCode) ↦
          MixedCentralPolynomialCode.liftTerm
            L p.1.1 p.2)
    exact
      hliftTerm.comp
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          Primrec.snd)
  exact
    (Primrec.list_map Primrec.snd hmap).of_eq
      (fun _ ↦ rfl)

/-- The mixed-central field compiler is primitive recursive jointly in a
runtime clearing exponent and source field. -/
theorem mixedFieldCode_withExponent_primrec
    {n k l : ℕ}
    (L : Fin n → Fin k ⊕ Fin l) :
    Primrec
      (fun input : ℕ × PolynomialFieldCode n ↦
        MixedCentralPolynomialCode.fieldCode
          L input.1 input.2) := by
  have hdot :
      ∀ b : Fin k,
        Primrec
          (fun input : ℕ × PolynomialFieldCode n ↦
            MixedCentralPolynomialCode.affineBlockDotCode
              L input.1 input.2 b) := by
    intro b
    apply PolynomialCode.sumCodes_primrec.comp
    apply Primrec.list_ofFn
    intro j
    by_cases hj : L j = Sum.inl b
    · have hPj :
          Primrec
            (fun input : ℕ × PolynomialFieldCode n ↦
              MixedCentralPolynomialCode.homogenize
                L input.1 (input.2 j)) :=
        (homogenize_withExponent_primrec L).comp
          (Primrec.pair Primrec.fst
            (Primrec.fin_app.comp Primrec.snd
              (Primrec.const j)))
      exact
        (PolynomialCode.mul_primrec.comp
          (Primrec.const
            (PolynomialCode.varCode
              (MixedCentralPolynomialCode.xIndex (k := k) j)))
          hPj).of_eq
          (by
            intro input
            simp [hj])
    · exact
        (Primrec.const PolynomialCode.zero).of_eq
          (by
            intro input
            simp [hj])
  have hx :
      ∀ j : Fin n,
        Primrec
          (fun input : ℕ × PolynomialFieldCode n ↦
            MixedCentralPolynomialCode.xFieldCode
              L input.1 input.2 j) := by
    intro j
    cases hj : L j with
    | inl b =>
        have hPj :
            Primrec
              (fun input : ℕ × PolynomialFieldCode n ↦
                MixedCentralPolynomialCode.homogenize
                  L input.1 (input.2 j)) :=
          (homogenize_withExponent_primrec L).comp
            (Primrec.pair Primrec.fst
              (Primrec.fin_app.comp Primrec.snd
                (Primrec.const j)))
        exact
          (PolynomialCode.mul_primrec.comp
            (Primrec.const
              (PolynomialCode.varCode
                (MixedCentralPolynomialCode.wIndex (n := n) b)))
            (PolynomialCode.sub_primrec.comp
              hPj
              (PolynomialCode.mul_primrec.comp
                (Primrec.const
                  (PolynomialCode.varCode
                    (MixedCentralPolynomialCode.xIndex (k := k) j)))
                (hdot b)))).of_eq
            (by
              intro input
              rw [MixedCentralPolynomialCode.xFieldCode, hj])
    | inr c =>
        exact
          ((homogenize_withExponent_primrec L).comp
            (Primrec.pair Primrec.fst
              (Primrec.fin_app.comp Primrec.snd
                (Primrec.const j)))).of_eq
            (by
              intro input
              simp [MixedCentralPolynomialCode.xFieldCode, hj])
  have hw :
      ∀ b : Fin k,
        Primrec
          (fun input : ℕ × PolynomialFieldCode n ↦
            MixedCentralPolynomialCode.wFieldCode
              L input.1 input.2 b) := by
    intro b
    exact
      (PolynomialCode.neg_primrec.comp
        (PolynomialCode.mul_primrec.comp
          (Primrec.const
            (PolynomialCode.pow
              (PolynomialCode.varCode
                (MixedCentralPolynomialCode.wIndex (n := n) b)) 2))
          (hdot b))).of_eq
        (fun _ ↦ rfl)
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro q
  cases hq : finSumFinEquiv.symm q with
  | inl j =>
      exact
        (hx j).of_eq
          (by
            intro input
            rw [MixedCentralPolynomialCode.fieldCode, hq])
  | inr b =>
      exact
        (hw b).of_eq
          (by
            intro input
            rw [MixedCentralPolynomialCode.fieldCode, hq])

/-! ## Effectivity of the complete specialization -/

/-- Packaging of the concrete field, drift, scale, and reward data is
primitive recursive. -/
theorem toPipelineInput_primrec :
    Primrec
      (toPipelineInput :
        CompilerInput eqs vars →
          CompactAccumulatorPipelineCode.CompilerInput
            (sourceDimension eqs vars) (driftDimension vars)) := by
  have hfieldDrift :
      Primrec
        (fun u : CompilerInput eqs vars ↦
          FixedDetectorDriftCode.fieldAndDriftCode u.1.1) :=
    FixedDetectorDriftCode.fieldAndDriftCode_primrec.comp
      (Primrec.fst.comp Primrec.fst)
  exact
    (Primrec.pair
      (Primrec.pair
        (Primrec.pair
          (Primrec.snd.comp Primrec.fst)
          (Primrec.fst.comp hfieldDrift))
        (Primrec.snd.comp hfieldDrift))
      Primrec.snd).of_eq
      (fun _ ↦ rfl)

/-- The slowed drift family is primitive recursive jointly in its clearing
exponent, rational scale, and raw drift family. -/
theorem slowedDrift_withExponent_primrec
    {n k l m : ℕ}
    (L : Fin n → Fin k ⊕ Fin l) :
    Primrec
      (fun input :
          (ℕ × RationalCode) ×
            (Fin m → PolynomialCode n) ↦
        CompactAccumulatorPipelineCode.slowedDriftCode
          L input.1.1 input.1.2 input.2) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro i
  have hi :
      Primrec
        (fun input :
            (ℕ × RationalCode) ×
              (Fin m → PolynomialCode n) ↦
          input.2 i) :=
    Primrec.fin_app.comp Primrec.snd (Primrec.const i)
  have hhom :
      Primrec
        (fun input :
            (ℕ × RationalCode) ×
              (Fin m → PolynomialCode n) ↦
          MixedCentralPolynomialCode.homogenize
            L input.1.1 (input.2 i)) :=
    (homogenize_withExponent_primrec L).comp
      (Primrec.pair
        (Primrec.fst.comp Primrec.fst) hi)
  exact
    (PolynomialCode.mul_primrec.comp
      (PolynomialCode.constant_primrec.comp
        (Primrec.snd.comp Primrec.fst))
      hhom).of_eq
      (fun _ ↦ rfl)

set_option maxHeartbeats 1200000 in
-- Jointly encoded finite field families make this composition expensive.
/-- The compact pipeline field is primitive recursive jointly in the
runtime clearing exponent and ordinary field input. -/
theorem pipelineField_withExponent_primrec
    {n k l m : ℕ}
    (L : Fin n → Fin k ⊕ Fin l) :
    Primrec
      (fun input :
          (ℕ × PolynomialFieldCode n) ×
            (RationalCode ×
              (Fin m → PolynomialCode n)) ↦
        CompactAccumulatorPipelineCode.fieldCode
          L input.1.1 input.2.1 input.1.2 input.2.2) := by
  have hbase :
      Primrec
        (fun input :
            (ℕ × PolynomialFieldCode n) ×
              (RationalCode ×
                (Fin m → PolynomialCode n)) ↦
          MixedCentralPolynomialCode.fieldCode
            L input.1.1 input.1.2) :=
    (mixedFieldCode_withExponent_primrec L).comp Primrec.fst
  have hslow :
      Primrec
        (fun input :
            (ℕ × PolynomialFieldCode n) ×
              (RationalCode ×
                (Fin m → PolynomialCode n)) ↦
          CompactAccumulatorPipelineCode.slowedDriftCode
            L input.1.1 input.2.1 input.2.2) :=
    (slowedDrift_withExponent_primrec L).comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))
  exact
    ((AccumulatorPolynomialCode.fieldCode_primrec
      (n + k) m).comp
        (Primrec.pair hbase hslow)).of_eq
      (fun _ ↦ rfl)

/-- The generic compact pipeline is primitive recursive jointly in a
runtime clearing exponent and its usual compiler input. -/
theorem pipelineCompile_withExponent_primrec
    {n k l m : ℕ}
    (L : Fin n → Fin k ⊕ Fin l) :
    Primrec
      (fun input :
          ℕ × CompactAccumulatorPipelineCode.CompilerInput n m ↦
        CompactAccumulatorPipelineCode.compile
          L input.1 input.2) := by
  exact
    (Primrec.pair
      ((pipelineField_withExponent_primrec L).comp
        (Primrec.pair
          (Primrec.pair Primrec.fst
            (Primrec.snd.comp
              (Primrec.fst.comp
                (Primrec.fst.comp Primrec.snd))))
          (Primrec.pair
            (Primrec.fst.comp
              (Primrec.fst.comp
                (Primrec.fst.comp Primrec.snd)))
            (Primrec.snd.comp
              (Primrec.fst.comp Primrec.snd)))))
      ((CompactAccumulatorPipelineCode.rewardCode_primrec
        (n := n) (k := k) (m := m)).comp
          (Primrec.snd.comp Primrec.snd))).of_eq
      (fun _ ↦ rfl)

/-- The complete compact-source field/reward compiler is primitive
recursive even though its clearing exponent varies with the DQL table. -/
theorem compile_primrec :
    Primrec
      (compile :
        CompilerInput eqs vars →
          PolynomialFieldCode (finalDimension eqs vars) ×
            PolynomialCode (finalDimension eqs vars)) := by
  have hsystem :
      Primrec
        (fun u : CompilerInput eqs vars ↦ system u) :=
    (Primrec.snd.comp
      (Primrec.fst.comp Primrec.fst)).of_eq
      (fun _ ↦ rfl)
  exact
    ((pipelineCompile_withExponent_primrec layout).comp
      (Primrec.pair
        (clearingExponent_primrec.comp hsystem)
        toPipelineInput_primrec)).of_eq
      (fun _ ↦ rfl)

/-- Computable form of `compile_primrec`. -/
theorem compile_computable :
    Computable
      (compile :
        CompilerInput eqs vars →
          PolynomialFieldCode (finalDimension eqs vars) ×
            PolynomialCode (finalDimension eqs vars)) :=
  compile_primrec.to_comp

end FixedDetectorCompactSourceCode

end HGAS
