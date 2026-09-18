import HGAS.MeasureTheory.TransitiveInvariantProbabilityUnique
import HGAS.Modular.GammaTwoChosenHaarCuspBridge
import Mathlib.Topology.Algebra.Constructions

/-!
# Uniqueness of Γ(2) frame-Haar probability

This file proves that a probability measure on

`Γ(2) \ SL(2, ℝ)`

which is invariant under every descended right translation is unique.
It therefore identifies the older `Classical.choose` witness
`gammaTwoFrameHaarProbability` with the explicit normalized
fundamental-domain probability
`gammaTwoExplicitFrameHaarProbability`.

The quotient by `Γ(2)` is not a group: `Γ(2)` is not normal in
`SL(2, ℝ)`.  Accordingly, group-quotient Haar uniqueness cannot be
applied directly.  Instead, right translation is packaged as a left
action of the opposite group `SL(2, ℝ)ᵐᵒᵖ`.  This action is jointly
measurable and transitive.  The general theorem
`HGAS.MeasureTheory.invariantProbability_unique_of_pretransitive`
then applies without any normality assumption.
-/

namespace HGAS.Modular

open Function Matrix Topology
open _root_.MeasureTheory
open scoped ENNReal NNReal Pointwise

noncomputable section

/-! ## The opposite-group action -/

/-- The measurable and topological structures on the opposite frame
group define the same Borel σ-algebra.

Mathlib supplies both structures, but not this compatibility instance
for opposite types. -/
instance realModularFrameOppositeBorelSpace :
    BorelSpace RealModularFrameᵐᵒᵖ := by
  let e : RealModularFrameᵐᵒᵖ ≃ᵐ
      RealModularFrame :=
    { toEquiv := MulOpposite.opEquiv.symm
      measurable_toFun := measurable_mul_unop
      measurable_invFun := measurable_mul_op }
  exact
    e.measurableEmbedding.borelSpace
      MulOpposite.opHomeomorph.symm.isInducing

/-- Second countability transfers across the opposite-group
homeomorphism. -/
instance realModularFrameOppositeSecondCountable :
    SecondCountableTopology RealModularFrameᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

/-- Descended right multiplication, regarded as a left action of the
opposite frame group. -/
instance gammaTwoFrameQuotientOppositeSMul :
    SMul RealModularFrameᵐᵒᵖ
      GammaTwoFrameQuotient where
  smul a q := gammaTwoFrameRightMul a.unop q

/-- Right multiplication satisfies the action law after reversing
products in the opposite group. -/
instance gammaTwoFrameQuotientOppositeMulAction :
    MulAction RealModularFrameᵐᵒᵖ
      GammaTwoFrameQuotient where
  one_smul q := by
    change gammaTwoFrameRightMul 1 q = q
    rw [gammaTwoFrameRightMul_one]
    rfl
  mul_smul a b q := by
    change
      gammaTwoFrameRightMul (a * b).unop q =
        gammaTwoFrameRightMul a.unop
          (gammaTwoFrameRightMul b.unop q)
    rw [MulOpposite.unop_mul,
      gammaTwoFrameRightMul_mul]
    rfl

/-- The full opposite-group action on the quotient is continuous.

After precomposition with the open quotient map on the second
coordinate, this is simply the continuous map
`(a, g) ↦ Γ(2) · (g * a.unop)`. -/
theorem gammaTwoFrameQuotientOppositeSMul_continuous :
    Continuous
      (fun p : RealModularFrameᵐᵒᵖ ×
          GammaTwoFrameQuotient ↦ p.1 • p.2) := by
  rw [←
    (IsOpenQuotientMap.id.prodMap
      gammaTwoFrameQuotientMk_isOpenQuotientMap)
      |>.continuous_comp_iff]
  change Continuous
    (fun p : RealModularFrameᵐᵒᵖ ×
        RealModularFrame ↦
      gammaTwoFrameQuotientMk
        (p.2 * p.1.unop))
  exact
    gammaTwoFrameQuotientMk_isCoveringMap.continuous.comp
      (continuous_snd.mul
        (MulOpposite.continuous_unop.comp
          continuous_fst))

instance gammaTwoFrameQuotientOppositeMeasurableSMul :
    MeasurableSMul₂ RealModularFrameᵐᵒᵖ
      GammaTwoFrameQuotient where
  measurable_smul :=
    gammaTwoFrameQuotientOppositeSMul_continuous.measurable

/-- The action is transitive: the element represented by
`op (g⁻¹ * h)` sends the class of `g` to the class of `h`. -/
instance gammaTwoFrameQuotientOppositePretransitive :
    MulAction.IsPretransitive
      RealModularFrameᵐᵒᵖ
      GammaTwoFrameQuotient where
  exists_smul_eq q r := by
    induction q using Quotient.inductionOn with
    | _ g =>
      induction r using Quotient.inductionOn with
      | _ h =>
        refine
          ⟨MulOpposite.op (g⁻¹ * h), ?_⟩
        change
          gammaTwoFrameQuotientMk
              (g * (g⁻¹ * h)) =
            gammaTwoFrameQuotientMk h
        rw [mul_inv_cancel_left]

/-! ## Invariance and uniqueness -/

/-- The project's intrinsic right-invariance predicate is exactly
Mathlib's invariant-measure class for the opposite-group action. -/
theorem isRightInvariantFrameProbability_iff_smulInvariant
    (ν : ProbabilityMeasure GammaTwoFrameQuotient) :
    IsRightInvariantFrameProbability ν ↔
      SMulInvariantMeasure
        RealModularFrameᵐᵒᵖ
        GammaTwoFrameQuotient
        (ν : Measure GammaTwoFrameQuotient) := by
  constructor
  · intro h
    constructor
    intro a s hs
    have hmap :
        Measure.map (a • ·)
            (ν : Measure GammaTwoFrameQuotient) =
          (ν : Measure GammaTwoFrameQuotient) := by
      exact
        congrArg ProbabilityMeasure.toMeasure
          (h a.unop)
    exact
      Measure.measure_preimage_of_map_eq_self
        hmap hs.nullMeasurableSet
  · intro h
    letI : SMulInvariantMeasure
        RealModularFrameᵐᵒᵖ
        GammaTwoFrameQuotient
        (ν : Measure GammaTwoFrameQuotient) := h
    intro a
    apply ProbabilityMeasure.toMeasure_injective
    exact
      (measurePreserving_smul
        (MulOpposite.op a)
        (ν : Measure GammaTwoFrameQuotient)).map_eq

/-- Any two right-invariant probabilities on the Γ(2) frame quotient
are equal. -/
theorem gammaTwoRightInvariantProbability_unique
    (ν₁ ν₂ :
      ProbabilityMeasure GammaTwoFrameQuotient)
    (hν₁ : IsRightInvariantFrameProbability ν₁)
    (hν₂ : IsRightInvariantFrameProbability ν₂) :
    ν₁ = ν₂ := by
  letI : SMulInvariantMeasure
      RealModularFrameᵐᵒᵖ
      GammaTwoFrameQuotient
      (ν₁ : Measure GammaTwoFrameQuotient) :=
    (isRightInvariantFrameProbability_iff_smulInvariant
      ν₁).mp hν₁
  letI : SMulInvariantMeasure
      RealModularFrameᵐᵒᵖ
      GammaTwoFrameQuotient
      (ν₂ : Measure GammaTwoFrameQuotient) :=
    (isRightInvariantFrameProbability_iff_smulInvariant
      ν₂).mp hν₂
  apply ProbabilityMeasure.toMeasure_injective
  exact
    HGAS.MeasureTheory.invariantProbability_unique_of_pretransitive
      (Measure.haar :
        Measure RealModularFrameᵐᵒᵖ)
      (ν₁ : Measure GammaTwoFrameQuotient)
      (ν₂ : Measure GammaTwoFrameQuotient)

/-- The formerly isolated uniqueness proposition is now a theorem. -/
theorem gammaTwoRightInvariantProbabilityUnique :
    GammaTwoRightInvariantProbabilityUnique :=
  gammaTwoRightInvariantProbability_unique

/-- The opaque chosen Haar probability and the explicit normalized
fundamental-domain probability are equal. -/
theorem gammaTwoChosenHaarIdentification :
    GammaTwoChosenHaarIdentification :=
  GammaTwoRightInvariantProbabilityUnique.chosenHaarIdentification
    gammaTwoRightInvariantProbabilityUnique

@[simp]
theorem gammaTwoFrameHaarProbability_eq_explicit :
    gammaTwoFrameHaarProbability =
      gammaTwoExplicitFrameHaarProbability :=
  gammaTwoChosenHaarIdentification

/-! ## Unconditional cusp consequences -/

/-- The legacy chosen Haar probability has the explicit positive cusp
marginal, with no remaining identification hypothesis. -/
theorem
    exists_gammaTwoFrameHaarProbability_cuspMarginal_unconditional
    (Y : ℝ) (hY : 1 < Y) :
    ∃ c : ℝ≥0, c ≠ 0 ∧
      c • HGAS.Dynamics.cuspHeightMeasure Y ≤
        Measure.map
          (gammaTwoExplicitCuspHeight Y)
          (gammaTwoFrameHaarProbability :
            Measure GammaTwoFrameQuotient) :=
  exists_gammaTwoFrameHaarProbability_cuspMarginal
    gammaTwoChosenHaarIdentification Y hY

/-- The reciprocal-slowdown divergence theorem for the legacy chosen
Γ(2) Haar probability is unconditional. -/
theorem gammaTwoHaar_reciprocalSlowdown_lintegral_eq_top
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X)
    (proj : X → GammaTwoFrameQuotient)
    (hproj : Measurable proj)
    (reciprocalSlowdown : X → ℝ≥0∞)
    (Y : ℝ) (hY : 1 < Y)
    (Ychart : ℝ)
    (M : ℕ) (hM : 2 ≤ M)
    (hmarginal :
      Measure.map proj μ =
        (gammaTwoFrameHaarProbability :
          Measure GammaTwoFrameQuotient))
    (κ : ℝ≥0) (hκ : κ ≠ 0)
    (hchart :
      ∀ᵐ x ∂μ,
        (κ : ℝ≥0∞) ^ M *
            HGAS.Dynamics.cuspTailHeightPower
              Ychart M
              (gammaTwoExplicitCuspHeight
                Y (proj x)) ≤
          reciprocalSlowdown x) :
    ∫⁻ x, reciprocalSlowdown x ∂μ = ∞ :=
  chosenGammaTwoHaar_reciprocalSlowdown_lintegral_eq_top
    gammaTwoChosenHaarIdentification
    μ proj hproj reciprocalSlowdown
    Y hY Ychart M hM hmarginal
    κ hκ hchart

end

end HGAS.Modular
