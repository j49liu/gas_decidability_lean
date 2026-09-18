import HGAS.Modular.CanonicalLambdaQuotient
import HGAS.Dynamics.InvariantProbability
import Mathlib.Dynamics.Ergodic.Action.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
import Mathlib.Topology.Algebra.Group.DiscontinuousSubgroup
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.DiscreteSubset
import Mathlib.Tactic

/-!
# The level-two modular frame quotient and its horocycle flow

The upper-half-plane quotient in `CanonicalLambdaQuotient` remembers only
the base point of a modular frame.  Horocycle dynamics naturally lives on
the full frame bundle

```
  Γ(2) \ SL(2, ℝ).
```

This file constructs that quotient directly as an orbit quotient for left
multiplication.  Right multiplication commutes with the deck action, so
the upper-unipotent one-parameter subgroup descends to a continuous real
flow.

There is no ergodic theorem in this file.  In particular, no use is made of
Dani--Smillie, Ratner theory, reduction theory, or a Haar-volume formula.
The construction below is elementary topology and matrix algebra and is
intended to be reusable independently of the GAS reduction.
-/

namespace HGAS.Modular

open Filter Function Matrix MeasureTheory Set Topology
open scoped MatrixGroups CongruenceSubgroup

noncomputable section

/-- The ambient real frame group. -/
abbrev RealModularFrame := SL(2, ℝ)

/-!
Mathlib gives `SL(2, ℝ)` its induced topology as a closed subspace of the
matrix space, but it intentionally does not install all inherited
countability and local-compactness instances.  We record the two instances
needed for quotient topology and measure theory.
-/

private instance realMatrixLocallyCompact :
    LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
  inferInstanceAs
    (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))

private instance realMatrixSecondCountable :
    SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
  inferInstanceAs
    (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))

instance realModularFrameLocallyCompact :
    LocallyCompactSpace RealModularFrame :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace

instance realModularFrameSecondCountable :
    SecondCountableTopology RealModularFrame :=
  Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding
    |>.secondCountableTopology

instance realModularFrameMeasurableSpace :
    MeasurableSpace RealModularFrame :=
  borel RealModularFrame

instance realModularFrameBorelSpace :
    BorelSpace RealModularFrame :=
  ⟨rfl⟩

/-- Integral level-two matrices embedded in `SL(2, ℝ)`. -/
def gammaTwoToRealFrame : GammaTwo →* RealModularFrame :=
  (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)).comp
    GammaTwo.subtype

@[simp]
theorem gammaTwoToRealFrame_apply
    (γ : GammaTwo) :
    gammaTwoToRealFrame γ =
      Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ.1 :=
  rfl

/-- The integral embedding is injective, including after restriction to
`Γ(2)`. -/
theorem gammaTwoToRealFrame_injective :
    Function.Injective gammaTwoToRealFrame := by
  intro γ δ h
  apply Subtype.ext
  exact Matrix.SpecialLinearGroup.map_intCast_inj.mp h

/-- The restricted integral embedding is closed.  This is the effective
properness input behind discontinuity of the deck action. -/
theorem gammaTwoToRealFrame_isClosedEmbedding :
    IsClosedEmbedding gammaTwoToRealFrame := by
  have hsub :
      IsClosedEmbedding (GammaTwo.subtype : GammaTwo → SL(2, ℤ)) := by
    exact
      (isClosed_discrete (GammaTwo : Set SL(2, ℤ)))
        |>.isClosedEmbedding_subtypeVal
  have hcast :
      IsClosedEmbedding
        (Matrix.SpecialLinearGroup.map
          (Int.castRingHom ℝ) :
          SL(2, ℤ) → SL(2, ℝ)) :=
    by
      have h :
          IsClosedEmbedding (Int.castRingHom ℝ : ℤ → ℝ) := by
        simpa only [Int.coe_castRingHom] using
          Real.isClosedEmbedding_intCast
      exact h.specialLinearGroup_map
  exact hcast.comp hsub

/-- `Γ(2)` acts on real frames by left multiplication. -/
instance gammaTwoMulActionRealFrame :
    MulAction GammaTwo RealModularFrame :=
  MulAction.compHom RealModularFrame gammaTwoToRealFrame

@[simp]
theorem gammaTwo_smul_realFrame
    (γ : GammaTwo) (g : RealModularFrame) :
    γ • g = gammaTwoToRealFrame γ * g :=
  rfl

instance gammaTwoContinuousConstSMulRealFrame :
    ContinuousConstSMul GammaTwo RealModularFrame where
  continuous_const_smul γ := by
    simpa only [gammaTwo_smul_realFrame] using
      continuous_const_mul (gammaTwoToRealFrame γ)

/-- The left deck action is properly discontinuous.

The proof is worth keeping explicit.  If
`γ K ∩ L ≠ ∅`, then the embedded matrix `γ` belongs to the compact set
`L K⁻¹`.  Closedness of the integral embedding makes the preimage of that
compact set finite because `Γ(2)` is discrete. -/
instance gammaTwoProperlyDiscontinuousRealFrame :
    ProperlyDiscontinuousSMul GammaTwo RealModularFrame where
  finite_disjoint_inter_image {K L} hK hL := by
    let compactDifference : Set RealModularFrame :=
      (fun p : RealModularFrame × RealModularFrame ↦
        p.1 * p.2⁻¹) '' (L ×ˢ K)
    have hcompactDifference : IsCompact compactDifference := by
      exact (hL.prod hK).image
        (continuous_fst.mul continuous_snd.inv)
    have hproper :
        Tendsto gammaTwoToRealFrame cofinite
          (cocompact RealModularFrame) :=
      tendsto_cofinite_cocompact_of_discrete
        gammaTwoToRealFrame_isClosedEmbedding.tendsto_cocompact
    have hfinite :
        (gammaTwoToRealFrame ⁻¹' compactDifference).Finite :=
      tendsto_cofinite_cocompact_iff.mp hproper
        compactDifference hcompactDifference
    refine hfinite.subset ?_
    intro γ hγ
    rcases hγ with ⟨y, ⟨x, hxK, hγx⟩, hyL⟩
    change gammaTwoToRealFrame γ ∈ compactDifference
    refine ⟨(y, x), ⟨hyL, hxK⟩, ?_⟩
    rw [← hγx]
    simp only [gammaTwo_smul_realFrame]
    group

/-- Left multiplication on frames is free. -/
theorem gammaTwo_eq_one_of_smul_realFrame_eq
    (γ : GammaTwo) (g : RealModularFrame)
    (h : γ • g = g) :
    γ = 1 := by
  apply gammaTwoToRealFrame_injective
  apply mul_right_cancel (b := g)
  simpa only [gammaTwo_smul_realFrame, map_one, one_mul] using h

instance gammaTwoCancelSMulRealFrame :
    IsCancelSMul GammaTwo RealModularFrame :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr
    gammaTwo_eq_one_of_smul_realFrame_eq

/-- The level-two modular frame quotient `Γ(2) \ SL(2, ℝ)`. -/
abbrev GammaTwoFrameQuotient :=
  Quotient (MulAction.orbitRel GammaTwo RealModularFrame)

/-- Quotient projection from frames. -/
def gammaTwoFrameQuotientMk :
    RealModularFrame → GammaTwoFrameQuotient :=
  Quotient.mk _

/-- The frame projection is an open quotient map. -/
theorem gammaTwoFrameQuotientMk_isOpenQuotientMap :
    IsOpenQuotientMap gammaTwoFrameQuotientMk :=
  MulAction.isOpenQuotientMap_quotientMk

/-- The frame projection is a quotient covering map with deck group
`Γ(2)`. -/
theorem gammaTwoFrameQuotientMk_isQuotientCoveringMap :
    IsQuotientCoveringMap gammaTwoFrameQuotientMk GammaTwo :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- In particular the frame projection is a covering map. -/
theorem gammaTwoFrameQuotientMk_isCoveringMap :
    IsCoveringMap gammaTwoFrameQuotientMk :=
  gammaTwoFrameQuotientMk_isQuotientCoveringMap.isCoveringMap

instance gammaTwoFrameQuotientT2 :
    T2Space GammaTwoFrameQuotient :=
  inferInstance

instance gammaTwoFrameQuotientSecondCountable :
    SecondCountableTopology GammaTwoFrameQuotient :=
  ContinuousConstSMul.secondCountableTopology

instance gammaTwoFrameQuotientLocallyCompact :
    LocallyCompactSpace GammaTwoFrameQuotient :=
  gammaTwoFrameQuotientMk_isOpenQuotientMap.locallyCompactSpace

instance gammaTwoFrameQuotientMeasurableSpace :
    MeasurableSpace GammaTwoFrameQuotient :=
  borel GammaTwoFrameQuotient

instance gammaTwoFrameQuotientBorelSpace :
    BorelSpace GammaTwoFrameQuotient :=
  ⟨rfl⟩

/-- Right multiplication on representatives descends through the left
`Γ(2)` quotient. -/
def gammaTwoFrameRightMul
    (a : RealModularFrame) :
    GammaTwoFrameQuotient → GammaTwoFrameQuotient :=
  Quotient.lift
    (fun g ↦ gammaTwoFrameQuotientMk (g * a))
    (by
      intro g h hgh
      change g ∈ MulAction.orbit GammaTwo h at hgh
      obtain ⟨γ, rfl⟩ := hgh
      apply Quotient.sound
      exact ⟨γ, by
        simp only [gammaTwo_smul_realFrame, mul_assoc]⟩)

@[simp]
theorem gammaTwoFrameRightMul_mk
    (a g : RealModularFrame) :
    gammaTwoFrameRightMul a (gammaTwoFrameQuotientMk g) =
      gammaTwoFrameQuotientMk (g * a) :=
  rfl

/-- Right multiplication on the frame quotient is continuous. -/
theorem gammaTwoFrameRightMul_continuous
    (a : RealModularFrame) :
    Continuous (gammaTwoFrameRightMul a) := by
  apply Continuous.quotient_lift
  exact
    gammaTwoFrameQuotientMk_isCoveringMap.continuous.comp
      (continuous_mul_const a)

/-- Right multiplication respects products. -/
theorem gammaTwoFrameRightMul_mul
    (a b : RealModularFrame) :
    gammaTwoFrameRightMul (a * b) =
      gammaTwoFrameRightMul b ∘
        gammaTwoFrameRightMul a := by
  funext q
  induction q using Quotient.inductionOn with
  | _ g =>
      change
        gammaTwoFrameQuotientMk (g * (a * b)) =
          gammaTwoFrameQuotientMk ((g * a) * b)
      rw [mul_assoc]

@[simp]
theorem gammaTwoFrameRightMul_one :
    gammaTwoFrameRightMul (1 : RealModularFrame) = id := by
  funext q
  induction q using Quotient.inductionOn with
  | _ g =>
      change gammaTwoFrameQuotientMk (g * 1) =
        gammaTwoFrameQuotientMk g
      rw [mul_one]

/-- The upper-unipotent matrix

```
  u(t) = [1 t; 0 1].
```
-/
def upperUnipotent (t : ℝ) : RealModularFrame :=
  ⟨!![1, t; 0, 1], by
    simp [Matrix.det_fin_two]⟩

@[simp]
theorem upperUnipotent_coe (t : ℝ) :
    (upperUnipotent t : Matrix (Fin 2) (Fin 2) ℝ) =
      !![1, t; 0, 1] :=
  rfl

@[simp]
theorem upperUnipotent_zero :
    upperUnipotent 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent]

@[simp]
theorem upperUnipotent_add (s t : ℝ) :
    upperUnipotent (s + t) =
      upperUnipotent s * upperUnipotent t := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperUnipotent, Matrix.SpecialLinearGroup.coe_mul,
      add_comm]

/-- The upper-unipotent one-parameter subgroup is continuous. -/
theorem upperUnipotent_continuous :
    Continuous upperUnipotent := by
  apply continuous_induced_rng.mpr
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one,
      Function.comp_apply, upperUnipotent_coe, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
    fun_prop

/-- Joint right-unipotent action on quotient frames. -/
def gammaTwoHorocycleAction :
    ℝ × GammaTwoFrameQuotient →
      GammaTwoFrameQuotient :=
  fun p ↦ gammaTwoFrameRightMul (upperUnipotent p.1) p.2

@[simp]
theorem gammaTwoHorocycleAction_mk
    (t : ℝ) (g : RealModularFrame) :
    gammaTwoHorocycleAction
        (t, gammaTwoFrameQuotientMk g) =
      gammaTwoFrameQuotientMk
        (g * upperUnipotent t) :=
  rfl

/-- The descended horocycle action is jointly continuous. -/
theorem gammaTwoHorocycleAction_continuous :
    Continuous gammaTwoHorocycleAction := by
  let sourceQuotient :
      ℝ × RealModularFrame →
        ℝ × GammaTwoFrameQuotient :=
    fun p ↦ (p.1, gammaTwoFrameQuotientMk p.2)
  have hsource :
      IsOpenQuotientMap sourceQuotient := by
    simpa only [sourceQuotient] using
      (IsOpenQuotientMap.id.prodMap
        gammaTwoFrameQuotientMk_isOpenQuotientMap)
  apply hsource.isQuotientMap.continuous_iff.mpr
  change Continuous
    (fun p : ℝ × RealModularFrame ↦
      gammaTwoFrameQuotientMk
        (p.2 * upperUnipotent p.1))
  exact gammaTwoFrameQuotientMk_isCoveringMap.continuous.comp
    (continuous_snd.mul
      (upperUnipotent_continuous.comp continuous_fst))

/-- The continuous horocycle flow on `Γ(2) \ SL(2, ℝ)`. -/
def gammaTwoHorocycleFlow :
    Flow ℝ GammaTwoFrameQuotient where
  toFun t q := gammaTwoHorocycleAction (t, q)
  cont' := by
    simpa only [Function.uncurry_apply_pair] using
      gammaTwoHorocycleAction_continuous
  map_add' := by
    intro s t q
    induction q using Quotient.inductionOn with
    | _ g =>
        change
          gammaTwoFrameQuotientMk
              (g * upperUnipotent (s + t)) =
            gammaTwoFrameQuotientMk
              ((g * upperUnipotent t) *
                upperUnipotent s)
        rw [upperUnipotent_add]
        congr 1
        rw [mul_assoc]
        congr 1
        rw [← upperUnipotent_add,
          ← upperUnipotent_add, add_comm]
  map_zero' := by
    intro q
    induction q using Quotient.inductionOn with
    | _ g =>
        change
          gammaTwoFrameQuotientMk
              (g * upperUnipotent 0) =
            gammaTwoFrameQuotientMk g
        rw [upperUnipotent_zero, mul_one]

@[simp]
theorem gammaTwoHorocycleFlow_mk
    (t : ℝ) (g : RealModularFrame) :
    gammaTwoHorocycleFlow t
        (gammaTwoFrameQuotientMk g) =
      gammaTwoFrameQuotientMk
        (g * upperUnipotent t) :=
  rfl

@[simp]
theorem gammaTwoHorocycleFlow_eq_rightMul
    (t : ℝ) :
    gammaTwoHorocycleFlow t =
      gammaTwoFrameRightMul (upperUnipotent t) :=
  rfl

/-- Rescaling time by a real factor gives the fixed-scale horocycle flow
used by the modular source block. -/
def scaledGammaTwoHorocycleFlow (s : ℝ) :
    Flow ℝ GammaTwoFrameQuotient where
  toFun t q := gammaTwoHorocycleFlow (s * t) q
  cont' := gammaTwoHorocycleFlow.continuous
    (continuous_const.mul continuous_fst) continuous_snd
  map_add' := by
    intro t u q
    rw [mul_add, gammaTwoHorocycleFlow.map_add]
  map_zero' := by
    intro q
    simp only [mul_zero, gammaTwoHorocycleFlow.map_zero_apply]

@[simp]
theorem scaledGammaTwoHorocycleFlow_apply
    (s t : ℝ) (q : GammaTwoFrameQuotient) :
    scaledGammaTwoHorocycleFlow s t q =
      gammaTwoHorocycleFlow (s * t) q :=
  rfl

@[simp]
theorem scaledGammaTwoHorocycleFlow_one :
    scaledGammaTwoHorocycleFlow 1 =
      gammaTwoHorocycleFlow := by
  apply Flow.ext
  intro t q
  simp only [scaledGammaTwoHorocycleFlow_apply, one_mul]

/-! ## Projection to the modular surface -/

/-- The base point in the upper half-plane of a real modular frame. -/
def realModularFrameBasePoint
    (g : RealModularFrame) : UpperHalfPlane :=
  g • UpperHalfPlane.I

/-- Taking the base point of a frame is continuous. -/
theorem realModularFrameBasePoint_continuous :
    Continuous realModularFrameBasePoint := by
  unfold realModularFrameBasePoint
  exact continuous_smul.comp
    (continuous_id.prodMk continuous_const)

/-- Casting an integral special-linear matrix to the reals does not change
its Möbius action. -/
theorem gammaTwoToRealFrame_smul
    (γ : GammaTwo) (z : UpperHalfPlane) :
    gammaTwoToRealFrame γ • z = γ.1 • z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply,
    UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [
    gammaTwoToRealFrame,
    Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Int.coe_castRingHom]

/-- Forgetting the tangent direction gives the base modular-surface
quotient. -/
def gammaTwoFrameBaseProjection :
    GammaTwoFrameQuotient → LambdaModularQuotient :=
  Quotient.lift
    (fun g ↦
      lambdaModularQuotientMk
        (realModularFrameBasePoint g))
    (by
      intro g h hgh
      change g ∈ MulAction.orbit GammaTwo h at hgh
      obtain ⟨γ, rfl⟩ := hgh
      simpa only [gammaTwo_smul_realFrame,
        realModularFrameBasePoint, mul_smul,
        gammaTwoToRealFrame_smul] using
          (lambdaModularQuotientMk_smul_of_mem_Gamma_two
            γ.property (h • UpperHalfPlane.I)))

@[simp]
theorem gammaTwoFrameBaseProjection_mk
    (g : RealModularFrame) :
    gammaTwoFrameBaseProjection
        (gammaTwoFrameQuotientMk g) =
      lambdaModularQuotientMk
        (realModularFrameBasePoint g) :=
  rfl

/-- The frame-to-surface projection is continuous. -/
theorem gammaTwoFrameBaseProjection_continuous :
    Continuous gammaTwoFrameBaseProjection := by
  apply Continuous.quotient_lift
  exact
    lambdaModularQuotientMk_isCoveringMap.continuous.comp
      realModularFrameBasePoint_continuous

end

end HGAS.Modular
