import HGAS.Modular.GammaTwoHaarProbabilityUnique
import Mathlib.Tactic

/-!
# Orientation reversal on the level-two frame quotient

Conjugating a real or integral determinant-one matrix by
`diag(1, -1)` changes the signs of its off-diagonal entries:

```text
        ( a  b )             ( a  -b )
        ( c  d )    ↦        ( -c  d ).
```

Although `diag(1, -1)` itself has determinant `-1`, its conjugation
preserves `SL(2)`.  It also preserves the principal congruence subgroup
`Γ(2)`: changing signs does not alter either a diagonal congruence to
one or an off-diagonal congruence to zero.  It therefore descends to a
homeomorphic involution of `Γ(2) \ SL(2, ℝ)`.

The important dynamical identity is

```text
        reverse (q · u(t)) = reverse(q) · u(-t).
```

Thus the involution exchanges the two orientations of the horocycle
flow.  The construction is kept separate from equidistribution so it
can be reused anywhere a signed horocycle parameter occurs.
-/

namespace HGAS.Modular

open Matrix _root_.MeasureTheory Topology
open scoped MatrixGroups CongruenceSubgroup

noncomputable section

/-! ## The matrix involution over `ℝ` -/

/-- Change the signs of the off-diagonal entries of a real modular
frame.  This is conjugation by `diag(1, -1)`. -/
def reverseRealModularFrame
    (g : RealModularFrame) : RealModularFrame :=
  ⟨!![g 0 0, -g 0 1; -g 1 0, g 1 1], by
    simpa only [Matrix.det_fin_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, mul_neg, neg_mul, neg_neg]
      using g.property⟩

@[simp]
theorem reverseRealModularFrame_coe
    (g : RealModularFrame) :
    (reverseRealModularFrame g :
        Matrix (Fin 2) (Fin 2) ℝ) =
      !![g 0 0, -g 0 1; -g 1 0, g 1 1] :=
  rfl

@[simp]
theorem reverseRealModularFrame_apply_zero_zero
    (g : RealModularFrame) :
    reverseRealModularFrame g 0 0 = g 0 0 :=
  rfl

@[simp]
theorem reverseRealModularFrame_apply_zero_one
    (g : RealModularFrame) :
    reverseRealModularFrame g 0 1 = -g 0 1 :=
  rfl

@[simp]
theorem reverseRealModularFrame_apply_one_zero
    (g : RealModularFrame) :
    reverseRealModularFrame g 1 0 = -g 1 0 :=
  rfl

@[simp]
theorem reverseRealModularFrame_apply_one_one
    (g : RealModularFrame) :
    reverseRealModularFrame g 1 1 = g 1 1 :=
  rfl

@[simp]
theorem reverseRealModularFrame_involutive
    (g : RealModularFrame) :
    reverseRealModularFrame (reverseRealModularFrame g) = g := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp

@[simp]
theorem reverseRealModularFrame_one :
    reverseRealModularFrame (1 : RealModularFrame) = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [reverseRealModularFrame]

@[simp]
theorem reverseRealModularFrame_mul
    (g h : RealModularFrame) :
    reverseRealModularFrame (g * h) =
      reverseRealModularFrame g *
        reverseRealModularFrame h := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [reverseRealModularFrame,
      Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Orientation reversal as a multiplicative equivalence of
`SL(2, ℝ)`. -/
def reverseRealModularFrameMulEquiv :
    RealModularFrame ≃* RealModularFrame where
  toFun := reverseRealModularFrame
  invFun := reverseRealModularFrame
  left_inv := reverseRealModularFrame_involutive
  right_inv := reverseRealModularFrame_involutive
  map_mul' := reverseRealModularFrame_mul

/-- Orientation reversal is continuous on real frames. -/
theorem reverseRealModularFrame_continuous :
    Continuous reverseRealModularFrame := by
  apply continuous_induced_rng.mpr
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Function.comp_apply,
      reverseRealModularFrame_coe, Matrix.of_apply] <;> fun_prop

/-- Orientation reversal as a homeomorphism of real modular frames. -/
def reverseRealModularFrameHomeomorph :
    RealModularFrame ≃ₜ RealModularFrame where
  toEquiv := reverseRealModularFrameMulEquiv.toEquiv
  continuous_toFun := reverseRealModularFrame_continuous
  continuous_invFun := reverseRealModularFrame_continuous

/-! ## Compatibility with the integral deck group -/

/-- The same off-diagonal sign change on integral determinant-one
matrices. -/
def reverseIntegralModularFrame
    (g : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![g 0 0, -g 0 1; -g 1 0, g 1 1], by
    simpa only [Matrix.det_fin_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, mul_neg, neg_mul, neg_neg]
      using g.property⟩

@[simp]
theorem reverseIntegralModularFrame_involutive
    (g : SL(2, ℤ)) :
    reverseIntegralModularFrame
        (reverseIntegralModularFrame g) = g := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [reverseIntegralModularFrame]

@[simp]
theorem reverseIntegralModularFrame_mul
    (g h : SL(2, ℤ)) :
    reverseIntegralModularFrame (g * h) =
      reverseIntegralModularFrame g *
        reverseIntegralModularFrame h := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [reverseIntegralModularFrame,
      Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The sign change preserves the level-two congruence conditions. -/
theorem reverseIntegralModularFrame_mem_gammaTwo
    (g : SL(2, ℤ)) (hg : g ∈ GammaTwo) :
    reverseIntegralModularFrame g ∈ GammaTwo := by
  rw [CongruenceSubgroup.Gamma_mem] at hg ⊢
  rcases hg with ⟨h00, h01, h10, h11⟩
  refine ⟨h00, ?_, ?_, h11⟩
  · simp [reverseIntegralModularFrame, h01]
  · simp [reverseIntegralModularFrame, h10]

/-- Orientation reversal as an automorphism of the deck group
`Γ(2)`. -/
def reverseGammaTwo (γ : GammaTwo) : GammaTwo :=
  ⟨reverseIntegralModularFrame γ.1,
    reverseIntegralModularFrame_mem_gammaTwo γ.1 γ.2⟩

@[simp]
theorem reverseGammaTwo_involutive
    (γ : GammaTwo) :
    reverseGammaTwo (reverseGammaTwo γ) = γ := by
  apply Subtype.ext
  exact reverseIntegralModularFrame_involutive γ.1

@[simp]
theorem reverseGammaTwo_mul
    (γ δ : GammaTwo) :
    reverseGammaTwo (γ * δ) =
      reverseGammaTwo γ * reverseGammaTwo δ := by
  apply Subtype.ext
  exact reverseIntegralModularFrame_mul γ.1 δ.1

/-- Real casting commutes with orientation reversal. -/
theorem gammaTwoToRealFrame_reverseGammaTwo
    (γ : GammaTwo) :
    gammaTwoToRealFrame (reverseGammaTwo γ) =
      reverseRealModularFrame (gammaTwoToRealFrame γ) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [reverseGammaTwo, reverseIntegralModularFrame,
      reverseRealModularFrame, gammaTwoToRealFrame,
      Matrix.SpecialLinearGroup.map]

/-! ## The descended quotient involution -/

/-- Orientation reversal on the level-two frame quotient. -/
def gammaTwoFrameOrientationReversal :
    GammaTwoFrameQuotient → GammaTwoFrameQuotient :=
  Quotient.lift
    (fun g ↦ gammaTwoFrameQuotientMk
      (reverseRealModularFrame g))
    (by
      intro g h hgh
      change g ∈ MulAction.orbit GammaTwo h at hgh
      obtain ⟨γ, rfl⟩ := hgh
      apply Quotient.sound
      refine ⟨reverseGammaTwo γ, ?_⟩
      simp only [gammaTwo_smul_realFrame,
        reverseRealModularFrame_mul,
        gammaTwoToRealFrame_reverseGammaTwo])

@[simp]
theorem gammaTwoFrameOrientationReversal_mk
    (g : RealModularFrame) :
    gammaTwoFrameOrientationReversal
        (gammaTwoFrameQuotientMk g) =
      gammaTwoFrameQuotientMk
        (reverseRealModularFrame g) :=
  rfl

@[simp]
theorem gammaTwoFrameOrientationReversal_involutive
    (q : GammaTwoFrameQuotient) :
    gammaTwoFrameOrientationReversal
        (gammaTwoFrameOrientationReversal q) = q := by
  induction q using Quotient.inductionOn with
  | _ g =>
      change
        gammaTwoFrameQuotientMk
            (reverseRealModularFrame
              (reverseRealModularFrame g)) =
          gammaTwoFrameQuotientMk g
      rw [reverseRealModularFrame_involutive]

/-- The quotient orientation reversal is continuous. -/
theorem gammaTwoFrameOrientationReversal_continuous :
    Continuous gammaTwoFrameOrientationReversal := by
  apply Continuous.quotient_lift
  exact
    gammaTwoFrameQuotientMk_isCoveringMap.continuous.comp
      reverseRealModularFrame_continuous

/-- Orientation reversal as a homeomorphism of the frame quotient. -/
def gammaTwoFrameOrientationReversalHomeomorph :
    GammaTwoFrameQuotient ≃ₜ GammaTwoFrameQuotient where
  toFun := gammaTwoFrameOrientationReversal
  invFun := gammaTwoFrameOrientationReversal
  left_inv := gammaTwoFrameOrientationReversal_involutive
  right_inv := gammaTwoFrameOrientationReversal_involutive
  continuous_toFun :=
    gammaTwoFrameOrientationReversal_continuous
  continuous_invFun :=
    gammaTwoFrameOrientationReversal_continuous

/-- Orientation reversal intertwines right translations with the
reversed translating frame. -/
theorem gammaTwoFrameOrientationReversal_rightMul
    (a : RealModularFrame) (q : GammaTwoFrameQuotient) :
    gammaTwoFrameOrientationReversal
        (gammaTwoFrameRightMul a q) =
      gammaTwoFrameRightMul
        (reverseRealModularFrame a)
        (gammaTwoFrameOrientationReversal q) := by
  induction q using Quotient.inductionOn with
  | _ g =>
      change
        gammaTwoFrameQuotientMk
            (reverseRealModularFrame (g * a)) =
          gammaTwoFrameQuotientMk
            (reverseRealModularFrame g *
              reverseRealModularFrame a)
      rw [reverseRealModularFrame_mul]

@[simp]
theorem reverseRealModularFrame_upperUnipotent
    (t : ℝ) :
    reverseRealModularFrame (upperUnipotent t) =
      upperUnipotent (-t) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [reverseRealModularFrame, upperUnipotent]

/-- Orientation reversal exchanges forward and backward unit-speed
horocycle motion. -/
theorem gammaTwoFrameOrientationReversal_horocycleFlow
    (t : ℝ) (q : GammaTwoFrameQuotient) :
    gammaTwoFrameOrientationReversal
        (gammaTwoHorocycleFlow t q) =
      gammaTwoHorocycleFlow (-t)
        (gammaTwoFrameOrientationReversal q) := by
  rw [gammaTwoHorocycleFlow_eq_rightMul,
    gammaTwoFrameOrientationReversal_rightMul,
    reverseRealModularFrame_upperUnipotent]
  rfl

/-- More generally, orientation reversal changes the sign of every
constant horocycle scale. -/
theorem gammaTwoFrameOrientationReversal_scaledHorocycleFlow
    (s t : ℝ) (q : GammaTwoFrameQuotient) :
    gammaTwoFrameOrientationReversal
        (scaledGammaTwoHorocycleFlow s t q) =
      scaledGammaTwoHorocycleFlow (-s) t
        (gammaTwoFrameOrientationReversal q) := by
  change
    gammaTwoFrameOrientationReversal
        (gammaTwoHorocycleFlow (s * t) q) =
      gammaTwoHorocycleFlow ((-s) * t)
        (gammaTwoFrameOrientationReversal q)
  rw [gammaTwoFrameOrientationReversal_horocycleFlow]
  congr 2
  ring

/-! ## Preservation of normalized frame Haar probability -/

/-- Pushing a right-invariant frame probability through orientation
reversal again gives a right-invariant frame probability. -/
theorem IsRightInvariantFrameProbability.orientationReversal_map
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν) :
    IsRightInvariantFrameProbability
      (ν.map
        gammaTwoFrameOrientationReversal_continuous.measurable.aemeasurable) := by
  intro a
  apply ProbabilityMeasure.toMeasure_injective
  change
    Measure.map (gammaTwoFrameRightMul a)
        (Measure.map gammaTwoFrameOrientationReversal
          (ν : Measure GammaTwoFrameQuotient)) =
      Measure.map gammaTwoFrameOrientationReversal
        (ν : Measure GammaTwoFrameQuotient)
  rw [Measure.map_map
    (gammaTwoFrameRightMul_continuous a).measurable
    gammaTwoFrameOrientationReversal_continuous.measurable]
  have hintertwine :
      gammaTwoFrameRightMul a ∘
          gammaTwoFrameOrientationReversal =
        gammaTwoFrameOrientationReversal ∘
          gammaTwoFrameRightMul
            (reverseRealModularFrame a) := by
    funext q
    rw [Function.comp_apply, Function.comp_apply,
      gammaTwoFrameOrientationReversal_rightMul,
      reverseRealModularFrame_involutive]
  rw [hintertwine]
  rw [← Measure.map_map
    gammaTwoFrameOrientationReversal_continuous.measurable
    (gammaTwoFrameRightMul_continuous
      (reverseRealModularFrame a)).measurable]
  have hright :=
    congrArg ProbabilityMeasure.toMeasure
      (hν (reverseRealModularFrame a))
  exact congrArg
    (Measure.map gammaTwoFrameOrientationReversal)
    hright

/-- Every right-invariant frame probability is fixed by the orientation
reversal involution.  This follows from right-invariance of its
pushforward and uniqueness of normalized frame Haar probability. -/
theorem IsRightInvariantFrameProbability.orientationReversal_map_eq
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν) :
    ν.map
        gammaTwoFrameOrientationReversal_continuous.measurable.aemeasurable =
      ν := by
  exact
    gammaTwoRightInvariantProbability_unique _ _
      hν.orientationReversal_map hν

/-- Orientation reversal preserves every normalized frame Haar
probability. -/
def IsRightInvariantFrameProbability.measurePreservingOrientationReversal
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν) :
    MeasurePreserving gammaTwoFrameOrientationReversal
      (ν : Measure GammaTwoFrameQuotient)
      (ν : Measure GammaTwoFrameQuotient) where
  measurable :=
    gammaTwoFrameOrientationReversal_continuous.measurable
  map_eq :=
    congrArg ProbabilityMeasure.toMeasure
      hν.orientationReversal_map_eq

end

end HGAS.Modular
