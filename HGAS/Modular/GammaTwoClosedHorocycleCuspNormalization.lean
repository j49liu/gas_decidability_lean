import HGAS.Modular.CanonicalLambdaGammaTwo
import HGAS.Modular.GammaTwoPeriodicPrimitiveRow
import HGAS.Modular.HorizontalTrajectory
import Mathlib.Tactic

/-!
# Cusp normalization of a closed level-two horocycle

A periodic `Γ(2)` horocycle supplies a primitive integral row `v` whose
first moving lattice coordinate vanishes.  This file completes that row
to an integral special-linear matrix `A` and keeps the completion data
visible.

If the second row of `A` is `v`, then `A g` is upper triangular:

```text
                    A g = [a  b; 0  a⁻¹].
```

Consequently

```text
  base (A · (g u(t))) = a b + a² t + i a²,
```

an exactly parametrized horizontal line of nonzero speed `a²`.  A scaled
right orbit `u(σt)` has speed `a²σ`.

The integral completion need not lie in `Γ(2)`.  Its reduction modulo two
is the finite six-valued characteristic label relevant to theta
transformation laws.  We decompose the completion as a `Γ(2)` element
times the fixed lift of this label.  We also expose the coarser
three-valued cusp label determined by the second row modulo two.
-/

namespace HGAS.Modular

open Matrix Set
open scoped MatrixGroups CongruenceSubgroup

noncomputable section

/-- Upper-triangular determinant-one frame used after completing a
horizontal primitive row. -/
def upperTriangularFrame
    (a b : ℝ) (ha : a ≠ 0) : RealModularFrame :=
  ⟨!![a, b; 0, a⁻¹], by
    simp [Matrix.det_fin_two, ha]⟩

@[simp]
theorem upperTriangularFrame_coe
    (a b : ℝ) (ha : a ≠ 0) :
    (upperTriangularFrame a b ha :
      Matrix (Fin 2) (Fin 2) ℝ) =
        !![a, b; 0, a⁻¹] :=
  rfl

/-- Exact horizontal base path of an upper-triangular frame under right
upper-unipotent translation. -/
theorem upperTriangularFrame_basePoint_upperUnipotent
    (a b : ℝ) (ha : a ≠ 0) (t : ℝ) :
    realModularFrameBasePoint
        (upperTriangularFrame a b ha * upperUnipotent t) =
      horizontalLine
        (a * b) (a ^ 2) (a ^ 2)
        (sq_pos_of_ne_zero ha) t := by
  apply UpperHalfPlane.coe_injective
  simp only [realModularFrameBasePoint]
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  apply Complex.ext
  · simp [upperTriangularFrame,
      upperUnipotent, horizontalLine,
      Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two]
    field_simp [ha]
    ring
  · simp [upperTriangularFrame,
      upperUnipotent, horizontalLine,
      Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two]
    field_simp [ha]

/-- Scaled version: right translation by `u(σt)` has exact horizontal
speed `a²σ`. -/
theorem upperTriangularFrame_basePoint_scaledUpperUnipotent
    (a b σ : ℝ) (ha : a ≠ 0) (t : ℝ) :
    realModularFrameBasePoint
        (upperTriangularFrame a b ha *
          upperUnipotent (σ * t)) =
      horizontalLine
        (a * b) (a ^ 2) (a ^ 2 * σ)
        (sq_pos_of_ne_zero ha) t := by
  rw [upperTriangularFrame_basePoint_upperUnipotent]
  apply UpperHalfPlane.ext
  simp [horizontalLine]
  ring

/-- The completed row computes the lower-left entry of the transformed
frame. -/
theorem integralCompletion_lowerLeft_eq_rowMul
    (v : PrimitiveIntegralRow)
    (g : RealModularFrame)
    (A : IntegralModularGroup)
    (hA0 : A 1 0 = v.1 0)
    (hA1 : A 1 1 = v.1 1) :
    (A • g) 1 0 = primitiveIntegralRowMul v g 0 := by
  simp [integralModularGroup_smul_realFrame,
    integralToRealFrame, primitiveIntegralRowMul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, hA0, hA1,
    Fin.sum_univ_two]

/-- Data produced by completing one horizontal primitive row. -/
structure PrimitiveRowHorizontalization
    (v : PrimitiveIntegralRow)
    (g : RealModularFrame) where
  completion : IntegralModularGroup
  upperLeft : ℝ
  upperRight : ℝ
  upperLeft_ne_zero : upperLeft ≠ 0
  completion_row_zero :
    completion 1 0 = v.1 0
  completion_row_one :
    completion 1 1 = v.1 1
  completedFrame_eq :
    completion • g =
      upperTriangularFrame
        upperLeft upperRight upperLeft_ne_zero

namespace PrimitiveRowHorizontalization

/-- Exact horizontal path after applying the integral row completion. -/
theorem basePath_eq_horizontal
    {v : PrimitiveIntegralRow}
    {g : RealModularFrame}
    (h : PrimitiveRowHorizontalization v g)
    (t : ℝ) :
    realModularFrameBasePoint
        (h.completion • (g * upperUnipotent t)) =
      horizontalLine
        (h.upperLeft * h.upperRight)
        (h.upperLeft ^ 2)
        (h.upperLeft ^ 2)
        (sq_pos_of_ne_zero h.upperLeft_ne_zero) t := by
  have hframe :
      h.completion • (g * upperUnipotent t) =
        (h.completion • g) * upperUnipotent t := by
    simp only [integralModularGroup_smul_realFrame, mul_assoc]
  rw [hframe, h.completedFrame_eq]
  exact
    upperTriangularFrame_basePoint_upperUnipotent
      h.upperLeft h.upperRight h.upperLeft_ne_zero t

/-- Exact horizontal path for a nontrivially scaled closed horocycle. -/
theorem basePath_scaled_eq_horizontal
    {v : PrimitiveIntegralRow}
    {g : RealModularFrame}
    (h : PrimitiveRowHorizontalization v g)
    (σ : ℝ) (t : ℝ) :
    realModularFrameBasePoint
        (h.completion •
          (g * upperUnipotent (σ * t))) =
      horizontalLine
        (h.upperLeft * h.upperRight)
        (h.upperLeft ^ 2)
        (h.upperLeft ^ 2 * σ)
        (sq_pos_of_ne_zero h.upperLeft_ne_zero) t := by
  have hframe :
      h.completion • (g * upperUnipotent (σ * t)) =
        (h.completion • g) * upperUnipotent (σ * t) := by
    simp only [integralModularGroup_smul_realFrame, mul_assoc]
  rw [hframe, h.completedFrame_eq]
  exact
    upperTriangularFrame_basePoint_scaledUpperUnipotent
      h.upperLeft h.upperRight σ h.upperLeft_ne_zero t

/-- The horizontal speed in the scaled formula is nonzero whenever the
original horocycle speed is nonzero. -/
theorem scaledSpeed_ne_zero
    {v : PrimitiveIntegralRow}
    {g : RealModularFrame}
    (h : PrimitiveRowHorizontalization v g)
    {σ : ℝ} (hσ : σ ≠ 0) :
    h.upperLeft ^ 2 * σ ≠ 0 :=
  mul_ne_zero (pow_ne_zero 2 h.upperLeft_ne_zero) hσ

end PrimitiveRowHorizontalization

/-- Every primitive row with zero first moving coordinate admits an
integral completion which makes the frame exactly upper triangular. -/
theorem exists_primitiveRowHorizontalization
    (v : PrimitiveIntegralRow)
    (g : RealModularFrame)
    (hzero : primitiveIntegralRowMul v g 0 = 0) :
    Nonempty (PrimitiveRowHorizontalization v g) := by
  have hcoprime :
      IsCoprime (v.1 0) (v.1 1) :=
    (EisensteinSeries.mem_gammaSet_one v.1).mp v.2
  obtain ⟨A, hA0, hA1⟩ :=
    hcoprime.exists_SL2_row 1
  have hh10 : (A • g) 1 0 = 0 := by
    rw [integralCompletion_lowerLeft_eq_rowMul
      v g A hA0 hA1]
    exact hzero
  obtain ⟨a, b, ha, hab⟩ :=
    (A • g).fin_two_exists_eq_mk_of_apply_zero_one_eq_zero
      hh10
  exact
    ⟨{
      completion := A
      upperLeft := a
      upperRight := b
      upperLeft_ne_zero := ha
      completion_row_zero := hA0
      completion_row_one := hA1
      completedFrame_eq := by
        simpa only [upperTriangularFrame] using hab
    }⟩

/-- A periodic level-two horocycle therefore admits a primitive-row
horizontalization.  This theorem is the direct bridge from the intrinsic
closed-orbit statement to the explicit cusp chart. -/
theorem exists_primitiveRowHorizontalization_of_isPeriodicHorocyclePoint
    (g : RealModularFrame)
    (hperiodic :
      IsPeriodicHorocyclePoint 1
        (gammaTwoFrameQuotientMk g)) :
    ∃ v : PrimitiveIntegralRow,
      Nonempty (PrimitiveRowHorizontalization v g) := by
  obtain ⟨v, hv⟩ :=
    exists_primitiveRowMul_fst_eq_zero_of_isPeriodicHorocyclePoint
      g hperiodic
  exact
    ⟨v, exists_primitiveRowHorizontalization v g hv⟩

/-- The finite six-valued label governing the lambda/theta
transformation of an integral completion. -/
abbrev LevelTwoCharacteristicLabel :=
  SL(2, ZMod 2)

/-- Reduction of the chosen integral completion is its characteristic
label. -/
def integralCompletionCharacteristicLabel
    (A : IntegralModularGroup) :
    LevelTwoCharacteristicLabel :=
  reduceModTwo A

/-- The canonical integral representative of a finite characteristic
label. -/
def characteristicRepresentative
    (r : LevelTwoCharacteristicLabel) :
    IntegralModularGroup :=
  liftModTwo r

/-- The correction from the chosen completion to its canonical finite
representative. -/
def completionGammaTwoFactor
    (A : IntegralModularGroup) :
    IntegralModularGroup :=
  A *
    (characteristicRepresentative
      (integralCompletionCharacteristicLabel A))⁻¹

/-- The correction factor really belongs to `Γ(2)`. -/
theorem completionGammaTwoFactor_mem
    (A : IntegralModularGroup) :
    completionGammaTwoFactor A ∈ GammaTwo := by
  apply CongruenceSubgroup.Gamma_mem'.mpr
  change
    reduceModTwo (completionGammaTwoFactor A) = 1
  simp [completionGammaTwoFactor,
    characteristicRepresentative,
    integralCompletionCharacteristicLabel]

/-- Exact decomposition of an integral completion into a level-two deck
transformation and one of six fixed characteristic representatives. -/
theorem completion_eq_gammaTwoFactor_mul_representative
    (A : IntegralModularGroup) :
    A =
      completionGammaTwoFactor A *
        characteristicRepresentative
          (integralCompletionCharacteristicLabel A) := by
  simp [completionGammaTwoFactor,
    characteristicRepresentative,
    integralCompletionCharacteristicLabel]

/-- The three cusps of `Γ(2)`, identified by the nonzero second row
modulo two. -/
inductive GammaTwoCuspLabel
  | infinity
  | zero
  | one
  deriving DecidableEq, Fintype

/-- Coarse cusp label carried by a six-valued characteristic label. -/
def characteristicCuspLabel
    (r : LevelTwoCharacteristicLabel) :
    GammaTwoCuspLabel :=
  if r 1 0 = 0 then .infinity
  else if r 1 1 = 0 then .zero
  else .one

/-- Fixed integral representatives of the three level-two cusps. -/
def cuspRepresentative :
    GammaTwoCuspLabel → IntegralModularGroup
  | .infinity => 1
  | .zero => ModularGroup.S
  | .one => ModularGroup.S * ModularGroup.T

/-- The cusp representative has the same second row modulo two as the
full characteristic label. -/
theorem cuspRepresentative_secondRow
    (r : LevelTwoCharacteristicLabel) :
    ∀ j : Fin 2,
      reduceModTwo
          (cuspRepresentative
            (characteristicCuspLabel r)) 1 j =
        r 1 j := by
  rcases reduceModTwo_six_cases r with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

/-- A completion has two possible mod-two first rows above a fixed
nonzero second row.  Left multiplication by `T` exchanges them while
leaving the second row fixed.  This is the required parity correction. -/
def characteristicCuspAdjustment
    (r : LevelTwoCharacteristicLabel) :
    IntegralModularGroup :=
  if r =
      reduceModTwo
        (cuspRepresentative (characteristicCuspLabel r))
  then 1
  else ModularGroup.T

/-- The parity correction changes the full six-valued label to the
chosen representative of its three-valued cusp. -/
theorem reduce_characteristicCuspAdjustment_mul
    (r : LevelTwoCharacteristicLabel) :
    reduceModTwo (characteristicCuspAdjustment r) * r =
      reduceModTwo
        (cuspRepresentative
          (characteristicCuspLabel r)) := by
  rcases reduceModTwo_six_cases r with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

/-- Adjust an arbitrary integral completion by at most one left
multiplication by `T`. -/
def cuspNormalizedCompletion
    (A : IntegralModularGroup) :
    IntegralModularGroup :=
  characteristicCuspAdjustment
      (integralCompletionCharacteristicLabel A) * A

/-- The adjusted completion has exactly the selected cusp
representative as its reduction modulo two. -/
theorem reduce_cuspNormalizedCompletion
    (A : IntegralModularGroup) :
    reduceModTwo (cuspNormalizedCompletion A) =
      reduceModTwo
        (cuspRepresentative
          (characteristicCuspLabel
            (integralCompletionCharacteristicLabel A))) := by
  rw [cuspNormalizedCompletion, map_mul]
  exact
    reduce_characteristicCuspAdjustment_mul
      (integralCompletionCharacteristicLabel A)

/-- The cusp-normalized completion preserves the completed primitive
row, because the correcting matrix is either `1` or `T`. -/
theorem cuspNormalizedCompletion_secondRow
    (A : IntegralModularGroup) :
    ∀ j : Fin 2,
      cuspNormalizedCompletion A 1 j = A 1 j := by
  intro j
  unfold cuspNormalizedCompletion
    characteristicCuspAdjustment
  split_ifs
  · simp
  · fin_cases j <;>
      simp [ModularGroup.T,
        Matrix.SpecialLinearGroup.coe_mul,
        Matrix.mul_apply, Fin.sum_univ_two]

/-- Left multiplication by the integral translation `T` preserves
upper-triangular form and adds `a⁻¹` to the upper-right entry. -/
theorem integralToRealFrame_T_mul_upperTriangularFrame
    (a b : ℝ) (ha : a ≠ 0) :
    integralToRealFrame ModularGroup.T *
        upperTriangularFrame a b ha =
      upperTriangularFrame a (b + a⁻¹) ha := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [integralToRealFrame, ModularGroup.T,
      upperTriangularFrame,
      Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- A primitive-row horizontalization can be adjusted into the selected
`Γ(2)` cusp coset.  The correction preserves the completed row and
therefore remains an exact horizontalization. -/
theorem PrimitiveRowHorizontalization.exists_cuspNormalized
    {v : PrimitiveIntegralRow}
    {g : RealModularFrame}
    (h : PrimitiveRowHorizontalization v g) :
    ∃ h' : PrimitiveRowHorizontalization v g,
      h'.completion =
        cuspNormalizedCompletion h.completion := by
  by_cases hr :
      integralCompletionCharacteristicLabel h.completion =
        reduceModTwo
          (cuspRepresentative
            (characteristicCuspLabel
              (integralCompletionCharacteristicLabel
                h.completion)))
  · refine ⟨h, ?_⟩
    simp only [cuspNormalizedCompletion,
      characteristicCuspAdjustment, if_pos hr, one_mul]
  · let hT :
        (ModularGroup.T * h.completion) • g =
          integralToRealFrame ModularGroup.T *
            (h.completion • g) := by
      simp [integralModularGroup_smul_realFrame, mul_assoc]
    exact
      ⟨{
        completion := ModularGroup.T * h.completion
        upperLeft := h.upperLeft
        upperRight := h.upperRight + h.upperLeft⁻¹
        upperLeft_ne_zero := h.upperLeft_ne_zero
        completion_row_zero := by
          simpa [ModularGroup.T,
            Matrix.SpecialLinearGroup.coe_mul,
            Matrix.mul_apply, Fin.sum_univ_two] using
              h.completion_row_zero
        completion_row_one := by
          simpa [ModularGroup.T,
            Matrix.SpecialLinearGroup.coe_mul,
            Matrix.mul_apply, Fin.sum_univ_two] using
              h.completion_row_one
        completedFrame_eq := by
          rw [hT, h.completedFrame_eq]
          exact
            integralToRealFrame_T_mul_upperTriangularFrame
              h.upperLeft h.upperRight
                h.upperLeft_ne_zero
      },
      by
        simp only [cuspNormalizedCompletion,
          characteristicCuspAdjustment, if_neg hr]⟩

/-- Chosen cusp-normalized horizontalization. -/
noncomputable def PrimitiveRowHorizontalization.cuspNormalized
    {v : PrimitiveIntegralRow}
    {g : RealModularFrame}
    (h : PrimitiveRowHorizontalization v g) :
    PrimitiveRowHorizontalization v g :=
  Classical.choose h.exists_cuspNormalized

/-- The adjusted horizontalization uses exactly the normalized
completion defined above. -/
theorem PrimitiveRowHorizontalization.cuspNormalized_completion
    {v : PrimitiveIntegralRow}
    {g : RealModularFrame}
    (h : PrimitiveRowHorizontalization v g) :
    h.cuspNormalized.completion =
      cuspNormalizedCompletion h.completion :=
  Classical.choose_spec h.exists_cuspNormalized

/-- The `Γ(2)` factor in the cusp-normalized completion. -/
def cuspNormalizedGammaTwoFactor
    (A : IntegralModularGroup) :
    IntegralModularGroup :=
  cuspNormalizedCompletion A *
    (cuspRepresentative
      (characteristicCuspLabel
        (integralCompletionCharacteristicLabel A)))⁻¹

/-- After the parity correction, the remaining factor belongs to
`Γ(2)`. -/
theorem cuspNormalizedGammaTwoFactor_mem
    (A : IntegralModularGroup) :
    cuspNormalizedGammaTwoFactor A ∈ GammaTwo := by
  apply CongruenceSubgroup.Gamma_mem'.mpr
  change reduceModTwo
      (cuspNormalizedGammaTwoFactor A) = 1
  rw [cuspNormalizedGammaTwoFactor, map_mul, map_inv,
    reduce_cuspNormalizedCompletion]
  simp

/-- Exact cusp-normalized factorization. -/
theorem cuspNormalizedCompletion_eq_gammaTwoFactor_mul_representative
    (A : IntegralModularGroup) :
    cuspNormalizedCompletion A =
      cuspNormalizedGammaTwoFactor A *
        cuspRepresentative
          (characteristicCuspLabel
            (integralCompletionCharacteristicLabel A)) := by
  simp [cuspNormalizedGammaTwoFactor]

/-- Thus the completed primitive row exposes both the six-valued theta
label and its three-valued `Γ(2)` cusp label. -/
def PrimitiveRowHorizontalization.characteristicLabel
    {v : PrimitiveIntegralRow}
    {g : RealModularFrame}
    (h : PrimitiveRowHorizontalization v g) :
    LevelTwoCharacteristicLabel :=
  integralCompletionCharacteristicLabel h.completion

def PrimitiveRowHorizontalization.cuspLabel
    {v : PrimitiveIntegralRow}
    {g : RealModularFrame}
    (h : PrimitiveRowHorizontalization v g) :
    GammaTwoCuspLabel :=
  characteristicCuspLabel h.characteristicLabel

end

end HGAS.Modular
