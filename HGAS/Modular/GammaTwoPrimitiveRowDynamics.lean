import HGAS.Modular.GammaTwoMahlerCompactCore
import HGAS.Modular.HorocycleMeasureClassification
import Mathlib.Tactic

/-!
# Primitive lattice rows along the level-two horocycle flow

The elementary cusp argument for `Γ(2) \ SL(2,ℝ)` is most transparent in
lattice coordinates.  If a primitive integral row `v` satisfies

```text
  v g = (C,D),
```

then right translation by the upper unipotent gives

```text
  v g u(t) = (C, Ct + D).
```

Thus the first coordinate is constant, while the second moves affinely.
The exceptional case `C = 0` is exactly the closed-horocycle case.  This
file proves both statements directly, including the level-two congruence
calculation needed for the latter implication.
-/

namespace HGAS.Modular

open Matrix Set
open scoped MatrixGroups CongruenceSubgroup

noncomputable section

/-- Primitive-row coordinates evolve affinely under the upper-unipotent
right action. -/
theorem primitiveIntegralRowMul_upperUnipotent
    (v : PrimitiveIntegralRow) (g : RealModularFrame) (t : ℝ) :
    primitiveIntegralRowMul v (g * upperUnipotent t) =
      fun j ↦
        if j = 0 then
          primitiveIntegralRowMul v g 0
        else
          primitiveIntegralRowMul v g 0 * t +
            primitiveIntegralRowMul v g 1 := by
  funext j
  fin_cases j
  · simp [primitiveIntegralRowMul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
  · simp [primitiveIntegralRowMul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
    ring

@[simp]
theorem primitiveIntegralRowMul_upperUnipotent_fst
    (v : PrimitiveIntegralRow) (g : RealModularFrame) (t : ℝ) :
    primitiveIntegralRowMul v (g * upperUnipotent t) 0 =
      primitiveIntegralRowMul v g 0 := by
  rw [primitiveIntegralRowMul_upperUnipotent]
  simp

@[simp]
theorem primitiveIntegralRowMul_upperUnipotent_snd
    (v : PrimitiveIntegralRow) (g : RealModularFrame) (t : ℝ) :
    primitiveIntegralRowMul v (g * upperUnipotent t) 1 =
      primitiveIntegralRowMul v g 0 * t +
        primitiveIntegralRowMul v g 1 := by
  rw [primitiveIntegralRowMul_upperUnipotent]
  simp

/-- The integral upper translation by two. -/
def integralUpperUnipotentTwo : IntegralModularGroup :=
  ⟨!![(1 : ℤ), 2; 0, 1], by
    simp [Matrix.det_fin_two]⟩

@[simp]
theorem integralUpperUnipotentTwo_coe :
    (integralUpperUnipotentTwo :
      Matrix (Fin 2) (Fin 2) ℤ) =
      !![(1 : ℤ), 2; 0, 1] :=
  rfl

theorem integralUpperUnipotentTwo_mem_gammaTwo :
    integralUpperUnipotentTwo ∈ GammaTwo := by
  rw [CongruenceSubgroup.Gamma_mem]
  constructor
  · norm_num [integralUpperUnipotentTwo]
  constructor
  · change ((2 : ℤ) : ZMod 2) = 0
    exact
      (ZMod.intCast_zmod_eq_zero_iff_dvd 2 2).mpr
        dvd_rfl
  constructor <;>
    norm_num [integralUpperUnipotentTwo]

@[simp]
theorem integralToRealFrame_upperUnipotentTwo :
    integralToRealFrame integralUpperUnipotentTwo =
      upperUnipotent 2 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [integralToRealFrame,
      integralUpperUnipotentTwo, upperUnipotent,
      Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply]

private theorem row_completion_mul_apply
    (v : PrimitiveIntegralRow) (g : RealModularFrame)
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

/-- If a primitive row is horizontal in the moving lattice, then the
corresponding horocycle in the level-two quotient is periodic.

The factor `2` is forced by the elementary deck transformation
`u(2) ∈ Γ(2)`.  Completing the primitive row to `A ∈ SL(2,ℤ)` makes
`A g` upper triangular.  For

```text
  A g = [a b; 0 a⁻¹],
```

right translation by time `2a⁻²` equals left multiplication by `u(2)`.
Conjugating `u(2)` by `A` remains in `Γ(2)` because the principal
congruence subgroup is normal.
-/
theorem isPeriodicHorocyclePoint_of_primitiveRowMul_fst_eq_zero
    (v : PrimitiveIntegralRow) (g : RealModularFrame)
    (hzero : primitiveIntegralRowMul v g 0 = 0) :
    IsPeriodicHorocyclePoint 1
      (gammaTwoFrameQuotientMk g) := by
  have hcoprime :
      IsCoprime (v.1 0) (v.1 1) :=
    (EisensteinSeries.mem_gammaSet_one v.1).mp v.2
  obtain ⟨A, hA0, hA1⟩ :=
    hcoprime.exists_SL2_row 1
  let h : RealModularFrame := A • g
  have hh10 : h 1 0 = 0 := by
    rw [row_completion_mul_apply v g A hA0 hA1]
    exact hzero
  obtain ⟨a, b, ha, hab⟩ :=
    Matrix.SpecialLinearGroup.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero
      h hh10
  let T : ℝ := 2 * a⁻¹ ^ 2
  have hT : 0 < T := by
    positivity
  let η0 : IntegralModularGroup :=
    A⁻¹ * integralUpperUnipotentTwo * A
  have hη0 : η0 ∈ GammaTwo := by
    dsimp only [η0]
    simpa using
      (CongruenceSubgroup.Gamma_normal 2).conj_mem
        integralUpperUnipotentTwo
        integralUpperUnipotentTwo_mem_gammaTwo A⁻¹
  let η : GammaTwo := ⟨η0, hη0⟩
  have htriangular :
      h * upperUnipotent T =
        integralToRealFrame integralUpperUnipotentTwo * h := by
    rw [hab]
    rw [integralToRealFrame_upperUnipotentTwo]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [T, upperUnipotent,
        Matrix.SpecialLinearGroup.coe_mul]
    field_simp [ha]
    ring
  have hframe :
      g * upperUnipotent T =
        gammaTwoToRealFrame η * g := by
    have hAreal :
        integralToRealFrame A * g = h := rfl
    have hηreal :
        gammaTwoToRealFrame η =
          integralToRealFrame A⁻¹ *
            integralToRealFrame integralUpperUnipotentTwo *
              integralToRealFrame A := by
      apply Subtype.ext
      ext i j
      simp [η, η0, gammaTwoToRealFrame,
        integralToRealFrame,
        Matrix.SpecialLinearGroup.map_apply_coe,
        RingHom.mapMatrix_apply,
        Matrix.SpecialLinearGroup.coe_mul,
        Matrix.mul_apply]
    rw [hηreal]
    calc
      g * upperUnipotent T =
          (integralToRealFrame A)⁻¹ *
            ((integralToRealFrame A * g) *
              upperUnipotent T) := by group
      _ = integralToRealFrame A⁻¹ *
            (h * upperUnipotent T) := by
              rw [map_inv, hAreal]
      _ = integralToRealFrame A⁻¹ *
            (integralToRealFrame integralUpperUnipotentTwo *
              h) := by rw [htriangular]
      _ = (integralToRealFrame A⁻¹ *
            integralToRealFrame integralUpperUnipotentTwo *
              integralToRealFrame A) * g := by
              rw [← hAreal]
              simp only [mul_assoc]
  refine ⟨T, hT, ?_⟩
  rw [scaledGammaTwoHorocycleFlow_one]
  change
    gammaTwoFrameQuotientMk (g * upperUnipotent T) =
      gammaTwoFrameQuotientMk g
  rw [hframe]
  apply Quotient.sound
  exact ⟨η, rfl⟩

/-- Along a nonperiodic horocycle, every primitive row has nonzero first
coordinate. -/
theorem primitiveIntegralRowMul_fst_ne_zero_of_nonperiodic
    (g : RealModularFrame)
    (hnonperiodic :
      ¬ IsPeriodicHorocyclePoint 1
        (gammaTwoFrameQuotientMk g))
    (v : PrimitiveIntegralRow) :
    primitiveIntegralRowMul v g 0 ≠ 0 := by
  intro hzero
  exact hnonperiodic
    (isPeriodicHorocyclePoint_of_primitiveRowMul_fst_eq_zero
      v g hzero)

end

end HGAS.Modular
