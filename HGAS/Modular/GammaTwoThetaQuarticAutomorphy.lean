import HGAS.Modular.GammaTwoThetaSquareAutomorphy

/-!
# Signed level-two automorphy of the even theta quartics

The three weight-two functions

```text
                         H₂ = θ₂⁴,  H₃ = θ₃⁴,  H₄ = θ₄⁴
```

are permuted by the integral modular group, with signs.  Both the
permutation and the sign factor through `SL(2, ZMod 2)`.  This file records
the complete six-element table and proves it for every integral modular
matrix by generation from `S` and `T`.

Unlike the squared version in `GammaTwoThetaSquareAutomorphy`, this theorem
retains the sign.  It is the precise weight-two identity needed when a
canonical-lambda lift is moved into a horizontal cusp chart: the
automorphy factor then cancels the derivative of the Möbius
transformation, leaving a constant horizontal velocity.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Matrix ModularGroup ModularForm SlashAction
open scoped MatrixGroups ModularForm CongruenceSubgroup

noncomputable section

/-- The three even theta quartics, ordered as `H₂,H₃,H₄`. -/
def thetaEvenQuartic : Fin 3 → (ℍ → ℂ)
  | 0 => H₂
  | 1 => H₃
  | 2 => H₄

/-- Sign in the theta-quartic transformation table.

The rows, in the order `1,S,T,ST,TS,STS`, are

```text
  [ 1, 1, 1], [-1,-1,-1], [-1, 1, 1],
  [-1,-1, 1], [ 1,-1,-1], [ 1, 1,-1].
```
-/
def thetaQuarticSign
    (g : SL(2, ZMod 2)) (i : Fin 3) : ℤ :=
  if g = 1 then 1
  else if g = reduceModTwo S then -1
  else if g = reduceModTwo T then ![-1, 1, 1] i
  else if g = reduceModTwo (S * T) then ![-1, -1, 1] i
  else if g = reduceModTwo (T * S) then ![1, -1, -1] i
  else ![1, 1, -1] i

@[simp]
theorem thetaQuarticSign_one (i : Fin 3) :
    thetaQuarticSign 1 i = 1 := by
  simp [thetaQuarticSign]

@[simp]
theorem thetaQuarticSign_S (i : Fin 3) :
    thetaQuarticSign (reduceModTwo S) i = -1 := by
  unfold thetaQuarticSign
  rw [if_neg (by decide), if_pos rfl]

@[simp]
theorem thetaQuarticSign_T (i : Fin 3) :
    thetaQuarticSign (reduceModTwo T) i = ![-1, 1, 1] i := by
  unfold thetaQuarticSign
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

@[simp]
theorem thetaQuarticSign_ST (i : Fin 3) :
    thetaQuarticSign (reduceModTwo (S * T)) i =
      ![-1, -1, 1] i := by
  unfold thetaQuarticSign
  rw [if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_pos rfl]

@[simp]
theorem thetaQuarticSign_TS (i : Fin 3) :
    thetaQuarticSign (reduceModTwo (T * S)) i =
      ![1, -1, -1] i := by
  unfold thetaQuarticSign
  rw [if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_pos rfl]

@[simp]
theorem thetaQuarticSign_STS (i : Fin 3) :
    thetaQuarticSign (reduceModTwo (S * T * S)) i =
      ![1, 1, -1] i := by
  unfold thetaQuarticSign
  rw [if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide),
    if_neg (by decide)]

/-- The signed permutation table is multiplicative in the order dictated
by the right slash action. -/
theorem thetaQuarticSign_mul
    (g h : SL(2, ZMod 2)) (i : Fin 3) :
    thetaQuarticSign (g * h) i =
      thetaQuarticSign g i *
        thetaQuarticSign h (thetaSquareIndex g i) := by
  rcases reduceModTwo_six_cases g with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases reduceModTwo_six_cases h with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
  fin_cases i <;> decide

/-- Every table entry is a unit sign. -/
theorem thetaQuarticSign_sq
    (g : SL(2, ZMod 2)) (i : Fin 3) :
    thetaQuarticSign g i ^ 2 = 1 := by
  rcases reduceModTwo_six_cases g with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
  fin_cases i <;> decide

/-- Signed quartic transformation under `S`. -/
theorem thetaEvenQuartic_S_action (i : Fin 3) :
    thetaEvenQuartic i ∣[(2 : ℤ)] S =
      (thetaQuarticSign (reduceModTwo S) i : ℂ) •
        thetaEvenQuartic
          (thetaSquareIndex (reduceModTwo S) i) := by
  rw [thetaQuarticSign_S, thetaSquareIndex_S]
  fin_cases i
  · simpa [thetaEvenQuartic] using H₂_S_action
  · simpa [thetaEvenQuartic] using H₃_S_action
  · simpa [thetaEvenQuartic] using H₄_S_action

/-- Signed quartic transformation under `T`. -/
theorem thetaEvenQuartic_T_action (i : Fin 3) :
    thetaEvenQuartic i ∣[(2 : ℤ)] T =
      (thetaQuarticSign (reduceModTwo T) i : ℂ) •
        thetaEvenQuartic
          (thetaSquareIndex (reduceModTwo T) i) := by
  rw [thetaQuarticSign_T, thetaSquareIndex_T]
  fin_cases i
  · simpa [thetaEvenQuartic] using H₂_T_action
  · simpa [thetaEvenQuartic] using H₃_T_action
  · simpa [thetaEvenQuartic] using H₄_T_action

/-- Matrices for which the complete signed theta-quartic law is known. -/
def thetaQuarticTransformationSubgroup : Subgroup SL(2, ℤ) where
  carrier :=
    {g | ∀ i : Fin 3,
      thetaEvenQuartic i ∣[(2 : ℤ)] g =
        (thetaQuarticSign (reduceModTwo g) i : ℂ) •
          thetaEvenQuartic
            (thetaSquareIndex (reduceModTwo g) i)}
  one_mem' := by
    intro i
    simp
  mul_mem' := by
    intro g h hg hh i
    rw [SlashAction.slash_mul, hg, map_mul,
      thetaQuarticSign_mul, thetaSquareIndex_mul]
    rw [ModularForm.SL_smul_slash]
    rw [hh]
    push_cast
    rw [smul_smul]
  inv_mem' := by
    intro g hg i
    let j :=
      thetaSquareIndex (reduceModTwo g⁻¹) i
    have h :=
      congrArg
        (fun f : ℍ → ℂ ↦ f ∣[(2 : ℤ)] g⁻¹)
        (hg j)
    have hindex :
        thetaSquareIndex (reduceModTwo g)
            (thetaSquareIndex (reduceModTwo g⁻¹) i) =
          i := by
      rw [← thetaSquareIndex_mul, ← map_mul,
        inv_mul_cancel, map_one, thetaSquareIndex_one]
    have hsign :
        thetaQuarticSign (reduceModTwo g) j *
            thetaQuarticSign (reduceModTwo g⁻¹) i =
          1 := by
      have hmul :=
        thetaQuarticSign_mul
          (reduceModTwo g⁻¹) (reduceModTwo g) i
      rw [← map_mul, inv_mul_cancel, map_one,
        thetaQuarticSign_one] at hmul
      simpa only [j, mul_comm] using hmul.symm
    change
      (thetaEvenQuartic j ∣[(2 : ℤ)] g) ∣[(2 : ℤ)] g⁻¹ =
        ((thetaQuarticSign (reduceModTwo g) j : ℂ) •
          thetaEvenQuartic
            (thetaSquareIndex (reduceModTwo g) j)) ∣[(2 : ℤ)] g⁻¹
      at h
    rw [hindex] at h
    rw [ModularForm.SL_smul_slash] at h
    rw [← SlashAction.slash_mul, mul_inv_cancel,
      SlashAction.slash_one] at h
    have hsignComplex :
        (thetaQuarticSign (reduceModTwo g) j : ℂ) *
            (thetaQuarticSign (reduceModTwo g⁻¹) i : ℂ) =
          1 := by
      exact_mod_cast hsign
    ext τ
    have hpoint := congrFun h τ
    have hpoint' :
      (thetaQuarticSign (reduceModTwo g) j : ℂ) *
          (thetaEvenQuartic i ∣[(2 : ℤ)] g⁻¹) τ =
        thetaEvenQuartic j τ := by
      simpa only [Pi.smul_apply, smul_eq_mul] using hpoint.symm
    change
      (thetaEvenQuartic i ∣[(2 : ℤ)] g⁻¹) τ =
        (thetaQuarticSign (reduceModTwo g⁻¹) i : ℂ) *
          thetaEvenQuartic j τ
    calc
      (thetaEvenQuartic i ∣[(2 : ℤ)] g⁻¹) τ =
          1 * (thetaEvenQuartic i ∣[(2 : ℤ)] g⁻¹) τ := by
            rw [one_mul]
      _ =
          ((thetaQuarticSign (reduceModTwo g) j : ℂ) *
            (thetaQuarticSign (reduceModTwo g⁻¹) i : ℂ)) *
              (thetaEvenQuartic i ∣[(2 : ℤ)] g⁻¹) τ := by
            rw [hsignComplex]
      _ =
          (thetaQuarticSign (reduceModTwo g⁻¹) i : ℂ) *
            ((thetaQuarticSign (reduceModTwo g) j : ℂ) *
              (thetaEvenQuartic i ∣[(2 : ℤ)] g⁻¹) τ) := by
            ring
      _ = _ := by rw [hpoint']

/-- The full signed transformation law for every integral determinant-one
matrix. -/
theorem thetaEvenQuartic_smul
    (g : SL(2, ℤ)) (i : Fin 3) :
    thetaEvenQuartic i ∣[(2 : ℤ)] g =
      (thetaQuarticSign (reduceModTwo g) i : ℂ) •
        thetaEvenQuartic
          (thetaSquareIndex (reduceModTwo g) i) := by
  have hle :
      Subgroup.closure ({S, T} : Set SL(2, ℤ)) ≤
        thetaQuarticTransformationSubgroup := by
    apply
      (Subgroup.closure_le thetaQuarticTransformationSubgroup).2
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact thetaEvenQuartic_S_action
    · exact thetaEvenQuartic_T_action
  exact hle (by
    rw [SpecialLinearGroup.SL2Z_generators]
    exact Subgroup.mem_top g) i

/-- Every element of `Γ(2)` fixes each weight-two theta quartic exactly. -/
theorem thetaEvenQuartic_smul_of_mem_Gamma_two
    {g : SL(2, ℤ)}
    (hg : g ∈ CongruenceSubgroup.Gamma 2)
    (i : Fin 3) :
    thetaEvenQuartic i ∣[(2 : ℤ)] g =
      thetaEvenQuartic i := by
  have hred : reduceModTwo g = 1 := by
    simpa only [reduceModTwo] using
      (CongruenceSubgroup.Gamma_mem'.mp hg)
  rw [thetaEvenQuartic_smul, hred,
    thetaQuarticSign_one, Int.cast_one, one_smul,
    thetaSquareIndex_one]

end

end HGAS.Modular
