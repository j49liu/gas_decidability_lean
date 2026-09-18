import HGAS.Modular.CanonicalLambdaGammaTwo
import HGAS.Modular.ThetaTransformations
import Mathlib.Tactic

/-!
# Exact level-two automorphy of the squared even theta constants

The fourth powers `H₂`, `H₃`, and `H₄` transform under the standard
generators `S,T` by signed permutations.  Squaring removes all signs.
Consequently the three weight-four functions

```
                         H₂², H₃², H₄²
```

carry an honest permutation action of `SL(2, ZMod 2)`.  This file
formalizes that finite action and proves, by the `S,T` generation theorem,
that every element of the principal congruence subgroup `Γ(2)` fixes each
of the three squares exactly.

The use of `H₄²`, rather than an arbitrarily chosen theta multiplier, is
important later: it gives a genuine continuous function on the full
`Γ(2)` frame quotient, while its norm has precisely the even power needed
by the polynomial compactification clock.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Matrix ModularGroup ModularForm SlashAction
open scoped MatrixGroups ModularForm CongruenceSubgroup

noncomputable section

/-- The three squared even theta fourth-powers, ordered as `H₂²,H₃²,H₄²`. -/
def thetaEvenSquare : Fin 3 → (ℍ → ℂ)
  | 0 => H₂ * H₂
  | 1 => H₃ * H₃
  | 2 => H₄ * H₄

/-- The permutation of the three theta squares attached to a matrix
modulo two.

The six rows, in the order `1,S,T,ST,TS,STS`, are

```
  [0,1,2], [2,1,0], [0,2,1], [1,2,0], [2,0,1], [1,0,2].
```

The convention is adapted to a right slash action:
`P(g*h) i = P(h) (P(g) i)`. -/
def thetaSquareIndex
    (g : SL(2, ZMod 2)) (i : Fin 3) : Fin 3 :=
  if g = 1 then i
  else if g = reduceModTwo S then ![2, 1, 0] i
  else if g = reduceModTwo T then ![0, 2, 1] i
  else if g = reduceModTwo (S * T) then ![1, 2, 0] i
  else if g = reduceModTwo (T * S) then ![2, 0, 1] i
  else ![1, 0, 2] i

@[simp]
theorem thetaSquareIndex_one (i : Fin 3) :
    thetaSquareIndex 1 i = i := by
  simp [thetaSquareIndex]

@[simp]
theorem thetaSquareIndex_S (i : Fin 3) :
    thetaSquareIndex (reduceModTwo S) i = ![2, 1, 0] i := by
  unfold thetaSquareIndex
  rw [if_neg (by decide), if_pos rfl]

@[simp]
theorem thetaSquareIndex_T (i : Fin 3) :
    thetaSquareIndex (reduceModTwo T) i = ![0, 2, 1] i := by
  unfold thetaSquareIndex
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

@[simp]
theorem thetaSquareIndex_ST (i : Fin 3) :
    thetaSquareIndex (reduceModTwo (S * T)) i =
      ![1, 2, 0] i := by
  unfold thetaSquareIndex
  rw [if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_pos rfl]

@[simp]
theorem thetaSquareIndex_TS (i : Fin 3) :
    thetaSquareIndex (reduceModTwo (T * S)) i =
      ![2, 0, 1] i := by
  unfold thetaSquareIndex
  rw [if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_pos rfl]

@[simp]
theorem thetaSquareIndex_STS (i : Fin 3) :
    thetaSquareIndex (reduceModTwo (S * T * S)) i =
      ![1, 0, 2] i := by
  unfold thetaSquareIndex
  rw [if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide),
    if_neg (by decide)]

/-- The finite permutation table respects multiplication, with the order
forced by the right slash action. -/
theorem thetaSquareIndex_mul
    (g h : SL(2, ZMod 2)) (i : Fin 3) :
    thetaSquareIndex (g * h) i =
      thetaSquareIndex h (thetaSquareIndex g i) := by
  rcases reduceModTwo_six_cases g with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases reduceModTwo_six_cases h with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
  fin_cases i <;> decide

/-- Squared theta transformation under `S`. -/
theorem thetaEvenSquare_S_action (i : Fin 3) :
    thetaEvenSquare i ∣[(4 : ℤ)] S =
      thetaEvenSquare
        (thetaSquareIndex (reduceModTwo S) i) := by
  rw [thetaSquareIndex_S]
  fin_cases i
  · change (H₂ * H₂) ∣[(4 : ℤ)] S = H₄ * H₄
    calc
      _ = (H₂ ∣[(2 : ℤ)] S) *
          (H₂ ∣[(2 : ℤ)] S) := by
            simpa using
              ModularForm.mul_slash_SL2
                (2 : ℤ) (2 : ℤ) S H₂ H₂
      _ = _ := by rw [H₂_S_action]; ring
  · change (H₃ * H₃) ∣[(4 : ℤ)] S = H₃ * H₃
    calc
      _ = (H₃ ∣[(2 : ℤ)] S) *
          (H₃ ∣[(2 : ℤ)] S) := by
            simpa using
              ModularForm.mul_slash_SL2
                (2 : ℤ) (2 : ℤ) S H₃ H₃
      _ = _ := by rw [H₃_S_action]; ring
  · change (H₄ * H₄) ∣[(4 : ℤ)] S = H₂ * H₂
    calc
      _ = (H₄ ∣[(2 : ℤ)] S) *
          (H₄ ∣[(2 : ℤ)] S) := by
            simpa using
              ModularForm.mul_slash_SL2
                (2 : ℤ) (2 : ℤ) S H₄ H₄
      _ = _ := by rw [H₄_S_action]; ring

/-- Squared theta transformation under `T`. -/
theorem thetaEvenSquare_T_action (i : Fin 3) :
    thetaEvenSquare i ∣[(4 : ℤ)] T =
      thetaEvenSquare
        (thetaSquareIndex (reduceModTwo T) i) := by
  rw [thetaSquareIndex_T]
  fin_cases i
  · change (H₂ * H₂) ∣[(4 : ℤ)] T = H₂ * H₂
    calc
      _ = (H₂ ∣[(2 : ℤ)] T) *
          (H₂ ∣[(2 : ℤ)] T) := by
            simpa using
              ModularForm.mul_slash_SL2
                (2 : ℤ) (2 : ℤ) T H₂ H₂
      _ = _ := by rw [H₂_T_action]; ring
  · change (H₃ * H₃) ∣[(4 : ℤ)] T = H₄ * H₄
    calc
      _ = (H₃ ∣[(2 : ℤ)] T) *
          (H₃ ∣[(2 : ℤ)] T) := by
            simpa using
              ModularForm.mul_slash_SL2
                (2 : ℤ) (2 : ℤ) T H₃ H₃
      _ = _ := by rw [H₃_T_action]
  · change (H₄ * H₄) ∣[(4 : ℤ)] T = H₃ * H₃
    calc
      _ = (H₄ ∣[(2 : ℤ)] T) *
          (H₄ ∣[(2 : ℤ)] T) := by
            simpa using
              ModularForm.mul_slash_SL2
                (2 : ℤ) (2 : ℤ) T H₄ H₄
      _ = _ := by rw [H₄_T_action]

/-- Matrices for which the complete theta-square permutation law is
known. -/
def thetaSquareTransformationSubgroup : Subgroup SL(2, ℤ) where
  carrier :=
    {g | ∀ i : Fin 3,
      thetaEvenSquare i ∣[(4 : ℤ)] g =
        thetaEvenSquare
          (thetaSquareIndex (reduceModTwo g) i)}
  one_mem' := by
    intro i
    simp only [SlashAction.slash_one, map_one,
      thetaSquareIndex_one]
  mul_mem' := by
    intro g h hg hh i
    rw [SlashAction.slash_mul, hg, hh, map_mul,
      thetaSquareIndex_mul]
  inv_mem' := by
    intro g hg i
    have h :=
      congrArg (fun f : ℍ → ℂ ↦ f ∣[(4 : ℤ)] g⁻¹)
        (hg (thetaSquareIndex (reduceModTwo g⁻¹) i))
    change
      (thetaEvenSquare
          (thetaSquareIndex (reduceModTwo g⁻¹) i) ∣[(4 : ℤ)] g) ∣[(4 : ℤ)] g⁻¹ =
        thetaEvenSquare
            (thetaSquareIndex (reduceModTwo g)
              (thetaSquareIndex (reduceModTwo g⁻¹) i)) ∣[(4 : ℤ)] g⁻¹
      at h
    have hindex :
        thetaSquareIndex (reduceModTwo g)
            (thetaSquareIndex (reduceModTwo g⁻¹) i) =
          i := by
      rw [← thetaSquareIndex_mul, ← map_mul,
        inv_mul_cancel, map_one, thetaSquareIndex_one]
    rw [hindex] at h
    rw [← SlashAction.slash_mul, mul_inv_cancel,
      SlashAction.slash_one] at h
    exact h.symm

/-- The full transformation law: integral determinant-one matrices
permute the three squared theta constants through their reduction modulo
two. -/
theorem thetaEvenSquare_smul
    (g : SL(2, ℤ)) (i : Fin 3) :
    thetaEvenSquare i ∣[(4 : ℤ)] g =
      thetaEvenSquare
        (thetaSquareIndex (reduceModTwo g) i) := by
  have hle :
      Subgroup.closure ({S, T} : Set SL(2, ℤ)) ≤
        thetaSquareTransformationSubgroup := by
    apply
      (Subgroup.closure_le thetaSquareTransformationSubgroup).2
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact thetaEvenSquare_S_action
    · exact thetaEvenSquare_T_action
  exact hle (by
    rw [SpecialLinearGroup.SL2Z_generators]
    exact Subgroup.mem_top g) i

/-- Every element of `Γ(2)` fixes all three squared theta constants. -/
theorem thetaEvenSquare_smul_of_mem_Gamma_two
    {g : SL(2, ℤ)}
    (hg : g ∈ CongruenceSubgroup.Gamma 2)
    (i : Fin 3) :
    thetaEvenSquare i ∣[(4 : ℤ)] g =
      thetaEvenSquare i := by
  have hred : reduceModTwo g = 1 := by
    simpa only [reduceModTwo] using
      (CongruenceSubgroup.Gamma_mem'.mp hg)
  rw [thetaEvenSquare_smul, hred, thetaSquareIndex_one]

/-- In particular, `H₄²` is an exact weight-four modular function for
`Γ(2)`. -/
theorem H₄_sq_smul_of_mem_Gamma_two
    {g : SL(2, ℤ)}
    (hg : g ∈ CongruenceSubgroup.Gamma 2) :
    (H₄ * H₄) ∣[(4 : ℤ)] g = H₄ * H₄ := by
  simpa only [thetaEvenSquare] using
    thetaEvenSquare_smul_of_mem_Gamma_two hg (2 : Fin 3)

end

end HGAS.Modular
