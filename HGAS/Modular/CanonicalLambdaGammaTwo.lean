import HGAS.Modular.CanonicalLambdaDeck
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# The level-two transformation law of canonical lambda

The transformations of modular lambda under `S` and `T` generate exactly
six fractional-linear transformations of the twice-punctured plane.  This
file packages those transformations as an action of `SL(2, ZMod 2)`.

The main payoff is a proof, using the standard `S,T` generation theorem for
`SL(2, ℤ)`, that lambda is invariant under every element of `Γ(2)`.  Thus the
invariance is not restricted to the two familiar explicit generators.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real ModularGroup
open scoped MatrixGroups CongruenceSubgroup

noncomputable section

/-- Reduction of an integral special-linear matrix modulo two. -/
def reduceModTwo : SL(2, ℤ) →* SL(2, ZMod 2) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 2))

/-- The six cross-ratio transforms, indexed by `SL(2, ZMod 2)`.

The order of the cases is `1, S, T, ST, TS, STS`.  These are all elements
of `SL(2, ZMod 2)`. -/
def lambdaCrossRatio (g : SL(2, ZMod 2)) (x : ℂ) : ℂ :=
  if g = 1 then x
  else if g = reduceModTwo S then 1 - x
  else if g = reduceModTwo T then x / (x - 1)
  else if g = reduceModTwo (S * T) then 1 / (1 - x)
  else if g = reduceModTwo (T * S) then (x - 1) / x
  else 1 / x

/-- There are exactly six matrices in `SL(2, ZMod 2)`. -/
theorem reduceModTwo_six_cases :
    ∀ g : SL(2, ZMod 2),
      g = 1 ∨
      g = reduceModTwo S ∨
      g = reduceModTwo T ∨
      g = reduceModTwo (S * T) ∨
      g = reduceModTwo (T * S) ∨
      g = reduceModTwo (S * T * S) := by
  decide

/-- Reduction modulo two is onto. -/
theorem reduceModTwo_surjective :
    Function.Surjective reduceModTwo := by
  intro g
  rcases reduceModTwo_six_cases g with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, map_one reduceModTwo⟩
  · exact ⟨S, rfl⟩
  · exact ⟨T, rfl⟩
  · exact ⟨S * T, rfl⟩
  · exact ⟨T * S, rfl⟩
  · exact ⟨S * T * S, rfl⟩

/-- A fixed integral lift of each matrix modulo two. -/
noncomputable def liftModTwo :
    SL(2, ZMod 2) → SL(2, ℤ) :=
  Function.surjInv reduceModTwo_surjective

@[simp]
theorem reduceModTwo_liftModTwo
    (g : SL(2, ZMod 2)) :
    reduceModTwo (liftModTwo g) = g :=
  Function.surjInv_eq reduceModTwo_surjective g

private theorem reduceModTwo_S_ne_one :
    reduceModTwo S ≠ 1 := by decide

private theorem reduceModTwo_T_ne_one :
    reduceModTwo T ≠ 1 := by decide

private theorem reduceModTwo_T_ne_S :
    reduceModTwo T ≠ reduceModTwo S := by decide

private theorem reduceModTwo_ST_ne_one :
    reduceModTwo (S * T) ≠ 1 := by decide

private theorem reduceModTwo_ST_ne_S :
    reduceModTwo (S * T) ≠ reduceModTwo S := by decide

private theorem reduceModTwo_ST_ne_T :
    reduceModTwo (S * T) ≠ reduceModTwo T := by decide

private theorem reduceModTwo_TS_ne_one :
    reduceModTwo (T * S) ≠ 1 := by decide

private theorem reduceModTwo_TS_ne_S :
    reduceModTwo (T * S) ≠ reduceModTwo S := by decide

private theorem reduceModTwo_TS_ne_T :
    reduceModTwo (T * S) ≠ reduceModTwo T := by decide

private theorem reduceModTwo_TS_ne_ST :
    reduceModTwo (T * S) ≠ reduceModTwo (S * T) := by decide

private theorem reduceModTwo_STS_ne_one :
    reduceModTwo (S * T * S) ≠ 1 := by decide

private theorem reduceModTwo_STS_ne_S :
    reduceModTwo (S * T * S) ≠ reduceModTwo S := by decide

private theorem reduceModTwo_STS_ne_T :
    reduceModTwo (S * T * S) ≠ reduceModTwo T := by decide

private theorem reduceModTwo_STS_ne_ST :
    reduceModTwo (S * T * S) ≠ reduceModTwo (S * T) := by decide

private theorem reduceModTwo_STS_ne_TS :
    reduceModTwo (S * T * S) ≠ reduceModTwo (T * S) := by decide

@[simp]
theorem lambdaCrossRatio_one (x : ℂ) :
    lambdaCrossRatio 1 x = x := by
  rw [lambdaCrossRatio, if_pos rfl]

@[simp]
theorem lambdaCrossRatio_S (x : ℂ) :
    lambdaCrossRatio (reduceModTwo S) x = 1 - x := by
  rw [lambdaCrossRatio, if_neg reduceModTwo_S_ne_one,
    if_pos rfl]

@[simp]
theorem lambdaCrossRatio_T (x : ℂ) :
    lambdaCrossRatio (reduceModTwo T) x = x / (x - 1) := by
  rw [lambdaCrossRatio, if_neg reduceModTwo_T_ne_one,
    if_neg reduceModTwo_T_ne_S, if_pos rfl]

@[simp]
theorem lambdaCrossRatio_ST (x : ℂ) :
    lambdaCrossRatio (reduceModTwo (S * T)) x = 1 / (1 - x) := by
  rw [lambdaCrossRatio, if_neg reduceModTwo_ST_ne_one,
    if_neg reduceModTwo_ST_ne_S,
    if_neg reduceModTwo_ST_ne_T, if_pos rfl]

@[simp]
theorem lambdaCrossRatio_TS (x : ℂ) :
    lambdaCrossRatio (reduceModTwo (T * S)) x = (x - 1) / x := by
  rw [lambdaCrossRatio, if_neg reduceModTwo_TS_ne_one,
    if_neg reduceModTwo_TS_ne_S,
    if_neg reduceModTwo_TS_ne_T,
    if_neg reduceModTwo_TS_ne_ST, if_pos rfl]

@[simp]
theorem lambdaCrossRatio_STS (x : ℂ) :
    lambdaCrossRatio (reduceModTwo (S * T * S)) x = 1 / x := by
  rw [lambdaCrossRatio, if_neg reduceModTwo_STS_ne_one,
    if_neg reduceModTwo_STS_ne_S,
    if_neg reduceModTwo_STS_ne_T,
    if_neg reduceModTwo_STS_ne_ST,
    if_neg reduceModTwo_STS_ne_TS]

/-- Every cross-ratio transform avoids zero when its input avoids zero and
one. -/
theorem lambdaCrossRatio_ne_zero
    (g : SL(2, ZMod 2)) {x : ℂ}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    lambdaCrossRatio g x ≠ 0 := by
  rcases reduceModTwo_six_cases g with
    rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using hx0
  · simpa only [lambdaCrossRatio_S] using
      sub_ne_zero.mpr hx1.symm
  · simpa only [lambdaCrossRatio_T] using
      div_ne_zero hx0 (sub_ne_zero.mpr hx1)
  · simpa only [lambdaCrossRatio_ST, one_div] using
      inv_ne_zero (sub_ne_zero.mpr hx1.symm)
  · simpa only [lambdaCrossRatio_TS] using
      div_ne_zero (sub_ne_zero.mpr hx1) hx0
  · simpa only [lambdaCrossRatio_STS, one_div] using
      inv_ne_zero hx0

/-- Every cross-ratio transform avoids one when its input avoids zero and
one. -/
theorem lambdaCrossRatio_ne_one
    (g : SL(2, ZMod 2)) {x : ℂ}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    lambdaCrossRatio g x ≠ 1 := by
  rcases reduceModTwo_six_cases g with
    rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using hx1
  · simp only [lambdaCrossRatio_S]
    intro h
    apply hx0
    linear_combination -h
  · simp only [lambdaCrossRatio_T]
    intro h
    field_simp [sub_ne_zero.mpr hx1] at h
    have hbad : (1 : ℂ) = 0 := by
      calc
        1 = x - (x - 1) := by ring
        _ = 0 := by rw [← h]; ring
    exact one_ne_zero hbad
  · simp only [lambdaCrossRatio_ST]
    intro h
    field_simp [sub_ne_zero.mpr hx1.symm] at h
    apply hx0
    calc
      x = 1 - (1 - x) := by ring
      _ = 0 := by rw [← h]; ring
  · simp only [lambdaCrossRatio_TS]
    intro h
    field_simp [hx0] at h
    have hbad : (1 : ℂ) = 0 := by
      calc
        1 = x - (x - 1) := by ring
        _ = 0 := by rw [h]; ring
    exact one_ne_zero hbad
  · simp only [lambdaCrossRatio_STS]
    intro h
    field_simp [hx0] at h
    exact hx1 h.symm

/-- The cross-ratio action on the twice-punctured plane. -/
def lambdaCrossRatioPunctured
    (g : SL(2, ZMod 2)) (x : LambdaPuncturedPlane) :
    LambdaPuncturedPlane :=
  ⟨lambdaCrossRatio g x,
    lambdaCrossRatio_ne_zero g x.property.1 x.property.2,
    lambdaCrossRatio_ne_one g x.property.1 x.property.2⟩

@[simp]
theorem lambdaCrossRatioPunctured_coe
    (g : SL(2, ZMod 2)) (x : LambdaPuncturedPlane) :
    (lambdaCrossRatioPunctured g x : ℂ) =
      lambdaCrossRatio g x :=
  rfl

/-- Names for the six elements of `SL(2, ZMod 2)`. -/
private inductive LambdaSix
  | one | s | t | st | ts | sts
  deriving DecidableEq, Fintype

/-- The matrix represented by a name in `LambdaSix`. -/
private def LambdaSix.matrix : LambdaSix → SL(2, ZMod 2)
  | .one => 1
  | .s => reduceModTwo S
  | .t => reduceModTwo T
  | .st => reduceModTwo (S * T)
  | .ts => reduceModTwo (T * S)
  | .sts => reduceModTwo (S * T * S)

/-- Multiplication table of the six names. -/
private def LambdaSix.mul : LambdaSix → LambdaSix → LambdaSix
  | .one, b => b
  | .s, .one => .s
  | .s, .s => .one
  | .s, .t => .st
  | .s, .st => .t
  | .s, .ts => .sts
  | .s, .sts => .ts
  | .t, .one => .t
  | .t, .s => .ts
  | .t, .t => .one
  | .t, .st => .sts
  | .t, .ts => .s
  | .t, .sts => .st
  | .st, .one => .st
  | .st, .s => .sts
  | .st, .t => .s
  | .st, .st => .ts
  | .st, .ts => .one
  | .st, .sts => .t
  | .ts, .one => .ts
  | .ts, .s => .t
  | .ts, .t => .sts
  | .ts, .st => .one
  | .ts, .ts => .st
  | .ts, .sts => .s
  | .sts, .one => .sts
  | .sts, .s => .st
  | .sts, .t => .ts
  | .sts, .st => .s
  | .sts, .ts => .t
  | .sts, .sts => .one

private theorem LambdaSix.matrix_mul :
    ∀ a b : LambdaSix,
      (a.mul b).matrix = a.matrix * b.matrix := by
  decide

private theorem exists_lambdaSix_matrix
    (g : SL(2, ZMod 2)) :
    ∃ a : LambdaSix, g = a.matrix := by
  rcases reduceModTwo_six_cases g with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.one, rfl⟩
  · exact ⟨.s, rfl⟩
  · exact ⟨.t, rfl⟩
  · exact ⟨.st, rfl⟩
  · exact ⟨.ts, rfl⟩
  · exact ⟨.sts, rfl⟩

/- Composition of the six cross-ratio transformations agrees with matrix
multiplication modulo two. -/
theorem lambdaCrossRatio_mul
    (g h : SL(2, ZMod 2)) {x : ℂ}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    lambdaCrossRatio (g * h) x =
      lambdaCrossRatio g (lambdaCrossRatio h x) := by
  obtain ⟨a, rfl⟩ := exists_lambdaSix_matrix g
  obtain ⟨b, rfl⟩ := exists_lambdaSix_matrix h
  rw [← LambdaSix.matrix_mul]
  cases a <;> cases b <;>
  simp only [LambdaSix.matrix, LambdaSix.mul,
    lambdaCrossRatio_one, lambdaCrossRatio_S,
    lambdaCrossRatio_T, lambdaCrossRatio_ST,
    lambdaCrossRatio_TS, lambdaCrossRatio_STS] <;>
  field_simp [hx0, sub_ne_zero.mpr hx1,
    sub_ne_zero.mpr hx1.symm] <;>
  ring

instance : SMul (SL(2, ZMod 2)) LambdaPuncturedPlane where
  smul := lambdaCrossRatioPunctured

instance : MulAction (SL(2, ZMod 2)) LambdaPuncturedPlane where
  one_smul x := by
    apply Subtype.ext
    exact lambdaCrossRatio_one x
  mul_smul g h x := by
    apply Subtype.ext
    exact lambdaCrossRatio_mul g h
      x.property.1 x.property.2

theorem lambdaCrossRatio_smul_coe
    (g : SL(2, ZMod 2)) (x : LambdaPuncturedPlane) :
    (g • x : LambdaPuncturedPlane) =
      lambdaCrossRatioPunctured g x :=
  rfl

/-- Each of the six cross-ratio transformations is continuous on the
twice-punctured plane. -/
theorem lambdaCrossRatio_smul_continuous
    (g : SL(2, ZMod 2)) :
    Continuous (g • · : LambdaPuncturedPlane →
      LambdaPuncturedPlane) := by
  rcases reduceModTwo_six_cases g with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact continuous_id
  · apply Continuous.subtype_mk
    simpa only [lambdaCrossRatio_smul_coe,
      lambdaCrossRatioPunctured_coe,
      lambdaCrossRatio_S] using
        continuous_const.sub continuous_subtype_val
  · apply Continuous.subtype_mk
    simpa only [lambdaCrossRatio_smul_coe,
      lambdaCrossRatioPunctured_coe,
      lambdaCrossRatio_T] using
        continuous_subtype_val.div
          (continuous_subtype_val.sub continuous_const)
          (fun x ↦ sub_ne_zero.mpr x.property.2)
  · apply Continuous.subtype_mk
    simpa only [lambdaCrossRatio_smul_coe,
      lambdaCrossRatioPunctured_coe,
      lambdaCrossRatio_ST] using
        continuous_const.div
          (continuous_const.sub continuous_subtype_val)
          (fun x ↦ sub_ne_zero.mpr x.property.2.symm)
  · apply Continuous.subtype_mk
    simpa only [lambdaCrossRatio_smul_coe,
      lambdaCrossRatioPunctured_coe,
      lambdaCrossRatio_TS] using
        (continuous_subtype_val.sub continuous_const).div
          continuous_subtype_val
          (fun x ↦ x.property.1)
  · apply Continuous.subtype_mk
    simpa only [lambdaCrossRatio_smul_coe,
      lambdaCrossRatioPunctured_coe,
      lambdaCrossRatio_STS] using
        continuous_const.div continuous_subtype_val
          (fun x ↦ x.property.1)

/-- The theta transformation under `S`, expressed as equivariance for the
six-element cross-ratio action. -/
theorem canonicalLambdaPunctured_S_smul (z : ℍ) :
    canonicalLambdaPunctured (S • z) =
      reduceModTwo S • canonicalLambdaPunctured z := by
  apply Subtype.ext
  simpa only [canonicalLambdaPunctured_coe,
    lambdaCrossRatio_smul_coe,
    lambdaCrossRatioPunctured_coe,
    lambdaCrossRatio_S,
    UpperHalfPlane.modular_S_smul] using
      canonicalLambda_modularSPoint z

/-- The theta transformation under `T`, expressed as equivariance for the
six-element cross-ratio action. -/
theorem canonicalLambdaPunctured_T_smul (z : ℍ) :
    canonicalLambdaPunctured (T • z) =
      reduceModTwo T • canonicalLambdaPunctured z := by
  apply Subtype.ext
  simpa only [canonicalLambdaPunctured_coe,
    lambdaCrossRatio_smul_coe,
    lambdaCrossRatioPunctured_coe,
    lambdaCrossRatio_T,
    UpperHalfPlane.modular_T_smul] using
      canonicalLambda_vadd_one z

/-- Integral matrices for which the full level-two equivariance law is
known.  Closure under multiplication and inverse is a consequence of the
genuine action proved above. -/
def lambdaTransformationSubgroup : Subgroup SL(2, ℤ) where
  carrier :=
    {g | ∀ z : ℍ,
      canonicalLambdaPunctured (g • z) =
        reduceModTwo g • canonicalLambdaPunctured z}
  one_mem' := by
    intro z
    rw [one_smul, map_one, one_smul]
  mul_mem' := by
    intro g h hg hh z
    rw [mul_smul, hg, hh, map_mul, mul_smul]
  inv_mem' := by
    intro g hg z
    have h :
        canonicalLambdaPunctured z =
          reduceModTwo g •
            canonicalLambdaPunctured (g⁻¹ • z) := by
      simpa only [smul_inv_smul] using hg (g⁻¹ • z)
    calc
      canonicalLambdaPunctured (g⁻¹ • z) =
          (reduceModTwo g)⁻¹ •
            (reduceModTwo g •
              canonicalLambdaPunctured (g⁻¹ • z)) := by
            exact (inv_smul_smul _ _).symm
      _ = (reduceModTwo g)⁻¹ •
            canonicalLambdaPunctured z :=
          congrArg ((reduceModTwo g)⁻¹ • ·) h.symm
      _ = reduceModTwo g⁻¹ •
            canonicalLambdaPunctured z := by
          rw [map_inv]

/-- The complete six-valued transformation law for canonical lambda under
`SL(2, ℤ)`. -/
theorem canonicalLambdaPunctured_smul
    (g : SL(2, ℤ)) (z : ℍ) :
    canonicalLambdaPunctured (g • z) =
      reduceModTwo g • canonicalLambdaPunctured z := by
  have hle :
      Subgroup.closure ({S, T} : Set SL(2, ℤ)) ≤
        lambdaTransformationSubgroup := by
    apply (Subgroup.closure_le
      lambdaTransformationSubgroup).2
    intro a ha
    simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact canonicalLambdaPunctured_S_smul
    · exact canonicalLambdaPunctured_T_smul
  exact hle (by
    rw [SpecialLinearGroup.SL2Z_generators]
    exact Subgroup.mem_top g) z

/-- Every matrix in the principal congruence subgroup `Γ(2)` preserves
canonical lambda. -/
theorem canonicalLambdaPunctured_smul_of_mem_Gamma_two
    {g : SL(2, ℤ)}
    (hg : g ∈ CongruenceSubgroup.Gamma 2) (z : ℍ) :
    canonicalLambdaPunctured (g • z) =
      canonicalLambdaPunctured z := by
  have hred : reduceModTwo g = 1 := by
    simpa only [reduceModTwo] using
      (CongruenceSubgroup.Gamma_mem'.mp hg)
  rw [canonicalLambdaPunctured_smul, hred, one_smul]

/-- The ambient-complex form of level-two invariance. -/
theorem canonicalLambda_smul_of_mem_Gamma_two
    {g : SL(2, ℤ)}
    (hg : g ∈ CongruenceSubgroup.Gamma 2) (z : ℍ) :
    canonicalLambda (g • z) = canonicalLambda z := by
  exact congrArg Subtype.val
    (canonicalLambdaPunctured_smul_of_mem_Gamma_two hg z)

end

end HGAS.Modular
