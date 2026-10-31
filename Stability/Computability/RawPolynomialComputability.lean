import Stability.Computability.RawGridCertificate

/-!
# Uniform computability of raw sparse arithmetic

Every dimension argument in this file is input data. The proofs use
primitive recursion on natural numbers and lists; no fixed-dimension
computability theorem is promoted to a uniform assertion.
-/

namespace Stability

open HGAS

-- Register the function property locally, so automation affects only
-- these proofs and leaves the imported computability API unchanged.
attribute [local fun_prop] Primrec Primrec.id Primrec.const Primrec.fst Primrec.snd
attribute [local fun_prop] Primrec.comp Primrec.pair Primrec.list_range Primrec.list_length

namespace RawCodePrimrec

@[local fun_prop] theorem natAdd : Primrec (fun q : ℕ × ℕ ↦ q.1 + q.2) := Primrec.nat_add
@[local fun_prop] theorem natMul : Primrec (fun q : ℕ × ℕ ↦ q.1 * q.2) := Primrec.nat_mul
@[local fun_prop] theorem natSub : Primrec (fun q : ℕ × ℕ ↦ q.1 - q.2) := Primrec.nat_sub
@[local fun_prop] theorem natMod : Primrec (fun q : ℕ × ℕ ↦ q.1 % q.2) := Primrec.nat_mod
@[local fun_prop] theorem boolAnd : Primrec (fun q : Bool × Bool ↦ q.1 && q.2) := Primrec.and
@[local fun_prop] theorem boolOr : Primrec (fun q : Bool × Bool ↦ q.1 || q.2) := Primrec.or
attribute [local fun_prop] Primrec.not

@[local fun_prop] theorem ratAdd :
    Primrec (fun q : RationalCode × RationalCode ↦ RationalCode.add q.1 q.2) :=
  RationalCode.add_primrec
@[local fun_prop] theorem ratMul :
    Primrec (fun q : RationalCode × RationalCode ↦ RationalCode.mul q.1 q.2) :=
  RationalCode.mul_primrec
@[local fun_prop] theorem ratEqual :
    Primrec (fun q : RationalCode × RationalCode ↦ RationalCode.equal q.1 q.2) :=
  RationalCode.equal_primrec
@[local fun_prop] theorem ratPow :
    Primrec (fun q : RationalCode × ℕ ↦ RationalCode.pow q.1 q.2) := RationalCode.pow_primrec
@[local fun_prop] theorem ratLt :
    Primrec (fun q : RationalCode × RationalCode ↦ RationalCode.lt q.1 q.2) :=
  RationalCode.lt_primrec
attribute [local fun_prop] RationalCode.neg_primrec RationalCode.abs_primrec
attribute [local fun_prop] RationalCode.ofNat_primrec RationalCode.unitFraction_primrec

variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]

@[local fun_prop] theorem listGetD (d : α) :
    Primrec (fun q : List α × ℕ ↦ q.1.getD q.2 d) := Primrec.list_getD d

@[local fun_prop] theorem listCons :
    Primrec (fun q : α × List α ↦ q.1 :: q.2) := Primrec.list_cons

@[local fun_prop] theorem listAppend :
    Primrec (fun q : List α × List α ↦ q.1 ++ q.2) := Primrec.list_append

@[local fun_prop] theorem beq [DecidableEq α] :
    Primrec (fun q : α × α ↦ q.1 == q.2) := Primrec.beq

@[local fun_prop] theorem decideEq [DecidableEq α] :
    Primrec (fun q : α × α ↦ decide (q.1 = q.2)) := Primrec.eq.decide

@[local fun_prop] theorem decideLt :
    Primrec (fun q : ℕ × ℕ ↦ decide (q.1 < q.2)) := Primrec.nat_lt.decide

@[local fun_prop] theorem iteEq [DecidableEq β] {f g : α → β} {u v : α → γ}
    (hf : Primrec f) (hg : Primrec g) (hu : Primrec u) (hv : Primrec v) :
    Primrec (fun a ↦ if f a = g a then u a else v a) :=
  Primrec.ite (Primrec.eq.comp hf hg) hu hv

theorem listMap {f : α → List β} {g : α → β → γ}
    (hf : Primrec f) (hg : Primrec (fun q : α × β ↦ g q.1 q.2)) :
    Primrec (fun a ↦ (f a).map (g a)) := Primrec.list_map hf hg

theorem listFlatMap {f : α → List β} {g : α → β → List γ}
    (hf : Primrec f) (hg : Primrec (fun q : α × β ↦ g q.1 q.2)) :
    Primrec (fun a ↦ (f a).flatMap (g a)) := Primrec.list_flatMap hf hg

theorem listFoldr {f : α → List β} {g : α → γ} {h : α → β × γ → γ}
    (hf : Primrec f) (hg : Primrec g)
    (hh : Primrec (fun q : α × (β × γ) ↦ h q.1 q.2)) :
    Primrec (fun a ↦ (f a).foldr (fun b c ↦ h a (b, c)) (g a)) :=
  Primrec.list_foldr hf hg hh

theorem listAll {f : α → List β} {g : α → β → Bool}
    (hf : Primrec f) (hg : Primrec (fun q : α × β ↦ g q.1 q.2)) :
    Primrec (fun a ↦ (f a).all (g a)) := by
  have h := listFoldr (h := fun a bc ↦ g a bc.1 && bc.2) hf (Primrec.const true)
    (Primrec.and.comp (hg.comp (Primrec.pair Primrec.fst
      (Primrec.fst.comp Primrec.snd))) (Primrec.snd.comp Primrec.snd))
  exact h.of_eq fun a ↦ by
    induction f a with
    | nil => rfl
    | cons b l ih => simp [ih]

@[local fun_prop] theorem listSum : Primrec (List.sum : List ℕ → ℕ) := by
  have h := listFoldr (h := fun (_ : List ℕ) bc ↦ bc.1 + bc.2)
    (Primrec.id : Primrec (id : List ℕ → _)) (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact h.of_eq fun l ↦ by induction l <;> simp_all

theorem listDedup [DecidableEq α] : Primrec (@List.dedup α _) := by
  have hmem : PrimrecPred (fun q : α × List α ↦ q.1 ∈ q.2) :=
    ((PrimrecRel.exists_mem_list (Primrec.eq : PrimrecRel (@Eq α))).comp
      Primrec.snd Primrec.fst).of_eq fun q ↦ by simp
  have hstep : Primrec₂ (fun (_ : List α) (q : α × List α × List α) ↦
      if q.1 ∈ q.2.1 then q.2.2 else q.1 :: q.2.2) :=
    Primrec.ite (hmem.comp (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact (Primrec.list_rec Primrec.id (Primrec.const []) hstep).of_eq fun l ↦ by
    induction l with
    | nil => rfl
    | cons a l ih =>
        simp only [id_eq]
        rw [List.dedup_cons]
        split <;> simp_all

end RawCodePrimrec

open RawCodePrimrec

attribute [local fun_prop] natAdd natMul natSub natMod boolAnd boolOr Primrec.not
attribute [local fun_prop] ratAdd ratMul ratEqual ratPow ratLt listGetD listCons listAppend
attribute [local fun_prop] beq decideEq decideLt listSum
attribute [local fun_prop] RationalCode.neg_primrec RationalCode.abs_primrec
attribute [local fun_prop] RationalCode.ofNat_primrec RationalCode.unitFraction_primrec

namespace RawExponentCode

@[local fun_prop] theorem zero_primrec : Primrec zero := by
  unfold zero
  apply listMap <;> fun_prop

@[local fun_prop] theorem add_primrec :
    Primrec (fun q : ℕ × (RawExponentCode × RawExponentCode) ↦ add q.1 q.2.1 q.2.2) := by
  unfold add
  apply listMap <;> fun_prop

@[local fun_prop] theorem predAt_primrec :
    Primrec (fun q : ℕ × (ℕ × RawExponentCode) ↦ predAt q.1 q.2.1 q.2.2) := by
  unfold predAt
  apply listMap
  · fun_prop
  · apply iteEq <;> fun_prop

@[local fun_prop] theorem variablePower_primrec :
    Primrec (fun q : ℕ × (ℕ × ℕ) ↦ variablePower q.1 q.2.1 q.2.2) := by
  unfold variablePower
  apply listMap
  · fun_prop
  · apply iteEq <;> fun_prop

end RawExponentCode

attribute [local fun_prop] RawExponentCode.zero_primrec RawExponentCode.add_primrec
attribute [local fun_prop] RawExponentCode.predAt_primrec RawExponentCode.variablePower_primrec

namespace RawPolynomialCode

@[local fun_prop] theorem wellFormed_primrec :
    Primrec (fun q : ℕ × RawPolynomialCode ↦ wellFormed q.1 q.2) := by
  unfold wellFormed
  apply listAll <;> fun_prop

@[local fun_prop] theorem coefficient_primrec :
    Primrec (fun q : RawExponentCode × RawPolynomialCode ↦ coefficient q.1 q.2) := by
  unfold coefficient
  apply listFoldr (f := fun q : RawExponentCode × RawPolynomialCode ↦ q.2)
    (g := fun _ ↦ RationalCode.zero)
    (h := fun (q : RawExponentCode × RawPolynomialCode)
      (t : (RawExponentCode × RationalCode) × RationalCode) ↦
        if t.1.1 = q.1 then RationalCode.add t.1.2 t.2 else t.2)
  · fun_prop
  · fun_prop
  · apply iteEq <;> fun_prop

@[local fun_prop] theorem homogeneous_primrec :
    Primrec (fun q : ℕ × RawPolynomialCode ↦ homogeneous q.1 q.2) := by
  unfold homogeneous
  apply listAll
  · apply listMap <;> fun_prop
  · apply Primrec.or.comp
    · fun_prop
    · exact (Primrec.eq.comp (listSum.comp Primrec.snd)
        (Primrec.fst.comp Primrec.fst)).decide

@[local fun_prop] theorem constant_primrec :
    Primrec (fun q : ℕ × RationalCode ↦ constant q.1 q.2) := by
  unfold constant
  fun_prop

@[local fun_prop] theorem neg_primrec : Primrec neg := by
  unfold neg
  apply listMap <;> fun_prop

@[local fun_prop] theorem mulByTerm_primrec :
    Primrec (fun q : ℕ × ((RawExponentCode × RationalCode) × RawPolynomialCode) ↦
      mulByTerm q.1 q.2.1 q.2.2) := by
  unfold mulByTerm
  apply listMap <;> fun_prop

@[local fun_prop] theorem mul_primrec :
    Primrec (fun q : ℕ × (RawPolynomialCode × RawPolynomialCode) ↦ mul q.1 q.2.1 q.2.2) := by
  unfold mul
  apply listFlatMap <;> fun_prop

@[local fun_prop] theorem pderivTerm_primrec :
    Primrec (fun q : ℕ × (ℕ × (RawExponentCode × RationalCode)) ↦
      pderivTerm q.1 q.2.1 q.2.2) := by
  unfold pderivTerm
  apply iteEq <;> fun_prop

@[local fun_prop] theorem pderiv_primrec :
    Primrec (fun q : ℕ × (ℕ × RawPolynomialCode) ↦ pderiv q.1 q.2.1 q.2.2) := by
  unfold pderiv
  apply listFlatMap <;> fun_prop

@[local fun_prop] theorem rhoCode_primrec : Primrec rhoCode := by
  unfold rhoCode
  apply listMap <;> fun_prop

@[local fun_prop] theorem varCode_primrec :
    Primrec (fun q : ℕ × ℕ ↦ varCode q.1 q.2) := by
  unfold varCode
  fun_prop

@[local fun_prop] theorem gradientDotField_primrec :
    Primrec (fun q : ℕ × (RawPolynomialCode × RawPolynomialFieldCode) ↦
      gradientDotField q.1 q.2.1 q.2.2) := by
  unfold gradientDotField
  apply listFlatMap <;> fun_prop

@[local fun_prop] theorem radialDotField_primrec :
    Primrec (fun q : ℕ × RawPolynomialFieldCode ↦ radialDotField q.1 q.2) := by
  unfold radialDotField
  apply listFlatMap <;> fun_prop

@[local fun_prop] theorem rationalLyapunovNumerator_primrec :
    Primrec (fun q : ℕ × (RawPolynomialFieldCode × (RawPolynomialCode × ℕ)) ↦
      rationalLyapunovNumerator q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold rationalLyapunovNumerator
  fun_prop

end RawPolynomialCode

attribute [local fun_prop] RawPolynomialCode.wellFormed_primrec

namespace RawPolynomialFieldCode

theorem wellFormed_primrec :
    Primrec (fun q : ℕ × RawPolynomialFieldCode ↦ wellFormed q.1 q.2) := by
  unfold wellFormed
  apply Primrec.and.comp
  · fun_prop
  · apply listAll <;> fun_prop

end RawPolynomialFieldCode

end Stability
