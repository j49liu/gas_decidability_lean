import Stability.Computability.FormulaRadicalFamilyCode
import Stability.Simulation.FiniteRadicalFamily

/-!
# Radical codes in a fixed finite extended coordinate space

This specializes the exact extraction homomorphism to the actual
finite-root restriction. Out-of-range roots map to zero, including when
the fixed root count is zero. The coordinate equivalence is a fixed
compiler parameter and does not depend on the register input.
-/

namespace Stability.FormulaTemplate

open HGAS Simulation

variable {α σ : Type*} {n J : ℕ}

def finiteRootCode (e : (σ ⊕ Fin J) ≃ Fin n) (j : ℕ) : PolynomialCode n :=
  if h : j < J then PolynomialCode.varCode (e (.inr ⟨j, h⟩)) else PolynomialCode.zero

noncomputable def finiteTargetHom (e : (σ ⊕ Fin J) ≃ Fin n) :
    MvPolynomial (σ ⊕ ℕ) ℚ →ₐ[ℚ] MvPolynomial (Fin n) ℚ :=
  (MvPolynomial.rename e).comp (MvPolynomial.bind₁ (RadicalProgram.finiteVariable J))

@[simp]
theorem finiteTargetHom_X_base (e : (σ ⊕ Fin J) ≃ Fin n) (i : σ) :
    finiteTargetHom e (MvPolynomial.X (.inl i)) = MvPolynomial.X (e (.inl i)) := by
  simp [finiteTargetHom, RadicalProgram.finiteVariable]

@[simp]
theorem finiteTargetHom_X_root (e : (σ ⊕ Fin J) ≃ Fin n) (j : ℕ) :
    finiteTargetHom e (MvPolynomial.X (.inr j)) = PolynomialCode.decode (finiteRootCode e j) := by
  by_cases h : j < J <;>
    simp [finiteTargetHom, finiteRootCode, RadicalProgram.finiteVariable, h]

theorem finiteTargetHom_basePolynomial (e : (σ ⊕ Fin J) ≃ Fin n) (p : MvPolynomial σ ℚ) :
    finiteTargetHom e (RadicalProgram.basePolynomial p) =
      MvPolynomial.rename (fun i ↦ e (.inl i)) p := by
  have h : (finiteTargetHom e).comp (MvPolynomial.rename Sum.inl) =
      MvPolynomial.rename (fun i ↦ e (.inl i)) := by
    ext i
    simp
  exact congrArg (fun f : MvPolynomial σ ℚ →ₐ[ℚ] MvPolynomial (Fin n) ℚ ↦ f p) h

def finiteFamilyCode (e : (σ ⊕ Fin J) ≃ Fin n) (L : α → PolynomialCode n)
    (es : List (FormulaTemplate α σ)) : α → FamilyExpansionCode n :=
  extractFamilyCode (fun i ↦ e (.inl i)) (finiteRootCode e) L es 0

theorem finiteFamilyCode_primrec [Primcodable α] (e : (σ ⊕ Fin J) ≃ Fin n)
    (L : α → PolynomialCode n) (hL : Primrec L) (es : List (FormulaTemplate α σ))
    (he : ∀ f ∈ es, PrimitiveConstants f) : Primrec (finiteFamilyCode e L es) :=
  extractFamilyCode_primrec _ _ L hL es he 0

/-- Exact finite restriction before selecting individual radicands or outputs. -/
theorem decode_finiteFamilyCode (e : (σ ⊕ Fin J) ≃ Fin n)
    (L : α → PolynomialCode n) (P : α → MvPolynomial σ ℚ)
    (hL : ∀ x, PolynomialCode.decode (L x) = MvPolynomial.rename (fun i ↦ e (.inl i)) (P x))
    (es : List (FormulaTemplate α σ)) (x : α) :
    let E := finiteFamilyCode e L es x
    let F := AbsFormula.extractRadicalFamily (P x) (es.map (instantiate · x)) 0
    E.1.map PolynomialCode.decode =
      F.program.map (fun p ↦ MvPolynomial.rename e (RadicalProgram.finitePolynomial J p)) ∧
      E.2.map (fun f ↦ (PolynomialCode.decode f.1, f.2)) =
        F.results.map (fun f ↦
          (MvPolynomial.rename e (RadicalProgram.finitePolynomial J f.numerator), f.exponent)) :=
  decode_extractFamilyCode _ _ L P (finiteTargetHom e)
    (finiteTargetHom_X_base e) (finiteTargetHom_X_root e)
    (fun x ↦ (hL x).trans (finiteTargetHom_basePolynomial e (P x)).symm) es 0 x

/-- A total raw-code selector; valid generated positions are identified below. -/
def radicandCode (e : (σ ⊕ Fin J) ≃ Fin n) (L : α → PolynomialCode n)
    (es : List (FormulaTemplate α σ)) (j : Fin J) (x : α) : PolynomialCode n :=
  (finiteFamilyCode e L es x).1.getD j.val PolynomialCode.zero

def outputCode (e : (σ ⊕ Fin J) ≃ Fin n) (L : α → PolynomialCode n)
    (es : List (FormulaTemplate α σ)) (i : Fin es.length) (x : α) : PowerFractionCode n :=
  (finiteFamilyCode e L es x).2.getD i.val (PolynomialCode.zero, 0)

private theorem map_getD_of_map_eq {A B C : Type*} (f : A → C) (g : B → C)
    (a : List A) (b : List B) (da : A) (db : B) (hdefault : f da = g db)
    (h : a.map f = b.map g) (i : ℕ) : f (a.getD i da) = g (b.getD i db) := by
  rw [← List.getD_map a da f, h, hdefault, List.getD_map b db g]

/-- Every selected radicand is the actual extracted polynomial after
finite-root restriction; the equality also respects the total fallback. -/
theorem decode_radicandCode (e : (σ ⊕ Fin J) ≃ Fin n)
    (L : α → PolynomialCode n) (P : α → MvPolynomial σ ℚ)
    (hL : ∀ x, PolynomialCode.decode (L x) = MvPolynomial.rename (fun i ↦ e (.inl i)) (P x))
    (es : List (FormulaTemplate α σ)) (j : Fin J) (x : α) :
    PolynomialCode.decode (radicandCode e L es j x) =
      MvPolynomial.rename e (RadicalProgram.finitePolynomial J
        ((AbsFormula.extractRadicalFamily (P x) (es.map (instantiate · x)) 0).program.getD
          j.val 0)) := by
  exact map_getD_of_map_eq PolynomialCode.decode (finiteTargetHom e) _ _
    PolynomialCode.zero 0 (by simp)
    (decode_finiteFamilyCode e L P hL es x).1 j.val

/-- Stored output numerators and exponents agree, not merely their values. -/
theorem decode_outputCode (e : (σ ⊕ Fin J) ≃ Fin n)
    (L : α → PolynomialCode n) (P : α → MvPolynomial σ ℚ)
    (hL : ∀ x, PolynomialCode.decode (L x) = MvPolynomial.rename (fun i ↦ e (.inl i)) (P x))
    (es : List (FormulaTemplate α σ)) (i : Fin es.length) (x : α) :
    let f := (AbsFormula.extractRadicalFamily (P x)
      (es.map (instantiate · x)) 0).results.getD i.val ⟨0, 0⟩
    (PolynomialCode.decode (outputCode e L es i x).1, (outputCode e L es i x).2) =
      (MvPolynomial.rename e (RadicalProgram.finitePolynomial J f.numerator), f.exponent) := by
  exact map_getD_of_map_eq (fun f : PowerFractionCode n ↦ (PolynomialCode.decode f.1, f.2))
    (fun f : PowerFraction (σ ⊕ ℕ) ↦ (finiteTargetHom e f.numerator, f.exponent)) _ _
    (PolynomialCode.zero, 0) ⟨0, 0⟩ (by simp)
    (decode_finiteFamilyCode e L P hL es x).2 i.val

private theorem rename_finitePolynomial_cast {K : ℕ} (h : K = J)
    (p : RadicalProgram.Polynomial σ) :
    MvPolynomial.rename (Sum.map id (Fin.cast h)) (RadicalProgram.finitePolynomial K p) =
      RadicalProgram.finitePolynomial J p := by
  subst J
  have hid : Sum.map (id : σ → σ) (Fin.cast rfl : Fin K → Fin K) = id := by
    funext i
    cases i <;> rfl
  rw [hid, MvPolynomial.rename_id]
  rfl

/-- With the proved fixed root count, the code represents the actual
finite-family radicand in the fixed extended coordinate encoding. -/
theorem decode_radicandCode_eq_finiteRadicalFamily (e : (σ ⊕ Fin J) ≃ Fin n)
    (L : α → PolynomialCode n) (P : α → MvPolynomial σ ℚ)
    (hL : ∀ x, PolynomialCode.decode (L x) = MvPolynomial.rename (fun i ↦ e (.inl i)) (P x))
    (es : List (FormulaTemplate α σ)) (x : α)
    (hJ : (AbsFormula.finiteRadicalFamily (P x) (es.map (instantiate · x))).rootCount = J)
    (j : Fin J) :
    PolynomialCode.decode (radicandCode e L es j x) =
      MvPolynomial.rename (e ∘ Sum.map id (Fin.cast hJ))
        ((AbsFormula.finiteRadicalFamily (P x) (es.map (instantiate · x))).radicands
          (j.cast hJ.symm)) := by
  rw [decode_radicandCode e L P hL es j x]
  let E := AbsFormula.extractRadicalFamily (P x) (es.map (instantiate · x)) 0
  change E.program.length = J at hJ
  change MvPolynomial.rename e (RadicalProgram.finitePolynomial J
    (E.program.getD j.val 0)) =
      MvPolynomial.rename (e ∘ Sum.map id (Fin.cast hJ))
        (RadicalProgram.finitePolynomial E.program.length (E.program.get (j.cast hJ.symm)))
  have hget : E.program.getD j.val 0 = E.program.get (j.cast hJ.symm) :=
    List.getD_eq_get E.program 0 (j.cast hJ.symm)
  rw [hget, ← MvPolynomial.rename_rename, rename_finitePolynomial_cast hJ]

/-- The actual finite output fraction is preserved in the same fixed
coordinate encoding, including its unchanged denominator exponent. -/
theorem decode_outputCode_eq_finiteRadicalFamily (e : (σ ⊕ Fin J) ≃ Fin n)
    (L : α → PolynomialCode n) (P : α → MvPolynomial σ ℚ)
    (hL : ∀ x, PolynomialCode.decode (L x) = MvPolynomial.rename (fun i ↦ e (.inl i)) (P x))
    (es : List (FormulaTemplate α σ)) (x : α)
    (hJ : (AbsFormula.finiteRadicalFamily (P x) (es.map (instantiate · x))).rootCount = J)
    (i : Fin es.length) :
    let f := (AbsFormula.finiteRadicalFamily (P x)
      (es.map (instantiate · x))).outputs.getD i.val ⟨0, 0⟩
    (PolynomialCode.decode (outputCode e L es i x).1, (outputCode e L es i x).2) =
      (MvPolynomial.rename (e ∘ Sum.map id (Fin.cast hJ)) f.numerator, f.exponent) := by
  let E := AbsFormula.extractRadicalFamily (P x) (es.map (instantiate · x)) 0
  change E.program.length = J at hJ
  have hzero : AbsFormula.finiteFraction E.program.length
      (⟨0, 0⟩ : PowerFraction (σ ⊕ ℕ)) = ⟨0, 0⟩ := by
    simp [AbsFormula.finiteFraction, RadicalProgram.finitePolynomial]
  change _ = ((MvPolynomial.rename (e ∘ Sum.map id (Fin.cast hJ)))
    (((E.results.map (AbsFormula.finiteFraction E.program.length)).getD i.val ⟨0, 0⟩).numerator),
      ((E.results.map (AbsFormula.finiteFraction E.program.length)).getD i.val ⟨0, 0⟩).exponent)
  rw [← hzero, List.getD_map]
  dsimp only [AbsFormula.finiteFraction]
  rw [← MvPolynomial.rename_rename, rename_finitePolynomial_cast hJ]
  exact decode_outputCode e L P hL es i x

/-- A named actual formula list avoids unfolding large fixed templates
inside dependent root-index casts. -/
theorem decode_radicandCode_of_formulaList_eq (e : (σ ⊕ Fin J) ≃ Fin n)
    (L : α → PolynomialCode n) (P : α → MvPolynomial σ ℚ)
    (hL : ∀ x, PolynomialCode.decode (L x) = MvPolynomial.rename (fun i ↦ e (.inl i)) (P x))
    (es : List (FormulaTemplate α σ)) (x : α) (fs : List (AbsFormula σ))
    (hfs : es.map (instantiate · x) = fs)
    (hJ : (AbsFormula.finiteRadicalFamily (P x) fs).rootCount = J) (j : Fin J) :
    PolynomialCode.decode (radicandCode e L es j x) =
      MvPolynomial.rename (e ∘ Sum.map id (Fin.cast hJ))
        ((AbsFormula.finiteRadicalFamily (P x) fs).radicands (j.cast hJ.symm)) := by
  subst fs
  exact decode_radicandCode_eq_finiteRadicalFamily e L P hL es x hJ j

theorem decode_outputCode_of_formulaList_eq (e : (σ ⊕ Fin J) ≃ Fin n)
    (L : α → PolynomialCode n) (P : α → MvPolynomial σ ℚ)
    (hL : ∀ x, PolynomialCode.decode (L x) = MvPolynomial.rename (fun i ↦ e (.inl i)) (P x))
    (es : List (FormulaTemplate α σ)) (x : α) (fs : List (AbsFormula σ))
    (hfs : es.map (instantiate · x) = fs)
    (hJ : (AbsFormula.finiteRadicalFamily (P x) fs).rootCount = J) (i : Fin es.length) :
    let f := (AbsFormula.finiteRadicalFamily (P x) fs).outputs.getD i.val ⟨0, 0⟩
    (PolynomialCode.decode (outputCode e L es i x).1, (outputCode e L es i x).2) =
      (MvPolynomial.rename (e ∘ Sum.map id (Fin.cast hJ)) f.numerator, f.exponent) := by
  subst fs
  exact decode_outputCode_eq_finiteRadicalFamily e L P hL es x hJ i

theorem radicandCode_primrec [Primcodable α] (e : (σ ⊕ Fin J) ≃ Fin n)
    (L : α → PolynomialCode n) (hL : Primrec L) (es : List (FormulaTemplate α σ))
    (he : ∀ f ∈ es, PrimitiveConstants f) (j : Fin J) :
    Primrec (radicandCode e L es j) :=
  (Primrec.list_getD PolynomialCode.zero).comp
    (Primrec.fst.comp (finiteFamilyCode_primrec e L hL es he)) (Primrec.const j.val)

theorem outputCode_primrec [Primcodable α] (e : (σ ⊕ Fin J) ≃ Fin n)
    (L : α → PolynomialCode n) (hL : Primrec L) (es : List (FormulaTemplate α σ))
    (he : ∀ f ∈ es, PrimitiveConstants f) (i : Fin es.length) :
    Primrec (outputCode e L es i) :=
  (Primrec.list_getD (PolynomialCode.zero, 0)).comp
    (Primrec.snd.comp (finiteFamilyCode_primrec e L hL es he)) (Primrec.const i.val)

end Stability.FormulaTemplate
