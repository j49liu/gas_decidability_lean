import Stability.Computability.PolynomialFractionCode
import Stability.Simulation.PositiveDenominatorClearing

/-!
# Effective joint denominator clearing

The common multiplier and every cleared numerator are the products used
by the actual construction. A fixed finite family order is part of the
compiler; the resulting polynomials are independent of that order.
-/

namespace Stability.PolynomialClearingCode

open HGAS Simulation PolynomialCodeOperations PolynomialFractionCode

noncomputable section

variable {σ ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

def denominator (F : ι → PolynomialFractionCode n) : PolynomialCode n :=
  product (Finset.univ.toList.map fun i ↦ (F i).2)

def numerator (F : ι → PolynomialFractionCode n) (i : ι) : PolynomialCode n :=
  PolynomialCode.mul (F i).1 (product ((Finset.univ.erase i).toList.map fun j ↦ (F j).2))

omit [DecidableEq ι] in
theorem decode_denominator (e : σ → Fin n) (F : ι → PolynomialFractionCode n)
    (W : ι → PolynomialFraction σ)
    (hF : ∀ i, PolynomialFractionCode.decode (F i) = PolynomialFractionCode.rename e (W i)) :
    PolynomialCode.decode (denominator F) =
      MvPolynomial.rename e (PolynomialFraction.commonDenominator W) := by
  have hden i := congrArg PolynomialFraction.denominator (hF i)
  dsimp only [PolynomialFractionCode.decode, PolynomialFractionCode.rename] at hden
  simp [denominator, hden, PolynomialFraction.commonDenominator]

theorem decode_numerator (e : σ → Fin n) (F : ι → PolynomialFractionCode n)
    (W : ι → PolynomialFraction σ)
    (hF : ∀ i, PolynomialFractionCode.decode (F i) = PolynomialFractionCode.rename e (W i))
    (i : ι) : PolynomialCode.decode (numerator F i) =
      MvPolynomial.rename e (PolynomialFraction.clearedNumerator W i) := by
  have hden i := congrArg PolynomialFraction.denominator (hF i)
  have hnum i := congrArg PolynomialFraction.numerator (hF i)
  dsimp only [PolynomialFractionCode.decode, PolynomialFractionCode.rename] at hden hnum
  simp [numerator, hden, hnum, PolynomialFraction.clearedNumerator]

private theorem product_map_primrec {α β : Type*} [Primcodable α] (indices : List β)
    (F : α → β → PolynomialCode n) (hF : ∀ i, Primrec (fun a ↦ F a i)) :
    Primrec (fun a ↦ product (indices.map (F a))) := by
  induction indices with
  | nil => exact Primrec.const _
  | cons i indices ih => exact PolynomialCode.mul_primrec.comp (hF i) ih

omit [DecidableEq ι] in
theorem denominator_primrec {α : Type*} [Primcodable α]
    (F : α → ι → PolynomialFractionCode n) (hF : ∀ i, Primrec (fun a ↦ F a i)) :
    Primrec (fun a ↦ denominator (F a)) :=
  product_map_primrec _ _ (fun i ↦ Primrec.snd.comp (hF i))

theorem numerator_primrec {α : Type*} [Primcodable α]
    (F : α → ι → PolynomialFractionCode n) (hF : ∀ i, Primrec (fun a ↦ F a i)) (i : ι) :
    Primrec (fun a ↦ numerator (F a) i) :=
  PolynomialCode.mul_primrec.comp (Primrec.fst.comp (hF i))
    (product_map_primrec _ _ (fun j ↦ Primrec.snd.comp (hF j)))

omit [DecidableEq ι] in
theorem commonDenominator_comp_equiv {κ : Type*} [Fintype κ]
    (r : ι ≃ κ) (W : κ → PolynomialFraction σ) :
    PolynomialFraction.commonDenominator (fun i ↦ W (r i)) =
      PolynomialFraction.commonDenominator W :=
  Equiv.prod_comp r (fun i ↦ (W i).denominator)

theorem clearedNumerator_comp_equiv {κ : Type*} [Fintype κ] [DecidableEq κ]
    (r : ι ≃ κ) (W : κ → PolynomialFraction σ) (i : ι) :
    PolynomialFraction.clearedNumerator (fun j ↦ W (r j)) i =
      PolynomialFraction.clearedNumerator W (r i) := by
  unfold PolynomialFraction.clearedNumerator
  congr 1
  apply Finset.prod_bij (fun j _ ↦ r j)
  · intro j hj
    simpa only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, EmbeddingLike.apply_eq_iff_eq]
      using hj
  · intro a _ b _ hab
    exact r.injective hab
  · intro b hb
    refine ⟨r.symm b, ?_, r.apply_symm_apply b⟩
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hb ⊢
    intro h
    exact hb (by simpa [h] using r.apply_symm_apply b |>.symm)
  · intro j _
    rfl

end

end Stability.PolynomialClearingCode
