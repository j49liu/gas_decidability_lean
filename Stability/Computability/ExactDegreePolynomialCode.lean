import Stability.Computability.ExactPolynomialLanguages
import HGAS.Propagation.DegreePaddingCode

/-!
# Adjoining a polynomial factor of exact degree

For a field `F` in `n` variables, the compiler emits
`(F(x), -w^3, -z^3 + w^d)`. The last coordinate forces exact degree `d`
whenever the source coordinates have degree at most three and `d ≥ 3`.
This remains true for a zero source field and for even target degrees.
-/

namespace Stability

open HGAS MvPolynomial

namespace ExactDegreeCode

abbrev wIndex (n : ℕ) : Fin (n + 2) := DegreePaddingCode.sinkIndex n 2 0
abbrev zIndex (n : ℕ) : Fin (n + 2) := DegreePaddingCode.sinkIndex n 2 1

theorem zIndex_ne_wIndex (n : ℕ) : zIndex n ≠ wIndex n := by
  intro h
  have h' := congrArg finSumFinEquiv.symm h
  simp at h'

/-- The last coordinate has a noncancelling pure power of the first new
variable, independent of the source field. -/
def carrierLastCode (n d : ℕ) : PolynomialCode (n + 2) :=
  PolynomialCode.add
    (PolynomialCode.neg (PolynomialCode.pow (PolynomialCode.varCode (zIndex n)) 3))
    (PolynomialCode.pow (PolynomialCode.varCode (wIndex n)) d)

/-- Append the exact-degree factor to a raw polynomial field code. -/
def appendDegreeCarrierCode (n d : ℕ) (F : PolynomialFieldCode n) :
    PolynomialFieldCode (n + 2) := fun q ↦
  match finSumFinEquiv.symm q with
  | Sum.inl i => PolynomialCode.dimensionEmbed 2 (F i)
  | Sum.inr r => if r = 0 then
      PolynomialCode.neg (PolynomialCode.pow (PolynomialCode.varCode (wIndex n)) 3)
    else carrierLastCode n d

@[simp]
theorem appendDegreeCarrierCode_base (n d : ℕ) (F : PolynomialFieldCode n) (i : Fin n) :
    appendDegreeCarrierCode n d F (DegreePaddingCode.baseIndex n 2 i) =
      PolynomialCode.dimensionEmbed 2 (F i) := by
  simp [appendDegreeCarrierCode]

@[simp]
theorem appendDegreeCarrierCode_w (n d : ℕ) (F : PolynomialFieldCode n) :
    appendDegreeCarrierCode n d F (wIndex n) =
      PolynomialCode.neg (PolynomialCode.pow (PolynomialCode.varCode (wIndex n)) 3) := by
  simp [appendDegreeCarrierCode]

@[simp]
theorem appendDegreeCarrierCode_z (n d : ℕ) (F : PolynomialFieldCode n) :
    appendDegreeCarrierCode n d F (zIndex n) = carrierLastCode n d := by
  simp [appendDegreeCarrierCode]

theorem appendDegreeCarrierCode_primrec (n d : ℕ) :
    Primrec (appendDegreeCarrierCode n d) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro q
  cases hq : finSumFinEquiv.symm q with
  | inl i =>
    exact ((PolynomialCode.dimensionEmbed_primrec n 2).comp
      (Primrec.fin_app.comp Primrec.id (Primrec.const i))).of_eq
        fun F ↦ by simp [appendDegreeCarrierCode, hq]
  | inr r =>
    exact (Primrec.const (if r = 0 then
      PolynomialCode.neg (PolynomialCode.pow (PolynomialCode.varCode (wIndex n)) 3)
      else carrierLastCode n d)).of_eq fun F ↦ by simp [appendDegreeCarrierCode, hq]

@[simp]
theorem decode_carrierLastCode (n d : ℕ) :
    PolynomialCode.decode (carrierLastCode n d) =
      -(X (zIndex n) ^ 3 : MvPolynomial (Fin (n + 2)) ℚ) + X (wIndex n) ^ d := by
  simp [carrierLastCode]

theorem totalDegree_carrierLastCode (n d : ℕ) (hd : 3 ≤ d) :
    (PolynomialCode.decode (carrierLastCode n d)).totalDegree = d := by
  rw [decode_carrierLastCode]
  apply le_antisymm
  · exact (totalDegree_add _ _).trans (by simp [totalDegree_neg, max_eq_right hd])
  · have hne : Finsupp.single (zIndex n) 3 ≠ Finsupp.single (wIndex n) d := by
      intro h
      have h' := DFunLike.congr_fun h (zIndex n)
      simp [Ne.symm (zIndex_ne_wIndex n)] at h'
    have hc : coeff (Finsupp.single (wIndex n) d)
        (-(X (zIndex n) ^ 3 : MvPolynomial (Fin (n + 2)) ℚ) + X (wIndex n) ^ d) = 1 := by
      simp [coeff_X_pow, hne]
    have hs := mem_support_iff.mpr (by rw [hc]; exact one_ne_zero)
    simpa using le_totalDegree hs

/-- The exact-degree assertion is about decoded polynomials, including
possible cancellation in the input source code. -/
theorem appendDegreeCarrierCode_exactDegree
    (n d : ℕ) (F : PolynomialFieldCode n) (hd : 3 ≤ d)
    (hF : ∀ i, (PolynomialCode.decode (F i)).totalDegree ≤ 3) :
    PolynomialFieldExactDegree (n + 2) d (appendDegreeCarrierCode n d F) := by
  refine ⟨?_, zIndex n, ?_⟩
  · intro q
    obtain ⟨i | r, rfl⟩ := finSumFinEquiv.surjective q
    · change (PolynomialCode.decode
        (appendDegreeCarrierCode n d F (DegreePaddingCode.baseIndex n 2 i))).totalDegree ≤ d
      rw [appendDegreeCarrierCode_base, PolynomialCode.decode_dimensionEmbed]
      exact (totalDegree_rename_le _ _).trans ((hF i).trans hd)
    · fin_cases r
      · change (PolynomialCode.decode (appendDegreeCarrierCode n d F (wIndex n))).totalDegree ≤ d
        simpa [PolynomialCode.decode_neg_code, PolynomialCode.decode_pow_code,
          PolynomialCode.decode_varCode, totalDegree_neg] using hd
      · change (PolynomialCode.decode (appendDegreeCarrierCode n d F (zIndex n))).totalDegree ≤ d
        rw [appendDegreeCarrierCode_z, totalDegree_carrierLastCode n d hd]
  · rw [appendDegreeCarrierCode_z, totalDegree_carrierLastCode n d hd]

/-- Identify flat target coordinates with the source and two scalar
auxiliary coordinates. -/
noncomputable def splitEquiv (n : ℕ) :
    (Fin (n + 2) → ℝ) ≃L[ℝ] ((Fin n → ℝ) × (ℝ × ℝ)) :=
  (DegreePaddingCode.splitEquiv n 2).trans
    ((ContinuousLinearEquiv.refl ℝ (Fin n → ℝ)).prodCongr
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ))

@[simp]
theorem splitEquiv_fst (n : ℕ) (x : Fin (n + 2) → ℝ) (i : Fin n) :
    (splitEquiv n x).1 i = x (DegreePaddingCode.baseIndex n 2 i) := rfl

@[simp]
theorem splitEquiv_w (n : ℕ) (x : Fin (n + 2) → ℝ) :
    (splitEquiv n x).2.1 = x (wIndex n) := rfl

@[simp]
theorem splitEquiv_z (n : ℕ) (x : Fin (n + 2) → ℝ) :
    (splitEquiv n x).2.2 = x (zIndex n) := rfl

@[simp]
theorem splitEquiv_symm_base (n : ℕ) (p : (Fin n → ℝ) × (ℝ × ℝ)) (i : Fin n) :
    (splitEquiv n).symm p (DegreePaddingCode.baseIndex n 2 i) = p.1 i := by
  have h := splitEquiv_fst n ((splitEquiv n).symm p) i
  simpa using h.symm

@[simp]
theorem splitEquiv_symm_w (n : ℕ) (p : (Fin n → ℝ) × (ℝ × ℝ)) :
    (splitEquiv n).symm p (wIndex n) = p.2.1 := by
  have h := splitEquiv_w n ((splitEquiv n).symm p)
  simpa using h.symm

@[simp]
theorem splitEquiv_symm_z (n : ℕ) (p : (Fin n → ℝ) × (ℝ × ℝ)) :
    (splitEquiv n).symm p (zIndex n) = p.2.2 := by
  have h := splitEquiv_z n ((splitEquiv n).symm p)
  simpa using h.symm

@[simp]
theorem realize_appendDegreeCarrierCode_base
    (n d : ℕ) (F : PolynomialFieldCode n) (x : Fin (n + 2) → ℝ) (i : Fin n) :
    PolynomialFieldCode.realize (appendDegreeCarrierCode n d F) x
        (DegreePaddingCode.baseIndex n 2 i) =
      PolynomialFieldCode.realize F (splitEquiv n x).1 i := by
  rw [PolynomialFieldCode.realize_apply, appendDegreeCarrierCode_base,
    DegreePaddingCode.eval₂Hom_dimensionEmbed]
  rfl

@[simp]
theorem realize_appendDegreeCarrierCode_w
    (n d : ℕ) (F : PolynomialFieldCode n) (x : Fin (n + 2) → ℝ) :
    PolynomialFieldCode.realize (appendDegreeCarrierCode n d F) x (wIndex n) =
      -(x (wIndex n)) ^ 3 := by
  simp [PolynomialFieldCode.realize_apply]

@[simp]
theorem realize_appendDegreeCarrierCode_z
    (n d : ℕ) (F : PolynomialFieldCode n) (x : Fin (n + 2) → ℝ) :
    PolynomialFieldCode.realize (appendDegreeCarrierCode n d F) x (zIndex n) =
      -(x (zIndex n)) ^ 3 + (x (wIndex n)) ^ d := by
  simp [PolynomialFieldCode.realize_apply]

/-- Semantic specification of the compiler: the appended coordinates
form an independent planar factor. -/
theorem realize_appendDegreeCarrierCode
    (n d : ℕ) (F : PolynomialFieldCode n) :
    PolynomialFieldCode.realize (appendDegreeCarrierCode n d F) =
      conjugateField (splitEquiv n).symm
        (productField (PolynomialFieldCode.realize F)
          (fun p : ℝ × ℝ ↦ (-p.1 ^ 3, -p.2 ^ 3 + p.1 ^ d))) := by
  funext x q
  obtain ⟨i | r, rfl⟩ := finSumFinEquiv.surjective q
  · change PolynomialFieldCode.realize (appendDegreeCarrierCode n d F) x
      (DegreePaddingCode.baseIndex n 2 i) =
      (splitEquiv n).symm _ (DegreePaddingCode.baseIndex n 2 i)
    rw [splitEquiv_symm_base, realize_appendDegreeCarrierCode_base]
    rfl
  · fin_cases r
    · change PolynomialFieldCode.realize (appendDegreeCarrierCode n d F) x (wIndex n) =
        (splitEquiv n).symm _ (wIndex n)
      rw [splitEquiv_symm_w, realize_appendDegreeCarrierCode_w]
      rfl
    · change PolynomialFieldCode.realize (appendDegreeCarrierCode n d F) x (zIndex n) =
        (splitEquiv n).symm _ (zIndex n)
      rw [splitEquiv_symm_z, realize_appendDegreeCarrierCode_z]
      rfl

/-- At every positive target degree, the compiler preserves an equilibrium
at the origin. -/
theorem appendDegreeCarrierCode_zero
    (n d : ℕ) (F : PolynomialFieldCode n) (hd : 0 < d)
    (hF : PolynomialFieldCode.realize F 0 = 0) :
    PolynomialFieldCode.realize (appendDegreeCarrierCode n d F) 0 = 0 := by
  rw [realize_appendDegreeCarrierCode]
  simp [conjugateField, productField, hF, Nat.ne_of_gt hd]

end ExactDegreeCode
end Stability
