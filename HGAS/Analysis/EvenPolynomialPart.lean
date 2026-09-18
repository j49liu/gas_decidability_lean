import HGAS.Analysis.RadialHomogenization
import HGAS.Algebra.HomogeneousEvaluation
import Mathlib.Tactic

/-!
# Even-total-degree part of a multivariate polynomial

A two-homogeneous function is even.  In the Bernstein approximation proof,
an arbitrary approximating polynomial `C` is therefore replaced by

```
(C(x) + C(-x)) / 2.
```

Algebraically this simply deletes all monomials of odd total degree.  The
definition below performs that deletion directly on the finite support.
This makes the parity data required by radial homogenization completely
explicit.
-/

namespace HGAS

open _root_.MvPolynomial
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- Retain exactly the monomials of even total degree. -/
def evenPolynomialPart (C : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  ∑ e ∈ C.support.filter (Even ∘ Finsupp.degree),
    monomial e (C.coeff e)

/-- Coefficients of the even part are the original coefficients in even
degree and zero in odd degree. -/
theorem coeff_evenPolynomialPart
    (C : MvPolynomial (Fin n) ℝ) (e : Fin n →₀ ℕ) :
    (evenPolynomialPart C).coeff e =
      if Even e.degree then C.coeff e else 0 := by
  classical
  by_cases heven : Even e.degree
  · by_cases hcoeff : C.coeff e = 0
    · simp [evenPolynomialPart, heven, hcoeff,
        MvPolynomial.coeff_sum]
    · simp [evenPolynomialPart, heven, hcoeff,
        MvPolynomial.coeff_sum]
  · simp [evenPolynomialPart, heven, MvPolynomial.coeff_sum]

/-- Exact support of the even part. -/
theorem mem_support_evenPolynomialPart_iff
    (C : MvPolynomial (Fin n) ℝ) (e : Fin n →₀ ℕ) :
    e ∈ (evenPolynomialPart C).support ↔
      e ∈ C.support ∧ Even e.degree := by
  classical
  rw [MvPolynomial.mem_support_iff,
    coeff_evenPolynomialPart]
  by_cases heven : Even e.degree
  · simp [heven, MvPolynomial.mem_support_iff]
  · simp [heven]

/-- The even part satisfies the parity condition for every even target
degree lying above the original support. -/
theorem evenPolynomialPart_hasRadialHomogenizationParity
    (C : MvPolynomial (Fin n) ℝ) (M : ℕ)
    (hM : Even M)
    (hdegree : ∀ e ∈ C.support, e.degree ≤ M) :
    HasRadialHomogenizationParity M (evenPolynomialPart C) := by
  intro e he
  have he' :=
    (mem_support_evenPolynomialPart_iff C e).mp he
  refine ⟨hdegree e he'.1, ?_⟩
  obtain ⟨a, ha⟩ := hM
  obtain ⟨b, hb⟩ := he'.2
  use a - b
  omega

/-- A homogeneous monomial evaluated at `-x` acquires the sign determined
by its total degree. -/
theorem eval_monomial_neg
    (e : Fin n →₀ ℕ) (c : ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval (-x) (monomial e c) =
      (-1 : ℝ) ^ e.degree *
        MvPolynomial.eval x (monomial e c) := by
  have hhom :
      (monomial e c :
        MvPolynomial (Fin n) ℝ).IsHomogeneous e.degree :=
    isHomogeneous_monomial c rfl
  change
    eval₂Hom (RingHom.id ℝ) (-x) (monomial e c) =
      (-1 : ℝ) ^ e.degree *
        eval₂Hom (RingHom.id ℝ) x (monomial e c)
  have hneg : (-1 : ℝ) • x = -x := by
    funext i
    simp
  rw [← hneg]
  exact MvPolynomial.IsHomogeneous.eval₂Hom_smul
    hhom (RingHom.id ℝ) x (-1 : ℝ)

/-- Function-level meaning of the even part: it is the average of `C` at
`x` and `-x`. -/
theorem eval_evenPolynomialPart
    (C : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval x (evenPolynomialPart C) =
      (MvPolynomial.eval x C + MvPolynomial.eval (-x) C) / 2 := by
  classical
  calc
    MvPolynomial.eval x (evenPolynomialPart C) =
        ∑ e ∈ C.support,
          if Even e.degree then
            MvPolynomial.eval x (monomial e (C.coeff e))
          else 0 := by
      rw [evenPolynomialPart, map_sum]
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e he
      by_cases h : Even e.degree <;> simp [h]
    _ = ∑ e ∈ C.support,
        (MvPolynomial.eval x (monomial e (C.coeff e)) +
          MvPolynomial.eval (-x) (monomial e (C.coeff e))) / 2 := by
      apply Finset.sum_congr rfl
      intro e he
      rw [eval_monomial_neg]
      by_cases heven : Even e.degree
      · have hsign : (-1 : ℝ) ^ e.degree = 1 :=
          Even.neg_one_pow heven
        simp [heven, hsign]
      · have hodd : Odd e.degree := Nat.not_even_iff_odd.mp heven
        have hsign : (-1 : ℝ) ^ e.degree = -1 :=
          Odd.neg_one_pow hodd
        simp [heven, hsign]
    _ = ((∑ e ∈ C.support,
          MvPolynomial.eval x (monomial e (C.coeff e))) +
        ∑ e ∈ C.support,
          MvPolynomial.eval (-x) (monomial e (C.coeff e))) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ = (MvPolynomial.eval x C +
        MvPolynomial.eval (-x) C) / 2 := by
      have hsupport :
          (∑ e ∈ C.support, monomial e (C.coeff e)) = C :=
        C.support_sum_monomial_coeff
      rw [← map_sum, ← map_sum, hsupport]

/-- Differentiating the averaging identity gives the corresponding exact
directional-derivative identity.  The minus sign in the second term is the
chain-rule contribution from `x ↦ -x`. -/
theorem mvPolynomialDifferential_evenPolynomialPart_apply
    (C : MvPolynomial (Fin n) ℝ) (x v : Fin n → ℝ) :
    mvPolynomialDifferential (evenPolynomialPart C) x v =
      (mvPolynomialDifferential C x v -
        mvPolynomialDifferential C (-x) v) / 2 := by
  let E := Fin n → ℝ
  have hneg :
      HasFDerivAt (fun y : E ↦ -y)
        (-(ContinuousLinearMap.id ℝ E)) x := by
    simpa only [id_eq] using
      (hasFDerivAt_id (𝕜 := ℝ) x).neg
  have hC :
      HasFDerivAt
        (fun y : E ↦ MvPolynomial.eval y C)
        (mvPolynomialDifferential C x) x :=
    hasFDerivAt_mvPolynomial_eval C x
  have hCneg :
      HasFDerivAt
        (fun y : E ↦ MvPolynomial.eval (-y) C)
        ((mvPolynomialDifferential C (-x)).comp
          (-(ContinuousLinearMap.id ℝ E))) x := by
    simpa only using
      (hasFDerivAt_mvPolynomial_eval C (-x)).comp x hneg
  have hright :
      HasFDerivAt
        (fun y : E ↦
          (MvPolynomial.eval y C + MvPolynomial.eval (-y) C) / 2)
        ((2 : ℝ)⁻¹ •
          (mvPolynomialDifferential C x +
            (mvPolynomialDifferential C (-x)).comp
              (-(ContinuousLinearMap.id ℝ E)))) x := by
    simpa only [div_eq_inv_mul, smul_eq_mul] using
      (hC.add hCneg).const_smul ((2 : ℝ)⁻¹)
  have hleft :=
    hasFDerivAt_mvPolynomial_eval (evenPolynomialPart C) x
  have hfunctions :
      (fun y : E ↦
        MvPolynomial.eval y (evenPolynomialPart C)) =
      (fun y : E ↦
        (MvPolynomial.eval y C + MvPolynomial.eval (-y) C) / 2) := by
    funext y
    exact eval_evenPolynomialPart C y
  have hmaps :
      mvPolynomialDifferential (evenPolynomialPart C) x =
        (2 : ℝ)⁻¹ •
          (mvPolynomialDifferential C x +
            (mvPolynomialDifferential C (-x)).comp
              (-(ContinuousLinearMap.id ℝ E))) := by
    rw [← hleft.fderiv, ← hright.fderiv, hfunctions]
  have happ := congrArg (fun L : E →L[ℝ] ℝ ↦ L v) hmaps
  simp only [ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply,
    map_neg, smul_eq_mul] at happ
  rw [happ]
  ring

/-- Bundled continuous-linear-map form of the preceding directional
identity. -/
theorem mvPolynomialDifferential_evenPolynomialPart
    (C : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    mvPolynomialDifferential (evenPolynomialPart C) x =
      (2 : ℝ)⁻¹ •
        (mvPolynomialDifferential C x -
          mvPolynomialDifferential C (-x)) := by
  ext v
  rw [mvPolynomialDifferential_evenPolynomialPart_apply]
  simp only [ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, smul_eq_mul]
  ring

/-- Averaging an approximation at two antipodal points does not enlarge
its strict value-error bound when the target function is even. -/
theorem abs_eval_evenPolynomialPart_sub_lt_of_even_target
    (C : MvPolynomial (Fin n) ℝ) (W : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) {ε : ℝ}
    (hWneg : W (-x) = W x)
    (hx : |MvPolynomial.eval x C - W x| < ε)
    (hnegx : |MvPolynomial.eval (-x) C - W (-x)| < ε) :
    |MvPolynomial.eval x (evenPolynomialPart C) - W x| < ε := by
  rw [hWneg] at hnegx
  rw [eval_evenPolynomialPart]
  have hrewrite :
      (MvPolynomial.eval x C + MvPolynomial.eval (-x) C) / 2 -
          W x =
        ((MvPolynomial.eval x C - W x) +
          (MvPolynomial.eval (-x) C - W x)) / 2 := by
    ring
  rw [hrewrite, abs_div]
  have htriangle :
      |(MvPolynomial.eval x C - W x) +
          (MvPolynomial.eval (-x) C - W x)| <
        ε + ε :=
    (abs_add_le _ _).trans_lt (add_lt_add hx hnegx)
  norm_num
  linarith

/-- Antipodal averaging also does not enlarge a strict operator-norm
first-derivative error bound when the target differential is odd in its
base point. -/
theorem norm_mvPolynomialDifferential_evenPolynomialPart_sub_lt
    (C : MvPolynomial (Fin n) ℝ)
    (D : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ)
    (x : Fin n → ℝ) {ε : ℝ}
    (hDneg : D (-x) = -D x)
    (hx : ‖mvPolynomialDifferential C x - D x‖ < ε)
    (hnegx :
      ‖mvPolynomialDifferential C (-x) - D (-x)‖ < ε) :
    ‖mvPolynomialDifferential (evenPolynomialPart C) x - D x‖ < ε := by
  have hmap :
      mvPolynomialDifferential (evenPolynomialPart C) x - D x =
        (2 : ℝ)⁻¹ •
          ((mvPolynomialDifferential C x - D x) -
            (mvPolynomialDifferential C (-x) - D (-x))) := by
    rw [mvPolynomialDifferential_evenPolynomialPart, hDneg]
    module
  rw [hmap, norm_smul]
  have htriangle :
      ‖(mvPolynomialDifferential C x - D x) -
          (mvPolynomialDifferential C (-x) - D (-x))‖ <
        ε + ε :=
    (norm_sub_le _ _).trans_lt (add_lt_add hx hnegx)
  norm_num
  linarith

/-- Directional scalar version of the preceding first-derivative
approximation lemma.  It is useful when an approximation theorem controls
the coordinate partial derivatives separately. -/
theorem abs_mvPolynomialDifferential_evenPolynomialPart_sub_lt
    (C : MvPolynomial (Fin n) ℝ)
    (D : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (x v : Fin n → ℝ) {ε : ℝ}
    (hDneg : D (-x) v = -D x v)
    (hx :
      |mvPolynomialDifferential C x v - D x v| < ε)
    (hnegx :
      |mvPolynomialDifferential C (-x) v - D (-x) v| < ε) :
    |mvPolynomialDifferential (evenPolynomialPart C) x v -
        D x v| < ε := by
  rw [mvPolynomialDifferential_evenPolynomialPart_apply]
  have hrewrite :
      (mvPolynomialDifferential C x v -
            mvPolynomialDifferential C (-x) v) / 2 -
          D x v =
        ((mvPolynomialDifferential C x v - D x v) -
          (mvPolynomialDifferential C (-x) v -
            D (-x) v)) / 2 := by
    rw [hDneg]
    ring
  rw [hrewrite, abs_div]
  have htriangle :
      |(mvPolynomialDifferential C x v - D x v) -
          (mvPolynomialDifferential C (-x) v -
            D (-x) v)| <
        ε + ε :=
    (abs_sub _ _).trans_lt (add_lt_add hx hnegx)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hhalf :
      |(mvPolynomialDifferential C x v - D x v) -
          (mvPolynomialDifferential C (-x) v -
            D (-x) v)| / (2 : ℝ) <
        (ε + ε) / 2 :=
    div_lt_div_of_pos_right htriangle (by norm_num)
  calc
    |(mvPolynomialDifferential C x v - D x v) -
        (mvPolynomialDifferential C (-x) v -
          D (-x) v)| / 2 <
        (ε + ε) / 2 := hhalf
    _ = ε := by ring

end

end HGAS
