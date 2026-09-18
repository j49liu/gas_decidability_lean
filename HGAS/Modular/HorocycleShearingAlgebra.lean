import HGAS.Modular.GammaTwoFrameQuotient
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Exact geodesic--horocycle shearing identities

This file formalizes the matrix calculation at the geometric core of the
elementary Dani--Smillie proof.

Write

```text
       1  s                 1  0
 U(s)=       ,       V(r)=       ,
       0  1                 r  1

       exp(t/2)       0
 G(t)=
          0       exp(-t/2).
```

If `1 - r s > 0`, then

```text
 V(r) G(t) U(s / (exp(t) (1-rs)))
   = U(s) V(r/(1-rs)) G(t + 2 log(1-rs)).
```

Thus a point on the local stable sheet through `x` can be flowed for a
slightly reparameterized time so that it remains on the local stable sheet
through `x U(s)`.  Hubbard--Miller call the reparameterized time
`αₓ(y,s)`; the displayed formula is their Lemma 4.1 (arXiv:0712.1300).

Everything below is exact algebra in `SL(2, ℝ)` and its level-two quotient.
Metric estimates and cusp geometry are intentionally left to later files.
-/

namespace HGAS.Modular

open Function Matrix
open scoped MatrixGroups

noncomputable section

/-- The lower-unipotent one-parameter subgroup

```text
  v(r) = [1 0; r 1].
```
-/
def lowerUnipotent (r : ℝ) : RealModularFrame :=
  ⟨!![1, 0; r, 1], by
    simp [Matrix.det_fin_two]⟩

@[simp]
theorem lowerUnipotent_coe (r : ℝ) :
    (lowerUnipotent r : Matrix (Fin 2) (Fin 2) ℝ) =
      !![1, 0; r, 1] :=
  rfl

@[simp]
theorem lowerUnipotent_zero :
    lowerUnipotent 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerUnipotent]

@[simp]
theorem lowerUnipotent_add (r s : ℝ) :
    lowerUnipotent (r + s) =
      lowerUnipotent r * lowerUnipotent s := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerUnipotent,
      Matrix.SpecialLinearGroup.coe_mul]

/-- The lower-unipotent subgroup depends continuously on its parameter. -/
theorem lowerUnipotent_continuous :
    Continuous lowerUnipotent := by
  apply continuous_induced_rng.mpr
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one,
      Function.comp_apply, lowerUnipotent_coe, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
    fun_prop

/-- The diagonal one-parameter subgroup generating the geodesic flow. -/
def geodesicFrame (t : ℝ) : RealModularFrame :=
  ⟨!![Real.exp (t / 2), 0; 0, Real.exp (-t / 2)], by
    simp [Matrix.det_fin_two, ← Real.exp_add]
    ring_nf⟩

@[simp]
theorem geodesicFrame_coe (t : ℝ) :
    (geodesicFrame t : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.exp (t / 2), 0; 0, Real.exp (-t / 2)] :=
  rfl

@[simp]
theorem geodesicFrame_zero :
    geodesicFrame 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [geodesicFrame]

@[simp]
theorem geodesicFrame_add (s t : ℝ) :
    geodesicFrame (s + t) =
      geodesicFrame s * geodesicFrame t := by
  have hpos :
      Real.exp ((s + t) / 2) =
        Real.exp (s / 2) * Real.exp (t / 2) := by
    rw [show (s + t) / 2 = s / 2 + t / 2 by ring,
      Real.exp_add]
  have hneg :
      Real.exp ((-t + -s) / 2) =
        Real.exp (-s / 2) * Real.exp (-t / 2) := by
    rw [show (-t + -s) / 2 = -s / 2 + -t / 2 by ring,
      Real.exp_add]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [geodesicFrame,
      Matrix.SpecialLinearGroup.coe_mul] using hpos
  · simp [geodesicFrame, Matrix.SpecialLinearGroup.coe_mul]
  · simp [geodesicFrame, Matrix.SpecialLinearGroup.coe_mul]
  · simpa [geodesicFrame,
      Matrix.SpecialLinearGroup.coe_mul] using hneg

/-- The diagonal subgroup depends continuously on time. -/
theorem geodesicFrame_continuous :
    Continuous geodesicFrame := by
  apply continuous_induced_rng.mpr
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one,
      Function.comp_apply, geodesicFrame_coe, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
    fun_prop

/-- Conjugating an upper horocycle by the geodesic subgroup rescales its
time parameter. -/
theorem geodesicFrame_upperUnipotent_conjugation
    (t s : ℝ) :
    geodesicFrame (-t) * upperUnipotent s * geodesicFrame t =
      upperUnipotent (Real.exp (-t) * s) := by
  have hscale :
      Real.exp (-t / 2) ^ 2 =
        Real.exp (-t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hcancel :
      Real.exp (-t / 2) *
          Real.exp (t / 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  have hcancel' :
      Real.exp (t / 2) *
          Real.exp (-t / 2) = 1 := by
    rw [mul_comm]
    exact hcancel
  have hentry :
      Real.exp (-t / 2) * s * Real.exp (-t / 2) =
        Real.exp (-t) * s := by
    calc
      Real.exp (-t / 2) * s * Real.exp (-t / 2) =
          Real.exp (-t / 2) ^ 2 * s := by ring
      _ = Real.exp (-t) * s := by rw [hscale]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [geodesicFrame, upperUnipotent,
      Matrix.SpecialLinearGroup.coe_mul] using hcancel
  · simpa [geodesicFrame, upperUnipotent,
      Matrix.SpecialLinearGroup.coe_mul] using hentry
  · simp [geodesicFrame, upperUnipotent,
      Matrix.SpecialLinearGroup.coe_mul]
  · simpa [geodesicFrame, upperUnipotent,
      Matrix.SpecialLinearGroup.coe_mul] using hcancel'

/-- The analogous rescaling identity for the lower horocycle. -/
theorem geodesicFrame_lowerUnipotent_conjugation
    (t r : ℝ) :
    geodesicFrame (-t) * lowerUnipotent r * geodesicFrame t =
      lowerUnipotent (Real.exp t * r) := by
  have hscale :
      Real.exp (t / 2) ^ 2 =
        Real.exp t := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hcancel :
      Real.exp (-t / 2) *
          Real.exp (t / 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  have hcancel' :
      Real.exp (t / 2) *
          Real.exp (-t / 2) = 1 := by
    rw [mul_comm]
    exact hcancel
  have hentry :
      Real.exp (t / 2) * r * Real.exp (t / 2) =
        Real.exp t * r := by
    calc
      Real.exp (t / 2) * r * Real.exp (t / 2) =
          Real.exp (t / 2) ^ 2 * r := by ring
      _ = Real.exp t * r := by rw [hscale]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [geodesicFrame, lowerUnipotent,
      Matrix.SpecialLinearGroup.coe_mul] using hcancel
  · simp [geodesicFrame, lowerUnipotent,
      Matrix.SpecialLinearGroup.coe_mul]
  · simpa [geodesicFrame, lowerUnipotent,
      Matrix.SpecialLinearGroup.coe_mul] using hentry
  · simpa [geodesicFrame, lowerUnipotent,
      Matrix.SpecialLinearGroup.coe_mul] using hcancel'

/-- The exact time change which aligns two nearby positive horocycles. -/
def horocycleShearTime (r t s : ℝ) : ℝ :=
  s / (Real.exp t * (1 - r * s))

@[simp]
theorem horocycleShearTime_zero_parameters (s : ℝ) :
    horocycleShearTime 0 0 s = s := by
  simp [horocycleShearTime]

/-- The derivative of the exact shear time.  The combination `r * s`,
rather than `r` and `s` separately, is what controls the distortion. -/
theorem hasDerivAt_horocycleShearTime
    (r t s : ℝ) (h : 1 - r * s ≠ 0) :
    HasDerivAt (horocycleShearTime r t)
      (Real.exp (-t) / (1 - r * s) ^ 2) s := by
  have hlinear :
      HasDerivAt (fun u : ℝ ↦ 1 - r * u) (-r) s := by
    convert
      (hasDerivAt_const s (1 : ℝ)).sub
        ((hasDerivAt_id s).const_mul r) using 1
    ring
  have hden :
      HasDerivAt
        (fun u : ℝ ↦ Real.exp t * (1 - r * u))
        (Real.exp t * (-r)) s :=
    hlinear.const_mul (Real.exp t)
  have hden_ne :
      Real.exp t * (1 - r * s) ≠ 0 :=
    mul_ne_zero (Real.exp_ne_zero t) h
  have hraw := (hasDerivAt_id s).div hden hden_ne
  unfold horocycleShearTime
  convert hraw using 1
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero, h]
  simp only [id_eq]
  ring

/-- The shear derivative, written in the two small parameters which
actually enter it: the geodesic displacement `t` and the product `v = rs`.
-/
def horocycleShearDerivativeParameters (t v : ℝ) : ℝ :=
  Real.exp (-t) / (1 - v) ^ 2

@[simp]
theorem horocycleShearDerivativeParameters_zero :
    horocycleShearDerivativeParameters 0 0 = 1 := by
  simp [horocycleShearDerivativeParameters]

/-- Near the origin, the shear derivative is uniformly close to one on a
small rectangle. -/
theorem exists_delta_horocycleShearDerivativeParameters
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      ∀ t v : ℝ,
        |t| < δ →
        |v| < δ →
        |horocycleShearDerivativeParameters t v - 1| < ε := by
  let F : ℝ × ℝ → ℝ :=
    fun p ↦ horocycleShearDerivativeParameters p.1 p.2
  have hF : ContinuousAt F (0, 0) := by
    unfold F horocycleShearDerivativeParameters
    apply ContinuousAt.div₀
    · fun_prop
    · fun_prop
    · norm_num
  obtain ⟨η, hη, hclose⟩ :=
    Metric.continuousAt_iff.mp hF ε hε
  let δ : ℝ := min η (1 / 2)
  have hδ : 0 < δ := by
    exact lt_min hη (by norm_num)
  refine ⟨δ, hδ, min_le_right _ _, ?_⟩
  intro t v ht hv
  have hpdist : dist (t, v) ((0 : ℝ), (0 : ℝ)) < η := by
    rw [Prod.dist_eq, max_lt_iff]
    constructor
    · simpa only [Real.dist_eq, sub_zero] using
        ht.trans_le (min_le_left _ _)
    · simpa only [Real.dist_eq, sub_zero] using
        hv.trans_le (min_le_left _ _)
  have hout := hclose hpdist
  simpa only [F, horocycleShearDerivativeParameters_zero,
    Real.dist_eq] using hout

/-- Uniform derivative control on the thin flow boxes used in the
good-return-time argument.

If `|r| < δ/T`, `|t| < δ`, and `0 ≤ s ≤ T`, then both small parameters
`t` and `r*s` lie in the rectangle from the preceding theorem. -/
theorem exists_delta_horocycleShearTime_derivative_close
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      ∀ (T r t s : ℝ),
        0 < T →
        |r| < δ / T →
        |t| < δ →
        0 ≤ s →
        s ≤ T →
        |Real.exp (-t) / (1 - r * s) ^ 2 - 1| < ε := by
  obtain ⟨δ, hδ, hδhalf, hδcontrol⟩ :=
    exists_delta_horocycleShearDerivativeParameters hε
  refine ⟨δ, hδ, hδhalf, ?_⟩
  intro T r t s hT hr ht hs hsT
  apply hδcontrol t (r * s) ht
  calc
    |r * s| = |r| * s := by
      rw [abs_mul, abs_of_nonneg hs]
    _ ≤ |r| * T :=
      mul_le_mul_of_nonneg_left hsT (abs_nonneg r)
    _ < (δ / T) * T :=
      mul_lt_mul_of_pos_right hr hT
    _ = δ := by field_simp

/-- **Exact horocycle shearing factorization.**

This is the explicit replacement for the implicit-function argument in
the Hubbard--Miller proof.  The positivity hypothesis says precisely that
the denominator has not reached the pole of the local flow box. -/
theorem lower_geodesic_upper_shear_factorization
    (r t s : ℝ) (h : 0 < 1 - r * s) :
    lowerUnipotent r * geodesicFrame t *
        upperUnipotent (horocycleShearTime r t s) =
      upperUnipotent s *
        lowerUnipotent (r / (1 - r * s)) *
          geodesicFrame
            (t + 2 * Real.log (1 - r * s)) := by
  have h' : 0 < 1 - s * r := by
    simpa only [mul_comm] using h
  have hplus :
      Real.exp ((t + 2 * Real.log (1 - r * s)) / 2) =
        Real.exp (t / 2) * (1 - r * s) := by
    rw [show (t + 2 * Real.log (1 - r * s)) / 2 =
      t / 2 + Real.log (1 - r * s) by ring,
      Real.exp_add, Real.exp_log h]
  have hminus :
      Real.exp (-(t + 2 * Real.log (1 - r * s)) / 2) =
        Real.exp (-t / 2) / (1 - r * s) := by
    rw [show -(t + 2 * Real.log (1 - r * s)) / 2 =
      -t / 2 - Real.log (1 - r * s) by ring,
      Real.exp_sub, Real.exp_log h]
  have hminus' :
      Real.exp
          ((-(2 * Real.log (1 - r * s)) + -t) / 2) =
        Real.exp (-t / 2) / (1 - r * s) := by
    rw [show (-(2 * Real.log (1 - r * s)) + -t) / 2 =
      -(t + 2 * Real.log (1 - r * s)) / 2 by ring]
    exact hminus
  have hexp :
      Real.exp t * Real.exp (-(t / 2)) =
        Real.exp (t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hlogneg :
      Real.exp (-(2 * Real.log (1 - r * s)) / 2) =
        (1 - r * s)⁻¹ := by
    rw [show -(2 * Real.log (1 - r * s)) / 2 =
      -Real.log (1 - r * s) by ring,
      Real.exp_neg, Real.exp_log h]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simp [lowerUnipotent, geodesicFrame, upperUnipotent,
      horocycleShearTime, Matrix.SpecialLinearGroup.coe_mul,
      hplus]
    field_simp [Real.exp_ne_zero, h.ne', h'.ne']
    ring
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one,
      Matrix.SpecialLinearGroup.coe_mul, lowerUnipotent_coe,
      geodesicFrame_coe, Matrix.cons_mul, Nat.succ_eq_add_one,
      Nat.reduceAdd, Matrix.vecMul_cons, Matrix.head_cons,
      one_smul, Matrix.tail_cons, zero_smul,
      Matrix.empty_vecMul, add_zero, Matrix.smul_cons,
      smul_eq_mul, mul_zero, Matrix.smul_empty,
      Matrix.add_cons, zero_add, Matrix.empty_add_empty,
      Matrix.empty_mul, Equiv.symm_apply_apply,
      upperUnipotent_coe, mul_one, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero,
      geodesicFrame_add, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true,
      mul_div_cancel_left₀]
    rw [hlogneg]
    unfold horocycleShearTime
    field_simp [Real.exp_ne_zero, h.ne', h'.ne']
    calc
      Real.exp (t / 2) * s =
          s * Real.exp (t / 2) := mul_comm _ _
      _ =
          s * (Real.exp t * Real.exp (-(t / 2))) := by
            rw [hexp]
      _ =
          s * Real.exp t * Real.exp (-(t / 2)) := by ring
  · simp [lowerUnipotent, geodesicFrame, upperUnipotent,
      horocycleShearTime, Matrix.SpecialLinearGroup.coe_mul,
      hplus]
    field_simp [Real.exp_ne_zero, h.ne', h'.ne']
  · simp only [Fin.mk_one, Fin.isValue,
      Matrix.SpecialLinearGroup.coe_mul, lowerUnipotent_coe,
      geodesicFrame_coe, Matrix.cons_mul,
      Nat.succ_eq_add_one, Nat.reduceAdd,
      Matrix.vecMul_cons, Matrix.head_cons, one_smul,
      Matrix.tail_cons, zero_smul, Matrix.empty_vecMul,
      add_zero, Matrix.smul_cons, smul_eq_mul, mul_zero,
      Matrix.smul_empty, Matrix.add_cons, zero_add,
      Matrix.empty_add_empty, Matrix.empty_mul,
      Equiv.symm_apply_apply, upperUnipotent_coe, mul_one,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one, geodesicFrame_add, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true,
      mul_div_cancel_left₀]
    rw [hlogneg]
    unfold horocycleShearTime
    field_simp [Real.exp_ne_zero, h.ne', h'.ne']
    calc
      r * Real.exp (t / 2) * s +
            Real.exp t * (1 - r * s) *
              Real.exp (-(t / 2)) =
          r * Real.exp (t / 2) * s +
            (1 - r * s) *
              (Real.exp t * Real.exp (-(t / 2))) := by ring
      _ =
          r * Real.exp (t / 2) * s +
            (1 - r * s) * Real.exp (t / 2) := by
              rw [hexp]
      _ =
          Real.exp t * Real.exp (-(t / 2)) := by
            rw [hexp]
            ring

/-- Quotient-level form of the shearing identity.

Starting at the stable-sheet point `q V(r) G(t)` and flowing for the
reparameterized time lands on the stable sheet through `q U(s)`. -/
theorem gammaTwoHorocycleFlow_shear
    (q : GammaTwoFrameQuotient)
    (r t s : ℝ) (h : 0 < 1 - r * s) :
    gammaTwoHorocycleFlow (horocycleShearTime r t s)
        (gammaTwoFrameRightMul
          (lowerUnipotent r * geodesicFrame t) q) =
      gammaTwoFrameRightMul
          (lowerUnipotent (r / (1 - r * s)) *
            geodesicFrame
              (t + 2 * Real.log (1 - r * s)))
        (gammaTwoHorocycleFlow s q) := by
  induction q using Quotient.inductionOn with
  | _ g =>
      change
        gammaTwoFrameQuotientMk
            ((g * (lowerUnipotent r * geodesicFrame t)) *
              upperUnipotent (horocycleShearTime r t s)) =
          gammaTwoFrameQuotientMk
            ((g * upperUnipotent s) *
              (lowerUnipotent (r / (1 - r * s)) *
                geodesicFrame
                  (t + 2 * Real.log (1 - r * s))))
      congr 1
      simp only [mul_assoc]
      congr 1
      simpa only [mul_assoc] using
        lower_geodesic_upper_shear_factorization r t s h

end

end HGAS.Modular
