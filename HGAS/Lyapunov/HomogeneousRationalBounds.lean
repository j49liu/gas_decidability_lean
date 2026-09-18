import HGAS.Algebra.HomogeneousEvaluation
import HGAS.Lyapunov.RationalCertificateSoundness
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

/-!
# Bounds and regularity for homogeneous rational Lyapunov functions

Let `p` be a form of degree `2r+2` and put

```
V(x) = p(x) / (x₁² + ... + xₙ²)^r.
```

Although the displayed quotient is only visibly smooth away from the
origin, homogeneity makes its extension at the origin quadratic.  This file
formalizes that elementary fact in a reusable way.  The proof normalizes a
nonzero vector by the ambient sup norm, bounds the numerator on the compact
unit sphere, and then scales back.  In particular, it does not choose a
coordinate expansion or a basis-dependent coefficient norm.

The resulting `O(‖x‖²)` estimate proves both continuity and differentiability
at the origin, with derivative zero.  These are exactly the analytic facts
needed to turn a checked rational Lyapunov certificate into a theorem about
the original polynomial ODE.
-/

namespace HGAS

open Filter MvPolynomial Set
open scoped Topology

noncomputable section

variable {n : ℕ}

/-- The square of the finite-product sup norm is bounded by the algebraic
sum of coordinate squares. -/
theorem norm_sq_le_normSq (x : Fin n → ℝ) :
    ‖x‖ ^ 2 ≤ normSq x := by
  have hnorm : ‖x‖ ≤ Real.sqrt (normSq x) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro i
    have hi : x i * x i ≤ normSq x := by
      exact Finset.single_le_sum
        (fun j _ ↦ mul_self_nonneg (x j)) (Finset.mem_univ i)
    rw [Real.norm_eq_abs]
    have hsqrt : (Real.sqrt (normSq x)) ^ 2 = normSq x :=
      Real.sq_sqrt (normSq_nonneg x)
    have habs : |x i| ^ 2 = x i * x i := by
      rw [sq_abs]
      ring
    nlinarith [abs_nonneg (x i), Real.sqrt_nonneg (normSq x)]
  have hsquare :=
    (sq_le_sq₀ (norm_nonneg x) (Real.sqrt_nonneg (normSq x))).2 hnorm
  simpa [Real.sq_sqrt (normSq_nonneg x)] using hsquare

/-- The algebraic squared norm vanishes exactly at the zero coordinate
vector. -/
@[simp]
theorem normSq_eq_zero_iff (x : Fin n → ℝ) :
    normSq x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply norm_eq_zero.mp
    have := norm_sq_le_normSq x
    rw [hx] at this
    nlinarith [norm_nonneg x]
  · rintro rfl
    exact normSq_zero

/-- Evaluation of a positive-degree homogeneous rational polynomial at the
zero vector is zero. -/
theorem ratMvPolynomialEval_zero_of_isHomogeneous
    {p : MvPolynomial (Fin n) ℚ} {d : ℕ}
    (hp : p.IsHomogeneous d) (hd : 0 < d) :
    ratMvPolynomialEval p 0 = 0 := by
  rw [ratMvPolynomialEval_eq_eval₂Hom]
  have hscale :=
    MvPolynomial.IsHomogeneous.eval₂Hom_smul hp
      (algebraMap ℚ ℝ) (0 : Fin n → ℝ) 0
  simpa [hd.ne'] using hscale

/-- A rational Lyapunov quotient built from a form of degree `2r+2`
vanishes at the origin under Lean's total division convention. -/
@[simp]
theorem rationalLyapunovValue_zero_of_isHomogeneous
    {p : MvPolynomial (Fin n) ℚ} {r : ℕ}
    (hp : p.IsHomogeneous (2 * (r + 1))) :
    rationalLyapunovValue p r 0 = 0 := by
  simp only [rationalLyapunovValue, normSq_zero]
  rw [ratMvPolynomialEval_zero_of_isHomogeneous hp (by omega)]
  simp

/-- The quotient has degree two: simultaneous scaling of all coordinates by
a nonzero real scalar multiplies its value by the scalar squared. -/
theorem rationalLyapunovValue_smul
    {p : MvPolynomial (Fin n) ℚ} {r : ℕ}
    (hp : p.IsHomogeneous (2 * (r + 1)))
    (x : Fin n → ℝ) {c : ℝ} (hc : c ≠ 0) :
    rationalLyapunovValue p r (c • x) =
      c ^ 2 * rationalLyapunovValue p r x := by
  by_cases hx : x = 0
  · subst x
    simp [rationalLyapunovValue_zero_of_isHomogeneous hp]
  have hρ : normSq x ≠ 0 :=
    (normSq_eq_zero_iff x).not.mpr hx
  rw [rationalLyapunovValue, rationalLyapunovValue,
    ratMvPolynomialEval_eq_eval₂Hom,
    MvPolynomial.IsHomogeneous.eval₂Hom_smul hp
      (algebraMap ℚ ℝ) x c, normSq_smul]
  simp only [ratMvPolynomialEval_eq_eval₂Hom]
  field_simp [hc, hρ]
  ring_nf

/-- On the compact unit sphere, the absolute value of a rational polynomial
numerator has a finite real upper bound. -/
theorem exists_abs_ratMvPolynomialEval_bound_on_unitSphere
    (p : MvPolynomial (Fin n) ℚ) :
    ∃ A : ℝ, ∀ x : Fin n → ℝ, ‖x‖ = 1 →
      |ratMvPolynomialEval p x| ≤ A := by
  have hcompact :
      IsCompact (Metric.sphere (0 : Fin n → ℝ) 1) :=
    isCompact_sphere _ _
  have hcontinuous :
      Continuous
        (fun x : Fin n → ℝ ↦ |ratMvPolynomialEval p x|) :=
    (contDiff_ratMvPolynomialEval p).continuous.abs
  obtain ⟨A, hA⟩ :=
    hcompact.bddAbove_image hcontinuous.continuousOn
  refine ⟨A, ?_⟩
  intro x hx
  apply hA
  exact ⟨x, by simpa [Metric.mem_sphere, dist_zero_right] using hx, rfl⟩

/-- Every two-homogeneous rational quotient admits a global quadratic bound
in the ambient finite-product norm. -/
theorem exists_rationalLyapunovValue_quadratic_bound
    {p : MvPolynomial (Fin n) ℚ} {r : ℕ}
    (hp : p.IsHomogeneous (2 * (r + 1))) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : Fin n → ℝ,
      |rationalLyapunovValue p r x| ≤ B * ‖x‖ ^ 2 := by
  obtain ⟨A, hA⟩ :=
    exists_abs_ratMvPolynomialEval_bound_on_unitSphere p
  let B : ℝ := max A 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨B, hB, ?_⟩
  intro x
  by_cases hx : x = 0
  · subst x
    simp [rationalLyapunovValue_zero_of_isHomogeneous hp]
  let y : Fin n → ℝ := ‖x‖⁻¹ • x
  have hxnorm : 0 < ‖x‖ := (norm_pos_iff.mpr hx)
  have hynorm : ‖y‖ = 1 := by
    simp [y, norm_smul, hxnorm.ne']
  have hρy : 1 ≤ normSq y := by
    simpa [hynorm] using norm_sq_le_normSq y
  have hρypos : 0 < normSq y := lt_of_lt_of_le zero_lt_one hρy
  have hden : 1 ≤ normSq y ^ r :=
    one_le_pow₀ hρy
  have hnum : |ratMvPolynomialEval p y| ≤ B :=
    (hA y hynorm).trans (le_max_left _ _)
  have hunit :
      |rationalLyapunovValue p r y| ≤ B := by
    rw [rationalLyapunovValue, abs_div,
      abs_of_nonneg (pow_nonneg (normSq_nonneg y) r)]
    exact (div_le_iff₀ (pow_pos hρypos r)).2
      (hnum.trans (le_mul_of_one_le_right hB.le hden))
  have hxy : ‖x‖ • y = x := by
    simp [y, smul_smul, hxnorm.ne']
  have hscale :
      rationalLyapunovValue p r x =
        ‖x‖ ^ 2 * rationalLyapunovValue p r y := by
    calc
      rationalLyapunovValue p r x =
          rationalLyapunovValue p r (‖x‖ • y) := by rw [hxy]
      _ = ‖x‖ ^ 2 * rationalLyapunovValue p r y :=
        rationalLyapunovValue_smul hp y hxnorm.ne'
  rw [hscale, abs_mul, abs_of_nonneg (sq_nonneg ‖x‖)]
  nlinarith [sq_nonneg ‖x‖]

/-- A global quadratic bound forces the rational quotient to be continuous
at the origin. -/
theorem continuousAt_rationalLyapunovValue_zero
    {p : MvPolynomial (Fin n) ℚ} {r : ℕ}
    (hp : p.IsHomogeneous (2 * (r + 1))) :
    ContinuousAt (rationalLyapunovValue p r) 0 := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_rationalLyapunovValue_quadratic_bound hp
  rw [Metric.continuousAt_iff]
  intro ε hε
  let δ : ℝ := Real.sqrt (ε / B)
  have hδ : 0 < δ := Real.sqrt_pos.2 (div_pos hε hB)
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  have hxnorm : ‖x‖ < δ := by
    simpa [dist_zero_right] using hx
  have hδsq : δ ^ 2 = ε / B := by
    dsimp [δ]
    exact Real.sq_sqrt (div_nonneg hε.le hB.le)
  have hquad : B * ‖x‖ ^ 2 < ε := by
    have hsquare : ‖x‖ ^ 2 < δ ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg x) hδ.le).2 hxnorm
    rw [hδsq] at hsquare
    simpa [mul_comm] using (lt_div_iff₀ hB).1 hsquare
  rw [rationalLyapunovValue_zero_of_isHomogeneous hp,
    dist_zero_right, Real.norm_eq_abs]
  exact (hbound x).trans_lt hquad

/-- Away from the origin, ordinary quotient continuity applies. -/
theorem continuousAt_rationalLyapunovValue_of_ne_zero
    {p : MvPolynomial (Fin n) ℚ} {r : ℕ}
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    ContinuousAt (rationalLyapunovValue p r) x := by
  unfold rationalLyapunovValue
  have hnormSq :
      Continuous (normSq : (Fin n → ℝ) → ℝ) := by
    unfold normSq dot
    fun_prop
  apply ContinuousAt.div
    (contDiff_ratMvPolynomialEval p).continuous.continuousAt
  · exact (hnormSq.pow r).continuousAt
  · exact pow_ne_zero r (normSq_pos_of_ne_zero hx).ne'

/-- The two-homogeneous quotient, extended by zero, is globally continuous. -/
theorem continuous_rationalLyapunovValue
    {p : MvPolynomial (Fin n) ℚ} {r : ℕ}
    (hp : p.IsHomogeneous (2 * (r + 1))) :
    Continuous (rationalLyapunovValue p r) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    exact continuousAt_rationalLyapunovValue_zero hp
  · exact continuousAt_rationalLyapunovValue_of_ne_zero hx

/-- A scalar function bounded by a quadratic norm has Fréchet derivative
zero at the origin. -/
theorem hasFDerivAt_zero_of_quadratic_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E → ℝ) (hVzero : V 0 = 0)
    {B : ℝ}
    (hbound : ∀ x, |V x| ≤ B * ‖x‖ ^ 2) :
    HasFDerivAt V (0 : E →L[ℝ] ℝ) 0 := by
  apply HasFDerivAt.of_isLittleO
  have hbig :
      (fun x : E ↦ V x) =O[𝓝 0] (fun x : E ↦ ‖x‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound B
    filter_upwards with x
    simpa [Real.norm_eq_abs] using hbound x
  have hlittle :
      (fun x : E ↦ V x) =o[𝓝 0] (fun x : E ↦ x) :=
    hbig.trans_isLittleO
      (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  simpa [hVzero] using hlittle

/-- Consequently, the homogeneous rational quotient is differentiable at
the origin with zero derivative. -/
theorem hasFDerivAt_rationalLyapunovValue_zero
    {p : MvPolynomial (Fin n) ℚ} {r : ℕ}
    (hp : p.IsHomogeneous (2 * (r + 1))) :
    HasFDerivAt (rationalLyapunovValue p r)
      (0 : (Fin n → ℝ) →L[ℝ] ℝ) 0 := by
  obtain ⟨B, _hB, hbound⟩ :=
    exists_rationalLyapunovValue_quadratic_bound hp
  exact hasFDerivAt_zero_of_quadratic_bound
    (rationalLyapunovValue p r)
    (rationalLyapunovValue_zero_of_isHomogeneous hp)
    hbound

/-- The quotient is differentiable away from the origin by the quotient
rule and at the origin by the global quadratic estimate. -/
theorem differentiable_rationalLyapunovValue
    {p : MvPolynomial (Fin n) ℚ} {r : ℕ}
    (hp : p.IsHomogeneous (2 * (r + 1))) :
    Differentiable ℝ (rationalLyapunovValue p r) := by
  intro x
  by_cases hx : x = 0
  · subst x
    exact (hasFDerivAt_rationalLyapunovValue_zero hp).differentiableAt
  · unfold rationalLyapunovValue
    have hnum :
        DifferentiableAt ℝ (ratMvPolynomialEval p) x :=
      (contDiff_ratMvPolynomialEval p).differentiable
        (by simp) x
    have hden :
        DifferentiableAt ℝ (fun y : Fin n → ℝ ↦ normSq y ^ r) x := by
      unfold normSq dot
      fun_prop
    simpa [div_eq_mul_inv] using
      hnum.mul
        (hden.inv
          (pow_ne_zero r (normSq_pos_of_ne_zero hx).ne'))

end

end HGAS
