import HGAS.Dynamics.Stability
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Tactic

/-!
# Reusable criteria for forward completeness

This file records two generic continuation tools for autonomous ODEs.

First, a bounded globally Lipschitz vector field on a complete real normed
space admits an integral curve through every initial state for all real
times.  The proof applies Picard--Lindelöf on each symmetric bounded time
interval and patches the resulting solutions by uniqueness.

Second, a map that is Lipschitz on a closed ball and vanishes on and outside
the boundary is globally Lipschitz with the same constant.  This is the
elementary estimate needed when a locally controlled vector field is
multiplied by a compact cutoff.

The results are independent of the polynomial constructions in the main
reduction and can be reused in other ODE developments.
-/

namespace HGAS

open Filter Function Metric Set
open scoped Topology NNReal

noncomputable section

/-! ## Bounded globally Lipschitz vector fields -/

/-- A bounded globally Lipschitz autonomous vector field on a complete real
normed space has a global integral curve through every initial state.

For each `a > 0`, Picard--Lindelöf supplies a solution on `[-a,a]`: boundedness
controls how far the solution can travel, while the global Lipschitz estimate
gives uniqueness.  Solutions on nested intervals therefore agree.  At time
`t` we select the solution on `[-(|t|+1), |t|+1]`; local compatibility makes
this pointwise definition differentiable and hence a global integral curve. -/
theorem exists_global_integralCurve_of_lipschitz_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → E) {K L : ℝ≥0} (hK : LipschitzWith K f)
    (hL : ∀ x, ‖f x‖ ≤ L) (x₀ : E) :
    ∃ γ : ℝ → E, γ 0 = x₀ ∧ IsIntegralCurve γ (fun _ ↦ f) := by
  have hlocal : ∀ a : ℝ, 0 < a → ∃ γ : ℝ → E, γ 0 = x₀ ∧
      ∀ t ∈ Icc (-a) a,
        HasDerivWithinAt γ (f (γ t)) (Icc (-a) a) t := by
    intro a ha
    let t₀ : Icc (-a) a := ⟨0, by constructor <;> linarith⟩
    let A : ℝ≥0 := L * ⟨a, ha.le⟩
    have hPL : IsPicardLindelof (fun _ ↦ f) t₀ x₀ A 0 L K := by
      apply IsPicardLindelof.of_time_independent
      · intro x hx
        exact hL x
      · exact hK.lipschitzOnWith
      · change (L : ℝ) * max (a - 0) (0 - -a) ≤ (A : ℝ) - 0
        simp only [sub_zero, zero_sub, neg_neg, max_self]
        rfl
    simpa [t₀] using hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  let localCurve : ℝ → ℝ → E := fun a ↦
    if ha : 0 < a then Classical.choose (hlocal a ha) else fun _ ↦ x₀
  have localCurve_zero (a : ℝ) (ha : 0 < a) : localCurve a 0 = x₀ := by
    simp only [localCurve, dif_pos ha]
    exact (Classical.choose_spec (hlocal a ha)).1
  have localCurve_deriv (a : ℝ) (ha : 0 < a) :
      ∀ t ∈ Icc (-a) a,
        HasDerivWithinAt (localCurve a) (f (localCurve a t))
          (Icc (-a) a) t := by
    simp only [localCurve, dif_pos ha]
    exact (Classical.choose_spec (hlocal a ha)).2
  have localCurve_deriv_open (a : ℝ) (ha : 0 < a) :
      ∀ t ∈ Ioo (-a) a,
        HasDerivAt (localCurve a) (f (localCurve a t)) t := by
    intro t ht
    exact (localCurve_deriv a ha t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  have localCurve_compatible {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
      EqOn (localCurve a) (localCurve b) (Ioo (-a) a) := by
    apply ODE_solution_unique_of_mem_Ioo
      (v := fun _ ↦ f) (s := fun _ ↦ (univ : Set E))
      (K := K) (t₀ := 0)
    · intro t ht
      exact hK.lipschitzOnWith
    · exact ⟨by linarith, ha⟩
    · intro t ht
      exact ⟨localCurve_deriv_open a ha t ht, mem_univ _⟩
    · intro t ht
      have htb : t ∈ Ioo (-b) b :=
        ⟨lt_of_le_of_lt (neg_le_neg hab) ht.1, lt_of_lt_of_le ht.2 hab⟩
      exact
        ⟨localCurve_deriv_open b (lt_of_lt_of_le ha hab) t htb, mem_univ _⟩
    · rw [localCurve_zero a ha,
        localCurve_zero b (lt_of_lt_of_le ha hab)]
  let γ : ℝ → E := fun t ↦ localCurve (|t| + 1) t
  refine ⟨γ, by simp [γ, localCurve_zero], ?_⟩
  intro t
  let a : ℝ := |t| + 1
  have ha : 0 < a := by positivity
  have ht : t ∈ Ioo (-a) a := by
    rw [mem_Ioo, ← abs_lt]
    exact lt_add_one |t|
  have heq : γ =ᶠ[𝓝 t] localCurve a := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Ioo (-a) a, Ioo_mem_nhds ht.1 ht.2, ?_⟩
    intro s hs
    change localCurve (|s| + 1) s = localCurve a s
    by_cases hle : |s| + 1 ≤ a
    · exact localCurve_compatible (by positivity) hle
        (by rw [mem_Ioo, ← abs_lt]; exact lt_add_one |s|)
    · exact (localCurve_compatible ha (le_of_not_ge hle)
        (by simpa [abs_lt] using hs)).symm
  exact (localCurve_deriv_open a ha t ht).congr_of_eventuallyEq heq

/-- A bounded globally Lipschitz autonomous vector field is forward complete
in the trajectory-based sense of `HGAS.ForwardComplete`. -/
theorem forwardComplete_of_lipschitz_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → E) {K L : ℝ≥0} (hK : LipschitzWith K f)
    (hL : ∀ x, ‖f x‖ ≤ L) :
    ForwardComplete f := by
  intro x₀
  obtain ⟨γ, hγ0, hγ⟩ :=
    exists_global_integralCurve_of_lipschitz_bounded f hK hL x₀
  refine ⟨γ, hγ0, ?_⟩
  intro t ht
  exact (hγ t).hasDerivWithinAt

/-! ## Extending a closed-ball Lipschitz estimate -/

/-- If one endpoint of a segment is inside a norm ball and the other is
outside, some point of the segment lies on the boundary sphere. -/
private theorem exists_segment_norm_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} {x y : E} (hx : ‖x‖ ≤ R) (hy : R ≤ ‖y‖) :
    ∃ u ∈ Icc (0 : ℝ) 1, ‖(1 - u) • x + u • y‖ = R := by
  let q : ℝ → ℝ := fun u ↦ ‖(1 - u) • x + u • y‖
  have hq : Continuous q := by
    unfold q
    fun_prop
  have hR : R ∈ Icc (q 0) (q 1) := by
    simpa [q] using ⟨hx, hy⟩
  obtain ⟨u, hu, huR⟩ :=
    intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
      hq.continuousOn hR
  exact ⟨u, hu, huR⟩

/-- A map that is Lipschitz on a closed ball and vanishes on and outside its
boundary is globally Lipschitz with the same constant.

The only nontrivial case has one point inside and one outside.  Intersect
their segment with the boundary sphere.  The map is zero both at that
boundary point and at the outside endpoint, so the closed-ball estimate
applies to the shorter part of the segment. -/
theorem lipschitzWith_of_lipschitzOn_closedBall_of_zero_outside
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} {R : ℝ} {K : ℝ≥0}
    (hK : LipschitzOnWith K g (closedBall (0 : E) R))
    (hzero : ∀ x, R ≤ ‖x‖ → g x = 0) :
    LipschitzWith K g := by
  have hcross {x y : E} (hx : ‖x‖ ≤ R) (hy : R ≤ ‖y‖) :
      dist (g x) (g y) ≤ (K : ℝ) * dist x y := by
    obtain ⟨u, hu, hzu⟩ := exists_segment_norm_eq hx hy
    let z : E := (1 - u) • x + u • y
    have hzmem : z ∈ closedBall (0 : E) R := by
      simp [mem_closedBall, dist_zero_right, z, hzu]
    have hxmem : x ∈ closedBall (0 : E) R := by
      simpa [mem_closedBall, dist_zero_right]
    have hgz : g z = 0 := hzero z (by simp [z, hzu])
    have hgy : g y = 0 := hzero y hy
    calc
      dist (g x) (g y) = dist (g x) (g z) := by rw [hgz, hgy]
      _ ≤ (K : ℝ) * dist x z := hK.dist_le_mul x hxmem z hzmem
      _ ≤ (K : ℝ) * dist x y := by
        gcongr
        rw [dist_eq_norm, dist_eq_norm]
        have hxy : x - z = u • (x - y) := by
          simp only [z]
          module
        rw [hxy, norm_smul, Real.norm_eq_abs, abs_of_nonneg hu.1]
        exact mul_le_of_le_one_left (norm_nonneg _) hu.2
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rcases le_total ‖x‖ R with hx | hx
  · rcases le_total ‖y‖ R with hy | hy
    · exact hK.dist_le_mul x
        (by simpa [mem_closedBall, dist_zero_right]) y
        (by simpa [mem_closedBall, dist_zero_right])
    · exact hcross hx hy
  · rcases le_total ‖y‖ R with hy | hy
    · simpa only [dist_comm] using hcross hy hx
    · rw [hzero x hx, hzero y hy, dist_zero]
      simpa using mul_nonneg K.coe_nonneg (dist_nonneg : 0 ≤ dist x y)

end

end HGAS
