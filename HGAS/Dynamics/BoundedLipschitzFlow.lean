import HGAS.Dynamics.ForwardCompleteness
import Mathlib.Dynamics.Flow
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic

/-!
# The flow of a bounded globally Lipschitz vector field

`ForwardCompleteness` constructs a global integral curve through each point.
This file makes the construction coherent in the initial point and packages
it as a genuine continuous `Flow ℝ E`.

There are three ingredients.

* ODE uniqueness gives the flow law.
* Grönwall gives
  `dist (Φ t x) (Φ t y) ≤ dist x y * exp (K * |t|)`.
* That estimate, together with continuity of each individual trajectory,
  gives joint continuity in `(t,x)`.

The result is deliberately independent of the polynomial application.  It
can be reused whenever a compact cutoff turns a locally Lipschitz vector
field into a bounded globally Lipschitz one.
-/

namespace HGAS

open Set Filter Function Metric
open scoped Topology NNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-- Our chosen global solution through `x`.  All algebraic properties of
this choice will follow from uniqueness of solutions. -/
noncomputable def globalCurve
    (f : E → E) {K L : ℝ≥0}
    (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)
    (x : E) : ℝ → E :=
  Classical.choose
    (exists_global_integralCurve_of_lipschitz_bounded f hK hL x)

@[simp]
theorem globalCurve_zero
    (f : E → E) {K L : ℝ≥0}
    (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)
    (x : E) :
    globalCurve f hK hL x 0 = x :=
  (Classical.choose_spec
    (exists_global_integralCurve_of_lipschitz_bounded f hK hL x)).1

/-- The chosen curve solves the autonomous ODE at every real time. -/
theorem globalCurve_isIntegralCurve
    (f : E → E) {K L : ℝ≥0}
    (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)
    (x : E) :
    IsIntegralCurve (globalCurve f hK hL x) (fun _ ↦ f) :=
  (Classical.choose_spec
    (exists_global_integralCurve_of_lipschitz_bounded f hK hL x)).2

/-! ## Dependence on the initial point -/

/-- Forward-time Grönwall estimate for two chosen trajectories. -/
theorem globalCurve_dist_le_of_nonneg
    (f : E → E) {K L : ℝ≥0}
    (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)
    (x y : E) (t : ℝ) (ht : 0 ≤ t) :
    dist (globalCurve f hK hL x t)
        (globalCurve f hK hL y t) ≤
      dist x y * Real.exp ((K : ℝ) * t) := by
  have hbound :=
    dist_le_of_trajectories_ODE
      (v := fun _ : ℝ ↦ f) (K := K)
      (a := 0) (b := t) (δ := dist x y)
      (fun _ ↦ hK)
      (globalCurve_isIntegralCurve f hK hL x).continuous.continuousOn
      (fun s _ ↦
        ((globalCurve_isIntegralCurve f hK hL x) s).hasDerivWithinAt)
      (globalCurve_isIntegralCurve f hK hL y).continuous.continuousOn
      (fun s _ ↦
        ((globalCurve_isIntegralCurve f hK hL y) s).hasDerivWithinAt)
      (by simp)
      t ⟨ht, le_rfl⟩
  simpa using hbound

/-- Backward-time Grönwall estimate, proved by reversing both trajectories
and applying the forward estimate to the vector field `-f`. -/
theorem globalCurve_dist_le_of_nonpos
    (f : E → E) {K L : ℝ≥0}
    (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)
    (x y : E) (t : ℝ) (ht : t ≤ 0) :
    dist (globalCurve f hK hL x t)
        (globalCurve f hK hL y t) ≤
      dist x y * Real.exp ((K : ℝ) * (-t)) := by
  let γx : ℝ → E := fun s ↦ globalCurve f hK hL x (-s)
  let γy : ℝ → E := fun s ↦ globalCurve f hK hL y (-s)
  have hγx : IsIntegralCurve γx (fun _ ↦ -f) := by
    intro s
    have h :=
      ((globalCurve_isIntegralCurve f hK hL x) (-s)).scomp s
        (hasDerivAt_neg s)
    simpa [γx, Function.comp_def] using h
  have hγy : IsIntegralCurve γy (fun _ ↦ -f) := by
    intro s
    have h :=
      ((globalCurve_isIntegralCurve f hK hL y) (-s)).scomp s
        (hasDerivAt_neg s)
    simpa [γy, Function.comp_def] using h
  have hbound :=
    dist_le_of_trajectories_ODE
      (v := fun _ : ℝ ↦ -f) (K := K)
      (a := 0) (b := -t) (δ := dist x y)
      (fun _ ↦ hK.neg)
      hγx.continuous.continuousOn
      (fun s _ ↦ (hγx s).hasDerivWithinAt)
      hγy.continuous.continuousOn
      (fun s _ ↦ (hγy s).hasDerivWithinAt)
      (by simp [γx, γy])
      (-t) ⟨by linarith, le_rfl⟩
  simpa [γx, γy] using hbound

/-- Two-sided Grönwall estimate.  This is the key uniform-in-the-initial-data
bound used for joint continuity of the flow. -/
theorem globalCurve_dist_le
    (f : E → E) {K L : ℝ≥0}
    (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)
    (x y : E) (t : ℝ) :
    dist (globalCurve f hK hL x t)
        (globalCurve f hK hL y t) ≤
      dist x y * Real.exp ((K : ℝ) * |t|) := by
  rcases le_total 0 t with ht | ht
  · simpa [abs_of_nonneg ht] using
      globalCurve_dist_le_of_nonneg f hK hL x y t ht
  · simpa [abs_of_nonpos ht] using
      globalCurve_dist_le_of_nonpos f hK hL x y t ht

/-! ## Flow law and joint continuity -/

/-- Time translation of a solution is the solution through the translated
point.  This is the flow law, before packaging the curves as a `Flow`. -/
theorem globalCurve_add
    (f : E → E) {K L : ℝ≥0}
    (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)
    (x : E) (t₁ t₂ : ℝ) :
    globalCurve f hK hL x (t₁ + t₂) =
      globalCurve f hK hL (globalCurve f hK hL x t₂) t₁ := by
  let γ₁ : ℝ → E := fun s ↦ globalCurve f hK hL x (s + t₂)
  let γ₂ : ℝ → E :=
    globalCurve f hK hL (globalCurve f hK hL x t₂)
  have hγ₁ : IsIntegralCurve γ₁ (fun _ ↦ f) := by
    intro s
    simpa [γ₁] using
      ((globalCurve_isIntegralCurve f hK hL x) (s + t₂)).comp_add_const s t₂
  have hγ₂ : IsIntegralCurve γ₂ (fun _ ↦ f) := by
    simpa [γ₂] using
      globalCurve_isIntegralCurve f hK hL
        (globalCurve f hK hL x t₂)
  have heq : γ₁ = γ₂ := by
    apply ODE_solution_unique_univ
      (v := fun _ : ℝ ↦ f) (s := fun _ ↦ (Set.univ : Set E))
      (K := K) (t₀ := 0)
    · intro _
      exact hK.lipschitzOnWith
    · intro s
      exact ⟨hγ₁ s, Set.mem_univ _⟩
    · intro s
      exact ⟨hγ₂ s, Set.mem_univ _⟩
    · simp [γ₁, γ₂]
  simpa [γ₁, γ₂] using congrFun heq t₁

/-- The solution map is jointly continuous in time and initial point.

For `(s,y)` near `(t,x)`, insert the intermediate point `Φ(s,x)`.  The
distance from `Φ(s,y)` to `Φ(s,x)` is controlled by the two-sided Grönwall
estimate, while `Φ(s,x) → Φ(t,x)` follows from continuity of the one fixed
trajectory through `x`. -/
theorem continuous_uncurry_globalCurve
    (f : E → E) {K L : ℝ≥0}
    (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L) :
    Continuous
      (Function.uncurry fun t x ↦ globalCurve f hK hL x t) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t, x⟩
  let Φ : ℝ × E → E := fun p ↦ globalCurve f hK hL p.2 p.1
  let g : ℝ × E → ℝ := fun p ↦
    dist p.2 x * Real.exp ((K : ℝ) * |p.1|) +
      dist (globalCurve f hK hL x p.1) (globalCurve f hK hL x t)
  have hg_nonneg : ∀ p, 0 ≤ g p := by
    intro p
    dsimp [g]
    positivity
  have hΦ_le : ∀ p, dist (Φ p) (Φ (t, x)) ≤ g p := by
    intro p
    calc
      dist (Φ p) (Φ (t, x)) ≤
          dist (globalCurve f hK hL p.2 p.1)
              (globalCurve f hK hL x p.1) +
            dist (globalCurve f hK hL x p.1)
              (globalCurve f hK hL x t) := by
        simpa [Φ] using
          dist_triangle
            (globalCurve f hK hL p.2 p.1)
            (globalCurve f hK hL x p.1)
            (globalCurve f hK hL x t)
      _ ≤ g p := by
        dsimp [g]
        gcongr
        exact globalCurve_dist_le f hK hL p.2 x p.1
  have hg_cont : ContinuousAt g (t, x) := by
    have hcurve :
        Continuous (globalCurve f hK hL x) :=
      (globalCurve_isIntegralCurve f hK hL x).continuous
    have hcurveAt :
        ContinuousAt
          (fun p : ℝ × E ↦ globalCurve f hK hL x p.1) (t, x) :=
      hcurve.continuousAt.comp continuousAt_fst
    have hdx :
        ContinuousAt (fun p : ℝ × E ↦ dist p.2 x) (t, x) :=
      continuousAt_snd.dist continuousAt_const
    have hexp :
        ContinuousAt
          (fun p : ℝ × E ↦ Real.exp ((K : ℝ) * |p.1|)) (t, x) := by
      have hmul :
          ContinuousAt
            (fun p : ℝ × E ↦ (K : ℝ) * |p.1|) (t, x) :=
        continuousAt_const.mul continuousAt_fst.abs
      exact Real.continuous_exp.continuousAt.comp hmul
    have hdt :
        ContinuousAt
          (fun p : ℝ × E ↦
            dist (globalCurve f hK hL x p.1)
              (globalCurve f hK hL x t)) (t, x) :=
      hcurveAt.dist continuousAt_const
    simpa [g] using (hdx.mul hexp).add hdt
  have hg_zero : g (t, x) = 0 := by
    simp [g]
  change Tendsto Φ (𝓝 (t, x)) (𝓝 (Φ (t, x)))
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero
  · exact fun _ ↦ dist_nonneg
  · exact hΦ_le
  · change Tendsto g (𝓝 (t, x)) (𝓝 (g (t, x))) at hg_cont
    rwa [hg_zero] at hg_cont

/-- The global flow generated by a bounded globally Lipschitz autonomous
vector field. -/
noncomputable def boundedLipschitzFlow
    (f : E → E) {K L : ℝ≥0}
    (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L) :
    Flow ℝ E where
  toFun t x := globalCurve f hK hL x t
  cont' := continuous_uncurry_globalCurve f hK hL
  map_add' t₁ t₂ x := globalCurve_add f hK hL x t₁ t₂
  map_zero' x := globalCurve_zero f hK hL x

@[simp]
theorem boundedLipschitzFlow_apply
    (f : E → E) {K L : ℝ≥0}
    (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)
    (t : ℝ) (x : E) :
    boundedLipschitzFlow f hK hL t x =
      globalCurve f hK hL x t :=
  rfl

/-- Each orbit of `boundedLipschitzFlow` has derivative `f`. -/
theorem boundedLipschitzFlow_isIntegralCurve
    (f : E → E) {K L : ℝ≥0}
    (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)
    (x : E) :
    IsIntegralCurve (fun t ↦ boundedLipschitzFlow f hK hL t x)
      (fun _ ↦ f) :=
  globalCurve_isIntegralCurve f hK hL x

/-! ## A scalar uniqueness lemma for invariant level sets -/

/-- If `z' = b(t) z`, the coefficient `b` is continuous, and `z(0)=0`,
then `z` vanishes for all positive and negative times.

This elementary form of uniqueness is convenient for proving invariance of
a regular level set: after composing its defining function with an orbit,
the error from the level often satisfies precisely this scalar equation.
The proof uses Grönwall on each compact positive-time interval and applies
the same argument to the time-reversed functions for negative time. -/
theorem eq_zero_of_hasDerivAt_eq_mul_self
    (z b : ℝ → ℝ)
    (hz : ∀ t, HasDerivAt z (b t * z t) t)
    (hb : Continuous b) (hzero : z 0 = 0) :
    ∀ t, z t = 0 := by
  have hforward :
      ∀ (z₁ b₁ : ℝ → ℝ),
        (∀ s, HasDerivAt z₁ (b₁ s * z₁ s) s) →
        Continuous b₁ → z₁ 0 = 0 →
        ∀ T, 0 ≤ T → z₁ T = 0 := by
    intro z₁ b₁ hz₁ hb₁ hz₁zero T hT
    obtain ⟨C, hC⟩ :=
      isCompact_Icc.exists_bound_of_continuousOn hb₁.continuousOn
    have hz₁cont : Continuous z₁ := by
      rw [continuous_iff_continuousAt]
      exact fun s ↦ (hz₁ s).continuousAt
    apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (f := z₁) (f' := fun s ↦ b₁ s * z₁ s)
      (K := C) (a := 0) (b := T)
      hz₁cont.continuousOn
      (fun s _ ↦ (hz₁ s).hasDerivWithinAt)
      hz₁zero
      (fun s hs ↦ by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (hC s (Set.Ico_subset_Icc_self hs))
          (norm_nonneg _))
      T ⟨hT, le_rfl⟩
  intro t
  rcases le_total 0 t with ht | ht
  · exact hforward z b hz hb hzero t ht
  · let zr : ℝ → ℝ := fun s ↦ z (-s)
    let br : ℝ → ℝ := fun s ↦ -b (-s)
    have hzr : ∀ s, HasDerivAt zr (br s * zr s) s := by
      intro s
      have h := (hz (-s)).scomp s (hasDerivAt_neg s)
      simpa [zr, br, Function.comp_def] using h
    have hbr : Continuous br := by
      dsimp [br]
      fun_prop
    have hzrzero : zr 0 = 0 := by
      simpa [zr] using hzero
    have hresult :=
      hforward zr br hzr hbr hzrzero (-t) (neg_nonneg.mpr ht)
    simpa [zr] using hresult

end

end HGAS
