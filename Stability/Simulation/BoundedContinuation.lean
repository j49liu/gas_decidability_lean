import Stability.Simulation.FormulaLocalExistence
import HGAS.Dynamics.ForwardCompleteness

/-!
# Continuation from uniform finite-horizon bounds

A locally Lipschitz field is cut off outside a large norm ball. The
cutoff field is bounded and globally Lipschitz. A first-exit argument
then turns an a priori bound for original solution segments into a
solution on any prescribed finite horizon. No differentiability of the
field is required. Local-Lipschitz uniqueness then patches these solutions
into a global forward curve.
-/

namespace Stability.Simulation

open Filter Metric Set
open scoped Topology NNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def normCutoffField (radius : ℝ) (f : E → E) (x : E) : E :=
  max 0 (min 1 (radius + 1 - ‖x‖)) • f x

private theorem normCutoffField_eq {radius : ℝ} {f : E → E} {x : E}
    (hx : ‖x‖ ≤ radius) : normCutoffField radius f x = f x := by
  have h : (1 : ℝ) ≤ radius + 1 - ‖x‖ := by linarith
  simp [normCutoffField, min_eq_left h]

private theorem normCutoffField_zero {radius : ℝ} {f : E → E} {x : E}
    (hx : radius + 1 ≤ ‖x‖) : normCutoffField radius f x = 0 := by
  have h : min 1 (radius + 1 - ‖x‖) ≤ (0 : ℝ) :=
    (min_le_right _ _).trans (by linarith)
  simp [normCutoffField, max_eq_left h]

private theorem normCutoffField_locallyLipschitz {f : E → E}
    (hf : LocallyLipschitz f) (radius : ℝ) : LocallyLipschitz (normCutoffField radius f) := by
  have hc : LocallyLipschitz (fun x : E ↦ max 0 (min 1 (radius + 1 - ‖x‖))) :=
    ((LocallyLipschitz.const (radius + 1)).sub lipschitzWith_one_norm.locallyLipschitz)
      |>.const_min 1 |>.const_max 0
  have hsmul : LocallyLipschitz (fun p : ℝ × E ↦ p.1 • p.2) :=
    (show ContDiff ℝ 1 (fun p : ℝ × E ↦ p.1 • p.2) from by fun_prop).locallyLipschitz
  exact hsmul.comp (hc.prodMk hf)

variable [CompleteSpace E] [ProperSpace E]

private theorem exists_global_cutoff_solution {f : E → E}
    (hf : LocallyLipschitz f) (radius : ℝ) (x₀ : E) :
    ∃ γ : ℝ → E, γ 0 = x₀ ∧ IsIntegralCurve γ (fun _ ↦ normCutoffField radius f) := by
  have hlocal := normCutoffField_locallyLipschitz hf radius
  have hcomp := isCompact_closedBall (0 : E) (radius + 1)
  obtain ⟨K, hK⟩ := hlocal.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hcomp
  have hglobal : LipschitzWith K (normCutoffField radius f) :=
    HGAS.lipschitzWith_of_lipschitzOn_closedBall_of_zero_outside hK
      (fun x hx ↦ normCutoffField_zero hx)
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hlocal.continuous.continuousOn
  let L : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hbound (x : E) : ‖normCutoffField radius f x‖ ≤ L := by
    by_cases hx : ‖x‖ ≤ radius + 1
    · exact (hC x (by simpa only [mem_closedBall, dist_zero_right] using hx)).trans
        (le_max_left _ _)
    · rw [normCutoffField_zero (le_of_not_ge hx), norm_zero]
      exact L.property
  exact HGAS.exists_global_integralCurve_of_lipschitz_bounded _ hglobal hbound x₀

/-- A uniform bound for every original solution segment through `x₀`
up to time `T` guarantees an actual solution on all of `[0,T]`.
The a priori premise concerns arbitrary supplied segments, not cutoffs. -/
theorem exists_solution_on_Icc_of_finite_bound {f : E → E}
    (hf : LocallyLipschitz f) (x₀ : E) {T R : ℝ}
    (hbound : ∀ b ∈ Icc (0 : ℝ) T, ∀ γ : ℝ → E,
      γ 0 = x₀ → ContinuousOn γ (Icc 0 b) →
      (∀ t ∈ Ioo 0 b, HasDerivAt γ (f (γ t)) t) →
      ∀ t ∈ Icc 0 b, ‖γ t‖ ≤ R) :
    ∃ γ : ℝ → E, γ 0 = x₀ ∧ Continuous γ ∧
      ∀ t ∈ Icc 0 T, HasDerivAt γ (f (γ t)) t := by
  obtain ⟨γ, hγ₀, hγ⟩ := exists_global_cutoff_solution hf (R + 1) x₀
  have hinside : ∀ t ∈ Icc (0 : ℝ) T, ‖γ t‖ < R + 1 := by
    by_contra! hbad
    obtain ⟨t, ht, hnorm⟩ := hbad
    let exits := Icc (0 : ℝ) T ∩ {r : ℝ | R + 1 ≤ ‖γ r‖}
    have hexits : IsCompact exits :=
      isCompact_Icc.inter_right (isClosed_le continuous_const hγ.continuous.norm)
    obtain ⟨τ, hτ⟩ := hexits.exists_isLeast ⟨t, ht, hnorm⟩
    have hbefore (r : ℝ) (hr : r ∈ Ioo 0 τ) : ‖γ r‖ < R + 1 := by
      by_contra! hlarge
      have hτr : τ ≤ r := hτ.2 ⟨⟨hr.1.le, hr.2.le.trans hτ.1.1.2⟩, hlarge⟩
      exact (not_lt_of_ge hτr) hr.2
    have horiginal : ∀ r ∈ Ioo 0 τ, HasDerivAt γ (f (γ r)) r := by
      intro r hr
      simpa only [normCutoffField_eq (hbefore r hr).le] using hγ r
    have hτbound := hbound τ hτ.1.1 γ hγ₀ hγ.continuous.continuousOn horiginal
      τ ⟨hτ.1.1.1, le_rfl⟩
    have hτnorm : R + 1 ≤ ‖γ τ‖ := hτ.1.2
    linarith
  refine ⟨γ, hγ₀, hγ.continuous, fun t ht ↦ ?_⟩
  simpa only [normCutoffField_eq (hinside t ht).le] using hγ t

omit [CompleteSpace E] in
private theorem solution_eqOn_of_locallyLipschitz {f : E → E}
    (hf : LocallyLipschitz f) {T : ℝ} {α β : ℝ → E}
    (hα : ContinuousOn α (Icc 0 T)) (hβ : ContinuousOn β (Icc 0 T))
    (hαderiv : ∀ t ∈ Icc 0 T, HasDerivAt α (f (α t)) t)
    (hβderiv : ∀ t ∈ Icc 0 T, HasDerivAt β (f (β t)) t)
    (hzero : α 0 = β 0) : EqOn α β (Icc 0 T) := by
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hα
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hβ
  obtain ⟨K, hK⟩ := hf.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : E) (max A B))
  apply ODE_solution_unique_of_mem_Icc_right (v := fun _ ↦ f)
    (s := fun _ ↦ closedBall 0 (max A B)) (K := K)
    (fun _ _ ↦ hK) hα
    (fun t ht ↦ (hαderiv t (Ico_subset_Icc_self ht)).hasDerivWithinAt) ?_ hβ
    (fun t ht ↦ (hβderiv t (Ico_subset_Icc_self ht)).hasDerivWithinAt) ?_ hzero
  · intro t ht
    simpa only [mem_closedBall, dist_zero_right] using
      (hA t (Ico_subset_Icc_self ht)).trans (le_max_left A B)
  · intro t ht
    simpa only [mem_closedBall, dist_zero_right] using
      (hB t (Ico_subset_Icc_self ht)).trans (le_max_right A B)

/-- Uniform a priori bounds on all finite horizons give an actual global
forward solution. Bounded-horizon solutions are constructed by cutoff
and agree by local-Lipschitz uniqueness before they are patched. -/
theorem exists_global_forward_solution_of_finite_bounds {f : E → E}
    (hf : LocallyLipschitz f) (x₀ : E)
    (hbound : ∀ T : ℝ, 0 ≤ T → ∃ R : ℝ, ∀ b ∈ Icc (0 : ℝ) T, ∀ γ : ℝ → E,
      γ 0 = x₀ → ContinuousOn γ (Icc 0 b) →
      (∀ t ∈ Ioo 0 b, HasDerivAt γ (f (γ t)) t) →
      ∀ t ∈ Icc 0 b, ‖γ t‖ ≤ R) :
    ∃ γ : ℝ → E, γ 0 = x₀ ∧
      ∀ t ≥ (0 : ℝ), HasDerivWithinAt γ (f (γ t)) (Ici 0) t := by
  have hfinite (T : ℝ) (hT : 0 < T) :
      ∃ γ : ℝ → E, γ 0 = x₀ ∧ Continuous γ ∧
        ∀ t ∈ Icc 0 T, HasDerivAt γ (f (γ t)) t := by
    obtain ⟨R, hR⟩ := hbound T hT.le
    exact exists_solution_on_Icc_of_finite_bound hf x₀ hR
  let localCurve : ℝ → ℝ → E := fun T ↦
    if hT : 0 < T then Classical.choose (hfinite T hT) else fun _ ↦ x₀
  have localCurve_zero (T : ℝ) (hT : 0 < T) : localCurve T 0 = x₀ := by
    simp only [localCurve, dif_pos hT]
    exact (Classical.choose_spec (hfinite T hT)).1
  have localCurve_continuous (T : ℝ) (hT : 0 < T) : Continuous (localCurve T) := by
    simp only [localCurve, dif_pos hT]
    exact (Classical.choose_spec (hfinite T hT)).2.1
  have localCurve_deriv (T : ℝ) (hT : 0 < T) :
      ∀ t ∈ Icc 0 T, HasDerivAt (localCurve T) (f (localCurve T t)) t := by
    simp only [localCurve, dif_pos hT]
    exact (Classical.choose_spec (hfinite T hT)).2.2
  have compatible {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
      EqOn (localCurve A) (localCurve B) (Icc 0 A) := by
    have hB := hA.trans_le hAB
    apply solution_eqOn_of_locallyLipschitz hf
      (localCurve_continuous A hA).continuousOn (localCurve_continuous B hB).continuousOn
      (localCurve_deriv A hA)
      (fun t ht ↦ localCurve_deriv B hB t ⟨ht.1, ht.2.trans hAB⟩)
    rw [localCurve_zero A hA, localCurve_zero B hB]
  let γ : ℝ → E := fun t ↦ localCurve (|t| + 1) t
  refine ⟨γ, by simp [γ, localCurve_zero], ?_⟩
  intro t ht
  let A : ℝ := t + 1
  have hA : 0 < A := by dsimp [A]; linarith
  have htA : t < A := by dsimp [A]; linarith
  have hpoint : γ t = localCurve A t := by simp only [γ, abs_of_nonneg ht, A]
  have heq : γ =ᶠ[𝓝[Ici 0] t] localCurve A := by
    change ∀ᶠ s in 𝓝[Ici 0] t, γ s = localCurve A s
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds htA] with s hs
    intro hs₀
    change 0 ≤ s at hs₀
    change localCurve (|s| + 1) s = localCurve A s
    by_cases hle : |s| + 1 ≤ A
    · exact compatible (by positivity) hle ⟨hs₀, by linarith [le_abs_self s]⟩
    · exact (compatible hA (le_of_not_ge hle) ⟨hs₀, hs.le⟩).symm
  rw [hpoint]
  exact HasDerivWithinAt.congr_of_eventuallyEq
    (localCurve_deriv A hA t ⟨ht, htA.le⟩).hasDerivWithinAt heq hpoint

end

end Stability.Simulation
