import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-!
# Zero solutions of time-dependent linear ODEs

Polynomial reductions often impose algebraic relations by adjoining their
residuals to the state.  After differentiating, the residual vector usually
satisfies a time-dependent *linear homogeneous* equation

```
                         r'(t) = A(t) r(t).
```

The elementary but important conclusion is that a residual which vanishes
at one time vanishes for the entire trajectory.  This file packages that
argument independently of polynomials.

The coefficient operator is only assumed continuous; it need not be
globally bounded.  For each compact interval between the initial and target
times, continuity supplies an operator-norm bound.  ODE uniqueness on that
interval then compares the given solution with the identically zero
solution.  This local-on-compact proof is reusable for complex residual
systems after realification as well as for ordinary real systems.
-/

namespace HGAS

open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A solution of a continuous time-dependent linear homogeneous ODE which
is zero at one time is identically zero.

This formulation takes `A t` to be a real continuous linear endomorphism.
Complex-linear residual systems fit it by forgetting complex linearity. -/
theorem eq_zero_of_hasDerivAt_eq_continuousLinearMap
    (A : ℝ → E →L[ℝ] E) (r : ℝ → E)
    (hA : Continuous A)
    (hr : ∀ t : ℝ, HasDerivAt r (A t (r t)) t)
    {t₀ : ℝ} (hr₀ : r t₀ = 0) :
    r = fun _ ↦ 0 := by
  have hr_cont : Continuous r :=
    continuous_iff_continuousAt.mpr fun t ↦ (hr t).continuousAt
  funext t
  rcases le_total t₀ t with ht | ht
  · obtain ⟨(C : ℝ), hC⟩ :=
      (isCompact_Icc : IsCompact (Icc t₀ t)).exists_bound_of_continuousOn
        hA.continuousOn
    let K : NNReal := ⟨max C 0, le_max_right C 0⟩
    have hLip :
        ∀ s ∈ Ico t₀ t,
          LipschitzOnWith K (A s) (univ : Set E) := by
      intro s hs
      apply LipschitzWith.lipschitzOnWith
      apply (A s).lipschitz.weaken
      apply NNReal.coe_le_coe.mp
      change ‖A s‖ ≤ max C 0
      exact (hC s ⟨hs.1, hs.2.le⟩).trans (le_max_left C 0)
    have hzero :
        ∀ s ∈ Ico t₀ t,
          HasDerivWithinAt (fun _ : ℝ ↦ (0 : E))
            (A s 0) (Ici s) s := by
      intro s hs
      simpa using (hasDerivAt_const s (0 : E)).hasDerivWithinAt
    have heq :=
      ODE_solution_unique_of_mem_Icc_right
        (v := fun s x ↦ A s x)
        (s := fun _ ↦ (univ : Set E))
        hLip
        hr_cont.continuousOn
        (fun s hs ↦ (hr s).hasDerivWithinAt)
        (fun _ _ ↦ trivial)
        continuous_const.continuousOn
        hzero
        (fun _ _ ↦ trivial)
        hr₀
    exact heq ⟨ht, le_rfl⟩
  · obtain ⟨(C : ℝ), hC⟩ :=
      (isCompact_Icc : IsCompact (Icc t t₀)).exists_bound_of_continuousOn
        hA.continuousOn
    let K : NNReal := ⟨max C 0, le_max_right C 0⟩
    have hLip :
        ∀ s ∈ Ioc t t₀,
          LipschitzOnWith K (A s) (univ : Set E) := by
      intro s hs
      apply LipschitzWith.lipschitzOnWith
      apply (A s).lipschitz.weaken
      apply NNReal.coe_le_coe.mp
      change ‖A s‖ ≤ max C 0
      exact (hC s ⟨hs.1.le, hs.2⟩).trans (le_max_left C 0)
    have hzero :
        ∀ s ∈ Ioc t t₀,
          HasDerivWithinAt (fun _ : ℝ ↦ (0 : E))
            (A s 0) (Iic s) s := by
      intro s hs
      simpa using (hasDerivAt_const s (0 : E)).hasDerivWithinAt
    have heq :=
      ODE_solution_unique_of_mem_Icc_left
        (v := fun s x ↦ A s x)
        (s := fun _ ↦ (univ : Set E))
        hLip
        hr_cont.continuousOn
        (fun s hs ↦ (hr s).hasDerivWithinAt)
        (fun _ _ ↦ trivial)
        continuous_const.continuousOn
        hzero
        (fun _ _ ↦ trivial)
        hr₀
    exact heq ⟨le_rfl, ht⟩

/-- Scalar complex specialization.  If `r' = a r` with continuous complex
coefficient `a`, a single zero of `r` propagates for all real times. -/
theorem complex_eq_zero_of_hasDerivAt_eq_mul
    (a r : ℝ → ℂ)
    (ha : Continuous a)
    (hr : ∀ t : ℝ, HasDerivAt r (a t * r t) t)
    {t₀ : ℝ} (hr₀ : r t₀ = 0) :
    r = fun _ ↦ 0 := by
  let A : ℝ → ℂ →L[ℝ] ℂ :=
    fun t ↦ ContinuousLinearMap.lsmul ℝ ℂ (a t)
  apply eq_zero_of_hasDerivAt_eq_continuousLinearMap A r
  · exact (ContinuousLinearMap.lsmul ℝ ℂ).continuous.comp ha
  · intro t
    simpa [A] using hr t
  · exact hr₀

/-- Scalar real specialization.  A solution of `r' = a r` which vanishes
once vanishes for all real time. -/
theorem real_eq_zero_of_hasDerivAt_eq_mul
    (a r : ℝ → ℝ)
    (ha : Continuous a)
    (hr : ∀ t : ℝ, HasDerivAt r (a t * r t) t)
    {t₀ : ℝ} (hr₀ : r t₀ = 0) :
    r = fun _ ↦ 0 := by
  let A : ℝ → ℝ →L[ℝ] ℝ :=
    fun t ↦ ContinuousLinearMap.lsmul ℝ ℝ (a t)
  apply eq_zero_of_hasDerivAt_eq_continuousLinearMap A r
  · exact (ContinuousLinearMap.lsmul ℝ ℝ).continuous.comp ha
  · intro t
    simpa [A] using hr t
  · exact hr₀

end

end HGAS
