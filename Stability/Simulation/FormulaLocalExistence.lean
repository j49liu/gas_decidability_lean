import Stability.Simulation.ClockedMonitorFormula
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-!
# Local solutions for absolute-value formula fields

Finite absolute-value formulas define locally Lipschitz maps, even when
they are not continuously differentiable. This gives genuine local
solutions through every state of the clocked monitor. Continuation to
arbitrarily large positive times is a separate assertion.
-/

namespace Stability.Simulation

open Filter Metric Set
open scoped Topology NNReal

noncomputable section

namespace AbsFormula

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

/-- Absolute-value formulas are locally Lipschitz in their real coordinates. -/
theorem locallyLipschitz_eval (e : AbsFormula σ) :
    LocallyLipschitz (fun x : σ → ℝ ↦ eval x e) := by
  induction e with
  | coordinate i => exact (LipschitzWith.eval i).locallyLipschitz
  | constant c => exact LocallyLipschitz.const (c : ℝ)
  | add e f he hf => exact he.add hf
  | mul e f he hf =>
      have hm : LocallyLipschitz (fun p : ℝ × ℝ ↦ p.1 * p.2) :=
        (show ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ p.1 * p.2) from by fun_prop).locallyLipschitz
      exact hm.comp (he.prodMk hf)
  | abs e he =>
      simpa only [Real.norm_eq_abs] using
        (lipschitzWith_one_norm (E := ℝ)).locallyLipschitz.comp he

/-- A finite family of formulas is locally Lipschitz as a vector-valued map. -/
theorem locallyLipschitz_family (formulas : τ → AbsFormula σ) :
    LocallyLipschitz (fun x : σ → ℝ ↦ fun i ↦ eval x (formulas i)) := by
  intro x
  have hcomp := isCompact_closedBall x (1 : ℝ)
  have hcoord (i : τ) : ∃ K : ℝ≥0,
      LipschitzOnWith K (fun y ↦ eval y (formulas i)) (closedBall x 1) :=
    (locallyLipschitz_eval (formulas i)).locallyLipschitzOn
      |>.exists_lipschitzOnWith_of_compact hcomp
  choose K hK using hcoord
  refine ⟨Finset.univ.sup K, closedBall x 1, closedBall_mem_nhds x zero_lt_one, ?_⟩
  intro y hy z hz
  apply edist_pi_le_iff.mpr
  intro i
  exact (hK i).weaken (Finset.le_sup (Finset.mem_univ i)) hy hz

end AbsFormula

/-- A locally Lipschitz field on a proper complete real normed space has
a genuine solution on a neighborhood of any prescribed initial time. -/
theorem exists_local_solution_of_locallyLipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [ProperSpace E] {f : E → E}
    (hf : LocallyLipschitz f) (x₀ : E) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ α : ℝ → E, α t₀ = x₀ ∧
      ContinuousOn α (Icc (t₀ - ε) (t₀ + ε)) ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (f (α t)) t := by
  have hcomp := isCompact_closedBall x₀ (1 : ℝ)
  obtain ⟨K, hK⟩ := hf.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hcomp
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hf.continuous.continuousOn
  let L : ℝ≥0 := ⟨max C 0 + 1, by positivity⟩
  have hL : 0 < (L : ℝ) := by
    change 0 < max C 0 + 1
    linarith [le_max_right C 0]
  let ε : ℝ := (L : ℝ)⁻¹
  have hε : 0 < ε := inv_pos.mpr hL
  let time : Icc (t₀ - ε) (t₀ + ε) := ⟨t₀, by constructor <;> linarith⟩
  have hPL : IsPicardLindelof (fun _ ↦ f) time x₀ 1 0 L K := by
    apply IsPicardLindelof.of_time_independent
    · intro x hx
      apply (hC x hx).trans
      change C ≤ max C 0 + 1
      linarith [le_max_left C 0]
    · exact hK
    · change (L : ℝ) * max (t₀ + ε - t₀) (t₀ - (t₀ - ε)) ≤ (1 : ℝ) - 0
      simp only [add_sub_cancel_left, sub_sub_cancel, max_self, sub_zero]
      exact le_of_eq (mul_inv_cancel₀ hL.ne')
  obtain ⟨α, hα₀, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨ε, hε, α, hα₀, HasDerivWithinAt.continuousOn hα, ?_⟩
  intro t ht
  exact (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

namespace ClockedMonitor

variable {k s : ℕ}

/-- Local Lipschitz regularity of the actual, unsmoothed monitor field. -/
theorem locallyLipschitz_field (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) :
    LocallyLipschitz (field program entry initial) := by
  simpa only [eval_fieldFormula] using
    AbsFormula.locallyLipschitz_family (fieldFormula program entry initial)

/-- Every initial monitor state lies on an actual local trajectory. -/
theorem exists_local_solution (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (x₀ : MonitorCoordinate k → ℝ) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ α : ℝ → MonitorCoordinate k → ℝ, α t₀ = x₀ ∧
      ContinuousOn α (Icc (t₀ - ε) (t₀ + ε)) ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt α (field program entry initial (α t)) t :=
  exists_local_solution_of_locallyLipschitz
    (locallyLipschitz_field program entry initial) x₀ t₀

end ClockedMonitor

end

end Stability.Simulation
