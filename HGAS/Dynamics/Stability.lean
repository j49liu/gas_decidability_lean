import Mathlib.Analysis.ODE.Basic

/-!
# Global asymptotic stability for autonomous ODEs

This file gives reusable, trajectory-based definitions of forward
completeness, Lyapunov stability, global attraction, and global asymptotic
stability.

The definitions quantify over every forward integral curve. This avoids
silently assuming uniqueness at the definition level; uniqueness can be
added later from local Lipschitz hypotheses for polynomial vector fields.
-/

namespace HGAS

open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A solution of the autonomous ODE `x' = F x` on all nonnegative times,
with prescribed initial value. Values at negative times are immaterial. -/
def IsForwardTrajectory (F : E → E) (γ : ℝ → E) (x₀ : E) : Prop :=
  γ 0 = x₀ ∧ IsIntegralCurveOn γ (fun _ ↦ F) (Ici 0)

/-- Every initial state admits a trajectory defined on the whole forward
time ray. -/
def ForwardComplete (F : E → E) : Prop :=
  ∀ x₀ : E, ∃ γ : ℝ → E, IsForwardTrajectory F γ x₀

/-- Lyapunov stability of an equilibrium, expressed directly in the ambient
metric and quantified over every forward trajectory. -/
def LyapunovStable (F : E → E) (xEq : E) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x₀ : E, dist x₀ xEq < δ →
        ∀ γ : ℝ → E, IsForwardTrajectory F γ x₀ →
          ∀ t : ℝ, 0 ≤ t → dist (γ t) xEq < ε

/-- Every forward trajectory converges to the equilibrium, in the
epsilon–time form convenient for later estimates. -/
def GloballyAttractive (F : E → E) (xEq : E) : Prop :=
  ∀ x₀ : E, ∀ γ : ℝ → E, IsForwardTrajectory F γ x₀ →
    ∀ ε : ℝ, 0 < ε →
      ∃ T : ℝ, 0 ≤ T ∧
        ∀ t : ℝ, T ≤ t → dist (γ t) xEq < ε

/-- Global asymptotic stability includes the equilibrium identity, forward
completeness, Lyapunov stability, and global attraction. -/
structure GloballyAsymptoticallyStable (F : E → E) (xEq : E) : Prop where
  equilibrium : F xEq = 0
  forwardComplete : ForwardComplete F
  stable : LyapunovStable F xEq
  attractive : GloballyAttractive F xEq

namespace GloballyAsymptoticallyStable

variable {F : E → E} {xEq : E}

/-- GAS immediately supplies a forward trajectory through every state. -/
theorem exists_forwardTrajectory
    (h : GloballyAsymptoticallyStable F xEq) (x₀ : E) :
    ∃ γ : ℝ → E, IsForwardTrajectory F γ x₀ :=
  h.forwardComplete x₀

end GloballyAsymptoticallyStable

end

end HGAS
