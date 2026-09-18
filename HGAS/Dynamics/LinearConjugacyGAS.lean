import HGAS.Dynamics.Stability
import HGAS.Propagation.DegreePadding
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic

/-!
# GAS under continuous linear changes of coordinates

If `e : E ≃L[ℝ] H` is a continuous linear equivalence, the vector field
transported to `H` is

```
G(y) = e (F (e⁻¹ y)).
```

This file proves directly from the trajectory-based definition that
`F` is globally asymptotically stable at the origin if and only if `G`
is.  Forward trajectories are pushed through `e` by the chain rule.
Lyapunov stability and attraction are transferred using the operator
norm bounds for `e` and `e⁻¹`.

The result is independent of finite dimensionality and is reusable for
normalizing positive-definite quadratic forms, including the weighted
Veronese form `Q`.
-/

namespace HGAS

open Function Metric Set

noncomputable section

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Transport a vector field through a continuous linear equivalence. -/
def conjugateField
    (e : E ≃L[ℝ] H) (F : E → E) : H → H :=
  fun y ↦ e (F (e.symm y))

@[simp]
theorem conjugateField_apply_equiv
    (e : E ≃L[ℝ] H) (F : E → E) (x : E) :
    conjugateField e F (e x) = e (F x) := by
  simp [conjugateField]

@[simp]
theorem conjugateField_symm_conjugateField
    (e : E ≃L[ℝ] H) (F : E → E) :
    conjugateField e.symm (conjugateField e F) = F := by
  funext x
  simp [conjugateField]

/-- A continuous linear change of coordinates preserves every order of
Fréchet differentiability. -/
theorem ContDiff.conjugateField
    (e : E ≃L[ℝ] H) {F : E → E} {m : WithTop ℕ∞}
    (hF : ContDiff ℝ m F) :
    ContDiff ℝ m (conjugateField e F) := by
  exact e.contDiff.comp (hF.comp e.symm.contDiff)

/-- Semantic homogeneity is invariant under a linear coordinate change. -/
theorem scalesAsDegree_conjugateField
    (e : E ≃L[ℝ] H) {F : E → E} {d : ℕ}
    (hF : ScalesAsDegree ℝ d F) :
    ScalesAsDegree ℝ d (conjugateField e F) := by
  intro c y
  simp only [conjugateField, map_smul]
  rw [hF]
  simp

/-- An equilibrium at the origin remains an equilibrium after a linear
coordinate change. -/
theorem conjugateField_zero
    (e : E ≃L[ℝ] H) {F : E → E}
    (hzero : F 0 = 0) :
    conjugateField e F 0 = 0 := by
  simp [conjugateField, hzero]

/-- A forward trajectory remains a trajectory after a continuous linear
change of coordinates. -/
theorem IsForwardTrajectory.map_continuousLinearEquiv
    (e : E ≃L[ℝ] H) {F : E → E}
    {γ : ℝ → E} {x₀ : E}
    (hγ : IsForwardTrajectory F γ x₀) :
    IsForwardTrajectory (conjugateField e F)
      (fun t ↦ e (γ t)) (e x₀) := by
  constructor
  · simp [hγ.1]
  · intro t ht
    have hcomp :=
      e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt
        t (hγ.2 t ht)
    simpa only [Function.comp_apply,
      conjugateField_apply_equiv] using hcomp

/-- A trajectory of the conjugated field pulls back to a trajectory of
the original field. -/
theorem IsForwardTrajectory.comap_continuousLinearEquiv
    (e : E ≃L[ℝ] H) {F : E → E}
    {η : ℝ → H} {y₀ : H}
    (hη : IsForwardTrajectory (conjugateField e F) η y₀) :
    IsForwardTrajectory F
      (fun t ↦ e.symm (η t)) (e.symm y₀) := by
  have hmap :=
    hη.map_continuousLinearEquiv e.symm
  simpa only [conjugateField_symm_conjugateField] using hmap

/-- Global asymptotic stability is preserved by a continuous linear
coordinate equivalence. -/
theorem GloballyAsymptoticallyStable.conjugateField
    (e : E ≃L[ℝ] H) {F : E → E}
    (hgas : GloballyAsymptoticallyStable F 0) :
    GloballyAsymptoticallyStable (conjugateField e F) 0 := by
  let C : ℝ := max ‖e.toContinuousLinearMap‖ 1
  let D : ℝ := max ‖e.symm.toContinuousLinearMap‖ 1
  have hC : 0 < C := by
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hD : 0 < D := by
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have heBound :
      ∀ x : E, ‖e x‖ ≤ C * ‖x‖ := by
    intro x
    exact (e.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right
        (le_max_left _ _) (norm_nonneg x))
  have hesymmBound :
      ∀ y : H, ‖e.symm y‖ ≤ D * ‖y‖ := by
    intro y
    exact (e.symm.toContinuousLinearMap.le_opNorm y).trans
      (mul_le_mul_of_nonneg_right
        (le_max_left _ _) (norm_nonneg y))
  refine
    { equilibrium := by
        change e (F (e.symm 0)) = 0
        rw [map_zero, hgas.equilibrium, map_zero]
      forwardComplete := ?_
      stable := ?_
      attractive := ?_ }
  · intro y₀
    obtain ⟨γ, hγ⟩ := hgas.forwardComplete (e.symm y₀)
    refine ⟨fun t ↦ e (γ t), ?_⟩
    simpa using hγ.map_continuousLinearEquiv e
  · intro ε hε
    obtain ⟨δ, hδ, hstable⟩ :=
      hgas.stable (ε / C) (div_pos hε hC)
    refine ⟨δ / D, div_pos hδ hD, ?_⟩
    intro y₀ hy₀ η hη t ht
    let x₀ : E := e.symm y₀
    let γ : ℝ → E := fun s ↦ e.symm (η s)
    have hγ :
        IsForwardTrajectory F γ x₀ := by
      exact hη.comap_continuousLinearEquiv e
    have hx₀ :
        dist x₀ 0 < δ := by
      rw [dist_zero_right]
      calc
        ‖x₀‖ ≤ D * ‖y₀‖ := hesymmBound y₀
        _ = D * dist y₀ 0 := by rw [dist_zero_right]
        _ < D * (δ / D) :=
          mul_lt_mul_of_pos_left hy₀ hD
        _ = δ := by field_simp [hD.ne']
    have hsmall :=
      hstable x₀ hx₀ γ hγ t ht
    rw [show η t = e (γ t) by
      simp [γ]]
    rw [dist_zero_right] at hsmall ⊢
    calc
      ‖e (γ t)‖ ≤ C * ‖γ t‖ := heBound (γ t)
      _ < C * (ε / C) :=
        mul_lt_mul_of_pos_left hsmall hC
      _ = ε := by field_simp [hC.ne']
  · intro y₀ η hη ε hε
    let x₀ : E := e.symm y₀
    let γ : ℝ → E := fun s ↦ e.symm (η s)
    have hγ :
        IsForwardTrajectory F γ x₀ :=
      hη.comap_continuousLinearEquiv e
    obtain ⟨T, hT, hattract⟩ :=
      hgas.attractive x₀ γ hγ
        (ε / C) (div_pos hε hC)
    refine ⟨T, hT, ?_⟩
    intro t ht
    have hsmall := hattract t ht
    rw [show η t = e (γ t) by
      simp [γ]]
    rw [dist_zero_right] at hsmall ⊢
    calc
      ‖e (γ t)‖ ≤ C * ‖γ t‖ := heBound (γ t)
      _ < C * (ε / C) :=
        mul_lt_mul_of_pos_left hsmall hC
      _ = ε := by field_simp [hC.ne']

/-- Coordinate-invariant form of the preceding theorem. -/
theorem globallyAsymptoticallyStable_conjugateField_iff
    (e : E ≃L[ℝ] H) (F : E → E) :
    GloballyAsymptoticallyStable (conjugateField e F) 0 ↔
      GloballyAsymptoticallyStable F 0 := by
  constructor
  · intro h
    have hback := h.conjugateField e.symm
    simpa only [conjugateField_symm_conjugateField] using hback
  · exact fun h ↦ h.conjugateField e

end

end HGAS
