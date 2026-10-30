import HGAS.Stability.KordaLyapunov
import HGAS.Dynamics.LinearConjugacyGAS
import Mathlib.Tactic

/-!
# Lyapunov stability under linear changes of coordinates

Lyapunov stability with existence of solutions is invariant under a
continuous linear equivalence.  This is used to transport the angular
criterion (Korda's Lemma 2.2) from Euclidean space to the source and weighted
Veronese coordinates.
-/

namespace HGAS

open Set

noncomputable section

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Lyapunov stability (with existence) is preserved by a continuous linear
coordinate equivalence. -/
theorem LyapunovStableWithExistence.conjugateField
    (e : E ≃L[ℝ] H) {F : E → E}
    (hls : LyapunovStableWithExistence F 0) :
    LyapunovStableWithExistence (conjugateField e F) 0 := by
  let C : ℝ := max ‖e.toContinuousLinearMap‖ 1
  let D : ℝ := max ‖e.symm.toContinuousLinearMap‖ 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have heBound : ∀ x : E, ‖e x‖ ≤ C * ‖x‖ := fun x ↦
    (e.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x))
  have hesymmBound : ∀ y : H, ‖e.symm y‖ ≤ D * ‖y‖ := fun y ↦
    (e.symm.toContinuousLinearMap.le_opNorm y).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg y))
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := hls (ε / C) (div_pos hε hC)
  refine ⟨δ / D, div_pos hδ hD, ?_⟩
  intro y₀ hy₀
  have hx₀ : dist (e.symm y₀) 0 < δ := by
    rw [dist_zero_right]
    rw [dist_zero_right] at hy₀
    calc
      ‖e.symm y₀‖ ≤ D * ‖y₀‖ := hesymmBound y₀
      _ < D * (δ / D) := mul_lt_mul_of_pos_left hy₀ hD
      _ = δ := by field_simp
  refine ⟨?_, ?_⟩
  · obtain ⟨γ, hγ⟩ := (hball (e.symm y₀) hx₀).1
    refine ⟨fun t ↦ e (γ t), ?_⟩
    simpa using hγ.map_continuousLinearEquiv e
  · intro η hη t ht
    have hγ : IsForwardTrajectory F (fun s ↦ e.symm (η s)) (e.symm y₀) :=
      hη.comap_continuousLinearEquiv e
    have hsmall := (hball (e.symm y₀) hx₀).2 _ hγ t ht
    rw [show η t = e (e.symm (η t)) by simp]
    rw [dist_zero_right] at hsmall ⊢
    calc
      ‖e (e.symm (η t))‖ ≤ C * ‖e.symm (η t)‖ := heBound _
      _ < C * (ε / C) := mul_lt_mul_of_pos_left hsmall hC
      _ = ε := by field_simp

/-- Coordinate-invariant form of the preceding theorem. -/
theorem lyapunovStableWithExistence_conjugateField_iff
    (e : E ≃L[ℝ] H) (F : E → E) :
    LyapunovStableWithExistence (conjugateField e F) 0 ↔
      LyapunovStableWithExistence F 0 := by
  constructor
  · intro h
    have h' := h.conjugateField e.symm
    simpa only [conjugateField_symm_conjugateField] using h'
  · intro h
    exact h.conjugateField e

end

end HGAS
