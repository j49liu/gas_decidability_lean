import HGAS.Analysis.PolynomialCubeBounds
import Mathlib.Tactic

/-!
# Uniform margins for strict polynomial positivity

Strict positivity of a homogeneous polynomial is tested on a compact
cross-section of the rays through the origin.  This file records the compact
minimum argument in a form that can be reused by both the Lyapunov search and
the cubic transverse-stabilization development.

The result is deliberately stated for the ordinary norm-one sphere.  Every
point of that sphere lies in the coordinatewise unit cube, so the explicit
coefficient estimates in `PolynomialCubeBounds` apply without changing
constants.
-/

namespace HGAS

open MvPolynomial Set

noncomputable section

variable {n : ℕ}

/-- A rational polynomial which is positive at every point of the unit
sphere has one uniform positive real margin there. -/
theorem exists_pos_lower_bound_ratMvPolynomialEval_on_unitSphere
    (p : MvPolynomial (Fin n) ℚ)
    (hpos : ∀ x : Fin n → ℝ, ‖x‖ = 1 →
      0 < ratMvPolynomialEval p x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : Fin n → ℝ, ‖x‖ = 1 →
      ε ≤ ratMvPolynomialEval p x := by
  obtain ⟨ε, hε, hbound⟩ :=
    (isCompact_sphere (0 : Fin n → ℝ) 1).exists_forall_le'
      (contDiff_ratMvPolynomialEval p).continuous.continuousOn
      (a := 0) (by
        intro x hx
        exact hpos x (by
          simpa [Metric.mem_sphere, dist_zero_right] using hx))
  refine ⟨ε, hε, ?_⟩
  intro x hx
  exact hbound x (by
    simpa [Metric.mem_sphere, dist_zero_right] using hx)

/-- On the unit sphere, the value of a perturbation is bounded by its
coefficient `ℓ¹` norm. -/
theorem abs_ratMvPolynomialEval_sub_le_cubeAbsBound
    (p q : MvPolynomial (Fin n) ℚ) (x : Fin n → ℝ)
    (hx : ‖x‖ = 1) :
    |ratMvPolynomialEval p x - ratMvPolynomialEval q x| ≤
      polynomialCubeAbsBound (p - q) := by
  have hcoord : ∀ i, |x i| ≤ 1 := by
    intro i
    simpa [Real.norm_eq_abs, hx] using norm_le_pi_norm x i
  convert
    abs_ratMvPolynomialEval_le_cubeAbsBound (p - q) x hcoord using 1
  simp [ratMvPolynomialEval]

/-- A coefficient perturbation smaller than a strict sphere margin preserves
strict positivity on the sphere. -/
theorem ratMvPolynomialEval_pos_on_unitSphere_of_cubeAbsBound_lt
    (p q : MvPolynomial (Fin n) ℚ) {ε : ℝ}
    (hmargin : ∀ x : Fin n → ℝ, ‖x‖ = 1 →
      ε ≤ ratMvPolynomialEval p x)
    (hclose : polynomialCubeAbsBound (p - q) < ε) :
    ∀ x : Fin n → ℝ, ‖x‖ = 1 →
      0 < ratMvPolynomialEval q x := by
  intro x hx
  have herr :=
    abs_ratMvPolynomialEval_sub_le_cubeAbsBound p q x hx
  have hlower := hmargin x hx
  have hdiff :
      ratMvPolynomialEval p x - ratMvPolynomialEval q x ≤
        polynomialCubeAbsBound (p - q) :=
    (le_abs_self _).trans herr
  linarith

end

end HGAS
