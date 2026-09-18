import HGAS.Compactification.Stereographic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-!
# Differentiating inverse stereographic trajectories

`Stereographic.lean` proves the pointwise algebra identifying the
derivative of inverse stereographic projection with the compact
accumulator field.  This file supplies the analytic chain rule.

It is stated coordinatewise because that is the natural interface for
finite polynomial ODEs and for bounded primitives over a compact base
flow.
-/

namespace HGAS

open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- Coordinatewise differentiability of a finite vector curve gives the
expected derivative of its algebraic squared norm. -/
theorem normSq_hasDerivAt_of_coordinates
    (z g : ℝ → FinVector n ℝ) (t : ℝ)
    (hz :
      ∀ i,
        HasDerivAt (fun s ↦ z s i) (g t i) t) :
    HasDerivAt
      (fun s ↦ normSq (z s))
      (2 * dot (z t) (g t)) t := by
  have hsum :
      HasDerivAt
        (fun s ↦ ∑ i : Fin n, z s i * z s i)
        (∑ i : Fin n,
          (g t i * z t i + z t i * g t i)) t := by
    apply HasDerivAt.fun_sum
    intro i _
    exact (hz i).mul (hz i)
  convert hsum using 1
  simp only [dot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Chain rule for the vector coordinate of inverse stereographic
projection. -/
theorem stereoU_hasDerivAt
    (z g : ℝ → FinVector n ℝ) (t : ℝ)
    (hz :
      ∀ i,
        HasDerivAt (fun s ↦ z s i) (g t i) t) :
    ∀ i,
      HasDerivAt
        (fun s ↦ stereoU (z s) i)
        (accumulatorUField
          (stereoU (z t)) (stereoW (z t)) (g t) i) t := by
  intro i
  have hnorm :=
    normSq_hasDerivAt_of_coordinates z g t hz
  have hden : 1 + normSq (z t) ≠ 0 :=
    ne_of_gt (stereo_denominator_pos (z t))
  have hquot :=
    ((hz i).const_mul 2).div (hnorm.const_add 1) hden
  have hchart :
      HasDerivAt
        (fun s ↦ stereoU (z s) i)
        (stereoUDeriv (z t) (g t) i) t := by
    simpa only [stereoU, stereoUDeriv] using
      hquot.congr_deriv (by
        field_simp [hden]
        ring)
  rw [stereoUDeriv_eq_field] at hchart
  exact hchart

/-- Chain rule for the scalar coordinate of inverse stereographic
projection. -/
theorem stereoW_hasDerivAt
    (z g : ℝ → FinVector n ℝ) (t : ℝ)
    (hz :
      ∀ i,
        HasDerivAt (fun s ↦ z s i) (g t i) t) :
    HasDerivAt
      (fun s ↦ stereoW (z s))
      (accumulatorWField
        (stereoU (z t)) (stereoW (z t)) (g t)) t := by
  have hnorm :=
    normSq_hasDerivAt_of_coordinates z g t hz
  have hden : 1 + normSq (z t) ≠ 0 :=
    ne_of_gt (stereo_denominator_pos (z t))
  have hquot :=
    ((hasDerivAt_const t (1 : ℝ)).sub hnorm).div
      (hnorm.const_add 1) hden
  have hchart :
      HasDerivAt
        (fun s ↦ stereoW (z s))
        (stereoWDeriv (z t) (g t)) t := by
    simpa only [stereoW, stereoWDeriv] using
      hquot.congr_deriv (by
        simp only [Pi.sub_apply]
        field_simp [hden]
        ring)
  rw [stereoWDeriv_eq_field] at hchart
  exact hchart

end

end HGAS
