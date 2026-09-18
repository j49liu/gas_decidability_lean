import HGAS.Analysis.CenteredCubeC1PolynomialApproximation
import HGAS.Lyapunov.HomogeneousConverseApproximation
import Mathlib.Tactic

/-!
# `C¹` polynomial approximation on the Euclidean unit sphere

Every point of the Euclidean unit sphere lies in the centered cube
`[-1,1]^n`.  Consequently the centered-cube Bernstein theorem restricts
immediately to the sphere used by the homogeneous converse-Lyapunov
argument.
-/

namespace HGAS

open Set

noncomputable section

variable {n : ℕ}

/-- The Euclidean unit sphere is contained in `[-1,1]^n`. -/
theorem euclideanUnitSphere_subset_closedCenteredUnitCubeSet :
    euclideanUnitSphere n ⊆
      closedCenteredUnitCubeSet n := by
  intro x hx
  rw [mem_closedCenteredUnitCubeSet]
  have hnorm :
      ‖x‖ ≤ 1 :=
    norm_le_one_of_normSq_eq_one x hx
  rw [pi_norm_le_iff_of_nonneg
    (by norm_num : (0 : ℝ) ≤ 1)] at hnorm
  intro i
  have hi := hnorm i
  rw [Real.norm_eq_abs] at hi
  exact (abs_le.mp hi)

/-- Restriction of the centered-cube `C¹` approximation theorem to the
Euclidean unit sphere. -/
theorem hasC1MvPolynomialApproximationOn_euclideanUnitSphere_of_centeredCube
    (f : (Fin n → ℝ) → ℝ)
    (D : (Fin n → ℝ) → Fin n → ℝ)
    (hf :
      ContinuousOn f
        (closedCenteredUnitCubeSet n))
    (hD :
      ∀ i,
        ContinuousOn (fun x ↦ D x i)
          (closedCenteredUnitCubeSet n))
    (hderiv :
      ∀ x ∈ closedCenteredUnitCubeSet n, ∀ i,
        HasDerivAt
          (fun t : ℝ ↦
            f (Function.update x i t))
          (D x i) (x i)) :
    HasC1MvPolynomialApproximationOn
      (euclideanUnitSphere n) f D := by
  exact
    (hasC1MvPolynomialApproximationOn_closedCenteredUnitCube
      f D hf hD hderiv).mono
        euclideanUnitSphere_subset_closedCenteredUnitCubeSet

/-- Convenient global-hypothesis form of the sphere theorem. -/
theorem hasC1MvPolynomialApproximationOn_euclideanUnitSphere
    (f : (Fin n → ℝ) → ℝ)
    (D : (Fin n → ℝ) → Fin n → ℝ)
    (hf : Continuous f)
    (hD : ∀ i, Continuous (fun x ↦ D x i))
    (hderiv :
      ∀ x, ∀ i,
        HasDerivAt
          (fun t : ℝ ↦
            f (Function.update x i t))
          (D x i) (x i)) :
    HasC1MvPolynomialApproximationOn
      (euclideanUnitSphere n) f D := by
  apply
    hasC1MvPolynomialApproximationOn_euclideanUnitSphere_of_centeredCube
  · exact hf.continuousOn
  · intro i
    exact (hD i).continuousOn
  · intro x hx i
    exact hderiv x i

/-- Every globally `C¹` scalar function has the simultaneous value-and-
gradient polynomial approximation property needed on the Euclidean unit
sphere. -/
theorem ContDiff.hasC1MvPolynomialApproximationOn_euclideanUnitSphere
    (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ 1 f) :
    HasC1MvPolynomialApproximationOn
      (euclideanUnitSphere n) f
      (fun x i ↦ fderiv ℝ f x (Pi.single i 1)) := by
  apply HGAS.hasC1MvPolynomialApproximationOn_euclideanUnitSphere
  · exact hf.continuous
  · intro i
    exact
      (hf.continuous_fderiv one_ne_zero).clm_apply
        continuous_const
  · intro x i
    have hcomp :=
      (hf.differentiable one_ne_zero
          (Function.update x i (x i))).hasFDerivAt.comp_hasDerivAt
        (x i) (hasDerivAt_update x i (x i))
    simpa using hcomp

end

end HGAS
