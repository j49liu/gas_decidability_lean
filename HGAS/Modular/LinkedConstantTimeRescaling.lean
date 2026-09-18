import HGAS.Modular.JacobiCoefficientLinkDynamics
import HGAS.Modular.UnaryConstantTimeRescaling
import Mathlib.Tactic

/-!
# Constant time rescaling for the full linked Jacobi trajectory

The unary rescaling theorem is already available independently.  This
module gives the corresponding reusable statement for all ten Jacobi
coordinates and combines both parts into the fourteen-coordinate linked
trajectory interface.
-/

namespace HGAS.Modular

noncomputable section

/-- Rescaling real time by `a` multiplies both Jacobi clocks by `a`. -/
theorem IsScaledJacobiTrajectory.rescale
    {κZ κPhi : ℂ}
    {z : ℝ → JacobiState ℂ}
    (hz : IsScaledJacobiTrajectory κZ κPhi z)
    (a : ℝ) :
    IsScaledJacobiTrajectory
      ((a : ℂ) * κZ) ((a : ℂ) * κPhi)
      (fun t ↦ z (a * t)) := by
  have hinner (t : ℝ) :
      HasDerivAt (fun s : ℝ ↦ a * s) a t := by
    convert (hasDerivAt_id t).const_mul a using 1
    all_goals simp
  constructor
  · intro t
    have h := (hz.p2 (a * t)).scomp t (hinner t)
    convert h using 1
    simp only [Complex.real_smul,
      JacobiState.combinedVectorField]
    ring
  · intro t
    have h := (hz.p3 (a * t)).scomp t (hinner t)
    convert h using 1
    simp only [Complex.real_smul,
      JacobiState.combinedVectorField]
    ring
  · intro t
    have h := (hz.p4 (a * t)).scomp t (hinner t)
    convert h using 1
    simp only [Complex.real_smul,
      JacobiState.combinedVectorField]
    ring
  · intro t
    have h := (hz.H (a * t)).scomp t (hinner t)
    convert h using 1
    simp only [Complex.real_smul,
      JacobiState.combinedVectorField]
    ring
  · intro t
    have h := (hz.T1 (a * t)).scomp t (hinner t)
    convert h using 1
    simp only [Complex.real_smul,
      JacobiState.combinedVectorField]
    ring
  · intro t
    have h := (hz.T2 (a * t)).scomp t (hinner t)
    convert h using 1
    simp only [Complex.real_smul,
      JacobiState.combinedVectorField]
    ring
  · intro t
    have h := (hz.T3 (a * t)).scomp t (hinner t)
    convert h using 1
    simp only [Complex.real_smul,
      JacobiState.combinedVectorField]
    ring
  · intro t
    have h := (hz.T4 (a * t)).scomp t (hinner t)
    convert h using 1
    simp only [Complex.real_smul,
      JacobiState.combinedVectorField]
    ring
  · intro t
    have h := (hz.Delta (a * t)).scomp t (hinner t)
    convert h using 1
    simp only [Complex.real_smul,
      JacobiState.combinedVectorField]
    ring
  · intro t
    have h := (hz.U (a * t)).scomp t (hinner t)
    convert h using 1
    simp only [Complex.real_smul,
      JacobiState.combinedVectorField]
    ring

/-- Rescaling real time by `a` multiplies both clocks of a linked
unary--Jacobi trajectory by `a`. -/
theorem IsScaledLinkedJacobiTrajectory.rescale
    {κZ κPhi : ℂ}
    {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    (a : ℝ) :
    IsScaledLinkedJacobiTrajectory
      ((a : ℂ) * κZ) ((a : ℂ) * κPhi)
      (fun t ↦ z (a * t)) where
  unary := hz.unary.rescale a
  jacobi := hz.jacobi.rescale a

end

end HGAS.Modular
