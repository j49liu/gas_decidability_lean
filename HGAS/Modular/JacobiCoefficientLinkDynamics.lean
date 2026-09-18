import HGAS.Modular.JacobiCoefficientLinks
import HGAS.Modular.JacobiResidualDynamics
import HGAS.Modular.UnaryDynamics
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Trajectory-level invariance of the Jacobi coefficient links

This module upgrades the formal identities in `JacobiCoefficientLinks` to
an ODE theorem.  A linked trajectory consists of

* a unary modular trajectory with clock `κΦ`; and
* a Jacobi trajectory with combined clock `κZ 𝒵 + κΦ Φ`.

The five residuals

```
                    (R_J,L₂,L₃,L₄,L_H)
```

satisfy an explicit continuous `5×5` homogeneous linear system.  Thus
simultaneous vanishing propagates globally.  Once those residuals vanish,
the signed link `p₃-Y²` is a scalar homogeneous linear equation and also
propagates.
-/

namespace HGAS.Modular

open HGAS

noncomputable section

/-- A trajectory of the linked unary/Jacobi coefficient system. -/
structure IsScaledLinkedJacobiTrajectory
    (κZ κPhi : ℂ) (z : ℝ → LinkedJacobiState ℂ) : Prop where
  unary :
    IsScaledUnaryModularTrajectory κPhi
      (fun t ↦ (z t).unary)
  jacobi :
    IsScaledJacobiTrajectory κZ κPhi
      (fun t ↦ (z t).jacobi)

namespace IsScaledLinkedJacobiTrajectory

variable {κZ κPhi : ℂ}
  {z : ℝ → LinkedJacobiState ℂ}

/-! ## Calculus bridge -/

theorem link2_hasDerivAt_differential
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦ LinkedJacobiState.link2 (z s))
      (LinkedJacobiState.link2Differential (z t)
        (LinkedJacobiState.combinedVectorField
          κZ κPhi (z t))) t := by
  have hraw :=
    ((hz.jacobi.p2 t).fun_pow 2).sub
      (hz.unary.A t)
  convert hraw using 1
  simp only [LinkedJacobiState.link2Differential,
    LinkedJacobiState.combinedVectorField]
  ring

theorem link3_hasDerivAt_differential
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦ LinkedJacobiState.link3 (z s))
      (LinkedJacobiState.link3Differential (z t)
        (LinkedJacobiState.combinedVectorField
          κZ κPhi (z t))) t := by
  have hraw :=
    ((hz.jacobi.p3 t).fun_pow 2).sub
      ((hz.unary.Y t).fun_pow 4)
  convert hraw using 1
  simp only [LinkedJacobiState.link3Differential,
    LinkedJacobiState.combinedVectorField]
  ring

theorem link4_hasDerivAt_differential
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦ LinkedJacobiState.link4 (z s))
      (LinkedJacobiState.link4Differential (z t)
        (LinkedJacobiState.combinedVectorField
          κZ κPhi (z t))) t := by
  have hraw :=
    ((hz.jacobi.p4 t).fun_pow 2).sub
      (hz.unary.C t)
  convert hraw using 1
  simp only [LinkedJacobiState.link4Differential,
    LinkedJacobiState.combinedVectorField]
  ring

theorem linkH_hasDerivAt_differential
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦ LinkedJacobiState.linkH (z s))
      (LinkedJacobiState.linkHDifferential (z t)
        (LinkedJacobiState.combinedVectorField
          κZ κPhi (z t))) t := by
  have hraw :=
    (HasDerivAt.const_mul (12 : ℂ)
      (hz.jacobi.H t)).sub (hz.unary.E t)
  simpa only [LinkedJacobiState.linkHDifferential,
    LinkedJacobiState.combinedVectorField] using hraw

theorem signedLink3_hasDerivAt_differential
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦ LinkedJacobiState.signedLink3 (z s))
      (LinkedJacobiState.signedLink3Differential (z t)
        (LinkedJacobiState.combinedVectorField
          κZ κPhi (z t))) t := by
  have hraw :=
    (hz.jacobi.p3 t).sub
      ((hz.unary.Y t).fun_pow 2)
  convert hraw using 1
  simp only [LinkedJacobiState.signedLink3Differential,
    LinkedJacobiState.combinedVectorField]
  ring

/-! ## The coupled five-residual matrix -/

def coefficientResidualVector
    (z : ℝ → LinkedJacobiState ℂ) (t : ℝ) :
    Fin 5 → ℂ :=
  ![LinkedJacobiState.jacobiResidual (z t),
    LinkedJacobiState.link2 (z t),
    LinkedJacobiState.link3 (z t),
    LinkedJacobiState.link4 (z t),
    LinkedJacobiState.linkH (z t)]

def coefficientResidualMatrix
    (κPhi : ℂ)
    (z : ℝ → LinkedJacobiState ℂ) (t : ℝ) :
    Matrix (Fin 5) (Fin 5) ℂ :=
  !![
    κPhi * ((1 / 3 : ℂ) *
      ((z t).unary.E + (z t).unary.A -
        (z t).unary.C)),
    0, 0, 0, 0;
    κPhi * ((z t).jacobi.p2 ^ 2 / 3),
    κPhi * ((1 / 3 : ℂ) *
      ((z t).unary.E + (z t).unary.A +
        2 * (z t).unary.C)),
    κPhi * ((z t).jacobi.p2 ^ 2 / 3),
    κPhi * ((z t).jacobi.p2 ^ 2 / 3),
    κPhi * ((z t).jacobi.p2 ^ 2 / 3);
    0,
    κPhi * ((z t).jacobi.p3 ^ 2 / 3),
    κPhi * ((1 / 3 : ℂ) *
      ((z t).unary.E + (z t).unary.A -
        (z t).unary.C)),
    κPhi * (-(z t).jacobi.p3 ^ 2 / 3),
    κPhi * ((z t).jacobi.p3 ^ 2 / 3);
    κPhi * (-(z t).jacobi.p4 ^ 2 / 3),
    κPhi * (-(z t).jacobi.p4 ^ 2 / 3),
    κPhi * (-(z t).jacobi.p4 ^ 2 / 3),
    κPhi * ((1 / 3 : ℂ) *
      ((z t).unary.E - 2 * (z t).unary.A -
        (z t).unary.C)),
    κPhi * ((z t).jacobi.p4 ^ 2 / 3);
    κPhi *
      (-((z t).jacobi.p3 ^ 2 +
        (z t).unary.A + (z t).unary.C) / 12),
    κPhi *
      (-((z t).jacobi.p2 ^ 2 +
        (z t).unary.A) / 12),
    κPhi *
      (-((z t).jacobi.p3 ^ 2 +
        (z t).unary.A + (z t).unary.C) / 12),
    κPhi *
      (-((z t).jacobi.p4 ^ 2 +
        (z t).unary.C) / 12),
    κPhi *
      ((12 * (z t).jacobi.H +
        (z t).unary.E) / 6)
  ]

theorem continuous_coefficientResidualMatrix
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z) :
    Continuous (coefficientResidualMatrix κPhi z) := by
  have hA := hz.unary.continuous_A
  have hC := hz.unary.continuous_C
  have hE := hz.unary.continuous_E
  have hp2 := hz.jacobi.continuous_p2
  have hp3 := hz.jacobi.continuous_p3
  have hp4 := hz.jacobi.continuous_p4
  have hH := hz.jacobi.continuous_H
  unfold coefficientResidualMatrix
  fun_prop

theorem coefficientResidualVector_hasDerivAt
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    (t : ℝ) :
    HasDerivAt
      (coefficientResidualVector z)
      (fun i ↦
        ∑ j,
          coefficientResidualMatrix κPhi z t i j *
            coefficientResidualVector z t j) t := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · convert hz.unary.jacobiResidual_hasDerivAt t using 1
    simp [coefficientResidualVector,
      coefficientResidualMatrix,
      LinkedJacobiState.jacobiResidual,
      UnaryModularState.jacobiResidual,
      Fin.sum_univ_succ]
  · convert link2_hasDerivAt_differential hz t using 1
    rw [LinkedJacobiState.combined_link2_certificate]
    simp [coefficientResidualVector,
      coefficientResidualMatrix, Fin.sum_univ_succ]
    ring
  · convert link3_hasDerivAt_differential hz t using 1
    rw [LinkedJacobiState.combined_link3_certificate]
    simp [coefficientResidualVector,
      coefficientResidualMatrix, Fin.sum_univ_succ]
    ring
  · convert link4_hasDerivAt_differential hz t using 1
    rw [LinkedJacobiState.combined_link4_certificate]
    simp [coefficientResidualVector,
      coefficientResidualMatrix, Fin.sum_univ_succ]
    ring
  · convert linkH_hasDerivAt_differential hz t using 1
    rw [LinkedJacobiState.combined_linkH_certificate]
    simp [coefficientResidualVector,
      coefficientResidualMatrix, Fin.sum_univ_succ]
    ring

/-- All five unsigned coefficient residuals vanish. -/
def CoefficientResidualsZero
    (w : LinkedJacobiState ℂ) : Prop :=
  LinkedJacobiState.jacobiResidual w = 0 ∧
    LinkedJacobiState.link2 w = 0 ∧
      LinkedJacobiState.link3 w = 0 ∧
        LinkedJacobiState.link4 w = 0 ∧
          LinkedJacobiState.linkH w = 0

theorem coefficientResiduals_eq_zero
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    {t₀ : ℝ}
    (hzero : CoefficientResidualsZero (z t₀)) :
    ∀ t, CoefficientResidualsZero (z t) := by
  rcases hzero with ⟨hJ, h2, h3, h4, hH⟩
  have hinitial :
      coefficientResidualVector z t₀ = 0 := by
    funext i
    fin_cases i <;>
      simp [coefficientResidualVector,
        hJ, h2, h3, h4, hH]
  have hident :=
    HGAS.complexMatrixODE_eq_zero
      (coefficientResidualMatrix κPhi z)
      (coefficientResidualVector z)
      (continuous_coefficientResidualMatrix hz)
      (coefficientResidualVector_hasDerivAt hz)
      hinitial
  intro t
  have ht : coefficientResidualVector z t = 0 :=
    congrFun hident t
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [coefficientResidualVector] using
      congrFun ht (0 : Fin 5)
  · simpa [coefficientResidualVector] using
      congrFun ht (1 : Fin 5)
  · simpa [coefficientResidualVector] using
      congrFun ht (2 : Fin 5)
  · simpa [coefficientResidualVector] using
      congrFun ht (3 : Fin 5)
  · simpa [coefficientResidualVector] using
      congrFun ht (4 : Fin 5)

def signedLink3Coefficient
    (κPhi : ℂ)
    (z : ℝ → LinkedJacobiState ℂ) (t : ℝ) :
    ℂ :=
  κPhi * ((1 / 6 : ℂ) *
    (12 * (z t).jacobi.H +
      (z t).jacobi.p2 ^ 2 -
      (z t).jacobi.p4 ^ 2))

theorem continuous_signedLink3Coefficient
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z) :
    Continuous (signedLink3Coefficient κPhi z) := by
  have hp2 := hz.jacobi.continuous_p2
  have hp4 := hz.jacobi.continuous_p4
  have hH := hz.jacobi.continuous_H
  unfold signedLink3Coefficient
  fun_prop

/-- Vanishing of all unsigned links and the signed link propagates along
the full combined trajectory. -/
theorem signedLink3_eq_zero
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    {t₀ : ℝ}
    (hunsigned : CoefficientResidualsZero (z t₀))
    (hsigned :
      LinkedJacobiState.signedLink3 (z t₀) = 0) :
    ∀ t, LinkedJacobiState.signedLink3 (z t) = 0 := by
  have hall := coefficientResiduals_eq_zero hz hunsigned
  have hderiv :
      ∀ t,
        HasDerivAt
          (fun s ↦ LinkedJacobiState.signedLink3 (z s))
          (signedLink3Coefficient κPhi z t *
            LinkedJacobiState.signedLink3 (z t)) t := by
    intro t
    rcases hall t with ⟨_hJ, h2, _h3, h4, hH⟩
    convert signedLink3_hasDerivAt_differential hz t using 1
    rw [LinkedJacobiState.combined_signedLink3_certificate]
    simp [signedLink3Coefficient, h2, h4, hH]
    ring
  have hident :=
    complex_eq_zero_of_hasDerivAt_eq_mul
      (signedLink3Coefficient κPhi z)
      (fun t ↦ LinkedJacobiState.signedLink3 (z t))
      (continuous_signedLink3Coefficient hz)
      hderiv hsigned
  intro t
  exact congrFun hident t

end IsScaledLinkedJacobiTrajectory

end

end HGAS.Modular
