import HGAS.Analysis.ComplexMatrixLinearODE
import HGAS.Modular.JacobiAlgebra
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Trajectory-level invariance of the Jacobi residual ideal

`JacobiAlgebra` checks the formal ideal-membership identities for the four
regular Jacobi-chart residuals.  This file turns those identities into an
honest trajectory theorem.

We allow any constant complex linear combination

```
                         κZ 𝒵 + κΦ Φ
```

of the elliptic and modular derivations.  The physical two-clock vector
field is a special case.  Along every differentiable trajectory, the
residual vector

```
                         (R₀,R₁,R₂,Rᵁ)
```

satisfies an explicit continuous `4×4` homogeneous linear ODE.  Finite
dimensional ODE uniqueness then proves that simultaneous vanishing at one
time propagates for all real time.

This is the rigorous trajectory-level content behind the phrase “the
residual ideal is invariant.”  Merely checking formal ideal membership
would not by itself establish this analytic conclusion.
-/

namespace HGAS.Modular

open HGAS

noncomputable section

/-- A real-time trajectory of a fixed linear combination of the two
Jacobi derivations. -/
structure IsScaledJacobiTrajectory
    (κZ κPhi : ℂ) (z : ℝ → JacobiState ℂ) : Prop where
  p2 : ∀ t, HasDerivAt (fun s ↦ (z s).p2)
    (JacobiState.combinedVectorField κZ κPhi (z t)).p2 t
  p3 : ∀ t, HasDerivAt (fun s ↦ (z s).p3)
    (JacobiState.combinedVectorField κZ κPhi (z t)).p3 t
  p4 : ∀ t, HasDerivAt (fun s ↦ (z s).p4)
    (JacobiState.combinedVectorField κZ κPhi (z t)).p4 t
  H : ∀ t, HasDerivAt (fun s ↦ (z s).H)
    (JacobiState.combinedVectorField κZ κPhi (z t)).H t
  T1 : ∀ t, HasDerivAt (fun s ↦ (z s).T1)
    (JacobiState.combinedVectorField κZ κPhi (z t)).T1 t
  T2 : ∀ t, HasDerivAt (fun s ↦ (z s).T2)
    (JacobiState.combinedVectorField κZ κPhi (z t)).T2 t
  T3 : ∀ t, HasDerivAt (fun s ↦ (z s).T3)
    (JacobiState.combinedVectorField κZ κPhi (z t)).T3 t
  T4 : ∀ t, HasDerivAt (fun s ↦ (z s).T4)
    (JacobiState.combinedVectorField κZ κPhi (z t)).T4 t
  Delta : ∀ t, HasDerivAt (fun s ↦ (z s).Delta)
    (JacobiState.combinedVectorField κZ κPhi (z t)).Delta t
  U : ∀ t, HasDerivAt (fun s ↦ (z s).U)
    (JacobiState.combinedVectorField κZ κPhi (z t)).U t

namespace IsScaledJacobiTrajectory

variable {κZ κPhi : ℂ} {z : ℝ → JacobiState ℂ}

/-! ## Coordinate continuity -/

theorem continuous_p2
    (hz : IsScaledJacobiTrajectory κZ κPhi z) :
    Continuous (fun t ↦ (z t).p2) :=
  continuous_iff_continuousAt.mpr
    fun t ↦ (hz.p2 t).continuousAt

theorem continuous_p3
    (hz : IsScaledJacobiTrajectory κZ κPhi z) :
    Continuous (fun t ↦ (z t).p3) :=
  continuous_iff_continuousAt.mpr
    fun t ↦ (hz.p3 t).continuousAt

theorem continuous_p4
    (hz : IsScaledJacobiTrajectory κZ κPhi z) :
    Continuous (fun t ↦ (z t).p4) :=
  continuous_iff_continuousAt.mpr
    fun t ↦ (hz.p4 t).continuousAt

theorem continuous_H
    (hz : IsScaledJacobiTrajectory κZ κPhi z) :
    Continuous (fun t ↦ (z t).H) :=
  continuous_iff_continuousAt.mpr
    fun t ↦ (hz.H t).continuousAt

theorem continuous_T1
    (hz : IsScaledJacobiTrajectory κZ κPhi z) :
    Continuous (fun t ↦ (z t).T1) :=
  continuous_iff_continuousAt.mpr
    fun t ↦ (hz.T1 t).continuousAt

theorem continuous_T2
    (hz : IsScaledJacobiTrajectory κZ κPhi z) :
    Continuous (fun t ↦ (z t).T2) :=
  continuous_iff_continuousAt.mpr
    fun t ↦ (hz.T2 t).continuousAt

theorem continuous_T3
    (hz : IsScaledJacobiTrajectory κZ κPhi z) :
    Continuous (fun t ↦ (z t).T3) :=
  continuous_iff_continuousAt.mpr
    fun t ↦ (hz.T3 t).continuousAt

theorem continuous_T4
    (hz : IsScaledJacobiTrajectory κZ κPhi z) :
    Continuous (fun t ↦ (z t).T4) :=
  continuous_iff_continuousAt.mpr
    fun t ↦ (hz.T4 t).continuousAt

theorem continuous_Delta
    (hz : IsScaledJacobiTrajectory κZ κPhi z) :
    Continuous (fun t ↦ (z t).Delta) :=
  continuous_iff_continuousAt.mpr
    fun t ↦ (hz.Delta t).continuousAt

theorem continuous_U
    (hz : IsScaledJacobiTrajectory κZ κPhi z) :
    Continuous (fun t ↦ (z t).U) :=
  continuous_iff_continuousAt.mpr
    fun t ↦ (hz.U t).continuousAt

/-! ## Calculus bridge from coordinate equations to formal differentials -/

theorem residualR0_hasDerivAt_differential
    (hz : IsScaledJacobiTrajectory κZ κPhi z)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦ JacobiState.residualR0 (z s))
      (JacobiState.residualR0Differential (z t)
        (JacobiState.combinedVectorField κZ κPhi (z t))) t := by
  have hraw :=
    (((hz.p3 t).fun_pow 2).sub
      ((hz.p2 t).fun_pow 2)).sub
        ((hz.p4 t).fun_pow 2)
  convert hraw using 1
  simp only [JacobiState.residualR0Differential]
  ring

theorem residualR1_hasDerivAt_differential
    (hz : IsScaledJacobiTrajectory κZ κPhi z)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦ JacobiState.residualR1 (z s))
      (JacobiState.residualR1Differential (z t)
        (JacobiState.combinedVectorField κZ κPhi (z t))) t := by
  have hfirst :=
    (hz.p2 t).mul ((hz.T4 t).fun_pow 2)
  have hsecond :=
    (hz.p4 t).mul ((hz.T2 t).fun_pow 2)
  have hthird :=
    (hz.p3 t).mul ((hz.T1 t).fun_pow 2)
  have hraw := (hfirst.sub hsecond).sub hthird
  convert hraw using 1
  simp only [JacobiState.residualR1Differential]
  ring

theorem residualR2_hasDerivAt_differential
    (hz : IsScaledJacobiTrajectory κZ κPhi z)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦ JacobiState.residualR2 (z s))
      (JacobiState.residualR2Differential (z t)
        (JacobiState.combinedVectorField κZ κPhi (z t))) t := by
  have hfirst :=
    (hz.p2 t).mul ((hz.T3 t).fun_pow 2)
  have hsecond :=
    (hz.p3 t).mul ((hz.T2 t).fun_pow 2)
  have hthird :=
    (hz.p4 t).mul ((hz.T1 t).fun_pow 2)
  have hraw := (hfirst.sub hsecond).sub hthird
  convert hraw using 1
  simp only [JacobiState.residualR2Differential]
  ring

theorem residualRU_hasDerivAt_differential
    (hz : IsScaledJacobiTrajectory κZ κPhi z)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦ JacobiState.residualRU (z s))
      (JacobiState.residualRUDifferential (z t)
        (JacobiState.combinedVectorField κZ κPhi (z t))) t := by
  have hraw :=
    ((hz.U t).mul (hz.T1 t)).sub_const 1
  simpa only [JacobiState.residualRU,
    JacobiState.residualRUDifferential] using hraw

/-! ## Explicit residual matrix -/

/-- Residual vector ordered as `(R₀,R₁,R₂,Rᵁ)`. -/
def residualVector
    (z : ℝ → JacobiState ℂ) (t : ℝ) :
    Fin 4 → ℂ :=
  ![JacobiState.residualR0 (z t),
    JacobiState.residualR1 (z t),
    JacobiState.residualR2 (z t),
    JacobiState.residualRU (z t)]

/-- Coefficient matrix of the homogeneous residual ODE. -/
def residualMatrix
    (κZ κPhi : ℂ) (z : ℝ → JacobiState ℂ)
    (t : ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  !![
    κPhi * (4 * (z t).H), 0, 0, 0;
    κPhi * JacobiState.q10 (z t),
    κZ * (2 * (z t).U * (z t).Delta) +
      κPhi * JacobiState.q11 (z t),
    κPhi * JacobiState.q12 (z t),
    κZ * (2 * (z t).p3 * (z t).T1 * (z t).Delta) +
      κPhi * JacobiState.q1U (z t);
    κPhi * JacobiState.q20 (z t),
    κPhi * JacobiState.q21 (z t),
    κZ * (2 * (z t).U * (z t).Delta) +
      κPhi * JacobiState.q22 (z t),
    κZ * (2 * (z t).p4 * (z t).T1 * (z t).Delta) +
      κPhi * JacobiState.q2U (z t);
    0, 0, 0,
    κZ * (-(z t).U * (z t).Delta) +
      κPhi *
        (-(z t).U *
          (JacobiState.modularVectorField (z t)).T1)
  ]

theorem continuous_residualMatrix
    (hz : IsScaledJacobiTrajectory κZ κPhi z) :
    Continuous (residualMatrix κZ κPhi z) := by
  have hp2 := continuous_p2 hz
  have hp3 := continuous_p3 hz
  have hp4 := continuous_p4 hz
  have hH := continuous_H hz
  have hT1 := continuous_T1 hz
  have hT2 := continuous_T2 hz
  have hT3 := continuous_T3 hz
  have hT4 := continuous_T4 hz
  have hDelta := continuous_Delta hz
  have hU := continuous_U hz
  unfold residualMatrix JacobiState.q10 JacobiState.q11
    JacobiState.q12 JacobiState.q1U JacobiState.q20
    JacobiState.q21 JacobiState.q22 JacobiState.q2U
    JacobiState.modularVectorField JacobiState.K
  fun_prop

theorem residualVector_hasDerivAt
    (hz : IsScaledJacobiTrajectory κZ κPhi z)
    (t : ℝ) :
    HasDerivAt
      (residualVector z)
      (fun i ↦
        ∑ j,
          residualMatrix κZ κPhi z t i j *
            residualVector z t j) t := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · convert residualR0_hasDerivAt_differential hz t using 1
    rw [JacobiState.combined_residualR0_certificate]
    simp [residualVector, residualMatrix,
      Fin.sum_univ_succ]
    ring
  · convert residualR1_hasDerivAt_differential hz t using 1
    rw [JacobiState.combined_residualR1_certificate]
    simp [residualVector, residualMatrix,
      Fin.sum_univ_succ]
    ring
  · convert residualR2_hasDerivAt_differential hz t using 1
    rw [JacobiState.combined_residualR2_certificate]
    simp [residualVector, residualMatrix,
      Fin.sum_univ_succ]
    ring
  · convert residualRU_hasDerivAt_differential hz t using 1
    rw [JacobiState.combined_residualRU_certificate]
    simp [residualVector, residualMatrix,
      Fin.sum_univ_succ]

/-! ## Simultaneous zero propagation -/

/-- All four regular Jacobi-chart residuals vanish. -/
def ResidualsZero (w : JacobiState ℂ) : Prop :=
  JacobiState.residualR0 w = 0 ∧
    JacobiState.residualR1 w = 0 ∧
      JacobiState.residualR2 w = 0 ∧
        JacobiState.residualRU w = 0

/-- If the four residuals vanish at one time, they vanish throughout the
entire trajectory. -/
theorem residuals_eq_zero
    (hz : IsScaledJacobiTrajectory κZ κPhi z)
    {t₀ : ℝ} (hzero : ResidualsZero (z t₀)) :
    ∀ t, ResidualsZero (z t) := by
  rcases hzero with ⟨h0, h1, h2, hU⟩
  have hinitial : residualVector z t₀ = 0 := by
    funext i
    fin_cases i <;>
      simp [residualVector, h0, h1, h2, hU]
  have hident :=
    HGAS.complexMatrixODE_eq_zero
      (residualMatrix κZ κPhi z)
      (residualVector z)
      (continuous_residualMatrix hz)
      (residualVector_hasDerivAt hz)
      hinitial
  intro t
  have ht : residualVector z t = 0 :=
    congrFun hident t
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [residualVector] using
      congrFun ht (0 : Fin 4)
  · simpa [residualVector] using
      congrFun ht (1 : Fin 4)
  · simpa [residualVector] using
      congrFun ht (2 : Fin 4)
  · simpa [residualVector] using
      congrFun ht (3 : Fin 4)

end IsScaledJacobiTrajectory

end

end HGAS.Modular
