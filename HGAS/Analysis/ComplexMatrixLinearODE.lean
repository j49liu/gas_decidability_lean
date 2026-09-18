import HGAS.Analysis.LinearODEZero
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Finite complex matrix ODEs as real continuous-linear ODEs

Complex polynomial residuals are usually written as a finite matrix system
`r' = M(t) r`.  The general uniqueness theorem in `LinearODEZero` is
formulated for real continuous-linear operators.  This module provides the
reusable conversion and the corresponding zero-propagation theorem.
-/

namespace HGAS

noncomputable section

/-- A complex matrix, regarded first as a complex-linear endomorphism. -/
def complexMatrixContinuousLinearMap {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) :
    (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' M)

/-- A complex matrix endomorphism with scalars restricted to `ℝ`. -/
def complexMatrixRealContinuousLinearMap {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) :
    (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) :=
  (complexMatrixContinuousLinearMap M).restrictScalars ℝ

@[simp] theorem complexMatrixRealContinuousLinearMap_apply
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (r : Fin n → ℂ) (i : Fin n) :
    complexMatrixRealContinuousLinearMap M r i =
      ∑ j, M i j * r j := by
  change Matrix.toLin' M r i = _
  rw [Matrix.toLin'_apply]
  rfl

/-- Continuous matrix coefficients give a continuous family of
real continuous-linear endomorphisms. -/
theorem continuous_complexMatrixRealContinuousLinearMap
    {n : ℕ} {M : ℝ → Matrix (Fin n) (Fin n) ℂ}
    (hM : Continuous M) :
    Continuous
      (fun t ↦ complexMatrixRealContinuousLinearMap (M t)) := by
  let L :
      Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ]
        ((Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp
      Matrix.toLin'.toLinearMap
  have hcomplex :
      Continuous
        (fun t ↦ complexMatrixContinuousLinearMap (M t)) :=
    L.continuous_of_finiteDimensional.comp hM
  exact
    (ContinuousLinearMap.restrictScalarsL
      ℂ (Fin n → ℂ) (Fin n → ℂ) ℝ ℝ).continuous.comp
        hcomplex

/-- A solution of a finite continuous complex matrix ODE which vanishes at
one time vanishes identically. -/
theorem complexMatrixODE_eq_zero
    {n : ℕ} (M : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (r : ℝ → Fin n → ℂ)
    (hM : Continuous M)
    (hr : ∀ t : ℝ,
      HasDerivAt r
        (fun i ↦ ∑ j, M t i j * r t j) t)
    {t₀ : ℝ} (hr₀ : r t₀ = 0) :
    r = fun _ ↦ 0 := by
  apply eq_zero_of_hasDerivAt_eq_continuousLinearMap
    (fun t ↦
      complexMatrixRealContinuousLinearMap (M t)) r
  · exact
      continuous_complexMatrixRealContinuousLinearMap hM
  · intro t
    simpa using hr t
  · exact hr₀

end

end HGAS
