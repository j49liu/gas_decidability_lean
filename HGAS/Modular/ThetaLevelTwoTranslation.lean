import HGAS.Modular.CanonicalUnaryRoots
import HGAS.Modular.JacobiThetaHorizontalReduction
import HGAS.Modular.JacobiThetaResiduals
import HGAS.Modular.LevelOneSlashGenerators
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.Tactic

/-!
# Canonical root coordinates under translation by two

The remaining sign ambiguity in the selected coefficient `p₂` is not a
defect: it is exactly the level-two deck translation `τ ↦ τ + 2`.
Directly from the theta-series translation formulas,

```text
  θ₂(τ+2)² = -θ₂(τ)²,
  θ₃(τ+2)² =  θ₃(τ)²,
  θ₄(τ+2)² =  θ₄(τ)².
```

The quasimodular Eisenstein series `E₂` is invariant under translation,
so the `H=E₂/12` coordinate is unchanged.  This module packages the four
identities in the exact `canonicalUnaryRoots` interface used by Jacobi
pointwise saturation.
-/

namespace HGAS.Modular

open Complex
open UpperHalfPlane hiding I
open ModularForm ModularGroup SlashAction
open scoped MatrixGroups ModularForm

noncomputable section

/-- The square of the `θ₂` multiplier for one level-two translation is
`-1`. -/
theorem horizontalThetaMultiplier_one_sq :
    horizontalThetaMultiplier 1 ^ 2 = (-1 : ℂ) := by
  unfold horizontalThetaMultiplier
  calc
    cexp ((Real.pi : ℂ) * I * ((1 : ℤ) : ℂ) / 2) ^ 2 =
        cexp
          (2 * ((Real.pi : ℂ) * I *
            ((1 : ℤ) : ℂ) / 2)) := by
          simpa using
            (Complex.exp_nat_mul
              ((Real.pi : ℂ) * I *
                ((1 : ℤ) : ℂ) / 2) 2).symm
    _ = cexp ((Real.pi : ℂ) * I) := by
      congr 1
      norm_num
      ring
    _ = -1 := Complex.exp_pi_mul_I

/-- Translation by two negates the canonical `p₂=θ₂²` root. -/
theorem theta₂_sq_vadd_two (τ : ℍ) :
    theta₂ ((2 : ℝ) +ᵥ τ) ^ 2 =
      -(theta₂ τ ^ 2) := by
  have h :=
    jacobiTheta2_tau_add_two_int
      0 (τ : ℂ) 1
  have hcoe :
      ((((2 : ℝ) +ᵥ τ : ℍ) : ℂ)) =
        (τ : ℂ) + 2 * ((1 : ℤ) : ℂ) := by
    simp [coe_vadd]
    ring
  rw [← hcoe] at h
  rw [
    jacobiTheta2_zero_eq_theta₂,
    jacobiTheta2_zero_eq_theta₂] at h
  rw [h, mul_pow, horizontalThetaMultiplier_one_sq]
  ring

/-- Translation by two fixes the canonical `p₃=θ₃²` root. -/
theorem theta₃_sq_vadd_two (τ : ℍ) :
    theta₃ ((2 : ℝ) +ᵥ τ) ^ 2 =
      theta₃ τ ^ 2 := by
  have h :=
    jacobiTheta3_tau_add_two_int
      0 (τ : ℂ) 1
  have hcoe :
      ((((2 : ℝ) +ᵥ τ : ℍ) : ℂ)) =
        (τ : ℂ) + 2 * ((1 : ℤ) : ℂ) := by
    simp [coe_vadd]
    ring
  rw [← hcoe] at h
  rw [
    jacobiTheta3_zero_eq_theta₃,
    jacobiTheta3_zero_eq_theta₃] at h
  rw [h]

/-- Translation by two fixes the canonical `p₄=θ₄²` root. -/
theorem theta₄_sq_vadd_two (τ : ℍ) :
    theta₄ ((2 : ℝ) +ᵥ τ) ^ 2 =
      theta₄ τ ^ 2 := by
  have h :=
    jacobiTheta4_tau_add_two_int
      0 (τ : ℂ) 1
  have hcoe :
      ((((2 : ℝ) +ᵥ τ : ℍ) : ℂ)) =
        (τ : ℂ) + 2 * ((1 : ℤ) : ℂ) := by
    simp [coe_vadd]
    ring
  rw [← hcoe] at h
  rw [
    jacobiTheta4_zero_eq_theta₄,
    jacobiTheta4_zero_eq_theta₄] at h
  rw [h]

/-- `E₂` is fixed by the unit modular translation. -/
theorem E2_vadd_one (τ : ℍ) :
    EisensteinSeries.E2 ((1 : ℝ) +ᵥ τ) =
      EisensteinSeries.E2 τ := by
  have h :=
    congrFun
      (EisensteinSeries.E2_slash_action ModularGroup.T) τ
  rw [EisensteinSeries.D2_T] at h
  simpa [modularSlashT_apply] using h

/-- Consequently `E₂` is fixed by translation by two. -/
theorem E2_vadd_two (τ : ℍ) :
    EisensteinSeries.E2 ((2 : ℝ) +ᵥ τ) =
      EisensteinSeries.E2 τ := by
  have hfirst := E2_vadd_one τ
  have hsecond := E2_vadd_one ((1 : ℝ) +ᵥ τ)
  have hvadd :
      (1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ τ) =
        (2 : ℝ) +ᵥ τ := by
    rw [← add_vadd]
    norm_num
  rw [hvadd, hfirst] at hsecond
  exact hsecond

/-- Complete root-coordinate transformation under the level-two
translation. -/
theorem canonicalUnaryRoots_vadd_two (τ : ℍ) :
    (canonicalUnaryRoots ((2 : ℝ) +ᵥ τ)).p2 =
        -(canonicalUnaryRoots τ).p2 ∧
      (canonicalUnaryRoots ((2 : ℝ) +ᵥ τ)).p3 =
        (canonicalUnaryRoots τ).p3 ∧
      (canonicalUnaryRoots ((2 : ℝ) +ᵥ τ)).p4 =
        (canonicalUnaryRoots τ).p4 ∧
      (canonicalUnaryRoots ((2 : ℝ) +ᵥ τ)).H =
        (canonicalUnaryRoots τ).H := by
  exact
    ⟨theta₂_sq_vadd_two τ,
      theta₃_sq_vadd_two τ,
      theta₄_sq_vadd_two τ,
      by
        simp only [canonicalUnaryRoots_H]
        rw [E2_vadd_two]⟩

end

end HGAS.Modular
