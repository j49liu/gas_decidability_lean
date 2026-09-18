import HGAS.Modular.GammaTwoClosedHorocycleCuspNormalization
import HGAS.Modular.CanonicalLambdaLocal
import Mathlib.Tactic

/-!
# The three projective unary branches at a level-two cusp

The modular part of the detector initially recovers only the lambda
coordinate

```text
                         λ = A / (A + C).
```

For a closed `Γ(2)` horocycle, a primitive integral row is completed and
the resulting lift is made horizontal.  After the parity normalization in
`GammaTwoClosedHorocycleCuspNormalization`, the completion lies over one
of the three representatives

```text
                         1,  S,  S*T.
```

This file records the elementary, but important, algebraic consequence.
No theta multiplier or square-root convention is needed.  The
transformation law of lambda and Jacobi's identity

```text
                         H₃ = H₂ + H₄
```

already determine the projective quartic triple.

* At the infinity cusp, `(A,B,C)` is proportional to
  `(H₂,H₃,H₄)`.
* At the zero cusp, it is proportional to `(H₄,H₃,H₂)`.
* At the one cusp, it is proportional to `(-H₄,H₂,H₃)`.

Here `B=A+C`.  The common nonzero scale contains every automorphy factor,
orientation, and covering multiplicity.  Keeping that scale abstract is
both stronger and cleaner than choosing square roots prematurely.
-/

namespace HGAS.Modular

open Complex
open ModularGroup

noncomputable section

/-- The projective theta-quartic branch associated with one of the three
cusps of `Γ(2)`.  The common factor is required to be nonzero. -/
def IsCuspQuarticBranch
    (cusp : GammaTwoCuspLabel)
    (z : UnaryModularState ℂ) (τ : UpperHalfPlane) : Prop :=
  ∃ q : ℂ, q ≠ 0 ∧
    match cusp with
    | .infinity =>
        z.A = q * H₂ τ ∧
        UnaryModularState.B z = q * H₃ τ ∧
        z.C = q * H₄ τ
    | .zero =>
        z.A = q * H₄ τ ∧
        UnaryModularState.B z = q * H₃ τ ∧
        z.C = q * H₂ τ
    | .one =>
        z.A = -(q * H₄ τ) ∧
        UnaryModularState.B z = q * H₂ τ ∧
        z.C = q * H₃ τ

/-- Equality of the untransformed lambda coordinates determines the
canonical projective quartic branch. -/
theorem isCuspQuarticBranch_infinity_of_lambda
    (z : UnaryModularState ℂ) (τ : UpperHalfPlane)
    (hB : UnaryModularState.B z ≠ 0)
    (hlambda :
      canonicalLambda τ =
        UnaryModularState.lambdaCoordinate z) :
    IsCuspQuarticBranch .infinity z τ := by
  let q : ℂ := UnaryModularState.B z / H₃ τ
  have hq : q ≠ 0 :=
    div_ne_zero hB (H₃_ne_zero τ)
  have hJacobi : H₂ τ + H₄ τ = H₃ τ := by
    simpa only [Pi.add_apply] using
      congrFun jacobi_quartic_identity τ
  have hcross :
      H₂ τ * UnaryModularState.B z =
        z.A * H₃ τ := by
    unfold canonicalLambda
      UnaryModularState.lambdaCoordinate at hlambda
    field_simp [H₃_ne_zero τ, hB] at hlambda
    simpa only [mul_comm] using hlambda
  have hAcross :
      z.A * H₃ τ =
        UnaryModularState.B z * H₂ τ := by
    simpa only [mul_comm] using hcross.symm
  have hCcross :
      z.C * H₃ τ =
        UnaryModularState.B z * H₄ τ := by
    have hBsum :
        UnaryModularState.B z = z.A + z.C := rfl
    linear_combination
      -H₃ τ * hBsum - hAcross -
        UnaryModularState.B z * hJacobi
  refine ⟨q, hq, ?_, ?_, ?_⟩
  · rw [show q * H₂ τ =
        (UnaryModularState.B z * H₂ τ) / H₃ τ by
      simp only [q, div_eq_mul_inv]
      ring]
    exact (eq_div_iff (H₃_ne_zero τ)).2 hAcross
  · exact
      (div_mul_cancel₀
        (UnaryModularState.B z) (H₃_ne_zero τ)).symm
  · rw [show q * H₄ τ =
        (UnaryModularState.B z * H₄ τ) / H₃ τ by
      simp only [q, div_eq_mul_inv]
      ring]
    exact (eq_div_iff (H₃_ne_zero τ)).2 hCcross

/-- The `S` cross-ratio exchanges the two outer quartics. -/
theorem isCuspQuarticBranch_zero_of_lambda
    (z : UnaryModularState ℂ) (τ : UpperHalfPlane)
    (hB : UnaryModularState.B z ≠ 0)
    (hlambda :
      canonicalLambda τ =
        1 - UnaryModularState.lambdaCoordinate z) :
    IsCuspQuarticBranch .zero z τ := by
  let q : ℂ := UnaryModularState.B z / H₃ τ
  have hq : q ≠ 0 :=
    div_ne_zero hB (H₃_ne_zero τ)
  have hJacobi : H₂ τ + H₄ τ = H₃ τ := by
    simpa only [Pi.add_apply] using
      congrFun jacobi_quartic_identity τ
  have hcross :
      H₂ τ * UnaryModularState.B z =
        z.C * H₃ τ := by
    unfold canonicalLambda
      UnaryModularState.lambdaCoordinate at hlambda
    have hBsum :
        UnaryModularState.B z = z.A + z.C := rfl
    field_simp [H₃_ne_zero τ, hB] at hlambda
    linear_combination hlambda + H₃ τ * hBsum
  have hCcross :
      z.C * H₃ τ =
        UnaryModularState.B z * H₂ τ := by
    simpa only [mul_comm] using hcross.symm
  have hAcross :
      z.A * H₃ τ =
        UnaryModularState.B z * H₄ τ := by
    have hBsum :
        UnaryModularState.B z = z.A + z.C := rfl
    linear_combination
      -H₃ τ * hBsum - hCcross -
        UnaryModularState.B z * hJacobi
  refine ⟨q, hq, ?_, ?_, ?_⟩
  · rw [show q * H₄ τ =
        (UnaryModularState.B z * H₄ τ) / H₃ τ by
      simp only [q, div_eq_mul_inv]
      ring]
    exact (eq_div_iff (H₃_ne_zero τ)).2 hAcross
  · exact
      (div_mul_cancel₀
        (UnaryModularState.B z) (H₃_ne_zero τ)).symm
  · rw [show q * H₂ τ =
        (UnaryModularState.B z * H₂ τ) / H₃ τ by
      simp only [q, div_eq_mul_inv]
      ring]
    exact (eq_div_iff (H₃_ne_zero τ)).2 hCcross

/-- The `S*T` cross-ratio places the half-characteristic quartic in the
middle (`B`) slot. -/
theorem isCuspQuarticBranch_one_of_lambda
    (z : UnaryModularState ℂ) (τ : UpperHalfPlane)
    (hB : UnaryModularState.B z ≠ 0)
    (hC : z.C ≠ 0)
    (hlambda :
      canonicalLambda τ =
        1 / (1 - UnaryModularState.lambdaCoordinate z)) :
    IsCuspQuarticBranch .one z τ := by
  let q : ℂ := UnaryModularState.B z / H₂ τ
  have hq : q ≠ 0 :=
    div_ne_zero hB (H₂_ne_zero τ)
  have hJacobi : H₂ τ + H₄ τ = H₃ τ := by
    simpa only [Pi.add_apply] using
      congrFun jacobi_quartic_identity τ
  have hcross :
      H₂ τ * z.C =
        UnaryModularState.B z * H₃ τ := by
    unfold canonicalLambda
      UnaryModularState.lambdaCoordinate at hlambda
    have hBsum :
        UnaryModularState.B z = z.A + z.C := rfl
    have honeSub :
        1 - z.A / UnaryModularState.B z =
          z.C / UnaryModularState.B z := by
      field_simp [hB]
      linear_combination hBsum
    rw [honeSub] at hlambda
    field_simp [H₃_ne_zero τ, hB, hC] at hlambda
    simpa only [mul_comm] using hlambda
  have hCcross :
      z.C * H₂ τ =
        UnaryModularState.B z * H₃ τ := by
    simpa only [mul_comm] using hcross
  have hAcross :
      z.A * H₂ τ =
        -(UnaryModularState.B z * H₄ τ) := by
    have hBsum :
        UnaryModularState.B z = z.A + z.C := rfl
    linear_combination
      -H₂ τ * hBsum - hCcross +
        UnaryModularState.B z * hJacobi
  refine ⟨q, hq, ?_, ?_, ?_⟩
  · rw [show -(q * H₄ τ) =
        -(UnaryModularState.B z * H₄ τ) / H₂ τ by
      simp only [q, div_eq_mul_inv]
      ring]
    exact (eq_div_iff (H₂_ne_zero τ)).2 hAcross
  · exact
      (div_mul_cancel₀
        (UnaryModularState.B z) (H₂_ne_zero τ)).symm
  · rw [show q * H₃ τ =
        (UnaryModularState.B z * H₃ τ) / H₂ τ by
      simp only [q, div_eq_mul_inv]
      ring]
    exact (eq_div_iff (H₂_ne_zero τ)).2 hCcross

/-- Uniform three-cusp statement.  The hypothesis is exactly the
cross-ratio law supplied by the cusp representative. -/
theorem isCuspQuarticBranch_of_cuspRepresentative_lambda
    (cusp : GammaTwoCuspLabel)
    (z : UnaryModularState ℂ) (τ : UpperHalfPlane)
    (hB : UnaryModularState.B z ≠ 0)
    (hC : z.C ≠ 0)
    (hlambda :
      canonicalLambda τ =
        lambdaCrossRatio
          (reduceModTwo (cuspRepresentative cusp))
          (UnaryModularState.lambdaCoordinate z)) :
    IsCuspQuarticBranch cusp z τ := by
  cases cusp with
  | infinity =>
      apply isCuspQuarticBranch_infinity_of_lambda z τ hB
      simpa [cuspRepresentative] using hlambda
  | zero =>
      apply isCuspQuarticBranch_zero_of_lambda z τ hB
      simpa [cuspRepresentative] using hlambda
  | one =>
      apply isCuspQuarticBranch_one_of_lambda z τ hB hC
      have h := hlambda
      simp only [cuspRepresentative] at h
      rw [lambdaCrossRatio_ST] at h
      simpa only [one_div] using h

end

end HGAS.Modular
