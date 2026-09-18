import HGAS.Modular.CanonicalUnaryComparison
import HGAS.Modular.ThetaZeroFree
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Local differential theory of the modular lambda coordinate

The canonical lambda coordinate is

```
                         Λ(τ) = H₂(τ) / H₃(τ).
```

The pointwise theta nonvanishing theorem shows that its values avoid both
`0` and `1`.  Its normalized derivative is

```
              DₘΛ = (1/2) H₃ Λ(1-Λ),
```

so its ordinary complex derivative is nowhere zero.

The main trajectory theorem removes a hypothesis from the abstract
two-jet reconstruction.  Suppose a differentiable curve `T : ℝ → ℍ`
lifts the lambda coordinate of a generic unary trajectory.  Differentiating
the equality of lambda coordinates and cancelling the three nonzero
factors `πi`, `Λ`, and `1-Λ` forces

```
                    T' = (A+C) / H₃(T).
```

Thus any differentiable lambda lift automatically has exactly the velocity
required by `CanonicalUnaryComparison`; its fractional-linear form then
follows without an additional assumption.

The remaining global issue is existence of such a lift, i.e. the covering
theorem for `Λ`.  This module settles all local differential and uniqueness
algebra needed after that existence theorem.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex
open scoped Manifold

noncomputable section

local notation "Dₘ" =>
  Derivative.normalizedDerivOfComplex

/-- Quotient rule for Mathlib's normalized upper-half-plane derivative. -/
theorem normalizedDeriv_div_apply
    (f g : ℍ → ℂ)
    (hf : MDiff f) (hg : MDiff g)
    (z : ℍ) (hgz : g z ≠ 0) :
    Dₘ (fun w ↦ f w / g w) z =
      (Dₘ f z * g z - f z * Dₘ g z) /
        g z ^ 2 := by
  have hfz :=
    UpperHalfPlane.mdifferentiableAt_iff.mp (hf z)
  have hgzDiff :=
    UpperHalfPlane.mdifferentiableAt_iff.mp (hg z)
  unfold Derivative.normalizedDerivOfComplex
  rw [show
      (fun w : ℍ ↦ f w / g w) ∘ ofComplex =
        (f ∘ ofComplex) / (g ∘ ofComplex) by
      rfl,
    deriv_div hfz hgzDiff (by simpa using hgz)]
  simp only [Function.comp_apply,
    UpperHalfPlane.ofComplex_apply]
  ring

/-- The canonical modular lambda function. -/
def canonicalLambda (z : ℍ) : ℂ :=
  H₂ z / H₃ z

/-- The canonical state quotient is the canonical lambda function. -/
theorem canonicalUnaryTheta_lambdaCoordinate
    (z : ℍ) :
    UnaryModularState.lambdaCoordinate
      (canonicalUnaryTheta z) =
        canonicalLambda z := by
  have hJacobi : H₂ z + H₄ z = H₃ z := by
    simpa only [Pi.add_apply] using
      congrFun jacobi_quartic_identity z
  simp only [UnaryModularState.lambdaCoordinate,
    UnaryModularState.B,
    canonicalUnaryTheta_A,
    canonicalUnaryTheta_C,
    canonicalLambda,
    hJacobi]

/-- The canonical lambda function never vanishes. -/
theorem canonicalLambda_ne_zero (z : ℍ) :
    canonicalLambda z ≠ 0 :=
  div_ne_zero (H₂_ne_zero z) (H₃_ne_zero z)

/-- Algebraic complement formula `1-Λ=H₄/H₃`. -/
theorem one_sub_canonicalLambda (z : ℍ) :
    1 - canonicalLambda z =
      H₄ z / H₃ z := by
  have hJacobi : H₂ z + H₄ z = H₃ z := by
    simpa only [Pi.add_apply] using
      congrFun jacobi_quartic_identity z
  unfold canonicalLambda
  field_simp [H₃_ne_zero z]
  linear_combination -hJacobi

/-- The canonical lambda function never takes the value one. -/
theorem canonicalLambda_ne_one (z : ℍ) :
    canonicalLambda z ≠ 1 := by
  intro hone
  have hzero : 1 - canonicalLambda z = 0 := by
    rw [hone]
    ring
  rw [one_sub_canonicalLambda] at hzero
  exact (div_ne_zero (H₄_ne_zero z) (H₃_ne_zero z))
    hzero

/-- Holomorphy of the canonical lambda function. -/
theorem canonicalLambda_mdifferentiable :
    MDiff canonicalLambda := by
  intro z
  exact
    (H₂_mdifferentiable z).div
      (H₃_mdifferentiable z)
      (H₃_ne_zero z)

/-- Exact normalized differential equation for modular lambda. -/
theorem normalizedDeriv_canonicalLambda
    (z : ℍ) :
    Dₘ canonicalLambda z =
      (1 / 2 : ℂ) * H₃ z *
        canonicalLambda z *
          (1 - canonicalLambda z) := by
  have hquot :=
    normalizedDeriv_div_apply
      H₂ H₃
      H₂_mdifferentiable
      H₃_mdifferentiable
      z (H₃_ne_zero z)
  rw [show canonicalLambda =
      (fun w ↦ H₂ w / H₃ w) by rfl,
    hquot]
  have hJacobi : H₂ z + H₄ z = H₃ z := by
    simpa only [Pi.add_apply] using
      congrFun jacobi_quartic_identity z
  have hD₂ :
      Dₘ H₂ z =
        (1 / 6 : ℂ) * H₂ z *
          (EisensteinSeries.E2 z +
            H₂ z + 2 * H₄ z) := by
    rw [congrFun normalizedDeriv_H₂ z]
    simp only [Pi.add_apply, Pi.mul_apply,
      Pi.pow_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hD₃ :
      Dₘ H₃ z =
        (1 / 6 : ℂ) * H₃ z *
          (EisensteinSeries.E2 z +
            H₂ z - H₄ z) := by
    rw [congrFun normalizedDeriv_H₃ z]
    simp only [Pi.add_apply, Pi.sub_apply,
      Pi.mul_apply, Pi.pow_apply, Pi.smul_apply,
      smul_eq_mul]
    linear_combination
      ((1 / 6 : ℂ) *
        (H₂ z - H₄ z)) * hJacobi
  rw [hD₂, hD₃]
  have hOneFormula :
      1 - H₂ z / H₃ z =
        H₄ z / H₃ z := by
    simpa only [canonicalLambda] using
      one_sub_canonicalLambda z
  change
    (1 / 6 * H₂ z *
          (EisensteinSeries.E2 z +
            H₂ z + 2 * H₄ z) * H₃ z -
        H₂ z *
          (1 / 6 * H₃ z *
            (EisensteinSeries.E2 z +
              H₂ z - H₄ z))) /
        H₃ z ^ 2 =
      1 / 2 * H₃ z *
        (H₂ z / H₃ z) *
          (1 - H₂ z / H₃ z)
  rw [hOneFormula]
  field_simp [H₃_ne_zero z]
  ring

/-- The normalized derivative of lambda is pointwise nonzero. -/
theorem normalizedDeriv_canonicalLambda_ne_zero
    (z : ℍ) :
    Dₘ canonicalLambda z ≠ 0 := by
  rw [normalizedDeriv_canonicalLambda]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (by norm_num) (H₃_ne_zero z))
      (canonicalLambda_ne_zero z))
    (sub_ne_zero.mpr (canonicalLambda_ne_one z).symm)

/-- Lambda along a differentiable upper-half-plane curve. -/
theorem canonicalLambda_comp_hasDerivAt
    (T : ℝ → ℍ) (t : ℝ) {v : ℂ}
    (hT :
      HasDerivAt (fun s : ℝ ↦ (T s : ℂ)) v t) :
    HasDerivAt
      (fun s ↦ canonicalLambda (T s))
      (modularIndependentVariableClock * v *
        H₃ (T t) *
        canonicalLambda (T t) *
        (1 - canonicalLambda (T t))) t := by
  have h :=
    hasDerivAt_comp_upperHalfPlaneCurve
      canonicalLambda
      canonicalLambda_mdifferentiable
      T t hT
  convert h using 1
  rw [normalizedDeriv_canonicalLambda]
  simp only [modularIndependentVariableClock]
  ring

/-- Generic source lambda values are nonzero. -/
theorem sourceLambda_ne_zero
    (z : UnaryModularState ℂ)
    (hA : z.A ≠ 0)
    (hB : UnaryModularState.B z ≠ 0) :
    UnaryModularState.lambdaCoordinate z ≠ 0 := by
  unfold UnaryModularState.lambdaCoordinate
  exact div_ne_zero hA hB

/-- Generic source lambda values are different from one. -/
theorem sourceLambda_ne_one
    (z : UnaryModularState ℂ)
    (hC : z.C ≠ 0)
    (hB : UnaryModularState.B z ≠ 0) :
    UnaryModularState.lambdaCoordinate z ≠ 1 := by
  intro hone
  have hA : z.A = UnaryModularState.B z := by
    apply (div_eq_one_iff_eq hB).mp
    exact hone
  apply hC
  simp only [UnaryModularState.B] at hA
  have hEq : z.A + z.C = z.A + 0 := by
    simpa using hA.symm
  exact add_left_cancel hEq

/-- **Automatic lift velocity.**  Every differentiable canonical lambda
lift of a generic unary trajectory has derivative equal to the relative
weight-two scale. -/
theorem canonicalLambdaLift_hasDerivAt_comparisonV
    {z : ℝ → UnaryModularState ℂ}
    {T : ℝ → ℍ}
    (hz :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock z)
    (hB : ∀ t, UnaryModularState.B (z t) ≠ 0)
    (hLambda : ∀ t,
      UnaryModularState.lambdaCoordinate (z t) =
        canonicalLambda (T t))
    (hTdiff : ∀ t, ∃ v : ℂ,
      HasDerivAt (fun s : ℝ ↦ (T s : ℂ)) v t)
    (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ (T s : ℂ))
      (unaryComparisonV z
        (fun q ↦ canonicalUnaryTheta (T q)) t) t := by
  obtain ⟨v, hTv⟩ := hTdiff t
  have hsource :=
    hz.lambdaCoordinate_hasDerivAt t (hB t)
  have hcanonical :=
    canonicalLambda_comp_hasDerivAt T t hTv
  have hsource' :
      HasDerivAt
        (fun s ↦ canonicalLambda (T s))
        (modularIndependentVariableClock *
          UnaryModularState.B (z t) *
          canonicalLambda (T t) *
          (1 - canonicalLambda (T t))) t := by
    convert hsource using 1
    · funext s
      exact (hLambda s).symm
    · rw [hLambda t]
  have hderivative := hsource'.unique hcanonical
  have hLambdaNonzero :
      canonicalLambda (T t) ≠ 0 := by
    exact canonicalLambda_ne_zero (T t)
  have hOne :
      1 - canonicalLambda (T t) ≠ 0 :=
    sub_ne_zero.mpr (canonicalLambda_ne_one (T t)).symm
  have hclock :
      modularIndependentVariableClock ≠ 0 :=
    modularIndependentVariableClock_ne_zero
  have hfactor :
      modularIndependentVariableClock *
          canonicalLambda (T t) *
            (1 - canonicalLambda (T t)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hclock hLambdaNonzero) hOne
  have hscaled :
      (modularIndependentVariableClock *
          canonicalLambda (T t) *
            (1 - canonicalLambda (T t))) *
          UnaryModularState.B (z t) =
        (modularIndependentVariableClock *
          canonicalLambda (T t) *
            (1 - canonicalLambda (T t))) *
          (H₃ (T t) * v) := by
    linear_combination hderivative
  have hBv :
      UnaryModularState.B (z t) =
        H₃ (T t) * v :=
    mul_left_cancel₀ hfactor hscaled
  convert hTv using 1
  unfold unaryComparisonV
  have hcanonicalB :
      UnaryModularState.B
        (canonicalUnaryTheta (T t)) =
          H₃ (T t) := by
    have hJacobi : H₂ (T t) + H₄ (T t) = H₃ (T t) := by
      simpa only [Pi.add_apply] using
        congrFun jacobi_quartic_identity (T t)
    simp only [UnaryModularState.B,
      canonicalUnaryTheta_A,
      canonicalUnaryTheta_C,
      hJacobi]
  rw [hcanonicalB]
  apply (div_eq_iff (H₃_ne_zero (T t))).mpr
  rw [hBv]
  ring

/-- A differentiable canonical lambda lift of a generic source trajectory
is a Riccati two-jet, with no separately assumed velocity equation. -/
theorem differentiableCanonicalLambdaLift_isRiccatiJetTrajectory
    {z : ℝ → UnaryModularState ℂ}
    {T : ℝ → ℍ}
    (hz :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock z)
    (hB : ∀ t, UnaryModularState.B (z t) ≠ 0)
    (hLambda : ∀ t,
      UnaryModularState.lambdaCoordinate (z t) =
        canonicalLambda (T t))
    (hTdiff : ∀ t, ∃ v : ℂ,
      HasDerivAt (fun s : ℝ ↦ (T s : ℂ)) v t) :
    IsRiccatiJetTrajectory
      (unaryComparisonU z
        (fun q ↦ canonicalUnaryTheta (T q)))
      (unaryComparisonV z
        (fun q ↦ canonicalUnaryTheta (T q)))
      (fun t ↦ (T t : ℂ)) := by
  apply canonicalUnaryTheta_lift_isRiccatiJetTrajectory
    hz hB
  · intro t
    rw [canonicalUnaryTheta_lambdaCoordinate]
    exact hLambda t
  · exact
      canonicalLambdaLift_hasDerivAt_comparisonV
        hz hB hLambda hTdiff

end

end HGAS.Modular
