import HGAS.Modular.RecurrentLiftEndpoint
import HGAS.Modular.RiccatiHorocycleFrameReconstruction
import HGAS.Modular.GenericUnaryLambdaLift

/-!
# Exact `Γ(2)` dynamics of a recurrent generic unary lift

`RecurrentLiftGeometry` records that a recurrent generic canonical-lambda
lift is either a horizontal line or lies on a Euclidean horocycle.  For
measure classification one needs the stronger, parametrized assertion:
the nonhorizontal curve must be a genuine right-unipotent orbit, not an
arbitrary time change on the same circle.

This file keeps the Riccati jet produced during reconstruction and applies
`RiccatiHorocycleFrameReconstruction`.  The result is an exhaustive
alternative in which the second branch is a literal scaled orbit in

```
                       Γ(2) \ SL(2,ℝ).
```
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I

noncomputable section

/-- A recurrent generic unary modular trajectory has either a globally
horizontal canonical-lambda lift or a lift which is exactly the base
projection of a nontrivial scaled `Γ(2)` horocycle orbit. -/
theorem recurrentGenericUnaryTrajectory_exists_horizontal_or_exactGammaTwoHorocycle
    {z : ℝ → UnaryModularState ℂ}
    (hz :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock z)
    {t₀ : ℝ}
    (hA₀ : (z t₀).A ≠ 0)
    (hC₀ : (z t₀).C ≠ 0)
    (hB₀ : UnaryModularState.B (z t₀) ≠ 0)
    (hrec : ForwardRecurrentUnaryModularAt z t₀) :
    ∃ T : ℝ → ℍ,
      Continuous T ∧
      (∀ t,
        UnaryModularState.lambdaCoordinate (z t) =
          canonicalLambda (T t)) ∧
      ((∃ x y s : ℝ, ∃ hy : 0 < y,
          ∀ t,
            T t = horizontalLine x y s hy t) ∨
        ∃ q : GammaTwoFrameQuotient, ∃ σ : ℝ,
          σ ≠ 0 ∧
          ∀ t : ℝ,
            lambdaModularQuotientMk (T t) =
              gammaTwoFrameBaseProjection
                (scaledGammaTwoHorocycleFlow σ t q)) := by
  have hA := hz.A_ne_zero hA₀
  have hC := hz.C_ne_zero hC₀
  have hB := hz.B_ne_zero hB₀
  obtain ⟨T, hTcont, hLambda, hTdiff⟩ :=
    exists_differentiable_canonicalLambdaLift_of_generic
      hz hA hC hB
  refine ⟨T, hTcont, hLambda, ?_⟩
  let r : ℝ → UnaryModularState ℂ :=
    fun t ↦ canonicalUnaryTheta (T t)
  let u : ℝ → ℂ := unaryComparisonU z r
  let v : ℝ → ℂ := unaryComparisonV z r
  have hjet :
      IsRiccatiJetTrajectory u v
        (fun t ↦ (T t : ℂ)) :=
    differentiableCanonicalLambdaLift_isRiccatiJetTrajectory
      hz hB hLambda hTdiff
  by_cases hu : u t₀ = 0
  · left
    refine
      ⟨(T t₀).re - (v t₀).re * t₀,
        (T t₀).im, (v t₀).re,
        (T t₀).im_pos, ?_⟩
    exact
      riccatiLift_eq_horizontalLine_of_u_eq_zero_at
        hjet t₀ hu
  · right
    have hendpoint :
        (IsRiccatiJetTrajectory.fractionalLinearEndpoint
          u v (fun t ↦ (T t : ℂ)) t₀).im = 0 := by
      simpa only [u, v, r] using
        recurrentCanonicalLambdaLift_endpoint_im_eq_zero
          hz hB hLambda hTdiff hrec (by
            simpa only [u, r] using hu)
    exact
      hjet.exists_exact_scaledGammaTwoHorocycle
        t₀ hu hendpoint

end

end HGAS.Modular
