import HGAS.Modular.RecurrentLiftExactFrame

/-!
# Differentiable exact-frame classification

The exact frame reconstruction is built from a differentiable
canonical-lambda lift, but the original public endpoint retained only
continuity.  Finite closed-cusp amplitude selection needs the derivative
of that same lift.  This module exposes the stronger result without
changing the established interface.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I

noncomputable section

/-- A recurrent generic unary trajectory admits a differentiable
canonical-lambda lift which is either horizontal or a literal nontrivial
scaled real-frame horocycle. -/
theorem
    recurrentGenericUnaryTrajectory_exists_differentiable_horizontal_or_exactFrame
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
      (∀ t, ∃ w : ℂ,
        HasDerivAt (fun s : ℝ ↦ (T s : ℂ)) w t) ∧
      ((∃ x y s : ℝ, ∃ hy : 0 < y,
          ∀ t,
            T t = horizontalLine x y s hy t) ∨
        ∃ g : RealModularFrame, ∃ σ : ℝ,
          σ ≠ 0 ∧
          ∀ t : ℝ,
            T t =
              realModularFrameBasePoint
                (g * upperUnipotent (σ * t))) := by
  have hA := hz.A_ne_zero hA₀
  have hC := hz.C_ne_zero hC₀
  have hB := hz.B_ne_zero hB₀
  obtain ⟨T, hTcont, hLambda, hTdiff⟩ :=
    exists_differentiable_canonicalLambdaLift_of_generic
      hz hA hC hB
  refine ⟨T, hTcont, hLambda, hTdiff, ?_⟩
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
      hjet.exists_exact_scaledHorocycleFrame
        t₀ hu hendpoint

end

end HGAS.Modular
