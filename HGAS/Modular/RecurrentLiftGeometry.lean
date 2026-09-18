import HGAS.Modular.RecurrentLiftEndpoint
import HGAS.Modular.RiccatiJetGeometry
import HGAS.Modular.GenericUnaryLambdaLift

/-!
# Geometric classification of a recurrent canonical-lambda lift

This file combines three independently reusable results:

1. a differentiable canonical-lambda lift of a generic unary trajectory
   reconstructs a Riccati jet;
2. recurrence forces the finite endpoint of its non-affine branch onto the
   real boundary; and
3. the two global Riccati branches inside the upper half-plane are a
   horizontal line or a Euclidean circle tangent to that boundary.

The resulting theorem is the precise geometric core of the modular
recurrent classification.  It does not yet quotient by a modular group or
classify invariant measures on the resulting horocycle; those are separate
topological and ergodic statements.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I

noncomputable section

/-- The two geometric alternatives for a canonical-lambda lift of a
recurrent generic unary trajectory. -/
def IsHorizontalOrHorocycleLift
    (z : ℝ → UnaryModularState ℂ)
    (T : ℝ → ℍ) (t₀ : ℝ) : Prop :=
  let r : ℝ → UnaryModularState ℂ :=
    fun t ↦ canonicalUnaryTheta (T t)
  let u := unaryComparisonU z r
  let v := unaryComparisonV z r
  (∃ x y s : ℝ, ∃ hy : 0 < y,
    ∀ t,
      T t = horizontalLine x y s hy t) ∨
  (let ξ :=
      IsRiccatiJetTrajectory.fractionalLinearEndpoint
        u v (fun t ↦ (T t : ℂ)) t₀
    let R := horocycleRadius (T t₀ : ℂ) ξ
    ξ.im = 0 ∧ 0 < R ∧
      ∀ t,
        Complex.normSq
            ((T t : ℂ) -
              horocycleCenter (T t₀ : ℂ) ξ) =
          R ^ 2)

/-- A canonical-lambda lift of a recurrent generic unary trajectory is
either a horizontal line or an explicitly parameterized Euclidean
horocycle. -/
theorem recurrentCanonicalLambdaLift_horizontal_or_horocycle
    {z : ℝ → UnaryModularState ℂ}
    {T : ℝ → ℍ}
    (hz :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock z)
    (hB : ∀ t, UnaryModularState.B (z t) ≠ 0)
    (hLambda : ∀ t,
      UnaryModularState.lambdaCoordinate (z t) =
        canonicalLambda (T t))
    (hTdiff : ∀ t, ∃ w : ℂ,
      HasDerivAt (fun s : ℝ ↦ (T s : ℂ)) w t)
    {t₀ : ℝ}
    (hrec : ForwardRecurrentUnaryModularAt z t₀) :
    let r : ℝ → UnaryModularState ℂ :=
      fun t ↦ canonicalUnaryTheta (T t)
    let u := unaryComparisonU z r
    let v := unaryComparisonV z r
    (∃ x y s : ℝ, ∃ hy : 0 < y,
      ∀ t,
        T t = horizontalLine x y s hy t) ∨
    (let ξ :=
        IsRiccatiJetTrajectory.fractionalLinearEndpoint
          u v (fun t ↦ (T t : ℂ)) t₀
      let R := horocycleRadius (T t₀ : ℂ) ξ
      ξ.im = 0 ∧ 0 < R ∧
        ∀ t,
          Complex.normSq
              ((T t : ℂ) -
                horocycleCenter (T t₀ : ℂ) ξ) =
            R ^ 2) := by
  dsimp only
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
    have hboundary :
        (IsRiccatiJetTrajectory.fractionalLinearEndpoint
          u v (fun t ↦ (T t : ℂ)) t₀).im = 0 := by
      simpa only [u, v, r] using
        recurrentCanonicalLambdaLift_endpoint_im_eq_zero
          hz hB hLambda hTdiff hrec (by
            simpa only [u, r] using hu)
    have hcircle :=
      riccatiLift_mem_horocycle_of_endpoint_im_eq_zero
        hjet t₀ hu hboundary
    exact ⟨hboundary, hcircle.1, hcircle.2⟩

/-- **Unconditional recurrent generic lift classification.**

Starting only from one generic point of the algebraic unary trajectory,
the invariant-divisor lemmas keep `A`, `C`, and `B=A+C` nonzero.  Global
lambda uniformization constructs the lift, and the Riccati argument then
places it on a horizontal line or a boundary-tangent horocycle. -/
theorem recurrentGenericUnaryTrajectory_exists_horizontal_or_horocycle
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
      IsHorizontalOrHorocycleLift z T t₀ := by
  have hA := hz.A_ne_zero hA₀
  have hC := hz.C_ne_zero hC₀
  have hB := hz.B_ne_zero hB₀
  obtain ⟨T, hTcont, hLambda, hTdiff⟩ :=
    exists_differentiable_canonicalLambdaLift_of_generic
      hz hA hC hB
  refine ⟨T, hTcont, hLambda, ?_⟩
  unfold IsHorizontalOrHorocycleLift
  exact
    recurrentCanonicalLambdaLift_horizontal_or_horocycle
      hz hB hLambda hTdiff hrec

end

end HGAS.Modular
