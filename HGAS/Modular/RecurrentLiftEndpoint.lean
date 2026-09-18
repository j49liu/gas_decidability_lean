import HGAS.Modular.CanonicalLambdaLocal
import HGAS.Modular.RiccatiJetAsymptotics
import HGAS.Modular.UnaryDegenerateRecurrence
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Tactic

/-!
# A recurrent generic modular lift cannot converge inside the upper half-plane

Suppose a generic unary modular trajectory `z(t)` admits a differentiable
lift `T(t)` through the canonical modular lambda function.  The local
comparison theorem constructs a Riccati jet `(u,v,T)`.  If `u(t₀) ≠ 0`,
the asymptotic theorem gives

```
        v(t) → 0,
        T(t) → T(t₀) + v(t₀)/u(t₀).
```

This file proves that the displayed endpoint cannot lie in the open upper
half-plane when `z` is forward recurrent at `t₀`.

The contradiction is especially transparent.  If the endpoint were an
upper-half-plane point `L`, continuity of the canonical theta reference
would keep its `B` coordinate finite.  The comparison identity

```
          B_z(t) = v(t) B_canonical(T(t))
```

would therefore imply `B_z(t) → 0`.  Along a recurrent return sequence,
however, `B_z(t)` tends back to the nonzero value `B_z(t₀)`.

Only the `B` coordinate is needed: no compactness theorem, Fourier
expansion, or measure classification enters this endpoint exclusion.
-/

namespace HGAS.Modular

open Filter Topology
open UpperHalfPlane hiding I

noncomputable section

/-- The Riccati endpoint of a recurrent generic canonical-lambda lift is
not the image of any point of the open upper half-plane. -/
theorem recurrentCanonicalLambdaLift_endpoint_not_in_upperHalfPlane
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
    (hrec : ForwardRecurrentUnaryModularAt z t₀)
    (hu :
      unaryComparisonU z
        (fun q ↦ canonicalUnaryTheta (T q)) t₀ ≠ 0) :
    ¬ ∃ L : ℍ,
      (L : ℂ) =
        IsRiccatiJetTrajectory.fractionalLinearEndpoint
          (unaryComparisonU z
            (fun q ↦ canonicalUnaryTheta (T q)))
          (unaryComparisonV z
            (fun q ↦ canonicalUnaryTheta (T q)))
          (fun t ↦ (T t : ℂ)) t₀ := by
  intro hinside
  obtain ⟨L, hL⟩ := hinside
  let r : ℝ → UnaryModularState ℂ :=
    fun t ↦ canonicalUnaryTheta (T t)
  let u : ℝ → ℂ := unaryComparisonU z r
  let v : ℝ → ℂ := unaryComparisonV z r
  have hjet :
      IsRiccatiJetTrajectory u v
        (fun t ↦ (T t : ℂ)) := by
    exact differentiableCanonicalLambdaLift_isRiccatiJetTrajectory
      hz hB hLambda hTdiff
  have hu' : u t₀ ≠ 0 := by
    simpa only [u, r] using hu
  have hTcomplex :
      Tendsto (fun t ↦ (T t : ℂ)) atTop (𝓝 (L : ℂ)) := by
    have hlimit :=
      hjet.T_tendsto_fractionalLinearEndpoint_atTop
        t₀ hu'
    rw [hL]
    simpa only [u, v, r] using hlimit
  have hT :
      Tendsto T atTop (𝓝 L) := by
    rw [UpperHalfPlane.isEmbedding_coe.tendsto_nhds_iff]
    simpa only [Function.comp_apply] using hTcomplex
  have hv :
      Tendsto v atTop (𝓝 0) :=
    hjet.v_tendsto_zero_atTop t₀ hu'
  have hreferenceB :
      Tendsto
        (fun t ↦ UnaryModularState.B (r t))
        atTop
        (𝓝
          (UnaryModularState.B
            (canonicalUnaryTheta L))) := by
    have hA :
        Tendsto
          (fun t ↦ (canonicalUnaryTheta (T t)).A)
          atTop
          (𝓝 (canonicalUnaryTheta L).A) :=
      (canonicalUnaryTheta_A_mdifferentiable L).continuousAt.tendsto.comp
        hT
    have hC :
        Tendsto
          (fun t ↦ (canonicalUnaryTheta (T t)).C)
          atTop
          (𝓝 (canonicalUnaryTheta L).C) :=
      (canonicalUnaryTheta_C_mdifferentiable L).continuousAt.tendsto.comp
        hT
    simpa only [UnaryModularState.B, r] using hA.add hC
  have hBzero :
      Tendsto
        (fun t ↦ UnaryModularState.B (z t))
        atTop (𝓝 0) := by
    have hproduct :
        Tendsto
          (fun t ↦
            v t * UnaryModularState.B (r t))
          atTop (𝓝 0) := by
      simpa using hv.mul hreferenceB
    apply hproduct.congr'
    filter_upwards with t
    exact
      (unaryComparison_B_eq z r t
        (by
          simpa only [r] using
            canonicalUnaryTheta_B_ne_zero (T t))).symm
  have hBzeroAlongReturns :
      Tendsto
        (fun n ↦ UnaryModularState.B (z (hrec.times n)))
        atTop (𝓝 0) :=
    hBzero.comp hrec.times_tendsto
  have hBreturn :
      Tendsto
        (fun n ↦ UnaryModularState.B (z (hrec.times n)))
        atTop
        (𝓝 (UnaryModularState.B (z t₀))) := by
    simpa only [UnaryModularState.B] using
      hrec.A_tendsto.add hrec.C_tendsto
  have hBbase :
      UnaryModularState.B (z t₀) = 0 :=
    tendsto_nhds_unique hBreturn hBzeroAlongReturns
  exact hB t₀ hBbase

/-- Equivalently, the finite endpoint of the non-affine branch has
nonpositive imaginary part. -/
theorem recurrentCanonicalLambdaLift_endpoint_im_nonpos
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
    (hrec : ForwardRecurrentUnaryModularAt z t₀)
    (hu :
      unaryComparisonU z
        (fun q ↦ canonicalUnaryTheta (T q)) t₀ ≠ 0) :
    (IsRiccatiJetTrajectory.fractionalLinearEndpoint
      (unaryComparisonU z
        (fun q ↦ canonicalUnaryTheta (T q)))
      (unaryComparisonV z
        (fun q ↦ canonicalUnaryTheta (T q)))
      (fun t ↦ (T t : ℂ)) t₀).im ≤ 0 := by
  apply le_of_not_gt
  intro hpositive
  apply recurrentCanonicalLambdaLift_endpoint_not_in_upperHalfPlane
    hz hB hLambda hTdiff hrec hu
  exact
    ⟨⟨IsRiccatiJetTrajectory.fractionalLinearEndpoint
        (unaryComparisonU z
          (fun q ↦ canonicalUnaryTheta (T q)))
        (unaryComparisonV z
          (fun q ↦ canonicalUnaryTheta (T q)))
        (fun t ↦ (T t : ℂ)) t₀,
      hpositive⟩, rfl⟩

/-- The non-affine recurrent endpoint lies exactly on the real boundary of
the upper half-plane.  Nonpositivity is the recurrence obstruction proved
above; nonnegativity follows because the entire lift remains in the open
upper half-plane and converges to this finite endpoint. -/
theorem recurrentCanonicalLambdaLift_endpoint_im_eq_zero
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
    (hrec : ForwardRecurrentUnaryModularAt z t₀)
    (hu :
      unaryComparisonU z
        (fun q ↦ canonicalUnaryTheta (T q)) t₀ ≠ 0) :
    (IsRiccatiJetTrajectory.fractionalLinearEndpoint
      (unaryComparisonU z
        (fun q ↦ canonicalUnaryTheta (T q)))
      (unaryComparisonV z
        (fun q ↦ canonicalUnaryTheta (T q)))
      (fun t ↦ (T t : ℂ)) t₀).im = 0 := by
  let r : ℝ → UnaryModularState ℂ :=
    fun t ↦ canonicalUnaryTheta (T t)
  let u : ℝ → ℂ := unaryComparisonU z r
  let v : ℝ → ℂ := unaryComparisonV z r
  let endpoint : ℂ :=
    IsRiccatiJetTrajectory.fractionalLinearEndpoint
      u v (fun t ↦ (T t : ℂ)) t₀
  have hjet :
      IsRiccatiJetTrajectory u v
        (fun t ↦ (T t : ℂ)) :=
    differentiableCanonicalLambdaLift_isRiccatiJetTrajectory
      hz hB hLambda hTdiff
  have hu' : u t₀ ≠ 0 := by
    simpa only [u, r] using hu
  have hlimit :
      Tendsto (fun t ↦ (T t : ℂ))
        atTop (𝓝 endpoint) :=
    hjet.T_tendsto_fractionalLinearEndpoint_atTop
      t₀ hu'
  have hnonneg : 0 ≤ endpoint.im :=
    upperHalfPlane_limit_im_nonneg T endpoint hlimit
  have hnonpos : endpoint.im ≤ 0 := by
    simpa only [endpoint, u, v, r] using
      recurrentCanonicalLambdaLift_endpoint_im_nonpos
        hz hB hLambda hTdiff hrec hu
  have heq : endpoint.im = 0 :=
    le_antisymm hnonpos hnonneg
  simpa only [endpoint, u, v, r] using heq

end

end HGAS.Modular
