import HGAS.Modular.JacobiThetaReciprocalCoveringUnconditional
import HGAS.Modular.RecurrentUnarySelectorReduction

/-!
# Recurrent linked trajectories have one coherent theta representation

The earlier pointwise saturation theorem represents the Jacobi coordinates
at each time by a scaled theta vector, but a separate choice at every time
does not describe one moving trajectory.  The reciprocal-theta covering
theorem removes exactly this ambiguity.

This file packages the resulting trajectory-level statement.  On the
generic recurrent branch there are

* one continuous upper-half-plane modulus `T(t)`;
* one pair of constant fourth-root coefficient twists;
* one continuous elliptic parameter `ξ(t)`;
* the forced continuous common scale and logarithmic slope.

At every time these data reproduce the four (twisted) Jacobi coordinates,
the normalized first derivative, and the reciprocal coordinate.  Thus the
original polynomial ODE trajectory is coherently represented by a single
moving-modulus theta path, rather than by unrelated pointwise choices.

The structure below deliberately says *representation*, not *explicit
simultaneous Bloch integral*.  Proving that the three continuous functions
have the special constant-parameter form of the complete Bloch integral is
a further differential-identity and ODE-uniqueness theorem.
-/

namespace HGAS.Modular

open HGAS
open Complex
open UpperHalfPlane hiding I

noncomputable section

/-- A single coherent moving-modulus theta representation of the Jacobi
coordinates of a linked trajectory.

The finite coefficient ambiguity is stored in `twist`; it is constant in
time.  The only remaining covering datum is the continuous elliptic
parameter `parameter`, together with the exact projective identity.  The
common scale and logarithmic slope are then forced by explicit formulas
and are exposed below as definitions. -/
structure CoherentMovingJacobiThetaRepresentation
    (T : ℝ → ℍ) (z : ℝ → LinkedJacobiState ℂ) where
  twist : CoherentJacobiCoefficientTwist T z
  parameter : ℝ → ℂ
  isProjectiveLift :
    IsCoherentJacobiThetaProjectiveLift T z twist parameter

namespace CoherentMovingJacobiThetaRepresentation

variable {κZ κPhi : ℂ}
  {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}

/-- The unique common scale selected by the first reciprocal-chart
coordinate. -/
def scale
    (r : CoherentMovingJacobiThetaRepresentation T z) :
    ℝ → ℂ :=
  coherentJacobiBlochScale r.twist r.parameter

/-- The unique logarithmic Bloch slope selected by the `Delta`
coordinate. -/
def slope
    (r : CoherentMovingJacobiThetaRepresentation T z) :
    ℝ → ℂ :=
  coherentJacobiBlochSlope r.twist r.parameter

/-- The elliptic parameter of a coherent representation is continuous. -/
theorem continuous_parameter
    (r : CoherentMovingJacobiThetaRepresentation T z) :
    Continuous r.parameter :=
  r.isProjectiveLift.continuous

/-- The forced common scale varies continuously along the actual
trajectory. -/
theorem continuous_scale
    (r : CoherentMovingJacobiThetaRepresentation T z)
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    (hT : Continuous T) :
    Continuous r.scale :=
  continuous_coherentJacobiBlochScale
    hz hT r.twist r.isProjectiveLift

/-- The forced logarithmic slope varies continuously along the actual
trajectory. -/
theorem continuous_slope
    (r : CoherentMovingJacobiThetaRepresentation T z)
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    {t₀ : ℝ}
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t₀) = 0)
    (hT : Continuous T) :
    Continuous r.slope :=
  continuous_coherentJacobiBlochSlope
    hz hresidual hT r.twist r.isProjectiveLift

/-- Exact moving-modulus theta formula for all four twisted Jacobi
coordinates. -/
theorem scale_smul_theta
    (r : CoherentMovingJacobiThetaRepresentation T z)
    (t : ℝ) :
    r.scale t •
        jacobiThetaVector
          (r.parameter t) (T t : ℂ) =
      jacobiCoefficientTwist
        r.twist.d₁ r.twist.d₂
        (jacobiResidualProjectiveCoordinates
          (z t).jacobi) :=
  coherentJacobiBlochScale_smul_theta
    r.twist r.isProjectiveLift t

/-- The normalized theta derivative plus logarithmic slope is exactly the
twisted `Delta` coordinate. -/
theorem firstDerivative
    (r : CoherentMovingJacobiThetaRepresentation T z)
    (t : ℝ)
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t) = 0) :
    r.scale t *
        (jacobiThetaVectorPrime
              (r.parameter t) (T t : ℂ) 0 /
                (Real.pi : ℂ) +
          r.slope t *
            jacobiThetaVector
              (r.parameter t) (T t : ℂ) 0) =
      r.twist.d₁ * (z t).jacobi.Delta := by
  simpa only [scale, slope,
    coherentJacobiThetaNormalizedPrime] using
    coherentJacobiBlochSlope_initialValue
      r.twist r.isProjectiveLift t hresidual

/-- The reciprocal residual is also recovered by the theta
representation.  Since the first twisted coordinate is
`d₁*T₁`, multiplication by the original `U` gives the constant `d₁`. -/
theorem reciprocal
    (r : CoherentMovingJacobiThetaRepresentation T z)
    (t : ℝ)
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t) = 0) :
    (z t).jacobi.U *
        (r.scale t *
          jacobiThetaVector
            (r.parameter t) (T t : ℂ) 0) =
      r.twist.d₁ := by
  have hvalue :=
    congrFun (r.scale_smul_theta t) 0
  have hreciprocal := hresidual .reciprocalChart
  change
    (z t).jacobi.U * (z t).jacobi.T1 - 1 = 0
      at hreciprocal
  have hUT : (z t).jacobi.U * (z t).jacobi.T1 = 1 :=
    sub_eq_zero.mp hreciprocal
  simp only [Pi.smul_apply, smul_eq_mul,
    jacobiCoefficientTwist_zero,
    jacobiResidualProjectiveCoordinates,
    Matrix.cons_val_zero] at hvalue
  rw [hvalue]
  calc
    (z t).jacobi.U *
          (r.twist.d₁ * (z t).jacobi.T1) =
        r.twist.d₁ *
          ((z t).jacobi.U * (z t).jacobi.T1) := by
      ring
    _ = r.twist.d₁ * 1 := by rw [hUT]
    _ = r.twist.d₁ := mul_one _

/-- The forced scale never vanishes anywhere on the propagated
reciprocal chart. -/
theorem scale_ne_zero
    (r : CoherentMovingJacobiThetaRepresentation T z)
    (t : ℝ)
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t) = 0) :
    r.scale t ≠ 0 :=
  coherentJacobiBlochScale_ne_zero
    r.twist r.isProjectiveLift t hresidual

/-- At an arbitrary displayed elliptic base point `w(t)`, a coherent
theta representation gives the corresponding exact Bloch initial seed.
This is a derived construction; no new choice is made. -/
def twistedBlochSeed
    (r : CoherentMovingJacobiThetaRepresentation T z)
    (w : ℝ → ℂ) (t : ℝ)
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t) = 0) :
    TwistedJacobiBlochSeed (T t) (z t) (w t) :=
  coherentTwistedJacobiBlochSeed
    r.twist r.isProjectiveLift w t hresidual

end CoherentMovingJacobiThetaRepresentation

/-- **Unconditional coherent theta representation along a linked
trajectory.**

Once a continuous canonical-lambda lift has been chosen, the invariant
residual equations and genericity produce one constant coefficient twist.
The reciprocal-theta covering then produces one continuous elliptic lift.
No pointwise choice remains. -/
theorem
    nonempty_coherentMovingJacobiThetaRepresentation_unconditional
    {κZ κPhi : ℂ}
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    {t₀ : ℝ}
    (hB : UnaryModularState.B (z t₀).unary ≠ 0)
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t₀) = 0)
    (hT : Continuous T)
    (hLambda :
      ∀ t,
        UnaryModularState.lambdaCoordinate (z t).unary =
          canonicalLambda (T t)) :
    Nonempty (CoherentMovingJacobiThetaRepresentation T z) := by
  obtain ⟨d⟩ :=
    nonempty_coherentJacobiCoefficientTwist_along_trajectory
      hz hB hresidual T hT hLambda
  obtain ⟨ξ, hξ⟩ :=
    exists_coherentJacobiThetaProjectiveLift_unconditional
      hz hB hresidual hT d
  exact
    ⟨{
      twist := d
      parameter := ξ
      isProjectiveLift := hξ
    }⟩

/-- **Recurrent trajectory endpoint with global theta coherence.**

For a recurrent linked polynomial trajectory on the full residual locus,
either the unary modular state is a degenerate equilibrium, or the entire
real-time trajectory has one classified canonical-lambda lift and one
coherent moving-modulus Jacobi-theta representation.

The latter representation contains constant finite twists and a continuous
elliptic lift.  Its common scale and logarithmic slope are continuous and
recover all four theta coordinates, `Delta`, and `U` by the theorems above.
-/
theorem
    recurrentLinkedJacobi_equilibrium_or_coherentMovingThetaTrajectory
    {κZ : ℂ}
    {z : ℝ → LinkedJacobiState ℂ}
    (hz :
      IsScaledLinkedJacobiTrajectory
        κZ modularIndependentVariableClock z)
    {t₀ : ℝ}
    (hrec :
      ForwardRecurrentAt
        (fun t ↦ LinkedJacobiPolynomialCode.point (z t)) t₀)
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t₀) = 0) :
    UnaryModularState.vectorField (z t₀).unary = 0 ∨
      ∃ T : ℝ → ℍ,
        Continuous T ∧
        (∀ t,
          UnaryModularState.lambdaCoordinate (z t).unary =
            canonicalLambda (T t)) ∧
        IsHorizontalOrHorocycleLift
          (fun t ↦ (z t).unary) T t₀ ∧
        Nonempty
          (CoherentMovingJacobiThetaRepresentation T z) := by
  have hUnaryJacobi :
      UnaryModularState.jacobiResidual (z t₀).unary = 0 := by
    simpa only [UnaryModularState.jacobiResidual,
      linkedJacobiResidual,
      LinkedJacobiState.jacobiResidual] using
      hresidual .unaryJacobi
  rcases
      recurrentLinkedJacobiUnarySelectorReduction
        hz hrec hUnaryJacobi with
    hdegenerate | hgeneric
  · exact Or.inl hdegenerate.2
  · right
    rcases hgeneric with
      ⟨_hA, _hC, hB, T, hT, hLambda, hgeometry⟩
    exact
      ⟨T, hT, hLambda, hgeometry,
        nonempty_coherentMovingJacobiThetaRepresentation_unconditional
          hz hB hresidual hT hLambda⟩

/-! ## Differential form of the recurrent endpoint -/

/-- Relative Riccati coordinate comparing a linked unary trajectory to
the canonical theta state over `T`. -/
def linkedJacobiThetaComparisonU
    (T : ℝ → ℍ) (z : ℝ → LinkedJacobiState ℂ) :
    ℝ → ℂ :=
  unaryComparisonU
    (fun t ↦ (z t).unary)
    (fun t ↦ canonicalUnaryTheta (T t))

/-- Relative weight-two velocity comparing a linked unary trajectory to
the canonical theta state over `T`. -/
def linkedJacobiThetaComparisonV
    (T : ℝ → ℍ) (z : ℝ → LinkedJacobiState ℂ) :
    ℝ → ℂ :=
  unaryComparisonV
    (fun t ↦ (z t).unary)
    (fun t ↦ canonicalUnaryTheta (T t))

/-- The coherent recurrent endpoint with the complete differential
information of the modular lift retained.

Besides the moving theta representation, the generic branch now records

```
                 u' = -u²,   v' = -2uv,   T' = v.
```

Consequently `T` has the explicit global fractional-linear formula from
`IsRiccatiJetTrajectory.T_eq_fractionalLinear`.  This is the exact
modular input needed by a subsequent proof of the constant-parameter
simultaneous Bloch formula. -/
theorem
    recurrentLinkedJacobi_equilibrium_or_differentiableCoherentThetaTrajectory
    {κZ : ℂ}
    {z : ℝ → LinkedJacobiState ℂ}
    (hz :
      IsScaledLinkedJacobiTrajectory
        κZ modularIndependentVariableClock z)
    {t₀ : ℝ}
    (hrec :
      ForwardRecurrentAt
        (fun t ↦ LinkedJacobiPolynomialCode.point (z t)) t₀)
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t₀) = 0) :
    UnaryModularState.vectorField (z t₀).unary = 0 ∨
      ∃ T : ℝ → ℍ,
        Continuous T ∧
        (∀ t,
          UnaryModularState.lambdaCoordinate (z t).unary =
            canonicalLambda (T t)) ∧
        (∀ t,
          HasDerivAt
            (fun s : ℝ ↦ (T s : ℂ))
            (linkedJacobiThetaComparisonV T z t) t) ∧
        IsRiccatiJetTrajectory
          (linkedJacobiThetaComparisonU T z)
          (linkedJacobiThetaComparisonV T z)
          (fun t ↦ (T t : ℂ)) ∧
        IsHorizontalOrHorocycleLift
          (fun t ↦ (z t).unary) T t₀ ∧
        Nonempty
          (CoherentMovingJacobiThetaRepresentation T z) := by
  have hUnaryJacobi :
      UnaryModularState.jacobiResidual (z t₀).unary = 0 := by
    simpa only [UnaryModularState.jacobiResidual,
      linkedJacobiResidual,
      LinkedJacobiState.jacobiResidual] using
      hresidual .unaryJacobi
  have hrecUnary :=
    forwardRecurrentUnaryModularAt_of_linkedPolynomialPoint
      hrec
  rcases
      recurrentLinkedJacobiUnarySelectorReduction
        hz hrec hUnaryJacobi with
    hdegenerate | hgeneric
  · exact Or.inl hdegenerate.2
  · right
    rcases hgeneric with
      ⟨hA₀, hC₀, hB₀, _Told, _hTold,
        _hLambdaOld, _hgeometryOld⟩
    have hA := hz.unary.A_ne_zero hA₀
    have hC := hz.unary.C_ne_zero hC₀
    have hB := hz.unary.B_ne_zero hB₀
    obtain ⟨T, hT, hLambda, hTdiffRaw⟩ :=
      exists_differentiable_canonicalLambdaLift_of_generic
        hz.unary hA hC hB
    have hTvelocity :
        ∀ t,
          HasDerivAt
            (fun s : ℝ ↦ (T s : ℂ))
            (linkedJacobiThetaComparisonV T z t) t := by
      intro t
      simpa only [linkedJacobiThetaComparisonV] using
        canonicalLambdaLift_hasDerivAt_comparisonV
          hz.unary hB hLambda hTdiffRaw t
    have hjet :
        IsRiccatiJetTrajectory
          (linkedJacobiThetaComparisonU T z)
          (linkedJacobiThetaComparisonV T z)
          (fun t ↦ (T t : ℂ)) := by
      simpa only [linkedJacobiThetaComparisonU,
        linkedJacobiThetaComparisonV] using
        differentiableCanonicalLambdaLift_isRiccatiJetTrajectory
          hz.unary hB hLambda hTdiffRaw
    have hgeometry :
        IsHorizontalOrHorocycleLift
          (fun t ↦ (z t).unary) T t₀ := by
      exact
        recurrentCanonicalLambdaLift_horizontal_or_horocycle
          hz.unary hB hLambda hTdiffRaw hrecUnary
    exact
      ⟨T, hT, hLambda, hTvelocity, hjet, hgeometry,
        nonempty_coherentMovingJacobiThetaRepresentation_unconditional
          hz hB₀ hresidual hT hLambda⟩

/-- Explicit fractional-linear formula for the modulus in the generic
branch of the differential recurrent endpoint. -/
theorem coherentThetaTrajectory_modulus_eq_fractionalLinear
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (hjet :
      IsRiccatiJetTrajectory
        (linkedJacobiThetaComparisonU T z)
        (linkedJacobiThetaComparisonV T z)
        (fun t ↦ (T t : ℂ)))
    (t₀ t : ℝ) :
    (T t : ℂ) =
      (T t₀ : ℂ) +
        linkedJacobiThetaComparisonV T z t₀ *
          ((t - t₀ : ℝ) : ℂ) /
          (1 +
            linkedJacobiThetaComparisonU T z t₀ *
              ((t - t₀ : ℝ) : ℂ)) :=
  hjet.T_eq_fractionalLinear t₀ t

end

end HGAS.Modular
