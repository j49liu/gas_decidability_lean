import HGAS.Modular.LinkedJacobiPointwiseBlochSeed
import HGAS.Topology.ContinuousFourthRootBranch

/-!
# Coherent finite coefficient branches along a linked Jacobi trajectory

`LinkedJacobiPointwiseBlochSeed` resolves, at each individual time, two
finite sign ambiguities between the moving linked coefficients

```
                       (p₂,p₃,p₄)
```

and the canonical theta-square coefficients over a lambda lift `T(t)`.
Pointwise existence alone does not rule out making unrelated branch
choices at different times.

This file closes exactly that finite-cover gap.  The two relevant pairs
of continuous functions have equal squares and nonzero denominators.
Since the time line is connected, their signs cannot jump.  Consequently
there are two *constant* fourth roots of unity `d₁,d₂` for which the
coefficient-twist identities hold for every time.

This is a coherence theorem for the finite coefficient cover.  It does
not assert that the remaining Bloch parameters `S, ξ, L` can be chosen
continuously, nor that the explicit moving-modulus Bloch formula solves
the linked Jacobi ODE.
-/

namespace HGAS.Modular

open HGAS
open Complex
open UpperHalfPlane hiding I

noncomputable section

/-- The target cross-product for the `p₃` coefficient branch. -/
def jacobiCoefficientBranchThreeTarget
    (T : ℝ → ℍ) (z : ℝ → LinkedJacobiState ℂ)
    (t : ℝ) : ℂ :=
  (canonicalUnaryRoots (T t)).p2 * (z t).jacobi.p3

/-- The base cross-product for the `p₃` coefficient branch. -/
def jacobiCoefficientBranchThreeBase
    (T : ℝ → ℍ) (z : ℝ → LinkedJacobiState ℂ)
    (t : ℝ) : ℂ :=
  (z t).jacobi.p2 * (canonicalUnaryRoots (T t)).p3

/-- The target cross-product for the `p₄` coefficient branch. -/
def jacobiCoefficientBranchFourTarget
    (T : ℝ → ℍ) (z : ℝ → LinkedJacobiState ℂ)
    (t : ℝ) : ℂ :=
  (canonicalUnaryRoots (T t)).p2 * (z t).jacobi.p4

/-- The base cross-product for the `p₄` coefficient branch. -/
def jacobiCoefficientBranchFourBase
    (T : ℝ → ℍ) (z : ℝ → LinkedJacobiState ℂ)
    (t : ℝ) : ℂ :=
  (z t).jacobi.p2 * (canonicalUnaryRoots (T t)).p4

/-- A single pair of fourth-root twists valid along an entire lifted
linked Jacobi trajectory. -/
structure CoherentJacobiCoefficientTwist
    (T : ℝ → ℍ) (z : ℝ → LinkedJacobiState ℂ) where
  d₁ : ℂ
  d₂ : ℂ
  d₁_ne_zero : d₁ ≠ 0
  d₂_ne_zero : d₂ ≠ 0
  d₁_fourth : d₁ ^ 4 = 1
  d₂_fourth : d₂ ^ 4 = 1
  coefficientThree :
    ∀ t,
      (z t).jacobi.p2 *
            (canonicalUnaryRoots (T t)).p3 *
            d₁ ^ 2 =
          (canonicalUnaryRoots (T t)).p2 *
            (z t).jacobi.p3
  coefficientFour :
    ∀ t,
      (z t).jacobi.p2 *
            (canonicalUnaryRoots (T t)).p4 *
            d₂ ^ 2 =
          (canonicalUnaryRoots (T t)).p2 *
            (z t).jacobi.p4

theorem continuous_jacobiCoefficientBranchThreeTarget
    {κZ κPhi : ℂ}
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (hT : Continuous T)
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z) :
    Continuous (jacobiCoefficientBranchThreeTarget T z) := by
  exact
    (canonicalUnaryRoots_p2_mdifferentiable.continuous.comp hT).mul
      hz.jacobi.continuous_p3

theorem continuous_jacobiCoefficientBranchThreeBase
    {κZ κPhi : ℂ}
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (hT : Continuous T)
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z) :
    Continuous (jacobiCoefficientBranchThreeBase T z) := by
  exact
    hz.jacobi.continuous_p2.mul
      (canonicalUnaryRoots_p3_mdifferentiable.continuous.comp hT)

theorem continuous_jacobiCoefficientBranchFourTarget
    {κZ κPhi : ℂ}
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (hT : Continuous T)
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z) :
    Continuous (jacobiCoefficientBranchFourTarget T z) := by
  exact
    (canonicalUnaryRoots_p2_mdifferentiable.continuous.comp hT).mul
      hz.jacobi.continuous_p4

theorem continuous_jacobiCoefficientBranchFourBase
    {κZ κPhi : ℂ}
    {T : ℝ → ℍ} {z : ℝ → LinkedJacobiState ℂ}
    (hT : Continuous T)
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z) :
    Continuous (jacobiCoefficientBranchFourBase T z) := by
  exact
    hz.jacobi.continuous_p2.mul
      (canonicalUnaryRoots_p4_mdifferentiable.continuous.comp hT)

/-- On the full linked residual locus, nonvanishing of the unary
`B=A+C` coordinate forces the linked `p₃` coordinate to be nonzero.

The signed residual says `p₃=Y²`, while the unary Jacobi residual says
`Y⁴=B`. -/
theorem linkedJacobi_p3_ne_zero_of_B_ne_zero
    (z : LinkedJacobiState ℂ)
    (hB : UnaryModularState.B z.unary ≠ 0)
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i z = 0) :
    z.jacobi.p3 ≠ 0 := by
  have hp3 :
      z.jacobi.p3 = z.unary.Y ^ 2 := by
    exact sub_eq_zero.mp
      (by
        simpa only [linkedJacobiResidual,
          LinkedJacobiState.signedLink3] using
          hresidual .signedRootLinkThree)
  have hY :
      z.unary.Y ^ 4 =
        UnaryModularState.B z.unary := by
    have h :=
      hresidual .unaryJacobi
    change
      z.unary.Y ^ 4 - z.unary.A - z.unary.C = 0 at h
    simp only [UnaryModularState.B]
    linear_combination h
  intro hp3zero
  have hYsquare : z.unary.Y ^ 2 = 0 := by
    rw [← hp3, hp3zero]
  have hYzero : z.unary.Y = 0 := by
    exact eq_zero_of_pow_eq_zero hYsquare
  apply hB
  rw [← hY, hYzero]
  norm_num

/-- Pointwise coefficient seeds imply equality of the two cross-product
squares.  This strips away the noncanonical sign of the seed and retains
the exact continuous datum needed for branch rigidity. -/
theorem jacobiCoefficientBranch_crossSquares
    (τ : ℍ) (z : LinkedJacobiState ℂ)
    (hB : UnaryModularState.B z.unary ≠ 0)
    (hLambda :
      UnaryModularState.lambdaCoordinate z.unary =
        canonicalLambda τ)
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i z = 0) :
    jacobiCoefficientBranchThreeTarget
          (fun _ ↦ τ) (fun _ ↦ z) 0 ^ 2 =
        jacobiCoefficientBranchThreeBase
          (fun _ ↦ τ) (fun _ ↦ z) 0 ^ 2 ∧
      jacobiCoefficientBranchFourTarget
          (fun _ ↦ τ) (fun _ ↦ z) 0 ^ 2 =
        jacobiCoefficientBranchFourBase
          (fun _ ↦ τ) (fun _ ↦ z) 0 ^ 2 := by
  let seed : TwistedJacobiBlochSeed τ z 0 :=
    Classical.choice
      (linkedResidualPoint_exists_twistedJacobiBlochSeed
        τ z 0 hB hLambda hresidual)
  constructor
  · calc
      jacobiCoefficientBranchThreeTarget
            (fun _ ↦ τ) (fun _ ↦ z) 0 ^ 2 =
          (jacobiCoefficientBranchThreeBase
              (fun _ ↦ τ) (fun _ ↦ z) 0 *
            seed.d₁ ^ 2) ^ 2 := by
              simpa only [
                jacobiCoefficientBranchThreeTarget,
                jacobiCoefficientBranchThreeBase] using
                congrArg (fun x : ℂ ↦ x ^ 2)
                  seed.coefficientThree.symm
      _ =
          jacobiCoefficientBranchThreeBase
              (fun _ ↦ τ) (fun _ ↦ z) 0 ^ 2 *
            seed.d₁ ^ 4 := by ring
      _ =
          jacobiCoefficientBranchThreeBase
              (fun _ ↦ τ) (fun _ ↦ z) 0 ^ 2 := by
            rw [seed.d₁_fourth, mul_one]
  · calc
      jacobiCoefficientBranchFourTarget
            (fun _ ↦ τ) (fun _ ↦ z) 0 ^ 2 =
          (jacobiCoefficientBranchFourBase
              (fun _ ↦ τ) (fun _ ↦ z) 0 *
            seed.d₂ ^ 2) ^ 2 := by
              simpa only [
                jacobiCoefficientBranchFourTarget,
                jacobiCoefficientBranchFourBase] using
                congrArg (fun x : ℂ ↦ x ^ 2)
                  seed.coefficientFour.symm
      _ =
          jacobiCoefficientBranchFourBase
              (fun _ ↦ τ) (fun _ ↦ z) 0 ^ 2 *
            seed.d₂ ^ 4 := by ring
      _ =
          jacobiCoefficientBranchFourBase
              (fun _ ↦ τ) (fun _ ↦ z) 0 ^ 2 := by
            rw [seed.d₂_fourth, mul_one]

/-- The base cross-products are nonzero at every generic linked residual
point. -/
theorem jacobiCoefficientBranch_bases_ne_zero
    (τ : ℍ) (z : LinkedJacobiState ℂ)
    (hB : UnaryModularState.B z.unary ≠ 0)
    (hLambda :
      UnaryModularState.lambdaCoordinate z.unary =
        canonicalLambda τ)
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i z = 0) :
    jacobiCoefficientBranchThreeBase
          (fun _ ↦ τ) (fun _ ↦ z) 0 ≠ 0 ∧
      jacobiCoefficientBranchFourBase
          (fun _ ↦ τ) (fun _ ↦ z) 0 ≠ 0 := by
  let seed : TwistedJacobiBlochSeed τ z 0 :=
    Classical.choice
      (linkedResidualPoint_exists_twistedJacobiBlochSeed
        τ z 0 hB hLambda hresidual)
  have hcanonical :=
    canonicalUnaryRoots_p_product_ne_zero τ
  have hP2 :
      (canonicalUnaryRoots τ).p2 ≠ 0 := by
    intro hzero
    apply hcanonical
    rw [hzero, zero_mul]
    exact zero_mul _
  have hP3 :
      (canonicalUnaryRoots τ).p3 ≠ 0 := by
    intro hzero
    apply hcanonical
    rw [hzero]
    ring
  have hP4 :
      (canonicalUnaryRoots τ).p4 ≠ 0 := by
    intro hzero
    apply hcanonical
    rw [hzero, mul_zero]
  have hp3 := linkedJacobi_p3_ne_zero_of_B_ne_zero
    z hB hresidual
  have htargetThree :
      jacobiCoefficientBranchThreeTarget
          (fun _ ↦ τ) (fun _ ↦ z) 0 ≠ 0 := by
    exact mul_ne_zero hP2 hp3
  have hbaseThree :
      jacobiCoefficientBranchThreeBase
          (fun _ ↦ τ) (fun _ ↦ z) 0 ≠ 0 := by
    intro hzero
    have hbranch := seed.coefficientThree
    change
      z.jacobi.p2 * (canonicalUnaryRoots τ).p3 = 0
        at hzero
    rw [hzero, zero_mul] at hbranch
    apply htargetThree
    change
      (canonicalUnaryRoots τ).p2 * z.jacobi.p3 = 0
    exact hbranch.symm
  have hp2 : z.jacobi.p2 ≠ 0 := by
    change
      z.jacobi.p2 * (canonicalUnaryRoots τ).p3 ≠ 0
        at hbaseThree
    exact left_ne_zero_of_mul hbaseThree
  constructor
  · exact hbaseThree
  · exact mul_ne_zero hp2 hP4

/-- **Global coherence of the two finite coefficient branches.**

For a generic linked trajectory on the invariant residual locus and any
continuous canonical-lambda lift, the two fourth-root twists can be
chosen once and for all.  Their values are constant in time. -/
theorem
    exists_constant_jacobiCoefficientTwist_along_trajectory
    {κZ κPhi : ℂ}
    {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    {t₀ : ℝ}
    (hB :
      UnaryModularState.B (z t₀).unary ≠ 0)
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t₀) = 0)
    (T : ℝ → ℍ)
    (hT : Continuous T)
    (hLambda :
      ∀ t,
        UnaryModularState.lambdaCoordinate (z t).unary =
          canonicalLambda (T t)) :
    ∃ d₁ d₂ : ℂ,
      d₁ ≠ 0 ∧ d₂ ≠ 0 ∧
      d₁ ^ 4 = 1 ∧ d₂ ^ 4 = 1 ∧
      (∀ t,
        (z t).jacobi.p2 *
              (canonicalUnaryRoots (T t)).p3 *
              d₁ ^ 2 =
            (canonicalUnaryRoots (T t)).p2 *
              (z t).jacobi.p3) ∧
      (∀ t,
        (z t).jacobi.p2 *
              (canonicalUnaryRoots (T t)).p4 *
              d₂ ^ 2 =
            (canonicalUnaryRoots (T t)).p2 *
              (z t).jacobi.p4) := by
  have hB_all := hz.unary.B_ne_zero hB
  have hresidual_all :=
    linkedJacobiResiduals_eq_zero_along_trajectory
      hz hresidual
  have hsquares :
      ∀ t,
        jacobiCoefficientBranchThreeTarget T z t ^ 2 =
            jacobiCoefficientBranchThreeBase T z t ^ 2 ∧
          jacobiCoefficientBranchFourTarget T z t ^ 2 =
            jacobiCoefficientBranchFourBase T z t ^ 2 := by
    intro t
    simpa only [jacobiCoefficientBranchThreeTarget,
      jacobiCoefficientBranchThreeBase,
      jacobiCoefficientBranchFourTarget,
      jacobiCoefficientBranchFourBase] using
      jacobiCoefficientBranch_crossSquares
        (T t) (z t) (hB_all t) (hLambda t)
        (hresidual_all t)
  have hbases :
      ∀ t,
        jacobiCoefficientBranchThreeBase T z t ≠ 0 ∧
          jacobiCoefficientBranchFourBase T z t ≠ 0 := by
    intro t
    simpa only [jacobiCoefficientBranchThreeBase,
      jacobiCoefficientBranchFourBase] using
      jacobiCoefficientBranch_bases_ne_zero
        (T t) (z t) (hB_all t) (hLambda t)
        (hresidual_all t)
  obtain ⟨d₁, hd₁zero, hd₁four, hd₁⟩ :=
    HGAS.Topology.exists_constant_complex_fourthRoot_branch
      (jacobiCoefficientBranchThreeTarget T z)
      (jacobiCoefficientBranchThreeBase T z)
      (continuous_jacobiCoefficientBranchThreeTarget hT hz)
      (continuous_jacobiCoefficientBranchThreeBase hT hz)
      (fun t ↦ (hsquares t).1)
      (fun t ↦ (hbases t).1)
  obtain ⟨d₂, hd₂zero, hd₂four, hd₂⟩ :=
    HGAS.Topology.exists_constant_complex_fourthRoot_branch
      (jacobiCoefficientBranchFourTarget T z)
      (jacobiCoefficientBranchFourBase T z)
      (continuous_jacobiCoefficientBranchFourTarget hT hz)
      (continuous_jacobiCoefficientBranchFourBase hT hz)
      (fun t ↦ (hsquares t).2)
      (fun t ↦ (hbases t).2)
  exact
    ⟨d₁, d₂, hd₁zero, hd₂zero, hd₁four, hd₂four,
      fun t ↦ hd₁ t, fun t ↦ hd₂ t⟩

/-- Structured form of
`exists_constant_jacobiCoefficientTwist_along_trajectory`. -/
theorem
    nonempty_coherentJacobiCoefficientTwist_along_trajectory
    {κZ κPhi : ℂ}
    {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    {t₀ : ℝ}
    (hB :
      UnaryModularState.B (z t₀).unary ≠ 0)
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t₀) = 0)
    (T : ℝ → ℍ)
    (hT : Continuous T)
    (hLambda :
      ∀ t,
        UnaryModularState.lambdaCoordinate (z t).unary =
          canonicalLambda (T t)) :
    Nonempty (CoherentJacobiCoefficientTwist T z) := by
  rcases
      exists_constant_jacobiCoefficientTwist_along_trajectory
        hz hB hresidual T hT hLambda with
    ⟨d₁, d₂, hd₁zero, hd₂zero, hd₁four, hd₂four,
      hd₁, hd₂⟩
  exact
    ⟨{
      d₁ := d₁
      d₂ := d₂
      d₁_ne_zero := hd₁zero
      d₂_ne_zero := hd₂zero
      d₁_fourth := hd₁four
      d₂_fourth := hd₂four
      coefficientThree := hd₁
      coefficientFour := hd₂
    }⟩

/-- Recurrent compiler-facing endpoint with the finite-cover ambiguity
fully resolved.

In the generic branch this theorem provides one continuous lambda lift,
one pair of *constant* coefficient twists on the whole time line, and
pointwise Bloch seeds made using those coefficient equations.  The
parameters stored in the pointwise seeds are still not asserted to form
continuous functions of time. -/
theorem
    recurrentLinkedJacobi_equilibrium_or_lift_with_coherentTwist_and_pointwiseBlochSeeds
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
        linkedJacobiResidual i (z t₀) = 0)
    (w : ℝ → ℂ) :
    UnaryModularState.vectorField (z t₀).unary = 0 ∨
      ∃ T : ℝ → ℍ,
        Continuous T ∧
        (∀ t,
          UnaryModularState.lambdaCoordinate (z t).unary =
            canonicalLambda (T t)) ∧
        IsHorizontalOrHorocycleLift
          (fun t ↦ (z t).unary) T t₀ ∧
        Nonempty (CoherentJacobiCoefficientTwist T z) ∧
        ∀ t,
          Nonempty
            (TwistedJacobiBlochSeed (T t) (z t) (w t)) := by
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
      ⟨_hA, _hC, hB, T, hTcontinuous,
        hLambda, hgeometry⟩
    have hB_all := hz.unary.B_ne_zero hB
    have hresidual_all :=
      linkedJacobiResiduals_eq_zero_along_trajectory
        hz hresidual
    refine
      ⟨T, hTcontinuous, hLambda, hgeometry,
        nonempty_coherentJacobiCoefficientTwist_along_trajectory
          hz hB hresidual T hTcontinuous hLambda, ?_⟩
    intro t
    exact
      linkedResidualPoint_exists_twistedJacobiBlochSeed
        (T t) (z t) (w t) (hB_all t) (hLambda t)
        (hresidual_all t)

end

end HGAS.Modular
