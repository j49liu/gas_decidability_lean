import HGAS.Modular.JacobiPointwiseSaturationUnconditional
import HGAS.Modular.JacobiResidualEnergy
import HGAS.Modular.RecurrentUnarySelectorReduction

/-!
# Twisted Bloch initial data for a linked Jacobi residual point

The projective saturation theorem is stated for the canonical coefficient
triple

```
  (theta₂(τ)^2, theta₃(τ)^2, theta₄(τ)^2).
```

A linked polynomial state has independent coefficient coordinates
`(p₂,p₃,p₄)`.  On the coefficient-link locus their squares have one common
nonzero scale relative to the canonical triple, but `p₂` and `p₄` still
carry finite square-root signs.  This file makes that finite ambiguity
explicit.

Two fourth roots of unity `d₁,d₂` act diagonally on the four Jacobi
coordinates by

```
       (T₁,T₂,T₃,T₄)
         ↦ (d₁T₁,d₂T₂,d₁d₂T₃,T₄).
```

The exact coefficient identities imply that this diagonal twist carries
the linked residual quadrics to the canonical residual quadrics.  The
unconditional projective saturation theorem can then be applied, and its
Bloch slope is chosen to match the correspondingly twisted `Delta`
coordinate.

The endpoint is pointwise initial data, not a global continuation theorem.
No claim is made here that the selected parameters vary continuously in
time or that the explicit Bloch family solves the complete moving-modulus
Jacobi system.
-/

namespace HGAS.Modular

open HGAS
open Complex
open UpperHalfPlane hiding I

noncomputable section

/-- Diagonal finite-cover twist converting a linked coefficient branch to
the canonical Jacobi residual curve. -/
def jacobiCoefficientTwist
    (d₁ d₂ : ℂ) (X : Fin 4 → ℂ) :
    Fin 4 → ℂ :=
  ![d₁ * X 0, d₂ * X 1,
    (d₁ * d₂) * X 2, X 3]

@[simp]
theorem jacobiCoefficientTwist_zero
    (d₁ d₂ : ℂ) (X : Fin 4 → ℂ) :
    jacobiCoefficientTwist d₁ d₂ X 0 =
      d₁ * X 0 := rfl

@[simp]
theorem jacobiCoefficientTwist_one
    (d₁ d₂ : ℂ) (X : Fin 4 → ℂ) :
    jacobiCoefficientTwist d₁ d₂ X 1 =
      d₂ * X 1 := rfl

@[simp]
theorem jacobiCoefficientTwist_two
    (d₁ d₂ : ℂ) (X : Fin 4 → ℂ) :
    jacobiCoefficientTwist d₁ d₂ X 2 =
      (d₁ * d₂) * X 2 := rfl

@[simp]
theorem jacobiCoefficientTwist_three
    (d₁ d₂ : ℂ) (X : Fin 4 → ℂ) :
    jacobiCoefficientTwist d₁ d₂ X 3 =
      X 3 := rfl

/-- Equal nonzero square scales of two coefficient triples produce the
two finite diagonal branch factors needed below. -/
theorem exists_jacobiCoefficientTwist_of_commonSquareScale
    (P₂ P₃ P₄ p₂ p₃ p₄ v : ℂ)
    (hP₂ : P₂ ≠ 0)
    (hv : v ≠ 0)
    (h₂ : p₂ ^ 2 = v * P₂ ^ 2)
    (h₃ : p₃ ^ 2 = v * P₃ ^ 2)
    (h₄ : p₄ ^ 2 = v * P₄ ^ 2) :
    ∃ d₁ d₂ : ℂ,
      d₁ ≠ 0 ∧ d₂ ≠ 0 ∧
      d₁ ^ 4 = 1 ∧ d₂ ^ 4 = 1 ∧
      p₂ * P₃ * d₁ ^ 2 = P₂ * p₃ ∧
      p₂ * P₄ * d₂ ^ 2 = P₂ * p₄ := by
  have hp₂ : p₂ ≠ 0 := by
    intro hp₂
    have hzero : v * P₂ ^ 2 = 0 := by
      rw [← h₂, hp₂]
      norm_num
    exact (mul_ne_zero hv (pow_ne_zero 2 hP₂)) hzero
  have hs₃ :
      (p₃ * P₂) ^ 2 = (p₂ * P₃) ^ 2 := by
    rw [mul_pow, mul_pow, h₃, h₂]
    ring
  have hs₄ :
      (p₄ * P₂) ^ 2 = (p₂ * P₄) ^ 2 := by
    rw [mul_pow, mul_pow, h₄, h₂]
    ring
  have hd₁ :
      ∃ d₁ : ℂ,
        d₁ ≠ 0 ∧ d₁ ^ 4 = 1 ∧
          p₂ * P₃ * d₁ ^ 2 = P₂ * p₃ := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs₃ with
      hplus | hminus
    · refine ⟨1, one_ne_zero, by norm_num, ?_⟩
      simpa [mul_comm] using hplus.symm
    · refine ⟨I, I_ne_zero, ?_, ?_⟩
      · rw [show (4 : ℕ) = 2 + 2 by norm_num,
          pow_add, I_sq]
        norm_num
      · rw [I_sq]
        calc
          p₂ * P₃ * -1 = -(p₂ * P₃) := by ring
          _ = P₂ * p₃ := by
            rw [← hminus]
            ring
  have hd₂ :
      ∃ d₂ : ℂ,
        d₂ ≠ 0 ∧ d₂ ^ 4 = 1 ∧
          p₂ * P₄ * d₂ ^ 2 = P₂ * p₄ := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs₄ with
      hplus | hminus
    · refine ⟨1, one_ne_zero, by norm_num, ?_⟩
      simpa [mul_comm] using hplus.symm
    · refine ⟨I, I_ne_zero, ?_, ?_⟩
      · rw [show (4 : ℕ) = 2 + 2 by norm_num,
          pow_add, I_sq]
        norm_num
      · rw [I_sq]
        calc
          p₂ * P₄ * -1 = -(p₂ * P₄) := by ring
          _ = P₂ * p₄ := by
            rw [← hminus]
            ring
  rcases hd₁ with ⟨d₁, hd₁zero, hd₁four, hd₁branch⟩
  rcases hd₂ with ⟨d₂, hd₂zero, hd₂four, hd₂branch⟩
  exact
    ⟨d₁, d₂, hd₁zero, hd₂zero,
      hd₁four, hd₂four, hd₁branch, hd₂branch⟩

/-- The finite diagonal twist transports both source quadrics to the
canonical coefficient triple. -/
theorem jacobiResiduals_coefficientTwist
    (P₂ P₃ P₄ p₂ p₃ p₄ d₁ d₂ : ℂ)
    (X : Fin 4 → ℂ)
    (hp₂ : p₂ ≠ 0)
    (hd₁four : d₁ ^ 4 = 1)
    (hd₂four : d₂ ^ 4 = 1)
    (hd₁branch :
      p₂ * P₃ * d₁ ^ 2 = P₂ * p₃)
    (hd₂branch :
      p₂ * P₄ * d₂ ^ 2 = P₂ * p₄)
    (hQ₁ :
      jacobiResidualQ1 p₂ p₃ p₄ X = 0)
    (hQ₂ :
      jacobiResidualQ2 p₂ p₃ p₄ X = 0) :
    jacobiResidualQ1 P₂ P₃ P₄
        (jacobiCoefficientTwist d₁ d₂ X) = 0 ∧
      jacobiResidualQ2 P₂ P₃ P₄
        (jacobiCoefficientTwist d₁ d₂ X) = 0 := by
  have hd₁reverse :
      p₂ * P₃ = P₂ * p₃ * d₁ ^ 2 := by
    calc
      p₂ * P₃ =
          p₂ * P₃ * d₁ ^ 4 := by
        rw [hd₁four]
        ring
      _ = (p₂ * P₃ * d₁ ^ 2) * d₁ ^ 2 := by
        ring
      _ = P₂ * p₃ * d₁ ^ 2 := by
        rw [hd₁branch]
  have hd₂reverse :
      p₂ * P₄ = P₂ * p₄ * d₂ ^ 2 := by
    calc
      p₂ * P₄ =
          p₂ * P₄ * d₂ ^ 4 := by
        rw [hd₂four]
        ring
      _ = (p₂ * P₄ * d₂ ^ 2) * d₂ ^ 2 := by
        ring
      _ = P₂ * p₄ * d₂ ^ 2 := by
        rw [hd₂branch]
  constructor
  · apply (mul_left_cancel₀ hp₂)
    rw [mul_zero]
    calc
      p₂ *
          jacobiResidualQ1 P₂ P₃ P₄
            (jacobiCoefficientTwist d₁ d₂ X) =
        P₂ * jacobiResidualQ1 p₂ p₃ p₄ X := by
          simp only [jacobiResidualQ1,
            jacobiCoefficientTwist_zero,
            jacobiCoefficientTwist_one,
            jacobiCoefficientTwist_three]
          linear_combination
            -(X 1) ^ 2 * hd₂branch -
              (X 0) ^ 2 * hd₁branch
      _ = 0 := by rw [hQ₁, mul_zero]
  · apply (mul_left_cancel₀ hp₂)
    rw [mul_zero]
    calc
      p₂ *
          jacobiResidualQ2 P₂ P₃ P₄
            (jacobiCoefficientTwist d₁ d₂ X) =
        (P₂ * d₁ ^ 2 * d₂ ^ 2) *
          jacobiResidualQ2 p₂ p₃ p₄ X := by
          simp only [jacobiResidualQ2,
            jacobiCoefficientTwist_zero,
            jacobiCoefficientTwist_one,
            jacobiCoefficientTwist_two]
          linear_combination
            -(d₂ ^ 2 * (X 1) ^ 2) * hd₁reverse -
              (d₁ ^ 2 * (X 0) ^ 2) * hd₂reverse
      _ = 0 := by rw [hQ₂, mul_zero]

/-- Exact pointwise Bloch initial data after resolving the two finite
coefficient signs. -/
structure TwistedJacobiBlochSeed
    (τ : ℍ) (z : LinkedJacobiState ℂ) (w : ℂ) where
  d₁ : ℂ
  d₂ : ℂ
  S : ℂ
  ξ : ℂ
  L : ℂ
  d₁_ne_zero : d₁ ≠ 0
  d₂_ne_zero : d₂ ≠ 0
  d₁_fourth : d₁ ^ 4 = 1
  d₂_fourth : d₂ ^ 4 = 1
  coefficientThree :
    z.jacobi.p2 * (canonicalUnaryRoots τ).p3 *
          d₁ ^ 2 =
      (canonicalUnaryRoots τ).p2 * z.jacobi.p3
  coefficientFour :
    z.jacobi.p2 * (canonicalUnaryRoots τ).p4 *
          d₂ ^ 2 =
      (canonicalUnaryRoots τ).p2 * z.jacobi.p4
  S_ne_zero : S ≠ 0
  value :
    jacobiBlochThetaVector
        (jacobiBlochParameterC S w (τ : ℂ) L)
        (jacobiBlochParameterA L)
        (jacobiBlochParameterB ξ w (τ : ℂ) L)
        (τ : ℂ) w =
      jacobiCoefficientTwist d₁ d₂
        (jacobiResidualProjectiveCoordinates z.jacobi)
  firstDerivative :
    jacobiBlochThetaVectorPrime
          (jacobiBlochParameterC S w (τ : ℂ) L)
          (jacobiBlochParameterA L)
          (jacobiBlochParameterB ξ w (τ : ℂ) L)
          (τ : ℂ) w 0 / (Real.pi : ℂ) =
      d₁ * z.jacobi.Delta

/-- The full ten-residual linked validity locus is invariant along the
combined linked trajectory.

This assembles the existing four-dimensional Jacobi residual ODE, the
five-dimensional coefficient-link ODE, and the signed-root scalar ODE
into the exact residual-index interface used by the compiler. -/
theorem linkedJacobiResiduals_eq_zero_along_trajectory
    {κZ κPhi : ℂ}
    {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    {t₀ : ℝ}
    (hzero :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i (z t₀) = 0) :
    ∀ t, ∀ i : LinkedJacobiResidualIndex,
      linkedJacobiResidual i (z t) = 0 := by
  have hcoefficientZero :
      IsScaledLinkedJacobiTrajectory.CoefficientResidualsZero
        (z t₀) := by
    exact
      ⟨hzero .unaryJacobi,
        hzero .coefficientLinkTwo,
        hzero .coefficientLinkThree,
        hzero .coefficientLinkFour,
        hzero .eisensteinLink⟩
  have hcoefficient :=
    hz.coefficientResiduals_eq_zero hcoefficientZero
  have hsigned :=
    hz.signedLink3_eq_zero hcoefficientZero
      (hzero .signedRootLinkThree)
  have hjacobiZero :
      IsScaledJacobiTrajectory.ResidualsZero
        (z t₀).jacobi := by
    exact
      ⟨hzero .coefficientCurve,
        hzero .thetaQuadricOne,
        hzero .thetaQuadricTwo,
        hzero .reciprocalChart⟩
  have hjacobi :=
    hz.jacobi.residuals_eq_zero hjacobiZero
  intro t i
  rcases hcoefficient t with
    ⟨hUnary, hLink₂, hLink₃, hLink₄, hLinkH⟩
  rcases hjacobi t with
    ⟨hR₀, hR₁, hR₂, hRU⟩
  cases i with
  | coefficientCurve => exact hR₀
  | thetaQuadricOne => exact hR₁
  | thetaQuadricTwo => exact hR₂
  | reciprocalChart => exact hRU
  | unaryJacobi => exact hUnary
  | coefficientLinkTwo => exact hLink₂
  | coefficientLinkThree => exact hLink₃
  | coefficientLinkFour => exact hLink₄
  | eisensteinLink => exact hLinkH
  | signedRootLinkThree => exact hsigned t

/-- Every generic linked residual point has exact Bloch initial data after
one of the finite diagonal coefficient twists.

The premise is the compiler's full ten-residual interface.  The proof
selects the unary and coefficient links, the two theta quadrics, and the
reciprocal link that are needed at this point.  In particular, `U*T₁=1`
supplies the nonzero first coordinate required by pointwise saturation; it
is not an extra regular-chart hypothesis. -/
theorem linkedResidualPoint_exists_twistedJacobiBlochSeed
    (τ : ℍ) (z : LinkedJacobiState ℂ) (w : ℂ)
    (hB : UnaryModularState.B z.unary ≠ 0)
    (hLambda :
      UnaryModularState.lambdaCoordinate z.unary =
        canonicalLambda τ)
    (hresidual :
      ∀ i : LinkedJacobiResidualIndex,
        linkedJacobiResidual i z = 0) :
    Nonempty (TwistedJacobiBlochSeed τ z w) := by
  let source : ℝ → UnaryModularState ℂ :=
    fun _ ↦ z.unary
  let reference : ℝ → UnaryModularState ℂ :=
    fun _ ↦ canonicalUnaryTheta τ
  let v : ℂ := unaryComparisonV source reference 0
  have hBcanonical :
      UnaryModularState.B (canonicalUnaryTheta τ) ≠ 0 :=
    canonicalUnaryTheta_B_ne_zero τ
  have hLambdaReference :
      UnaryModularState.lambdaCoordinate (source 0) =
        UnaryModularState.lambdaCoordinate (reference 0) := by
    simpa only [source, reference,
      canonicalUnaryTheta_lambdaCoordinate] using hLambda
  have hv : v ≠ 0 := by
    simpa only [v, source, reference, unaryComparisonV] using
      div_ne_zero hB hBcanonical
  have hA :
      z.unary.A =
        v * (canonicalUnaryTheta τ).A := by
    simpa only [source, reference, v] using
      unaryComparison_A_eq source reference 0
        hB hBcanonical hLambdaReference
  have hC :
      z.unary.C =
        v * (canonicalUnaryTheta τ).C := by
    simpa only [source, reference, v] using
      unaryComparison_C_eq source reference 0
        hB hBcanonical hLambdaReference
  have hcanonical₂ :
      (canonicalUnaryRoots τ).p2 ^ 2 =
        (canonicalUnaryTheta τ).A := by
    exact sub_eq_zero.mp
      (by
        simpa only [UnaryRootState.link2] using
          canonicalUnaryRoots_link2_eq_zero τ)
  have hcanonical₄ :
      (canonicalUnaryRoots τ).p4 ^ 2 =
        (canonicalUnaryTheta τ).C := by
    exact sub_eq_zero.mp
      (by
        simpa only [UnaryRootState.link4] using
          canonicalUnaryRoots_link4_eq_zero τ)
  have hlink₂ :
      z.jacobi.p2 ^ 2 = z.unary.A := by
    exact sub_eq_zero.mp
      (by
        simpa only [linkedJacobiResidual,
          LinkedJacobiState.link2] using
          hresidual .coefficientLinkTwo)
  have hlink₃ :
      z.jacobi.p3 ^ 2 = z.unary.Y ^ 4 := by
    exact sub_eq_zero.mp
      (by
        simpa only [linkedJacobiResidual,
          LinkedJacobiState.link3] using
          hresidual .coefficientLinkThree)
  have hlink₄ :
      z.jacobi.p4 ^ 2 = z.unary.C := by
    exact sub_eq_zero.mp
      (by
        simpa only [linkedJacobiResidual,
          LinkedJacobiState.link4] using
          hresidual .coefficientLinkFour)
  have hUnaryJacobi :
      z.unary.Y ^ 4 = z.unary.A + z.unary.C := by
    have h :=
      hresidual .unaryJacobi
    change
      z.unary.Y ^ 4 - z.unary.A - z.unary.C = 0 at h
    linear_combination h
  have hp₂square :
      z.jacobi.p2 ^ 2 =
        v * (canonicalUnaryRoots τ).p2 ^ 2 := by
    calc
      z.jacobi.p2 ^ 2 = z.unary.A := hlink₂
      _ = v * (canonicalUnaryTheta τ).A := hA
      _ = v * (canonicalUnaryRoots τ).p2 ^ 2 := by
        rw [hcanonical₂]
  have hp₄square :
      z.jacobi.p4 ^ 2 =
        v * (canonicalUnaryRoots τ).p4 ^ 2 := by
    calc
      z.jacobi.p4 ^ 2 = z.unary.C := hlink₄
      _ = v * (canonicalUnaryTheta τ).C := hC
      _ = v * (canonicalUnaryRoots τ).p4 ^ 2 := by
        rw [hcanonical₄]
  have hp₃square :
      z.jacobi.p3 ^ 2 =
        v * (canonicalUnaryRoots τ).p3 ^ 2 := by
    calc
      z.jacobi.p3 ^ 2 = z.unary.Y ^ 4 := hlink₃
      _ = z.unary.A + z.unary.C := hUnaryJacobi
      _ =
          v * (canonicalUnaryTheta τ).A +
            v * (canonicalUnaryTheta τ).C := by
        rw [hA, hC]
      _ =
          v *
            ((canonicalUnaryRoots τ).p2 ^ 2 +
              (canonicalUnaryRoots τ).p4 ^ 2) := by
        rw [hcanonical₂, hcanonical₄]
        ring
      _ = v * (canonicalUnaryRoots τ).p3 ^ 2 := by
        rw [canonicalUnaryRoots_p3_sq_eq]
  have hcanonicalProduct :=
    canonicalUnaryRoots_p_product_ne_zero τ
  have hP₂ :
      (canonicalUnaryRoots τ).p2 ≠ 0 := by
    intro hzero
    apply hcanonicalProduct
    rw [hzero, zero_mul]
    exact zero_mul _
  have hp₂ : z.jacobi.p2 ≠ 0 := by
    intro hzero
    have hcontradiction :
        v * (canonicalUnaryRoots τ).p2 ^ 2 = 0 := by
      rw [← hp₂square, hzero]
      norm_num
    exact
      (mul_ne_zero hv (pow_ne_zero 2 hP₂))
        hcontradiction
  obtain
      ⟨d₁, d₂, hd₁, hd₂, hd₁four, hd₂four,
        hd₁branch, hd₂branch⟩ :=
    exists_jacobiCoefficientTwist_of_commonSquareScale
      (canonicalUnaryRoots τ).p2
      (canonicalUnaryRoots τ).p3
      (canonicalUnaryRoots τ).p4
      z.jacobi.p2 z.jacobi.p3 z.jacobi.p4 v
      hP₂ hv hp₂square hp₃square hp₄square
  let X : Fin 4 → ℂ :=
    jacobiResidualProjectiveCoordinates z.jacobi
  have hQ₁ :
      jacobiResidualQ1
        z.jacobi.p2 z.jacobi.p3 z.jacobi.p4 X = 0 := by
    simpa only [X,
      jacobiResidualQ1_projectiveCoordinates] using
      hresidual .thetaQuadricOne
  have hQ₂ :
      jacobiResidualQ2
        z.jacobi.p2 z.jacobi.p3 z.jacobi.p4 X = 0 := by
    simpa only [X,
      jacobiResidualQ2_projectiveCoordinates] using
      hresidual .thetaQuadricTwo
  have hcanonicalQ :=
    jacobiResiduals_coefficientTwist
      (canonicalUnaryRoots τ).p2
      (canonicalUnaryRoots τ).p3
      (canonicalUnaryRoots τ).p4
      z.jacobi.p2 z.jacobi.p3 z.jacobi.p4
      d₁ d₂ X hp₂ hd₁four hd₂four
      hd₁branch hd₂branch hQ₁ hQ₂
  have hT₁ : z.jacobi.T1 ≠ 0 := by
    intro hzero
    have hreciprocal :=
      hresidual .reciprocalChart
    change z.jacobi.U * z.jacobi.T1 - 1 = 0 at hreciprocal
    rw [hzero, mul_zero] at hreciprocal
    norm_num at hreciprocal
  have htwisted₁ :
      jacobiCoefficientTwist d₁ d₂ X 0 ≠ 0 := by
    simp only [jacobiCoefficientTwist_zero, X,
      jacobiResidualProjectiveCoordinates,
      Matrix.cons_val_zero]
    exact mul_ne_zero hd₁ hT₁
  have htwisted :
      jacobiCoefficientTwist d₁ d₂ X ≠ 0 := by
    intro hzero
    exact htwisted₁ (congrFun hzero 0)
  obtain
      ⟨S, ξ, L, hS, _hscale, _hinitial,
        hvalue, hfirstDerivative⟩ :=
    pointwiseJacobiBlochSaturation τ
      (jacobiCoefficientTwist d₁ d₂ X)
      (d₁ * z.jacobi.Delta) w
      htwisted htwisted₁ hcanonicalQ.1 hcanonicalQ.2
  exact
    ⟨{
      d₁ := d₁
      d₂ := d₂
      S := S
      ξ := ξ
      L := L
      d₁_ne_zero := hd₁
      d₂_ne_zero := hd₂
      d₁_fourth := hd₁four
      d₂_fourth := hd₂four
      coefficientThree := hd₁branch
      coefficientFour := hd₂branch
      S_ne_zero := hS
      value := by simpa only [X] using hvalue
      firstDerivative := hfirstDerivative
    }⟩

/-- Recurrent compiler-facing endpoint.

For a recurrent linked polynomial trajectory on the ten-residual locus,
either the unary state is a degenerate equilibrium, or it has a global
canonical-lambda lift and the Jacobi coordinates at the recurrent time
have exact twisted Bloch initial data over that lift. -/
theorem recurrentLinkedJacobi_equilibrium_or_lift_with_twistedBlochSeed
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
    (w : ℂ) :
    UnaryModularState.vectorField (z t₀).unary = 0 ∨
      ∃ T : ℝ → ℍ,
        Continuous T ∧
        (∀ t,
          UnaryModularState.lambdaCoordinate (z t).unary =
            canonicalLambda (T t)) ∧
        IsHorizontalOrHorocycleLift
          (fun t ↦ (z t).unary) T t₀ ∧
        Nonempty
          (TwistedJacobiBlochSeed (T t₀) (z t₀) w) := by
  have hUnaryJacobi :
      UnaryModularState.jacobiResidual (z t₀).unary = 0 := by
    simpa only [UnaryModularState.jacobiResidual,
      linkedJacobiResidual,
      LinkedJacobiState.jacobiResidual] using
      hresidual .unaryJacobi
  rcases recurrentLinkedJacobiUnarySelectorReduction
      hz hrec hUnaryJacobi with
    hdegenerate | hgeneric
  · exact Or.inl hdegenerate.2
  · right
    rcases hgeneric with
      ⟨_hA, _hC, hB, T, hTcontinuous,
        hLambda, hgeometry⟩
    refine
      ⟨T, hTcontinuous, hLambda, hgeometry, ?_⟩
    exact
      linkedResidualPoint_exists_twistedJacobiBlochSeed
        (T t₀) (z t₀) w hB (hLambda t₀)
        hresidual

/-- Global pointwise-saturation endpoint along a recurrent trajectory.

In the generic branch, every time of the global canonical-lambda lift has
twisted Bloch initial data.  The twist and Bloch parameters are still
allowed to depend noncontinuously on time; this theorem deliberately does
not claim a global choice or ODE continuation. -/
theorem
    recurrentLinkedJacobi_equilibrium_or_lift_with_pointwiseBlochSeeds
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
        ∀ t,
          Nonempty
            (TwistedJacobiBlochSeed (T t) (z t) (w t)) := by
  have hUnaryJacobi :
      UnaryModularState.jacobiResidual (z t₀).unary = 0 := by
    simpa only [UnaryModularState.jacobiResidual,
      linkedJacobiResidual,
      LinkedJacobiState.jacobiResidual] using
      hresidual .unaryJacobi
  rcases recurrentLinkedJacobiUnarySelectorReduction
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
      ⟨T, hTcontinuous, hLambda, hgeometry, ?_⟩
    intro t
    exact
      linkedResidualPoint_exists_twistedJacobiBlochSeed
        (T t) (z t) (w t) (hB_all t) (hLambda t)
        (hresidual_all t)

end

end HGAS.Modular
