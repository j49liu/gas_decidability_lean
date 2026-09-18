import HGAS.Modular.CanonicalUnaryThetaSolution
import HGAS.Modular.FiniteClosedCuspMeanSelector
import HGAS.Modular.ThetaLevelTwoTranslation
import HGAS.Modular.UnaryECoordinateRigidity
import Mathlib.Tactic

/-!
# Canonical coefficient data from a normalized finite closed cusp

This module isolates the last algebraic step in the finite-horocycle
selector.  It is deliberately independent of the arithmetic detector.

Suppose a linked unary--Jacobi trajectory has:

* modular clock `π i`;
* a finite closed-cusp selection whose horizontal speed is exactly one;
* all ten linked residuals equal to zero.

The selector already gives

```text
  Y(t)  = θ₃(τ(t)),       p₄(t) = θ₄(τ(t))²,
  τ(t)  = x + t + i y.
```

The residual `p₄²-C=0` identifies `C=θ₄⁴`.  The unary Jacobi residual
`Y⁴-A-C=0`, together with Jacobi's quartic identity, then identifies
`A=θ₂⁴`.  Both the selected unary state and the canonical theta state
solve the same polynomial ODE with clock `π i`.  Their common nonzero
`Y` coordinate forces their Eisenstein coordinates to agree, by the
reusable derivative-cancellation lemma in `UnaryECoordinateRigidity`.

Thus `p₃=θ₃²`, `p₄=θ₄²`, and `H=E₂/12`.  The residual `p₂²=A` leaves
only the sign of `p₂`.  That sign is not spurious: translation
`τ ↦ τ+2` negates `θ₂²` and fixes the other three root coordinates.
Consequently one of `τ(0)` and `τ(0)+2` is an exact canonical root seed.
-/

namespace HGAS.Modular

open Complex
open UpperHalfPlane hiding I

noncomputable section

/-- On a normalized finite closed branch, the complete unary state is
the canonical theta--Eisenstein state along the selected horizontal
line.

The proof uses no covering-space uniqueness: the two theta coordinates
are supplied by the finite-cusp selector, `A` and `C` are recovered
algebraically, and `E` is recovered from the differential equation for
the common nonvanishing `Y` coordinate. -/
theorem finiteClosedSelection_unary_eq_canonical
    {κZ : ℂ}
    {cusp : GammaTwoCuspLabel}
    {z : ℝ → LinkedJacobiState ℂ}
    {x y s : ℝ} {hy : 0 < y} {q : ℂ}
    (hz :
      IsScaledLinkedJacobiTrajectory
        κZ modularIndependentVariableClock z)
    (selection :
      FiniteClosedCuspMeanSelection cusp z x y s hy q)
    (hs : s = 1)
    (hresidual :
      ∀ t (r : LinkedJacobiResidualIndex),
        linkedJacobiResidual r (z t) = 0) :
    ∀ t,
      (z t).unary =
        canonicalUnaryTheta
          (horizontalLine x y 1 hy t) := by
  let τ : ℝ → ℍ :=
    fun t ↦ horizontalLine x y 1 hy t
  have hcanonical :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock
        (fun t ↦ canonicalUnaryTheta (τ t)) := by
    have h :=
      canonicalUnaryTheta_horizontalTrajectory
        x y Real.pi hy
    have hclock :
        I * (Real.pi : ℂ) =
          modularIndependentVariableClock := by
      simp only [modularIndependentVariableClock]
      ring
    rw [hclock] at h
    simpa only [τ, div_self Real.pi_ne_zero] using h
  have hY :
      ∀ t, (z t).unary.Y =
        (canonicalUnaryTheta (τ t)).Y := by
    intro t
    simpa only [
      τ, canonicalUnaryTheta_Y, hs] using
      selection.Y_eq_theta₃ t
  have hC :
      ∀ t, (z t).unary.C =
        (canonicalUnaryTheta (τ t)).C := by
    intro t
    have hlink :=
      hresidual t .coefficientLinkFour
    change
      (z t).jacobi.p4 ^ 2 - (z t).unary.C = 0
        at hlink
    have hp4 :=
      selection.p4_eq_theta₄_sq t
    rw [hs] at hp4
    rw [sub_eq_zero.mp hlink |>.symm, hp4]
    simp only [canonicalUnaryTheta_C, H₄]
    ring
  have hA :
      ∀ t, (z t).unary.A =
        (canonicalUnaryTheta (τ t)).A := by
    intro t
    have hzJacobi :=
      hresidual t .unaryJacobi
    change
      (z t).unary.Y ^ 4 -
          (z t).unary.A - (z t).unary.C = 0
        at hzJacobi
    have htheta :=
      canonicalUnaryTheta_jacobiResidual_eq_zero (τ t)
    change
      (canonicalUnaryTheta (τ t)).Y ^ 4 -
          (canonicalUnaryTheta (τ t)).A -
            (canonicalUnaryTheta (τ t)).C = 0
        at htheta
    rw [hY t, hC t] at hzJacobi
    linear_combination htheta - hzJacobi
  have hYne :
      ∀ t, (canonicalUnaryTheta (τ t)).Y ≠ 0 := by
    intro t
    simpa only [canonicalUnaryTheta_Y] using
      theta₃_ne_zero (τ t)
  have hE :
      ∀ t, (z t).unary.E =
        (canonicalUnaryTheta (τ t)).E :=
    unaryE_eq_of_A_C_Y_eq
      modularIndependentVariableClock_ne_zero
      hz.unary hcanonical hA hC hY hYne
  intro t
  ext
  · exact hA t
  · exact hC t
  · exact hE t
  · exact hY t

/-- The normalized finite branch has an exact canonical square-root seed.

At time zero, the witness modulus is either the displayed horizontal
modulus or its level-two translate.  Translation by two absorbs the sole
remaining sign ambiguity in `p₂` while preserving `p₃`, `p₄`, and `H`. -/
theorem exists_canonicalRootSeed_of_finiteClosedSelection
    {κZ : ℂ}
    {cusp : GammaTwoCuspLabel}
    {z : ℝ → LinkedJacobiState ℂ}
    {x y s : ℝ} {hy : 0 < y} {q : ℂ}
    (hz :
      IsScaledLinkedJacobiTrajectory
        κZ modularIndependentVariableClock z)
    (selection :
      FiniteClosedCuspMeanSelection cusp z x y s hy q)
    (hs : s = 1)
    (hresidual :
      ∀ t (r : LinkedJacobiResidualIndex),
        linkedJacobiResidual r (z t) = 0) :
    ∃ τ : ℍ,
      (z 0).jacobi.p2 = (canonicalUnaryRoots τ).p2 ∧
      (z 0).jacobi.p3 = (canonicalUnaryRoots τ).p3 ∧
      (z 0).jacobi.p4 = (canonicalUnaryRoots τ).p4 ∧
      (z 0).jacobi.H = (canonicalUnaryRoots τ).H := by
  let τ₀ : ℍ :=
    horizontalLine x y 1 hy 0
  have hunary :=
    finiteClosedSelection_unary_eq_canonical
      hz selection hs hresidual
  have hp3₀ :
      (z 0).jacobi.p3 =
        (canonicalUnaryRoots τ₀).p3 := by
    have hlink :=
      hresidual 0 .signedRootLinkThree
    change
      (z 0).jacobi.p3 - (z 0).unary.Y ^ 2 = 0
        at hlink
    rw [sub_eq_zero.mp hlink, hunary 0]
    rfl
  have hp4₀ :
      (z 0).jacobi.p4 =
        (canonicalUnaryRoots τ₀).p4 := by
    have h := selection.p4_eq_theta₄_sq 0
    rw [hs] at h
    simpa only [τ₀, canonicalUnaryRoots_p4] using h
  have hH₀ :
      (z 0).jacobi.H =
        (canonicalUnaryRoots τ₀).H := by
    have hlink :=
      hresidual 0 .eisensteinLink
    change
      12 * (z 0).jacobi.H - (z 0).unary.E = 0
        at hlink
    have hE :
        (z 0).unary.E =
          EisensteinSeries.E2 τ₀ := by
      simpa only [canonicalUnaryTheta_E] using
        congrArg UnaryModularState.E (hunary 0)
    simp only [canonicalUnaryRoots_H]
    rw [← hE]
    linear_combination (1 / 12 : ℂ) * hlink
  have hp2sq :
      (z 0).jacobi.p2 ^ 2 =
        (canonicalUnaryRoots τ₀).p2 ^ 2 := by
    have hlink :=
      hresidual 0 .coefficientLinkTwo
    change
      (z 0).jacobi.p2 ^ 2 - (z 0).unary.A = 0
        at hlink
    have hA :
        (z 0).unary.A =
          (canonicalUnaryRoots τ₀).p2 ^ 2 := by
      rw [hunary 0]
      simp only [
        canonicalUnaryTheta_A,
        canonicalUnaryRoots_p2, H₂]
      ring
    exact (sub_eq_zero.mp hlink).trans hA
  rcases
      eq_or_eq_neg_of_sq_eq_sq
        (z 0).jacobi.p2
        (canonicalUnaryRoots τ₀).p2 hp2sq with
    hp2₀ | hp2₀
  · exact ⟨τ₀, hp2₀, hp3₀, hp4₀, hH₀⟩
  · let τ₁ : ℍ := (2 : ℝ) +ᵥ τ₀
    have htranslate :=
      canonicalUnaryRoots_vadd_two τ₀
    refine ⟨τ₁, ?_, ?_, ?_, ?_⟩
    · exact hp2₀.trans htranslate.1.symm
    · exact hp3₀.trans htranslate.2.1.symm
    · exact hp4₀.trans htranslate.2.2.1.symm
    · exact hH₀.trans htranslate.2.2.2.symm

end

end HGAS.Modular
