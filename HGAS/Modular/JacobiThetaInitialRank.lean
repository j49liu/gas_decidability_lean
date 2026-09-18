import HGAS.Modular.JacobiThetaResiduals
import Mathlib.Analysis.Calculus.Deriv.Pi

/-!
# Projective theta derivatives and the rank-three initial-value map

This module isolates the local differential content of equations
(8.5)--(8.8).  It has three layers.

1. The derivatives of all four theta functions are defined explicitly in
   terms of Mathlib's differentiated theta series and proved correct.
2. The three Jacobi Wronskian identities are packaged as one pointwise
   proposition.  If they hold, the theta vector and its derivative are
   linearly independent; hence the projective theta map is immersive.
3. For arbitrary independent vectors `T,Tξ`, the linearization of

```
 (S,ξ,L) ↦ (S T(ξ), S (θ₁'(ξ)/π + L θ₁(ξ)))
```

is injective, and therefore has complex rank three.

The second layer deliberately exposes the one analytic input not supplied
by Mathlib: the Jacobi derivative/Wronskian identities themselves.  The
rank proof after that input is entirely formal and reusable.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real

noncomputable section

/-! ## Actual derivatives of the four theta coordinates -/

def jacobiTheta3Prime
    (z τ : ℂ) : ℂ :=
  jacobiTheta₂' z τ

def jacobiTheta4Prime
    (z τ : ℂ) : ℂ :=
  jacobiTheta₂' (z + 1 / 2) τ

def jacobiTheta2Prime
    (z τ : ℂ) : ℂ :=
  cexp (π * I * (τ / 4 + z)) *
    (π * I * jacobiTheta₂ (z + τ / 2) τ +
      jacobiTheta₂' (z + τ / 2) τ)

def jacobiTheta1Prime
    (z τ : ℂ) : ℂ :=
  -jacobiTheta2Prime (z + 1 / 2) τ

def jacobiThetaVectorPrime
    (z τ : ℂ) : Fin 4 → ℂ :=
  ![jacobiTheta1Prime z τ, jacobiTheta2Prime z τ,
    jacobiTheta3Prime z τ, jacobiTheta4Prime z τ]

theorem hasDerivAt_jacobiTheta3
    (z τ : ℂ) (hτ : 0 < τ.im) :
    HasDerivAt (fun w ↦ jacobiTheta3 w τ)
      (jacobiTheta3Prime z τ) z := by
  simpa only [jacobiTheta3, jacobiTheta3Prime] using
    hasDerivAt_jacobiTheta₂_fst z hτ

theorem hasDerivAt_jacobiTheta4
    (z τ : ℂ) (hτ : 0 < τ.im) :
    HasDerivAt (fun w ↦ jacobiTheta4 w τ)
      (jacobiTheta4Prime z τ) z := by
  convert
    (hasDerivAt_jacobiTheta₂_fst
      (z + 1 / 2) hτ).comp z
        ((hasDerivAt_id z).add_const (1 / 2)) using 1
  simp [jacobiTheta4Prime]

theorem hasDerivAt_jacobiTheta2
    (z τ : ℂ) (hτ : 0 < τ.im) :
    HasDerivAt (fun w ↦ jacobiTheta2 w τ)
      (jacobiTheta2Prime z τ) z := by
  have hlinear :
      HasDerivAt
        (fun w : ℂ ↦ π * I * (τ / 4 + w))
        (π * I) z := by
    convert
      ((hasDerivAt_id z).const_add (τ / 4)).const_mul
        (π * I) using 1
    ring
  have hexp :
      HasDerivAt
        (fun w : ℂ ↦
          cexp (π * I * (τ / 4 + w)))
        (cexp (π * I * (τ / 4 + z)) *
          (π * I)) z :=
    hlinear.cexp
  have hshift :
      HasDerivAt
        (fun w : ℂ ↦
          jacobiTheta₂ (w + τ / 2) τ)
        (jacobiTheta₂' (z + τ / 2) τ) z :=
    by
      convert
        (hasDerivAt_jacobiTheta₂_fst
          (z + τ / 2) hτ).comp z
            ((hasDerivAt_id z).add_const (τ / 2)) using 1
      simp
  convert hexp.mul hshift using 1
  simp [jacobiTheta2Prime]
  ring

theorem hasDerivAt_jacobiTheta1
    (z τ : ℂ) (hτ : 0 < τ.im) :
    HasDerivAt (fun w ↦ jacobiTheta1 w τ)
      (jacobiTheta1Prime z τ) z := by
  convert
    ((hasDerivAt_jacobiTheta2
      (z + 1 / 2) τ hτ).comp z
        ((hasDerivAt_id z).add_const (1 / 2))).neg using 1
  simp [jacobiTheta1Prime]

/-- The displayed vector is the complex derivative of the four-theta
vector in the elliptic variable. -/
theorem hasDerivAt_jacobiThetaVector
    (z τ : ℂ) (hτ : 0 < τ.im) :
    HasDerivAt (fun w ↦ jacobiThetaVector w τ)
      (jacobiThetaVectorPrime z τ) z := by
  rw [hasDerivAt_pi]
  intro k
  fin_cases k
  · simpa only [jacobiThetaVector, jacobiThetaVectorPrime,
      Matrix.cons_val_zero] using
      hasDerivAt_jacobiTheta1 z τ hτ
  · simpa only [jacobiThetaVector, jacobiThetaVectorPrime,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      hasDerivAt_jacobiTheta2 z τ hτ
  · simpa only [jacobiThetaVector, jacobiThetaVectorPrime,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      hasDerivAt_jacobiTheta3 z τ hτ
  · simpa only [jacobiThetaVector, jacobiThetaVectorPrime,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      hasDerivAt_jacobiTheta4 z τ hτ

/-! ## The exact Wronskian input and projective immersion -/

/-- Pointwise form of the three derivative identities in (8.5), before
division by `θ₁²`. -/
def JacobiThetaWronskiansAt
    (p2 p3 p4 : ℂ) (T Tξ : Fin 4 → ℂ) : Prop :=
  Tξ 1 * T 0 - T 1 * Tξ 0 =
      -π * p2 * T 2 * T 3 ∧
    Tξ 2 * T 0 - T 2 * Tξ 0 =
      -π * p3 * T 3 * T 1 ∧
    Tξ 3 * T 0 - T 3 * Tξ 0 =
      -π * p4 * T 1 * T 2

/-- On a nonzero smooth residual point, no two of the three even
coordinates can vanish simultaneously. -/
theorem jacobiResidual_no_two_even_zero
    {p2 p3 p4 : ℂ}
    (hp : p2 * p3 * p4 ≠ 0)
    (hJacobi : p3 ^ 2 = p2 ^ 2 + p4 ^ 2)
    {T : Fin 4 → ℂ}
    (hT : T ≠ 0)
    (hQ1 : jacobiResidualQ1 p2 p3 p4 T = 0)
    (hQ2 : jacobiResidualQ2 p2 p3 p4 T = 0) :
    ¬ (T 1 = 0 ∧ T 2 = 0) ∧
      ¬ (T 1 = 0 ∧ T 3 = 0) ∧
        ¬ (T 2 = 0 ∧ T 3 = 0) := by
  change
    p2 * T 3 ^ 2 - p4 * T 1 ^ 2 -
      p3 * T 0 ^ 2 = 0 at hQ1
  change
    p2 * T 2 ^ 2 - p3 * T 1 ^ 2 -
      p4 * T 0 ^ 2 = 0 at hQ2
  have hp2 : p2 ≠ 0 := by
    intro h
    apply hp
    simp [h]
  have hp3 : p3 ≠ 0 := by
    intro h
    apply hp
    simp [h]
  have hp4 : p4 ≠ 0 := by
    intro h
    apply hp
    simp [h]
  constructor
  · rintro ⟨h1, h2⟩
    have h0 : T 0 = 0 := by
      simp [h1, h2] at hQ2
      exact hQ2.resolve_left hp4
    have h3 : T 3 = 0 := by
      simp [h0, h1] at hQ1
      exact hQ1.resolve_left hp2
    apply hT
    funext k
    fin_cases k <;> assumption
  constructor
  · rintro ⟨h1, h3⟩
    have h0 : T 0 = 0 := by
      simp [h1, h3] at hQ1
      exact hQ1.resolve_left hp3
    have h2 : T 2 = 0 := by
      simp [h0, h1] at hQ2
      exact hQ2.resolve_left hp2
    apply hT
    funext k
    fin_cases k <;> assumption
  · rintro ⟨h2, h3⟩
    have hs1 :
        p4 * T 1 ^ 2 + p3 * T 0 ^ 2 = 0 := by
      simp [h3] at hQ1
      linear_combination -hQ1
    have hs2 :
        p3 * T 1 ^ 2 + p4 * T 0 ^ 2 = 0 := by
      simp [h2] at hQ2
      linear_combination -hQ2
    have h1sq : T 1 ^ 2 = 0 := by
      have hdet : p3 ^ 2 - p4 ^ 2 = p2 ^ 2 := by
        rw [hJacobi]
        ring
      have hprod :
          p2 ^ 2 * T 1 ^ 2 = 0 := by
        rw [← hdet]
        linear_combination p3 * hs2 - p4 * hs1
      exact
        (mul_eq_zero.mp hprod).resolve_left
          (pow_ne_zero 2 hp2)
    have h1 : T 1 = 0 := sq_eq_zero_iff.mp h1sq
    have h0 : T 0 = 0 := by
      rw [h1, zero_pow (by norm_num), mul_zero,
        zero_add] at hs1
      exact sq_eq_zero_iff.mp
        ((mul_eq_zero.mp hs1).resolve_left hp3)
    apply hT
    funext k
    fin_cases k <;> assumption

/-- The Wronskian identities force the derivative out of the radial
direction, so the two vectors are linearly independent. -/
theorem linearIndependent_theta_and_derivative_of_wronskians
    {p2 p3 p4 : ℂ}
    (hp : p2 * p3 * p4 ≠ 0)
    (hJacobi : p3 ^ 2 = p2 ^ 2 + p4 ^ 2)
    {T Tξ : Fin 4 → ℂ}
    (hT : T ≠ 0)
    (hQ1 : jacobiResidualQ1 p2 p3 p4 T = 0)
    (hQ2 : jacobiResidualQ2 p2 p3 p4 T = 0)
    (hW : JacobiThetaWronskiansAt p2 p3 p4 T Tξ) :
    LinearIndependent ℂ ![T, Tξ] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hcoord (k : Fin 4) :
      a * T k + b * Tξ k = 0 := by
    have h := congrFun hab k
    simpa only [Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply] using h
  by_cases hb : b = 0
  · have haT : a • T = 0 := by
      funext k
      simpa only [Pi.smul_apply, smul_eq_mul, hb,
        zero_mul, add_zero] using hcoord k
    have ha : a = 0 := by
      exact (smul_eq_zero.mp haT).resolve_right hT
    exact ⟨ha, hb⟩
  have hno :=
    jacobiResidual_no_two_even_zero
      hp hJacobi hT hQ1 hQ2
  have hwronskian_zero (k : Fin 4) :
      Tξ k * T 0 - T k * Tξ 0 = 0 := by
    have hk := hcoord k
    have h0 := hcoord 0
    calc
      Tξ k * T 0 - T k * Tξ 0 =
          b⁻¹ *
            (b * Tξ k * T 0 -
              T k * (b * Tξ 0)) := by
                field_simp [hb]
      _ = b⁻¹ *
          ((-a * T k) * T 0 -
            T k * (-a * T 0)) := by
              rw [show b * Tξ k = -a * T k by
                    linear_combination hk,
                show b * Tξ 0 = -a * T 0 by
                    linear_combination h0]
      _ = 0 := by ring
  rcases hW with ⟨hW2, hW3, hW4⟩
  have hprod2 : T 2 * T 3 = 0 := by
    rw [hwronskian_zero 1] at hW2
    have hcoeff : -π * p2 ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr (ofReal_ne_zero.mpr pi_ne_zero))
        (by
          intro h
          apply hp
          simp [h])
    exact
      (mul_eq_zero.mp
        (show (-π * p2) * (T 2 * T 3) = 0 by
          linear_combination -hW2)).resolve_left hcoeff
  have hprod3 : T 3 * T 1 = 0 := by
    rw [hwronskian_zero 2] at hW3
    have hcoeff : -π * p3 ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr (ofReal_ne_zero.mpr pi_ne_zero))
        (by
          intro h
          apply hp
          simp [h])
    exact
      (mul_eq_zero.mp
        (show (-π * p3) * (T 3 * T 1) = 0 by
          linear_combination -hW3)).resolve_left hcoeff
  have hprod4 : T 1 * T 2 = 0 := by
    rw [hwronskian_zero 3] at hW4
    have hcoeff : -π * p4 ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr (ofReal_ne_zero.mpr pi_ne_zero))
        (by
          intro h
          apply hp
          simp [h])
    exact
      (mul_eq_zero.mp
        (show (-π * p4) * (T 1 * T 2) = 0 by
          linear_combination -hW4)).resolve_left hcoeff
  rcases mul_eq_zero.mp hprod2 with h2 | h3
  · rcases mul_eq_zero.mp hprod3 with h3 | h1
    · exact (hno.2.2 ⟨h2, h3⟩).elim
    · exact (hno.1 ⟨h1, h2⟩).elim
  · rcases mul_eq_zero.mp hprod4 with h1 | h2
    · exact (hno.2.1 ⟨h1, h3⟩).elim
    · exact (hno.2.2 ⟨h2, h3⟩).elim

/-! ### Canonical specialization and the ratio formulas -/

/-- The three missing analytic identities specialized to the canonical
theta vector and its actual derivative. -/
def CanonicalJacobiThetaWronskiansAt
    (z : ℂ) (τ : ℍ) : Prop :=
  JacobiThetaWronskiansAt
    (canonicalUnaryRoots τ).p2
    (canonicalUnaryRoots τ).p3
    (canonicalUnaryRoots τ).p4
    (jacobiThetaVector z (τ : ℂ))
    (jacobiThetaVectorPrime z (τ : ℂ))

/-- Once the three canonical Wronskian identities are supplied, the
projective theta map is immersive at that point. -/
theorem canonical_linearIndependent_theta_and_derivative
    (z : ℂ) (τ : ℍ)
    (hW : CanonicalJacobiThetaWronskiansAt z τ) :
    LinearIndependent ℂ
      ![jacobiThetaVector z (τ : ℂ),
        jacobiThetaVectorPrime z (τ : ℂ)] := by
  exact
    linearIndependent_theta_and_derivative_of_wronskians
      (canonicalUnaryRoots_p_product_ne_zero τ)
      (canonicalUnaryRoots_p3_sq_eq τ)
      (jacobiThetaVector_ne_zero z τ)
      (canonical_jacobiResidualQ1_jacobiThetaVector z τ)
      (canonical_jacobiResidualQ2_jacobiThetaVector z τ)
      hW

/-- Equation (8.5) for `θ₂/θ₁`, obtained from the first Wronskian
identity by the quotient rule. -/
theorem hasDerivAt_jacobiTheta2_div_jacobiTheta1
    (z : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0)
    (hW : CanonicalJacobiThetaWronskiansAt z τ) :
    HasDerivAt
      (fun w ↦
        jacobiTheta2 w (τ : ℂ) /
          jacobiTheta1 w (τ : ℂ))
      (-π * (canonicalUnaryRoots τ).p2 *
          jacobiTheta3 z (τ : ℂ) *
          jacobiTheta4 z (τ : ℂ) /
        jacobiTheta1 z (τ : ℂ) ^ 2) z := by
  have hquot :=
    (hasDerivAt_jacobiTheta2 z τ τ.im_pos).div
      (hasDerivAt_jacobiTheta1 z τ τ.im_pos) h1
  apply hquot.congr_deriv
  change
    (jacobiThetaVectorPrime z (τ : ℂ) 1 *
          jacobiThetaVector z (τ : ℂ) 0 -
        jacobiThetaVector z (τ : ℂ) 1 *
          jacobiThetaVectorPrime z (τ : ℂ) 0) /
        jacobiThetaVector z (τ : ℂ) 0 ^ 2 =
      _
  rw [hW.1]
  rfl

/-- Equation (8.5) for `θ₃/θ₁`. -/
theorem hasDerivAt_jacobiTheta3_div_jacobiTheta1
    (z : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0)
    (hW : CanonicalJacobiThetaWronskiansAt z τ) :
    HasDerivAt
      (fun w ↦
        jacobiTheta3 w (τ : ℂ) /
          jacobiTheta1 w (τ : ℂ))
      (-π * (canonicalUnaryRoots τ).p3 *
          jacobiTheta4 z (τ : ℂ) *
          jacobiTheta2 z (τ : ℂ) /
        jacobiTheta1 z (τ : ℂ) ^ 2) z := by
  have hquot :=
    (hasDerivAt_jacobiTheta3 z τ τ.im_pos).div
      (hasDerivAt_jacobiTheta1 z τ τ.im_pos) h1
  apply hquot.congr_deriv
  change
    (jacobiThetaVectorPrime z (τ : ℂ) 2 *
          jacobiThetaVector z (τ : ℂ) 0 -
        jacobiThetaVector z (τ : ℂ) 2 *
          jacobiThetaVectorPrime z (τ : ℂ) 0) /
        jacobiThetaVector z (τ : ℂ) 0 ^ 2 =
      _
  rw [hW.2.1]
  rfl

/-- Equation (8.5) for `θ₄/θ₁`. -/
theorem hasDerivAt_jacobiTheta4_div_jacobiTheta1
    (z : ℂ) (τ : ℍ)
    (h1 : jacobiTheta1 z (τ : ℂ) ≠ 0)
    (hW : CanonicalJacobiThetaWronskiansAt z τ) :
    HasDerivAt
      (fun w ↦
        jacobiTheta4 w (τ : ℂ) /
          jacobiTheta1 w (τ : ℂ))
      (-π * (canonicalUnaryRoots τ).p4 *
          jacobiTheta2 z (τ : ℂ) *
          jacobiTheta3 z (τ : ℂ) /
        jacobiTheta1 z (τ : ℂ) ^ 2) z := by
  have hquot :=
    (hasDerivAt_jacobiTheta4 z τ τ.im_pos).div
      (hasDerivAt_jacobiTheta1 z τ τ.im_pos) h1
  apply hquot.congr_deriv
  change
    (jacobiThetaVectorPrime z (τ : ℂ) 3 *
          jacobiThetaVector z (τ : ℂ) 0 -
        jacobiThetaVector z (τ : ℂ) 3 *
          jacobiThetaVectorPrime z (τ : ℂ) 0) /
        jacobiThetaVector z (τ : ℂ) 0 ^ 2 =
      _
  rw [hW.2.2]
  rfl

/-! ## A reusable rank-three initial-value linearization -/

/-- Linearization of the five-coordinate initial-value map.  The scalar
`A` is the value of its last coordinate divided by `S`, and `B` is the
elliptic derivative of that expression.  Their exact formulas are
irrelevant to injectivity: the first four coordinates determine the scale
and projective displacement, after which the last coordinate determines
the Bloch slope. -/
def jacobiInitialValueLinearization
    (S A B : ℂ) (T Tξ : Fin 4 → ℂ) :
    (ℂ × ℂ × ℂ) →ₗ[ℂ] ((Fin 4 → ℂ) × ℂ) where
  toFun v :=
    (fun k ↦
      v.1 * T k + S * v.2.1 * Tξ k,
      v.1 * A + S * v.2.1 * B +
        S * v.2.2 * T 0)
  map_add' v w := by
    ext k
    · simp only [Prod.fst_add, Prod.snd_add,
        Pi.add_apply]
      ring
    · simp only [Prod.fst_add, Prod.snd_add]
      ring
  map_smul' c v := by
    ext k
    · simp only [Prod.smul_fst, Prod.smul_snd,
        Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · simp only [Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul, RingHom.id_apply]
      ring

/-- Independence of scale and elliptic displacement, together with
`Sθ₁≠0`, makes the initial-value linearization injective. -/
theorem jacobiInitialValueLinearization_injective
    {S A B : ℂ} {T Tξ : Fin 4 → ℂ}
    (hS : S ≠ 0)
    (hT1 : T 0 ≠ 0)
    (hLI : LinearIndependent ℂ ![T, Tξ]) :
    Function.Injective
      (jacobiInitialValueLinearization S A B T Tξ) := by
  rw [← LinearMap.ker_eq_bot]
  apply (Submodule.eq_bot_iff _).mpr
  rintro ⟨dS, dξ, dL⟩ h
  change
    jacobiInitialValueLinearization S A B T Tξ
      (dS, dξ, dL) = 0 at h
  have hfirst :
      (fun k ↦
        dS * T k + S * dξ * Tξ k) = 0 :=
    congrArg Prod.fst h
  have hlin :
      dS • T + (S * dξ) • Tξ = 0 := by
    funext k
    simpa only [Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] using congrFun hfirst k
  have hcoeff :=
    LinearIndependent.pair_iff.mp hLI
      dS (S * dξ) hlin
  have hdξ : dξ = 0 :=
    (mul_eq_zero.mp hcoeff.2).resolve_left hS
  have hlast :
      dS * A + S * dξ * B + S * dL * T 0 = 0 := by
    have := congrArg Prod.snd h
    simpa only [jacobiInitialValueLinearization,
      Prod.snd_zero] using this
  have hdL : dL = 0 := by
    simp only [hcoeff.1, hdξ, zero_mul, mul_zero,
      zero_add] at hlast
    have hSdL : S * dL = 0 :=
      (mul_eq_zero.mp hlast).resolve_right hT1
    exact (mul_eq_zero.mp hSdL).resolve_left hS
  ext <;> simp [hcoeff.1, hdξ, hdL]

/-- The complex rank of the initial-value linearization is exactly three. -/
theorem jacobiInitialValueLinearization_range_finrank
    {S A B : ℂ} {T Tξ : Fin 4 → ℂ}
    (hS : S ≠ 0)
    (hT1 : T 0 ≠ 0)
    (hLI : LinearIndependent ℂ ![T, Tξ]) :
    Module.finrank ℂ
      (jacobiInitialValueLinearization S A B T Tξ).range =
      3 := by
  let f :=
    jacobiInitialValueLinearization S A B T Tξ
  have hinj : Function.Injective f :=
    jacobiInitialValueLinearization_injective
      hS hT1 hLI
  have hrank :=
    LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.ker_eq_bot.mpr hinj,
    finrank_bot, add_zero] at hrank
  simpa only [f, Module.finrank_prod,
    Module.finrank_self, Nat.reduceAdd] using hrank

/-- Canonical theta specialization of the rank-three statement. -/
theorem canonical_jacobiInitialValueLinearization_range_finrank
    {S A B : ℂ} (z : ℂ) (τ : ℍ)
    (hS : S ≠ 0)
    (hT1 : jacobiTheta1 z (τ : ℂ) ≠ 0)
    (hW : CanonicalJacobiThetaWronskiansAt z τ) :
    Module.finrank ℂ
      (jacobiInitialValueLinearization S A B
        (jacobiThetaVector z (τ : ℂ))
        (jacobiThetaVectorPrime z (τ : ℂ))).range =
      3 := by
  exact jacobiInitialValueLinearization_range_finrank
    hS hT1
    (canonical_linearIndependent_theta_and_derivative
      z τ hW)

end

end HGAS.Modular
