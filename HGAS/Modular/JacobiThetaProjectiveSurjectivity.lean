import HGAS.Modular.JacobiThetaProjectiveLine
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Tactic

/-!
# Global projective surjectivity of the four-theta map

Fix `τ ∈ ℍ` and the two diagonal residual quadrics `Q₁,Q₂`.  This file
proves that every nonzero common zero of these quadrics is, up to one
common nonzero scalar, a value of

```
        z ↦ (θ₁(z), θ₂(z), θ₃(z), θ₄(z)).
```

The global argument is deliberately elementary.

1. `JacobiThetaProjectiveLine` proves that `[θ₁:θ₂]` covers `ℂP¹`.
2. After matching those two coordinates, the residual equations force
   the squares of the remaining coordinates to match.
3. The symmetries `z ↦ z+1` and `z ↦ τ-z` realize all four independent
   sign choices.

Thus no connectedness theorem for a projective `(2,2)` complete
intersection is needed.  The result is also independent of the Jacobi
Wronskian formulas; those formulas control immersion and initial-value
rank, not set-theoretic saturation.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real

noncomputable section

/-! ## Parity and the two sign-changing deck symmetries -/

theorem jacobiTheta3_neg
    (z τ : ℂ) :
    jacobiTheta3 (-z) τ =
      jacobiTheta3 z τ := by
  exact jacobiTheta₂_neg_left z τ

theorem jacobiTheta2_neg
    (z τ : ℂ) :
    jacobiTheta2 (-z) τ =
      jacobiTheta2 z τ := by
  rw [jacobiTheta2, jacobiTheta2]
  have heven :
      jacobiTheta₂ (-z + τ / 2) τ =
        jacobiTheta₂ (z - τ / 2) τ := by
    calc
      jacobiTheta₂ (-z + τ / 2) τ =
          jacobiTheta₂ (-(-z + τ / 2)) τ :=
        (jacobiTheta₂_neg_left
          (-z + τ / 2) τ).symm
      _ = jacobiTheta₂ (z - τ / 2) τ := by
        congr 2
        ring
  have hshiftRaw :=
    jacobiTheta₂_add_int_lattice
      (z + τ / 2) τ 0 (-1)
  norm_num at hshiftRaw
  have hshift :
      jacobiTheta₂ (z - τ / 2) τ =
        cexp (2 * π * I * z) *
          jacobiTheta₂ (z + τ / 2) τ := by
    calc
      jacobiTheta₂ (z - τ / 2) τ =
          jacobiTheta₂
            (z + τ / 2 + -τ) τ := by
        rw [show z - τ / 2 =
          z + τ / 2 + -τ by ring]
      _ =
          cexp
              (-(π * I * τ) +
                2 * π * I * (z + τ / 2)) *
            jacobiTheta₂ (z + τ / 2) τ :=
        hshiftRaw
      _ =
          cexp (2 * π * I * z) *
            jacobiTheta₂ (z + τ / 2) τ := by
        congr 2
        ring
  rw [heven, hshift, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem jacobiTheta4_neg
    (z τ : ℂ) :
    jacobiTheta4 (-z) τ =
      jacobiTheta4 z τ := by
  rw [jacobiTheta4, jacobiTheta4]
  calc
    jacobiTheta₂ (-z + 1 / 2) τ =
        jacobiTheta₂ (z - 1 / 2) τ := by
      calc
        jacobiTheta₂ (-z + 1 / 2) τ =
            jacobiTheta₂ (-(-z + 1 / 2)) τ :=
          (jacobiTheta₂_neg_left
            (-z + 1 / 2) τ).symm
        _ = _ := by
          congr 2
          ring
    _ = jacobiTheta₂ (z + 1 / 2) τ := by
      have h :=
        jacobiTheta3_add_one
          (z - 1 / 2) τ
      simpa only [jacobiTheta3,
        show z - 1 / 2 + 1 = z + 1 / 2 by ring] using
          h.symm

theorem jacobiTheta1_neg
    (z τ : ℂ) :
    jacobiTheta1 (-z) τ =
      -jacobiTheta1 z τ := by
  rw [jacobiTheta1, jacobiTheta1,
    show -z + 1 / 2 =
      -(z - 1 / 2) by ring,
    jacobiTheta2_neg]
  have h :=
    jacobiTheta2_add_one
      (z - 1 / 2) τ
  rw [show z - 1 / 2 + 1 =
      z + 1 / 2 by ring] at h
  rw [h]
  ring

theorem jacobiTheta1_add_one
    (z τ : ℂ) :
    jacobiTheta1 (z + 1) τ =
      -jacobiTheta1 z τ := by
  rw [jacobiTheta1, jacobiTheta1,
    show z + 1 + 1 / 2 =
      (z + 1 / 2) + 1 by ring,
    jacobiTheta2_add_one]

theorem jacobiTheta4_add_one
    (z τ : ℂ) :
    jacobiTheta4 (z + 1) τ =
      jacobiTheta4 z τ := by
  rw [jacobiTheta4, jacobiTheta4,
    show z + 1 + 1 / 2 =
      (z + 1 / 2) + 1 by ring]
  simpa only [jacobiTheta3] using
    jacobiTheta3_add_one (z + 1 / 2) τ

/-- Reflection across `τ/2` fixes the first three projective signs and
flips only `θ₄`, before removal of one common nonzero multiplier. -/
theorem jacobiTheta1_tau_sub
    (z τ : ℂ) :
    jacobiTheta1 (τ - z) τ =
      thetaTauMultiplier (-z) τ *
        jacobiTheta1 z τ := by
  calc
    jacobiTheta1 (τ - z) τ =
        jacobiTheta1 (-z + τ) τ := by
      congr 2
      ring
    _ =
        -thetaTauMultiplier (-z) τ *
          jacobiTheta1 (-z) τ :=
      jacobiTheta1_add_tau (-z) τ
    _ = _ := by
      rw [jacobiTheta1_neg]
      ring

theorem jacobiTheta2_tau_sub
    (z τ : ℂ) :
    jacobiTheta2 (τ - z) τ =
      thetaTauMultiplier (-z) τ *
        jacobiTheta2 z τ := by
  calc
    jacobiTheta2 (τ - z) τ =
        jacobiTheta2 (-z + τ) τ := by
      congr 2
      ring
    _ =
        thetaTauMultiplier (-z) τ *
          jacobiTheta2 (-z) τ :=
      jacobiTheta2_add_tau (-z) τ
    _ = _ := by
      rw [jacobiTheta2_neg]

theorem jacobiTheta3_tau_sub
    (z τ : ℂ) :
    jacobiTheta3 (τ - z) τ =
      thetaTauMultiplier (-z) τ *
        jacobiTheta3 z τ := by
  calc
    jacobiTheta3 (τ - z) τ =
        jacobiTheta3 (-z + τ) τ := by
      congr 2
      ring
    _ =
        thetaTauMultiplier (-z) τ *
          jacobiTheta3 (-z) τ :=
      jacobiTheta3_add_tau (-z) τ
    _ = _ := by
      rw [jacobiTheta3_neg]

theorem jacobiTheta4_tau_sub
    (z τ : ℂ) :
    jacobiTheta4 (τ - z) τ =
      -thetaTauMultiplier (-z) τ *
        jacobiTheta4 z τ := by
  calc
    jacobiTheta4 (τ - z) τ =
        jacobiTheta4 (-z + τ) τ := by
      congr 2
      ring
    _ =
        -thetaTauMultiplier (-z) τ *
          jacobiTheta4 (-z) τ :=
      jacobiTheta4_add_tau (-z) τ
    _ = _ := by
      rw [jacobiTheta4_neg]

/-! ## Affine-up-to-scale saturation -/

/-- Every nonzero residual representative is a common nonzero scalar
multiple of one four-theta value.  This is the strongest convenient
affine formulation of projective saturation. -/
theorem exists_smul_jacobiThetaVector_eq_of_residual
    (τ : ℍ) (X : Fin 4 → ℂ)
    (hX : X ≠ 0)
    (hQ1 :
      jacobiResidualQ1
        (canonicalUnaryRoots τ).p2
        (canonicalUnaryRoots τ).p3
        (canonicalUnaryRoots τ).p4 X = 0)
    (hQ2 :
      jacobiResidualQ2
        (canonicalUnaryRoots τ).p2
        (canonicalUnaryRoots τ).p3
        (canonicalUnaryRoots τ).p4 X = 0) :
    ∃ z c : ℂ, c ≠ 0 ∧
      c • jacobiThetaVector z (τ : ℂ) = X := by
  let p2 := (canonicalUnaryRoots τ).p2
  let p3 := (canonicalUnaryRoots τ).p3
  let p4 := (canonicalUnaryRoots τ).p4
  have hp :=
    canonicalUnaryRoots_p_product_ne_zero τ
  have hp2 : p2 ≠ 0 := by
    intro hp2
    apply hp
    change p2 * p3 * p4 = 0
    rw [hp2, zero_mul]
    exact zero_mul _
  have hX01 : (X 0, X 1) ≠ 0 := by
    intro hpair
    have h0 : X 0 = 0 :=
      congrArg Prod.fst hpair
    have h1 : X 1 = 0 :=
      congrArg Prod.snd hpair
    have h2 : X 2 = 0 := by
      change
        p2 * X 2 ^ 2 -
            p3 * X 1 ^ 2 -
          p4 * X 0 ^ 2 = 0 at hQ2
      simp only [h0, h1,
        zero_pow (by norm_num : 2 ≠ 0),
        mul_zero, sub_zero] at hQ2
      exact
        sq_eq_zero_iff.mp
          ((mul_eq_zero.mp hQ2).resolve_left hp2)
    have h3 : X 3 = 0 := by
      change
        p2 * X 3 ^ 2 -
            p4 * X 1 ^ 2 -
          p3 * X 0 ^ 2 = 0 at hQ1
      simp only [h0, h1,
        zero_pow (by norm_num : 2 ≠ 0),
        mul_zero, sub_zero] at hQ1
      exact
        sq_eq_zero_iff.mp
          ((mul_eq_zero.mp hQ1).resolve_left hp2)
    apply hX
    funext k
    fin_cases k <;> assumption
  let target : ComplexProjectivePair :=
    ⟨(X 0, X 1), hX01⟩
  obtain ⟨z, hz⟩ :=
    jacobiTheta12Projective_surjective τ
      (complexProjectiveRatio target)
  let source : ComplexProjectivePair :=
    complexProjectivePairMap
      (fun w => jacobiTheta1 w (τ : ℂ))
      (fun w => jacobiTheta2 w (τ : ℂ))
      (fun w => jacobiTheta12_pair_ne_zero w τ) z
  have hz' :
      complexProjectiveRatio source =
        complexProjectiveRatio target := by
    exact hz
  obtain ⟨c, hc, hc0, hc1⟩ :=
    exists_common_scale_of_complexProjectiveRatio_eq
      source target hz'
  change
    c * jacobiTheta1 z (τ : ℂ) = X 0 at hc0
  change
    c * jacobiTheta2 z (τ : ℂ) = X 1 at hc1
  let T := jacobiThetaVector z (τ : ℂ)
  have hT0 : c * T 0 = X 0 := by
    simpa only [T, jacobiThetaVector,
      Matrix.cons_val_zero] using hc0
  have hT1 : c * T 1 = X 1 := by
    simpa only [T, jacobiThetaVector,
      Matrix.cons_val_one, Matrix.cons_val_zero] using hc1
  have hQT1 :=
    canonical_jacobiResidualQ1_jacobiThetaVector z τ
  have hQT2 :=
    canonical_jacobiResidualQ2_jacobiThetaVector z τ
  change
    p2 * T 3 ^ 2 -
        p4 * T 1 ^ 2 -
      p3 * T 0 ^ 2 = 0 at hQT1
  change
    p2 * T 2 ^ 2 -
        p3 * T 1 ^ 2 -
      p4 * T 0 ^ 2 = 0 at hQT2
  change
    p2 * X 3 ^ 2 -
        p4 * X 1 ^ 2 -
      p3 * X 0 ^ 2 = 0 at hQ1
  change
    p2 * X 2 ^ 2 -
        p3 * X 1 ^ 2 -
      p4 * X 0 ^ 2 = 0 at hQ2
  have hQ1' := hQ1
  have hQ2' := hQ2
  rw [← hT0, ← hT1] at hQ1' hQ2'
  have hm2 :
      p2 * (X 2 ^ 2 - (c * T 2) ^ 2) = 0 := by
    linear_combination hQ2' - c ^ 2 * hQT2
  have hm3 :
      p2 * (X 3 ^ 2 - (c * T 3) ^ 2) = 0 := by
    linear_combination hQ1' - c ^ 2 * hQT1
  have hs2 :
      X 2 ^ 2 = (c * T 2) ^ 2 := by
    exact sub_eq_zero.mp
      ((mul_eq_zero.mp hm2).resolve_left hp2)
  have hs3 :
      X 3 ^ 2 = (c * T 3) ^ 2 := by
    exact sub_eq_zero.mp
      ((mul_eq_zero.mp hm3).resolve_left hp2)
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hs2) with h2 | h2
  · rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hs3) with h3 | h3
    · change
        X 2 =
          c * jacobiTheta3 z (τ : ℂ) at h2
      change
        X 3 =
          c * jacobiTheta4 z (τ : ℂ) at h3
      refine ⟨z, c, hc, ?_⟩
      funext k
      fin_cases k
      · change
          c * jacobiTheta1 z (τ : ℂ) = X 0
        exact hc0
      · change
          c * jacobiTheta2 z (τ : ℂ) = X 1
        exact hc1
      · change
          c * jacobiTheta3 z (τ : ℂ) = X 2
        exact h2.symm
      · change
          c * jacobiTheta4 z (τ : ℂ) = X 3
        exact h3.symm
    · change
        X 2 =
          c * jacobiTheta3 z (τ : ℂ) at h2
      change
        X 3 =
          -(c * jacobiTheta4 z (τ : ℂ)) at h3
      let a := thetaTauMultiplier (-z) (τ : ℂ)
      have ha : a ≠ 0 :=
        thetaTauMultiplier_ne_zero (-z) (τ : ℂ)
      refine ⟨τ - z, c / a,
        div_ne_zero hc
          ha, ?_⟩
      have hca : (c / a) * a = c :=
        div_mul_cancel₀ c ha
      have hmul (u : ℂ) :
          (c / a) * (a * u) = c * u := by
        rw [← mul_assoc, hca]
      have hmulNeg (u : ℂ) :
          (c / a) * (-a * u) =
            -(c * u) := by
        calc
          (c / a) * (-a * u) =
              -((c / a) * (a * u)) := by ring
          _ = _ := by rw [hmul]
      funext k
      fin_cases k
      · change
          (c / a) *
              jacobiTheta1 (τ - z) (τ : ℂ) =
            X 0
        rw [jacobiTheta1_tau_sub, hmul]
        exact hc0
      · change
          (c / a) *
              jacobiTheta2 (τ - z) (τ : ℂ) =
            X 1
        rw [jacobiTheta2_tau_sub, hmul]
        exact hc1
      · change
          (c / a) *
              jacobiTheta3 (τ - z) (τ : ℂ) =
            X 2
        rw [jacobiTheta3_tau_sub, hmul]
        exact h2.symm
      · change
          (c / a) *
              jacobiTheta4 (τ - z) (τ : ℂ) =
            X 3
        rw [jacobiTheta4_tau_sub, hmulNeg]
        exact h3.symm
  · rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hs3) with h3 | h3
    · change
        X 2 =
          -(c * jacobiTheta3 z (τ : ℂ)) at h2
      change
        X 3 =
          c * jacobiTheta4 z (τ : ℂ) at h3
      let a := thetaTauMultiplier (-z) (τ : ℂ)
      have ha : a ≠ 0 :=
        thetaTauMultiplier_ne_zero (-z) (τ : ℂ)
      refine
        ⟨(τ - z) + 1, -(c / a),
          neg_ne_zero.mpr (div_ne_zero hc ha), ?_⟩
      have hca : (c / a) * a = c :=
        div_mul_cancel₀ c ha
      have hminusPlus (u : ℂ) :
          -(c / a) * (a * u) =
            -(c * u) := by
        calc
          -(c / a) * (a * u) =
              -((c / a) * a) * u := by ring
          _ = _ := by
            rw [hca]
            ring
      have hminusMinus (u : ℂ) :
          -(c / a) * (-(a * u)) =
            c * u := by
        calc
          -(c / a) * (-(a * u)) =
              ((c / a) * a) * u := by ring
          _ = _ := by rw [hca]
      funext k
      fin_cases k
      · change
          -(c / a) *
              jacobiTheta1 ((τ - z) + 1) (τ : ℂ) =
            X 0
        rw [jacobiTheta1_add_one,
          jacobiTheta1_tau_sub, hminusMinus]
        exact hc0
      · change
          -(c / a) *
              jacobiTheta2 ((τ - z) + 1) (τ : ℂ) =
            X 1
        rw [jacobiTheta2_add_one,
          jacobiTheta2_tau_sub, hminusMinus]
        exact hc1
      · change
          -(c / a) *
              jacobiTheta3 ((τ - z) + 1) (τ : ℂ) =
            X 2
        rw [jacobiTheta3_add_one,
          jacobiTheta3_tau_sub, hminusPlus]
        exact h2.symm
      · change
          -(c / a) *
              jacobiTheta4 ((τ - z) + 1) (τ : ℂ) =
            X 3
        rw [jacobiTheta4_add_one,
          jacobiTheta4_tau_sub]
        calc
          -(c / a) *
                (-a * jacobiTheta4 z (τ : ℂ)) =
              c * jacobiTheta4 z (τ : ℂ) := by
            convert
              hminusMinus
                (jacobiTheta4 z (τ : ℂ))
              using 1
            ring
          _ = X 3 := h3.symm
    · change
        X 2 =
          -(c * jacobiTheta3 z (τ : ℂ)) at h2
      change
        X 3 =
          -(c * jacobiTheta4 z (τ : ℂ)) at h3
      refine ⟨z + 1, -c, neg_ne_zero.mpr hc, ?_⟩
      funext k
      fin_cases k
      · change
          -c * jacobiTheta1 (z + 1) (τ : ℂ) =
            X 0
        rw [jacobiTheta1_add_one]
        convert hc0 using 1
        ring
      · change
          -c * jacobiTheta2 (z + 1) (τ : ℂ) =
            X 1
        rw [jacobiTheta2_add_one]
        convert hc1 using 1
        ring
      · change
          -c * jacobiTheta3 (z + 1) (τ : ℂ) =
            X 2
        rw [jacobiTheta3_add_one]
        convert h2.symm using 1
        ring
      · change
          -c * jacobiTheta4 (z + 1) (τ : ℂ) =
            X 3
        rw [jacobiTheta4_add_one]
        convert h3.symm using 1
        ring

/-! ## Projective formulation -/

/-- The first residual is homogeneous of degree two. -/
theorem jacobiResidualQ1_smul
    (c p2 p3 p4 : ℂ) (X : Fin 4 → ℂ) :
    jacobiResidualQ1 p2 p3 p4 (c • X) =
      c ^ 2 * jacobiResidualQ1 p2 p3 p4 X := by
  simp only [jacobiResidualQ1, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- The second residual is homogeneous of degree two. -/
theorem jacobiResidualQ2_smul
    (c p2 p3 p4 : ℂ) (X : Fin 4 → ℂ) :
    jacobiResidualQ2 p2 p3 p4 (c • X) =
      c ^ 2 * jacobiResidualQ2 p2 p3 p4 X := by
  simp only [jacobiResidualQ2, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- The projective point represented by the four Jacobi theta
coordinates.  Nonvanishing of the complete vector is a theorem, not a
side condition imposed on `z`. -/
def projectiveJacobiTheta
    (z : ℂ) (τ : ℍ) :
    Projectivization ℂ (Fin 4 → ℂ) :=
  Projectivization.mk ℂ
    (jacobiThetaVector z (τ : ℂ))
    (jacobiThetaVector_ne_zero z τ)

/-- The projective complete intersection cut out by the two canonical
Jacobi residual quadrics.  The existential representative formulation
makes the homogeneous nature of the definition explicit and is useful
for elimination arguments. -/
def jacobiResidualProjectiveCurve
    (τ : ℍ) :
    Set (Projectivization ℂ (Fin 4 → ℂ)) :=
  {P | ∃ (X : Fin 4 → ℂ) (hX : X ≠ 0),
    jacobiResidualQ1
        (canonicalUnaryRoots τ).p2
        (canonicalUnaryRoots τ).p3
        (canonicalUnaryRoots τ).p4 X = 0 ∧
      jacobiResidualQ2
        (canonicalUnaryRoots τ).p2
        (canonicalUnaryRoots τ).p3
        (canonicalUnaryRoots τ).p4 X = 0 ∧
      Projectivization.mk ℂ X hX = P}

/-- Membership in the projective residual curve can be checked on any
chosen nonzero representative. -/
theorem projectivization_mk_mem_jacobiResidualProjectiveCurve_iff
    (τ : ℍ) (X : Fin 4 → ℂ) (hX : X ≠ 0) :
    Projectivization.mk ℂ X hX ∈
        jacobiResidualProjectiveCurve τ ↔
      jacobiResidualQ1
          (canonicalUnaryRoots τ).p2
          (canonicalUnaryRoots τ).p3
          (canonicalUnaryRoots τ).p4 X = 0 ∧
        jacobiResidualQ2
          (canonicalUnaryRoots τ).p2
          (canonicalUnaryRoots τ).p3
          (canonicalUnaryRoots τ).p4 X = 0 := by
  constructor
  · rintro ⟨Y, hY, hYQ1, hYQ2, hYX⟩
    rcases
        (Projectivization.mk_eq_mk_iff' ℂ
          Y X hY hX).mp hYX with
      ⟨c, hcYX⟩
    have hc : c ≠ 0 := by
      intro hc
      subst c
      have hzero : (0 : Fin 4 → ℂ) = Y := by
        simpa using hcYX
      exact hY hzero.symm
    constructor
    · have hscaled :
          jacobiResidualQ1
              (canonicalUnaryRoots τ).p2
              (canonicalUnaryRoots τ).p3
              (canonicalUnaryRoots τ).p4
              (c • X) = 0 := by
          rw [hcYX]
          exact hYQ1
      rw [jacobiResidualQ1_smul] at hscaled
      exact
        (mul_eq_zero.mp hscaled).resolve_left
          (pow_ne_zero 2 hc)
    · have hscaled :
          jacobiResidualQ2
              (canonicalUnaryRoots τ).p2
              (canonicalUnaryRoots τ).p3
              (canonicalUnaryRoots τ).p4
              (c • X) = 0 := by
          rw [hcYX]
          exact hYQ2
      rw [jacobiResidualQ2_smul] at hscaled
      exact
        (mul_eq_zero.mp hscaled).resolve_left
          (pow_ne_zero 2 hc)
  · rintro ⟨hQ1, hQ2⟩
    exact ⟨X, hX, hQ1, hQ2, rfl⟩

/-- The projective four-theta map lands on the canonical residual
complete intersection. -/
theorem projectiveJacobiTheta_mem_residualCurve
    (z : ℂ) (τ : ℍ) :
    projectiveJacobiTheta z τ ∈
      jacobiResidualProjectiveCurve τ := by
  refine
    ⟨jacobiThetaVector z (τ : ℂ),
      jacobiThetaVector_ne_zero z τ,
      canonical_jacobiResidualQ1_jacobiThetaVector z τ,
      canonical_jacobiResidualQ2_jacobiThetaVector z τ, rfl⟩

/-- Translation by the doubled period lattice does not change the
projective theta point. -/
theorem projectiveJacobiTheta_add_levelTwo_lattice
    (z : ℂ) (τ : ℍ) (m n : ℤ) :
    projectiveJacobiTheta
        (z + 2 * (m : ℂ) + 2 * (n : ℂ) * (τ : ℂ)) τ =
      projectiveJacobiTheta z τ := by
  have h :=
    (Projectivization.mk_eq_mk_iff' ℂ
      (jacobiThetaVector
        (z + 2 * (m : ℂ) +
          2 * (n : ℂ) * (τ : ℂ)) (τ : ℂ))
      (jacobiThetaVector z (τ : ℂ))
      (jacobiThetaVector_ne_zero
        (z + 2 * (m : ℂ) +
          2 * (n : ℂ) * (τ : ℂ)) τ)
      (jacobiThetaVector_ne_zero z τ)).2
      ⟨levelTwoThetaMultiplier n z (τ : ℂ),
        (jacobiThetaVector_add_levelTwo_lattice
          z (τ : ℂ) m n).symm⟩
  simpa only [projectiveJacobiTheta] using h

/-- **Global projective saturation.** Every point on the two canonical
residual quadrics is represented by a value of the four Jacobi theta
functions.  This theorem is unconditional and does not use any
Wronskian or local-immersion hypothesis. -/
theorem projectiveJacobiTheta_surjective_onto_residualCurve
    (τ : ℍ)
    (P : Projectivization ℂ (Fin 4 → ℂ))
    (hP : P ∈ jacobiResidualProjectiveCurve τ) :
    ∃ z : ℂ, projectiveJacobiTheta z τ = P := by
  rcases hP with ⟨X, hX, hQ1, hQ2, rfl⟩
  rcases
      exists_smul_jacobiThetaVector_eq_of_residual
        τ X hX hQ1 hQ2 with
    ⟨z, c, hc, hscale⟩
  refine ⟨z, ?_⟩
  have hproj :
      Projectivization.mk ℂ X hX =
        Projectivization.mk ℂ
          (jacobiThetaVector z (τ : ℂ))
          (jacobiThetaVector_ne_zero z τ) :=
    (Projectivization.mk_eq_mk_iff' ℂ
      X (jacobiThetaVector z (τ : ℂ))
      hX (jacobiThetaVector_ne_zero z τ)).2
      ⟨c, hscale⟩
  simpa only [projectiveJacobiTheta] using hproj.symm

/-- Exact set-theoretic form of global saturation: the range of the
projective four-theta map is the whole residual complete intersection. -/
theorem range_projectiveJacobiTheta_eq_residualCurve
    (τ : ℍ) :
    Set.range (fun z : ℂ ↦ projectiveJacobiTheta z τ) =
      jacobiResidualProjectiveCurve τ := by
  ext P
  constructor
  · rintro ⟨z, rfl⟩
    exact projectiveJacobiTheta_mem_residualCurve z τ
  · intro hP
    rcases
        projectiveJacobiTheta_surjective_onto_residualCurve
          τ P hP with
      ⟨z, hz⟩
    exact ⟨z, hz⟩

end

end HGAS.Modular
