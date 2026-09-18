import HGAS.Modular.JacobiMomentResonanceArbitraryHorizon
import HGAS.Modular.JacobiBlochNormalization
import Mathlib.Tactic

/-!
# Rigidity of a Gaussian Jacobi--Bloch trace from three moments

## Legacy routing warning

This module is outside the public `HGAS.lean` import closure and is not
used by the completed endpoint.  In particular, its `ρ = 0` discussion
must not be read as a general selector theorem: the manuscript's explicit
counterexample shows that the raw three-moment data need not reduce to the
phase-tied scalar hypotheses used here.  The live theorem is
`JacobiThreeMomentTargetRigidity.quadraticTrace_eq_target_of_three_moments`,
which assumes irrational `ρ`; the augmented arithmetic pipeline proves
that assumption for every final input.

This file isolates the last algebraic step of the Jacobi selector.  A
real-Bloch leaf has a Gaussian--geometric coefficient family

```text
  D exp(q (n+a)^2) B^n
    exp(i ( (n+a)(n+a+ρ) α + (n+a) χ)).
```

Here `a` is the Bloch shift, `ρ` is the ratio of the two clock speeds,
and `α, χ` record the initial clock phases.  Cesàro extraction of the
mean and the two first twisted rows leaves only the direct and reflected
roots of the quadratic dispersion relation.

The main theorem below proves the complete rigidity statement.

* If `ρ` is irrational, mean one puts `a` in the integral or reflected
  Bloch class.  In the integral class the first twisted moment forces
  `B = 1`; in the reflected class it forces exactly the reflected
  amplitude and multiplier, whose trace is the canonical trace after
  the involution `k ↦ -k`.
* If `ρ = 0`, the two roots in the first twisted row occur together.
  Its correct doubled center gives `B + B⁻¹ = 2`, hence `B = 1`.

Thus both branches, including the zero-linear-character collision, give
the same full canonical Jacobi trace.  The theorem is stated along an
arbitrary sequence of physical horizons tending to infinity.
-/

noncomputable section

open Filter Topology

namespace HGAS.Modular

/-- The canonical Gaussian--phase coefficient at the initial clock
phase. -/
def canonicalQuadraticCoefficient
    (q ρ α χ : ℝ) (k : ℤ) : ℂ :=
  jacobiGaussianCoefficient q (k : ℝ) *
    jacobiUnitPhase
      (quadraticDispersion ρ (k : ℝ) * α +
        (k : ℝ) * χ)

/-- The general real-Bloch Gaussian--geometric coefficient before the
three moments have selected its shift, scale, and multiplier. -/
def generalQuadraticBlochCoefficient
    (q ρ a α χ : ℝ) (D B : ℂ) (n : ℤ) : ℂ :=
  D *
    jacobiGaussianCoefficient q ((n : ℝ) + a) *
    B ^ n *
    jacobiUnitPhase
      (quadraticDispersion ρ ((n : ℝ) + a) * α +
        ((n : ℝ) + a) * χ)

/-- Initial value of the character which twists the mean row to the
row with direct resonance `r`. -/
def quadraticMomentInitialTwist
    (ρ α χ : ℝ) (r : ℤ) : ℂ :=
  jacobiUnitPhase
    (-(quadraticDispersion ρ (r : ℝ) * α +
      (r : ℝ) * χ))

theorem quadraticMomentInitialTwist_ne_zero
    (ρ α χ : ℝ) (r : ℤ) :
    quadraticMomentInitialTwist ρ α χ r ≠ 0 :=
  jacobiUnitPhase_ne_zero _

theorem canonicalQuadraticCoefficient_zero
    (q ρ α χ : ℝ) :
    canonicalQuadraticCoefficient q ρ α χ 0 = 1 := by
  simp [canonicalQuadraticCoefficient, jacobiGaussianCoefficient,
    quadraticDispersion]

theorem canonicalQuadraticCoefficient_one_twisted
    (q ρ α χ : ℝ) :
    quadraticMomentInitialTwist ρ α χ 1 *
        canonicalQuadraticCoefficient q ρ α χ 1 =
      jacobiGaussianCoefficient q 1 := by
  unfold quadraticMomentInitialTwist canonicalQuadraticCoefficient
  norm_num only [Int.cast_one]
  let θ : ℝ :=
    quadraticDispersion ρ (1 : ℝ) * α + (1 : ℝ) * χ
  change
    jacobiUnitPhase (-θ) *
        (jacobiGaussianCoefficient q 1 * jacobiUnitPhase θ) =
      jacobiGaussianCoefficient q 1
  rw [show
      jacobiUnitPhase (-θ) *
          (jacobiGaussianCoefficient q 1 *
            jacobiUnitPhase θ) =
        jacobiGaussianCoefficient q 1 *
          (jacobiUnitPhase (-θ) * jacobiUnitPhase θ) by ring]
  rw [← jacobiUnitPhase_add]
  simp [jacobiUnitPhase_zero]

theorem canonicalQuadraticCoefficient_neg_one_twisted
    (q ρ α χ : ℝ) :
    quadraticMomentInitialTwist ρ α χ (-1) *
        canonicalQuadraticCoefficient q ρ α χ (-1) =
      jacobiGaussianCoefficient q 1 := by
  unfold quadraticMomentInitialTwist canonicalQuadraticCoefficient
  norm_num only [Int.cast_neg, Int.cast_one]
  let θ : ℝ :=
    quadraticDispersion ρ (-1 : ℝ) * α + (-1 : ℝ) * χ
  change
    jacobiUnitPhase (-θ) *
        (jacobiGaussianCoefficient q (-1) *
          jacobiUnitPhase θ) =
      jacobiGaussianCoefficient q 1
  rw [show
      jacobiUnitPhase (-θ) *
          (jacobiGaussianCoefficient q (-1) *
            jacobiUnitPhase θ) =
        jacobiGaussianCoefficient q (-1) *
          (jacobiUnitPhase (-θ) * jacobiUnitPhase θ) by ring]
  rw [← jacobiUnitPhase_add]
  simp [jacobiUnitPhase_zero, jacobiGaussianCoefficient]

/-! ## Resonant sums in the two separated classes -/

private theorem integral_mean_resonant_sum
    (coefficient : ℤ → ℂ)
    {ρ : ℝ} (hρ : Irrational ρ) (l : ℤ) :
    (∑' n : ℤ,
      if (n : ℝ) + (l : ℝ) = 0 ∨
          (n : ℝ) + (l : ℝ) = -ρ then
        coefficient n
      else 0) =
      coefficient (-l) := by
  have hpred (n : ℤ) :
      ((n : ℝ) + (l : ℝ) = 0 ∨
          (n : ℝ) + (l : ℝ) = -ρ) ↔
        n = -l := by
    constructor
    · rintro (hzero | hreflected)
      · have hz : n + l = 0 := by
          exact_mod_cast hzero
        omega
      · exfalso
        apply hρ.ne_int (-(n + l))
        push_cast
        linarith
    · rintro rfl
      left
      push_cast
      ring
  calc
    (∑' n : ℤ,
      if (n : ℝ) + (l : ℝ) = 0 ∨
          (n : ℝ) + (l : ℝ) = -ρ then
        coefficient n
      else 0) =
        ∑' n : ℤ, if n = -l then coefficient n else 0 := by
      apply tsum_congr
      intro n
      simp only [hpred n]
    _ = coefficient (-l) := tsum_ite_eq _ _

private theorem integral_plus_resonant_sum
    (coefficient : ℤ → ℂ)
    {ρ : ℝ} (hρ : Irrational ρ) (l : ℤ) :
    (∑' n : ℤ,
      if (n : ℝ) + (l : ℝ) = 1 ∨
          (n : ℝ) + (l : ℝ) = -1 - ρ then
        coefficient n
      else 0) =
      coefficient (1 - l) := by
  have hpred (n : ℤ) :
      ((n : ℝ) + (l : ℝ) = 1 ∨
          (n : ℝ) + (l : ℝ) = -1 - ρ) ↔
        n = 1 - l := by
    constructor
    · rintro (hdirect | hreflected)
      · have hz : n + l = 1 := by
          exact_mod_cast hdirect
        omega
      · exfalso
        apply hρ.ne_int (-(n + l + 1))
        push_cast
        linarith
    · rintro rfl
      left
      push_cast
      ring
  calc
    (∑' n : ℤ,
      if (n : ℝ) + (l : ℝ) = 1 ∨
          (n : ℝ) + (l : ℝ) = -1 - ρ then
        coefficient n
      else 0) =
        ∑' n : ℤ, if n = 1 - l then coefficient n else 0 := by
      apply tsum_congr
      intro n
      simp only [hpred n]
    _ = coefficient (1 - l) := tsum_ite_eq _ _

private theorem reflected_mean_resonant_sum
    (coefficient : ℤ → ℂ)
    {ρ : ℝ} (hρ : Irrational ρ) (l : ℤ) :
    (∑' n : ℤ,
      if (n : ℝ) + (-ρ + (l : ℝ)) = 0 ∨
          (n : ℝ) + (-ρ + (l : ℝ)) = -ρ then
        coefficient n
      else 0) =
      coefficient (-l) := by
  have hpred (n : ℤ) :
      ((n : ℝ) + (-ρ + (l : ℝ)) = 0 ∨
          (n : ℝ) + (-ρ + (l : ℝ)) = -ρ) ↔
        n = -l := by
    constructor
    · rintro (hdirect | hreflected)
      · exfalso
        apply hρ.ne_int (n + l)
        push_cast
        linarith
      · have hz : n + l = 0 := by
          exact_mod_cast (by linarith :
            (n : ℝ) + (l : ℝ) = 0)
        omega
    · rintro rfl
      right
      push_cast
      ring
  calc
    (∑' n : ℤ,
      if (n : ℝ) + (-ρ + (l : ℝ)) = 0 ∨
          (n : ℝ) + (-ρ + (l : ℝ)) = -ρ then
        coefficient n
      else 0) =
        ∑' n : ℤ, if n = -l then coefficient n else 0 := by
      apply tsum_congr
      intro n
      simp only [hpred n]
    _ = coefficient (-l) := tsum_ite_eq _ _

private theorem reflected_plus_resonant_sum
    (coefficient : ℤ → ℂ)
    {ρ : ℝ} (hρ : Irrational ρ) (l : ℤ) :
    (∑' n : ℤ,
      if (n : ℝ) + (-ρ + (l : ℝ)) = 1 ∨
          (n : ℝ) + (-ρ + (l : ℝ)) = -1 - ρ then
        coefficient n
      else 0) =
      coefficient (-1 - l) := by
  have hpred (n : ℤ) :
      ((n : ℝ) + (-ρ + (l : ℝ)) = 1 ∨
          (n : ℝ) + (-ρ + (l : ℝ)) = -1 - ρ) ↔
        n = -1 - l := by
    constructor
    · rintro (hdirect | hreflected)
      · exfalso
        apply hρ.ne_int (n + l - 1)
        push_cast
        linarith
      · have hz : n + l = -1 := by
          exact_mod_cast (by linarith :
            (n : ℝ) + (l : ℝ) = -1)
        omega
    · rintro rfl
      right
      push_cast
      ring
  calc
    (∑' n : ℤ,
      if (n : ℝ) + (-ρ + (l : ℝ)) = 1 ∨
          (n : ℝ) + (-ρ + (l : ℝ)) = -1 - ρ then
        coefficient n
      else 0) =
        ∑' n : ℤ, if n = -1 - l then coefficient n else 0 := by
      apply tsum_congr
      intro n
      simp only [hpred n]
    _ = coefficient (-1 - l) := tsum_ite_eq _ _

private theorem zeroRatio_mean_resonant_sum
    (coefficient : ℤ → ℂ) (l : ℤ) :
    (∑' n : ℤ,
      if (n : ℝ) + (l : ℝ) = 0 ∨
          (n : ℝ) + (l : ℝ) = 0 then
        coefficient n
      else 0) =
      coefficient (-l) := by
  have h :
      ∀ n : ℤ,
        ((n : ℝ) + (l : ℝ) = 0 ∨
            (n : ℝ) + (l : ℝ) = 0) ↔
          n = -l := by
    intro n
    constructor
    · rintro (hn | hn)
      · have hz : n + l = 0 := by exact_mod_cast hn
        omega
      · have hz : n + l = 0 := by exact_mod_cast hn
        omega
    · rintro rfl
      left
      push_cast
      ring
  calc
    (∑' n : ℤ,
      if (n : ℝ) + (l : ℝ) = 0 ∨
          (n : ℝ) + (l : ℝ) = 0 then
        coefficient n
      else 0) =
        ∑' n : ℤ, if n = -l then coefficient n else 0 := by
      apply tsum_congr
      intro n
      simp only [h n]
    _ = coefficient (-l) := tsum_ite_eq _ _

private theorem zeroRatio_plus_resonant_sum
    (coefficient : ℤ → ℂ) (l : ℤ) :
    (∑' n : ℤ,
      if (n : ℝ) + (l : ℝ) = 1 ∨
          (n : ℝ) + (l : ℝ) = -1 then
        coefficient n
      else 0) =
      coefficient (1 - l) + coefficient (-1 - l) := by
  have hsum :
      HasSum
        (fun n : ℤ =>
          (if n = 1 - l then coefficient (1 - l) else 0) +
          (if n = -1 - l then coefficient (-1 - l) else 0))
        (coefficient (1 - l) + coefficient (-1 - l)) :=
    (hasSum_ite_eq (1 - l) (coefficient (1 - l))).add
      (hasSum_ite_eq (-1 - l) (coefficient (-1 - l)))
  calc
    (∑' n : ℤ,
      if (n : ℝ) + (l : ℝ) = 1 ∨
          (n : ℝ) + (l : ℝ) = -1 then
        coefficient n
      else 0) =
        ∑' n : ℤ,
          ((if n = 1 - l then coefficient (1 - l) else 0) +
            (if n = -1 - l then coefficient (-1 - l) else 0)) := by
      apply tsum_congr
      intro n
      have hne : (1 - l : ℤ) ≠ -1 - l := by omega
      by_cases h₁ : n = 1 - l
      · subst n
        simp [hne]
      · by_cases h₂ : n = -1 - l
        · subst n
          have hne' : (-1 - l : ℤ) ≠ 1 - l := by omega
          simp [hne']
        · have hroot :
            ¬((n : ℝ) + (l : ℝ) = 1 ∨
              (n : ℝ) + (l : ℝ) = -1) := by
            rintro (hp | hm)
            · apply h₁
              have hz : n + l = 1 := by exact_mod_cast hp
              omega
            · apply h₂
              have hz : n + l = -1 := by exact_mod_cast hm
              omega
          simp [h₁, h₂, hroot]
    _ = coefficient (1 - l) + coefficient (-1 - l) :=
      hsum.tsum_eq

/-! ## Gaussian--geometric reindexing identities -/

private theorem generalCoefficient_integral_reindex
    (q ρ α χ : ℝ) (D B : ℂ) (hB : B ≠ 0)
    (l k : ℤ) :
    generalQuadraticBlochCoefficient
        q ρ (l : ℝ) α χ D B (k - l) =
      (D * B ^ (-l)) *
        jacobiGaussianCoefficient q (k : ℝ) *
        B ^ k *
        jacobiUnitPhase
          (quadraticDispersion ρ (k : ℝ) * α +
            (k : ℝ) * χ) := by
  unfold generalQuadraticBlochCoefficient
  have hcast :
      (((k - l : ℤ) : ℝ) + (l : ℝ)) = (k : ℝ) := by
    push_cast
    ring
  rw [hcast, zpow_sub₀ hB]
  rw [show B ^ k / B ^ l = B ^ (-l) * B ^ k by
    rw [zpow_neg, div_eq_mul_inv]
    ring]
  ring

private theorem generalCoefficient_reflected_reindex
    (q ρ α χ : ℝ) (D B : ℂ) (hB : B ≠ 0)
    (l k : ℤ) :
    generalQuadraticBlochCoefficient
        q ρ (-ρ + (l : ℝ)) α χ D B (k - l) =
      (D * B ^ (-l)) *
        jacobiGaussianCoefficient q ((k : ℝ) - ρ) *
        B ^ k *
        jacobiUnitPhase
          (quadraticDispersion ρ ((k : ℝ) - ρ) * α +
            ((k : ℝ) - ρ) * χ) := by
  unfold generalQuadraticBlochCoefficient
  have hcast :
      (((k - l : ℤ) : ℝ) + (-ρ + (l : ℝ))) =
        (k : ℝ) - ρ := by
    push_cast
    ring
  rw [hcast, zpow_sub₀ hB]
  rw [show B ^ k / B ^ l = B ^ (-l) * B ^ k by
    rw [zpow_neg, div_eq_mul_inv]
    ring]
  ring

private theorem integral_normalization_of_equations
    (q ρ α χ : ℝ) (D B : ℂ) (hB : B ≠ 0)
    (l : ℤ)
    (hmean :
      generalQuadraticBlochCoefficient
        q ρ (l : ℝ) α χ D B (-l) = 1)
    (hplus :
      quadraticMomentInitialTwist ρ α χ 1 *
          generalQuadraticBlochCoefficient
            q ρ (l : ℝ) α χ D B (1 - l) =
        jacobiGaussianCoefficient q 1) :
    D * B ^ (-l) = 1 ∧ B = 1 := by
  let D' : ℂ := D * B ^ (-l)
  have hmean' : D' = 1 := by
    have hreindex :=
      generalCoefficient_integral_reindex
        q ρ α χ D B hB l 0
    rw [zero_sub] at hreindex
    rw [hreindex] at hmean
    simpa [D', jacobiGaussianCoefficient,
      quadraticDispersion, jacobiUnitPhase_zero] using hmean
  have hplus' :
      D' * B * jacobiGaussianCoefficient q 1 =
        jacobiGaussianCoefficient q 1 := by
    have hreindex :=
      generalCoefficient_integral_reindex
        q ρ α χ D B hB l 1
    rw [hreindex] at hplus
    let θ : ℝ :=
      quadraticDispersion ρ (1 : ℝ) * α + (1 : ℝ) * χ
    have hphase :
        jacobiUnitPhase (-θ) * jacobiUnitPhase θ = 1 := by
      rw [← jacobiUnitPhase_add]
      simp [jacobiUnitPhase_zero]
    unfold quadraticMomentInitialTwist at hplus
    norm_num only [Int.cast_one, zpow_one] at hplus
    change
      jacobiUnitPhase (-θ) *
          (D' * jacobiGaussianCoefficient q 1 * B *
            jacobiUnitPhase θ) =
        jacobiGaussianCoefficient q 1 at hplus
    calc
      D' * B * jacobiGaussianCoefficient q 1 =
          jacobiUnitPhase (-θ) *
            (D' * jacobiGaussianCoefficient q 1 * B *
              jacobiUnitPhase θ) := by
                rw [show
                    jacobiUnitPhase (-θ) *
                        (D' * jacobiGaussianCoefficient q 1 * B *
                          jacobiUnitPhase θ) =
                      D' * B * jacobiGaussianCoefficient q 1 *
                        (jacobiUnitPhase (-θ) *
                          jacobiUnitPhase θ) by ring,
                  hphase, mul_one]
      _ = jacobiGaussianCoefficient q 1 := hplus
  refine ⟨hmean', ?_⟩
  rw [hmean', one_mul] at hplus'
  apply mul_right_cancel₀
    (jacobiGaussianCoefficient_ne_zero q 1)
  simpa only [one_mul] using hplus'

private theorem zeroRatio_normalization_of_equations
    (q α : ℝ) (D B : ℂ) (hB : B ≠ 0)
    (l : ℤ)
    (hmean :
      generalQuadraticBlochCoefficient
        q 0 (l : ℝ) α 0 D B (-l) = 1)
    (hplus :
      quadraticMomentInitialTwist 0 α 0 1 *
        (generalQuadraticBlochCoefficient
            q 0 (l : ℝ) α 0 D B (1 - l) +
          generalQuadraticBlochCoefficient
            q 0 (l : ℝ) α 0 D B (-1 - l)) =
        2 * jacobiGaussianCoefficient q 1) :
    D * B ^ (-l) = 1 ∧ B = 1 := by
  let D' : ℂ := D * B ^ (-l)
  have hmean' : D' = 1 := by
    have hreindex :=
      generalCoefficient_integral_reindex
        q 0 α 0 D B hB l 0
    rw [zero_sub] at hreindex
    rw [hreindex] at hmean
    simpa [D', jacobiGaussianCoefficient,
      quadraticDispersion, jacobiUnitPhase_zero] using hmean
  have hsum :
      B + B⁻¹ = 2 := by
    have hplusReindex :=
      generalCoefficient_integral_reindex
        q 0 α 0 D B hB l 1
    have hminusReindex :=
      generalCoefficient_integral_reindex
        q 0 α 0 D B hB l (-1)
    rw [hplusReindex, hminusReindex] at hplus
    rw [show D * B ^ (-l) = D' by rfl, hmean'] at hplus
    norm_num only [Int.cast_one, Int.cast_neg, zpow_one,
      zpow_neg, one_mul] at hplus
    have hg :
        jacobiGaussianCoefficient q (-1 : ℝ) =
          jacobiGaussianCoefficient q 1 := by
      simp [jacobiGaussianCoefficient]
    rw [hg] at hplus
    unfold quadraticMomentInitialTwist at hplus
    simp only [Int.cast_one, quadraticDispersion,
      add_zero, mul_zero, one_mul, neg_mul, neg_neg] at hplus
    have hphase :
        jacobiUnitPhase (-α) * jacobiUnitPhase α = 1 := by
      rw [← jacobiUnitPhase_add]
      simp [jacobiUnitPhase_zero]
    rw [show
        jacobiUnitPhase (-α) *
            (jacobiGaussianCoefficient q 1 * B *
                jacobiUnitPhase α +
              jacobiGaussianCoefficient q 1 * B⁻¹ *
                jacobiUnitPhase α) =
          jacobiGaussianCoefficient q 1 *
            (B * (jacobiUnitPhase
                (-α) * jacobiUnitPhase α) +
            B⁻¹ * (jacobiUnitPhase
                (-α) * jacobiUnitPhase α)) by ring,
        hphase] at hplus
    apply mul_left_cancel₀
      (jacobiGaussianCoefficient_ne_zero q 1)
    calc
      jacobiGaussianCoefficient q 1 * (B + B⁻¹) =
          2 * jacobiGaussianCoefficient q 1 := by
        simpa only [mul_one] using hplus
      _ = jacobiGaussianCoefficient q 1 * 2 := by ring
  refine ⟨hmean', ?_⟩
  have hfactor : (B - 1) * (B - 1) = 0 := by
    calc
      (B - 1) * (B - 1) =
          (B + B⁻¹ - 2) * B := by
            symm
            calc
              (B + B⁻¹ - 2) * B =
                  B * B + B⁻¹ * B - 2 * B := by ring
              _ = (B - 1) * (B - 1) := by
                rw [inv_mul_cancel₀ hB]
                ring
      _ = 0 := by rw [hsum]; ring
  rcases mul_eq_zero.mp hfactor with h | h
  · exact sub_eq_zero.mp h
  · exact sub_eq_zero.mp h

/-! ## Reflected normalization in the Gaussian--geometric notation -/

/-- Integer powers of the selected reflected multiplier agree with the
branch-free exponential formula used in `JacobiBlochNormalization`. -/
theorem reflectedBlochMultiplier_zpow
    (q ρ χ : ℝ) (k : ℤ) :
    reflectedBlochMultiplier q ρ χ ^ k =
      reflectedBlochMultiplierPower q ρ χ k := by
  let z : ℂ :=
    ((2 * q * ρ : ℝ) : ℂ) +
      (((-2 * χ : ℝ) : ℂ) * Complex.I)
  have hB :
      reflectedBlochMultiplier q ρ χ =
        Complex.exp z := by
    unfold reflectedBlochMultiplier jacobiUnitPhase
      HGAS.Analysis.realFrequencyExponential
    simp only [Complex.ofReal_one, mul_one]
    rw [Complex.ofReal_exp, ← Complex.exp_add]
  rw [hB, ← Complex.exp_int_mul]
  unfold reflectedBlochMultiplierPower jacobiUnitPhase
    HGAS.Analysis.realFrequencyExponential
  simp only [Complex.ofReal_one, mul_one]
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  dsimp only [z]
  push_cast
  ring

private theorem reflected_normalization_of_equations
    (q ρ α χ : ℝ) (D B : ℂ) (hB : B ≠ 0)
    (l : ℤ)
    (hmean :
      generalQuadraticBlochCoefficient
        q ρ (-ρ + (l : ℝ)) α χ D B (-l) = 1)
    (hplus :
      quadraticMomentInitialTwist ρ α χ 1 *
          generalQuadraticBlochCoefficient
            q ρ (-ρ + (l : ℝ)) α χ D B (-1 - l) =
        jacobiGaussianCoefficient q 1) :
    D * B ^ (-l) = reflectedBlochAmplitude q ρ χ ∧
      B = reflectedBlochMultiplier q ρ χ := by
  let D' : ℂ := D * B ^ (-l)
  have hmean' :
      ReflectedMeanCoefficientEquation q ρ χ D' := by
    have hreindex :=
      generalCoefficient_reflected_reindex
        q ρ α χ D B hB l 0
    rw [zero_sub] at hreindex
    rw [hreindex] at hmean
    unfold ReflectedMeanCoefficientEquation
      reflectedMeanMomentCoefficient
    change
      D' *
          (jacobiGaussianCoefficient q (-ρ) *
            jacobiUnitPhase (-ρ * χ)) =
        1
    simpa [D', quadraticDispersion, mul_assoc] using hmean
  have hplus' :
      ReflectedPlusOneCoefficientEquation q ρ χ D' B := by
    have hreindex :=
      generalCoefficient_reflected_reindex
        q ρ α χ D B hB l (-1)
    rw [hreindex] at hplus
    unfold ReflectedPlusOneCoefficientEquation
      reflectedPlusOneMomentCoefficient
    change
      (D' *
          jacobiGaussianCoefficient q (-1 - ρ) *
          jacobiUnitPhase ((-1 - ρ) * χ) *
          jacobiUnitPhase (-χ)) *
          B⁻¹ =
        jacobiGaussianCoefficient q 1
    unfold quadraticMomentInitialTwist at hplus
    norm_num only [Int.cast_one, Int.cast_neg, zpow_neg,
      Int.reduceNeg] at hplus
    have hDform : D * (B ^ l)⁻¹ = D' := by
      simp [D', zpow_neg]
    rw [hDform] at hplus
    simp only [zpow_one] at hplus
    have hdisp :
        quadraticDispersion ρ (-1 - ρ) =
          quadraticDispersion ρ 1 := by
      unfold quadraticDispersion
      ring
    rw [hdisp] at hplus
    norm_num only [one_mul] at hplus
    have hphase :
        jacobiUnitPhase
              (-(quadraticDispersion ρ 1 * α + χ)) *
            jacobiUnitPhase
              (quadraticDispersion ρ 1 * α +
                (-1 - ρ) * χ) =
          jacobiUnitPhase ((-1 - ρ) * χ) *
            jacobiUnitPhase (-χ) := by
      rw [← jacobiUnitPhase_add, ← jacobiUnitPhase_add]
      congr 1
      ring
    rw [show
        jacobiUnitPhase
              (-(quadraticDispersion ρ 1 * α + χ)) *
            (D' * jacobiGaussianCoefficient q (-1 - ρ) *
              B⁻¹ *
              jacobiUnitPhase
                (quadraticDispersion ρ 1 * α +
                  (-1 - ρ) * χ)) =
          (D' * jacobiGaussianCoefficient q (-1 - ρ) *
              (jacobiUnitPhase
                (-(quadraticDispersion ρ 1 * α + χ)) *
                jacobiUnitPhase
                  (quadraticDispersion ρ 1 * α +
                    (-1 - ρ) * χ))) *
            B⁻¹ by ring,
        hphase] at hplus
    simpa only [mul_assoc] using hplus
  exact
    (reflectedMean_plusOneCoefficientEquations_iff
      q ρ χ D' B).mp ⟨hmean', hplus'⟩

/-! ## Branchwise equality of the complete trace -/

private theorem generalCoefficient_integral_eq_canonical
    (q ρ α χ : ℝ) (D B : ℂ) (hB : B ≠ 0)
    (l : ℤ)
    (hD : D * B ^ (-l) = 1)
    (hBone : B = 1)
    (k : ℤ) :
    generalQuadraticBlochCoefficient
        q ρ (l : ℝ) α χ D B (k - l) =
      canonicalQuadraticCoefficient q ρ α χ k := by
  rw [generalCoefficient_integral_reindex
    q ρ α χ D B hB l k, hD, hBone]
  simp [canonicalQuadraticCoefficient]

private theorem generalCoefficient_reflected_eq_canonical_neg
    (q ρ α χ : ℝ) (D B : ℂ) (hB : B ≠ 0)
    (l : ℤ)
    (hD :
      D * B ^ (-l) = reflectedBlochAmplitude q ρ χ)
    (hBselected :
      B = reflectedBlochMultiplier q ρ χ)
    (k : ℤ) :
    generalQuadraticBlochCoefficient
        q ρ (-ρ + (l : ℝ)) α χ D B (k - l) =
      canonicalQuadraticCoefficient q ρ α χ (-k) := by
  rw [generalCoefficient_reflected_reindex
    q ρ α χ D B hB l k, hD, hBselected,
    reflectedBlochMultiplier_zpow]
  have hterm :=
    normalizedReflectedBlochTerm_eq_canonical_neg
      q ρ χ α k
  calc
    reflectedBlochAmplitude q ρ χ *
          jacobiGaussianCoefficient q ((k : ℝ) - ρ) *
          reflectedBlochMultiplierPower q ρ χ k *
          jacobiUnitPhase
            (quadraticDispersion ρ ((k : ℝ) - ρ) * α +
              ((k : ℝ) - ρ) * χ) =
        normalizedReflectedBlochTerm q ρ χ α k := by
      unfold normalizedReflectedBlochTerm
        normalizedReflectedBlochCoefficient
      rw [jacobiUnitPhase_add]
      rw [show
          quadraticDispersion ρ ((k : ℝ) - ρ) =
            (k : ℝ) ^ 2 - ρ * (k : ℝ) by
              unfold quadraticDispersion
              ring]
      ring
    _ =
        canonicalJacobiTraceTerm
          (fun j : ℤ ↦
            jacobiGaussianCoefficient q (j : ℝ))
          ρ χ α (-k) := hterm
    _ = canonicalQuadraticCoefficient q ρ α χ (-k) := by
      unfold canonicalJacobiTraceTerm
        canonicalQuadraticCoefficient
      congr 1
      congr 1
      simp only [Int.cast_neg, neg_sq]
      unfold quadraticDispersion
      ring

private theorem integral_trace_eq_canonical
    (q ρ α χ Ω : ℝ) (D B : ℂ) (hB : B ≠ 0)
    (l : ℤ)
    (hD : D * B ^ (-l) = 1)
    (hBone : B = 1)
    (t : ℝ) :
    quadraticMomentSeries
        (generalQuadraticBlochCoefficient
          q ρ (l : ℝ) α χ D B)
        Ω ρ (l : ℝ) 0 t =
      quadraticMomentSeries
        (canonicalQuadraticCoefficient q ρ α χ)
        Ω ρ 0 0 t := by
  unfold quadraticMomentSeries HGAS.Analysis.exponentialSeries
  rw [← (Equiv.addRight (-l : ℤ)).tsum_eq]
  apply tsum_congr
  intro k
  unfold HGAS.Analysis.exponentialSeriesTerm
  simp only [Equiv.coe_addRight, ← sub_eq_add_neg]
  rw [generalCoefficient_integral_eq_canonical
    q ρ α χ D B hB l hD hBone k]
  congr 1
  unfold quadraticMomentFrequency quadraticDispersion
  push_cast
  ring

private theorem reflected_trace_eq_canonical
    (q ρ α χ Ω : ℝ) (D B : ℂ) (hB : B ≠ 0)
    (l : ℤ)
    (hD :
      D * B ^ (-l) = reflectedBlochAmplitude q ρ χ)
    (hBselected :
      B = reflectedBlochMultiplier q ρ χ)
    (t : ℝ) :
    quadraticMomentSeries
        (generalQuadraticBlochCoefficient
          q ρ (-ρ + (l : ℝ)) α χ D B)
        Ω ρ (-ρ + (l : ℝ)) 0 t =
      quadraticMomentSeries
        (canonicalQuadraticCoefficient q ρ α χ)
        Ω ρ 0 0 t := by
  unfold quadraticMomentSeries HGAS.Analysis.exponentialSeries
  rw [← ((Equiv.neg ℤ).trans
    (Equiv.addRight (-l : ℤ))).tsum_eq]
  apply tsum_congr
  intro k
  unfold HGAS.Analysis.exponentialSeriesTerm
  simp only [Equiv.trans_apply, Equiv.neg_apply,
    Equiv.coe_addRight, ← sub_eq_add_neg]
  rw [generalCoefficient_reflected_eq_canonical_neg
    q ρ α χ D B hB l hD hBselected (-k)]
  simp only [neg_neg]
  congr 1
  unfold quadraticMomentFrequency quadraticDispersion
  push_cast
  ring

/-! ## Arbitrary-horizon three-moment rigidity -/

/-- **Three-moment Jacobi--Bloch rigidity.**

The hypotheses are exactly the absolutely summable classified series,
the nonzero private frequency, and the three corrected physical Cesàro
limits.  The zero-ratio branch requires `χ = 0`, which is precisely the
fact that a zero linear character has constant value one.  The conclusion
identifies the complete time-dependent output with the canonical trace. -/
theorem quadraticBlochTrace_eq_canonical_of_three_moments
    (q ρ a α χ Ω : ℝ) (D B : ℂ)
    (hB : B ≠ 0)
    (hΩ : Ω ≠ 0)
    (hsum :
      Summable fun n : ℤ ↦
        ‖generalQuadraticBlochCoefficient
          q ρ a α χ D B n‖)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    (hratio : Irrational ρ ∨ ρ = 0)
    (hchi : ρ = 0 → χ = 0)
    (hmean :
      Tendsto
        (fun N ↦ HGAS.Analysis.cesaroMeanAt
          (quadraticMomentSeries
            (generalQuadraticBlochCoefficient
              q ρ a α χ D B)
            Ω ρ a 0) (T N))
        atTop (𝓝 1))
    (hplus :
      Tendsto
        (fun N ↦ HGAS.Analysis.cesaroMeanAt
          (quadraticMomentSeries
            (fun n ↦
              quadraticMomentInitialTwist ρ α χ 1 *
                generalQuadraticBlochCoefficient
                  q ρ a α χ D B n)
            Ω ρ a 1) (T N))
        atTop
        (𝓝 (if ρ = 0 then
          2 * jacobiGaussianCoefficient q 1
        else
          jacobiGaussianCoefficient q 1)))
    (hminus :
      Tendsto
        (fun N ↦ HGAS.Analysis.cesaroMeanAt
          (quadraticMomentSeries
            (fun n ↦
              quadraticMomentInitialTwist ρ α χ (-1) *
                generalQuadraticBlochCoefficient
                  q ρ a α χ D B n)
            Ω ρ a (-1)) (T N))
        atTop
        (𝓝 (if ρ = 0 then
          2 * jacobiGaussianCoefficient q 1
        else
          jacobiGaussianCoefficient q 1))) :
    ∀ t : ℝ,
      quadraticMomentSeries
          (generalQuadraticBlochCoefficient
            q ρ a α χ D B)
          Ω ρ a 0 t =
        quadraticMomentSeries
          (canonicalQuadraticCoefficient q ρ α χ)
          Ω ρ 0 0 t := by
  have hsumPlus :
      Summable fun n : ℤ ↦
        ‖quadraticMomentInitialTwist ρ α χ 1 *
          generalQuadraticBlochCoefficient
            q ρ a α χ D B n‖ :=
    (hsum.of_norm.mul_left
      (quadraticMomentInitialTwist ρ α χ 1)).norm
  have hmeanExtract :=
    cesaroMeanAt_meanMomentSeries_tendsto
      (generalQuadraticBlochCoefficient
        q ρ a α χ D B)
      hsum hΩ ρ a hT
  have hmeanSum :
      meanResonantCoefficientSum
          (generalQuadraticBlochCoefficient
            q ρ a α χ D B) ρ a =
        1 :=
    tendsto_nhds_unique hmeanExtract hmean
  have hclasses :
      IsIntegralBlochClass a ∨
        IsReflectedBlochClass ρ a :=
    blochClasses_of_cesaroMeanAt_meanMoment_tendsto_one
      (generalQuadraticBlochCoefficient
        q ρ a α χ D B)
      hsum hΩ ρ a hT hmean
  rcases hratio with hρ | hρ
  · have hplusExtract :=
      cesaroMeanAt_plusMomentSeries_tendsto
        (fun n ↦
          quadraticMomentInitialTwist ρ α χ 1 *
            generalQuadraticBlochCoefficient
              q ρ a α χ D B n)
        hsumPlus hΩ ρ a hT
    have hplusTarget :
        (if ρ = 0 then
          2 * jacobiGaussianCoefficient q 1
        else jacobiGaussianCoefficient q 1) =
          jacobiGaussianCoefficient q 1 := by
      simp [hρ.ne_zero]
    rw [hplusTarget] at hplus
    rcases hclasses with ⟨l, rfl⟩ | ⟨l, rfl⟩
    · have hmeanEq :
          generalQuadraticBlochCoefficient
              q ρ (l : ℝ) α χ D B (-l) =
            1 := by
        rw [← hmeanSum]
        unfold meanResonantCoefficientSum
        exact
          (integral_mean_resonant_sum
            (generalQuadraticBlochCoefficient
              q ρ (l : ℝ) α χ D B) hρ l).symm
      have hplusEq :
          quadraticMomentInitialTwist ρ α χ 1 *
              generalQuadraticBlochCoefficient
                q ρ (l : ℝ) α χ D B (1 - l) =
            jacobiGaussianCoefficient q 1 := by
        have hsumEq :=
          tendsto_nhds_unique hplusExtract hplus
        simpa only [integral_plus_resonant_sum
          (fun n ↦
            quadraticMomentInitialTwist ρ α χ 1 *
              generalQuadraticBlochCoefficient
                q ρ (l : ℝ) α χ D B n) hρ l] using hsumEq
      obtain ⟨hD, hBone⟩ :=
        integral_normalization_of_equations
          q ρ α χ D B hB l hmeanEq hplusEq
      exact integral_trace_eq_canonical
        q ρ α χ Ω D B hB l hD hBone
    · have hmeanEq :
          generalQuadraticBlochCoefficient
              q ρ (-ρ + (l : ℝ)) α χ D B (-l) =
            1 := by
        rw [← hmeanSum]
        unfold meanResonantCoefficientSum
        exact
          (reflected_mean_resonant_sum
            (generalQuadraticBlochCoefficient
              q ρ (-ρ + (l : ℝ)) α χ D B) hρ l).symm
      have hplusEq :
          quadraticMomentInitialTwist ρ α χ 1 *
              generalQuadraticBlochCoefficient
                q ρ (-ρ + (l : ℝ)) α χ D B (-1 - l) =
            jacobiGaussianCoefficient q 1 := by
        have hsumEq :=
          tendsto_nhds_unique hplusExtract hplus
        simpa only [reflected_plus_resonant_sum
          (fun n ↦
            quadraticMomentInitialTwist ρ α χ 1 *
              generalQuadraticBlochCoefficient
                q ρ (-ρ + (l : ℝ)) α χ D B n) hρ l] using hsumEq
      obtain ⟨hD, hBselected⟩ :=
        reflected_normalization_of_equations
          q ρ α χ D B hB l hmeanEq hplusEq
      exact reflected_trace_eq_canonical
        q ρ α χ Ω D B hB l hD hBselected
  · subst ρ
    have hχ := hchi rfl
    subst χ
    have hIntegral : IsIntegralBlochClass a := by
      rcases hclasses with h | ⟨l, hl⟩
      · exact h
      · refine ⟨l, ?_⟩
        simpa using hl
    rcases hIntegral with ⟨l, rfl⟩
    have hmeanEq :
        generalQuadraticBlochCoefficient
            q 0 (l : ℝ) α 0 D B (-l) =
          1 := by
      rw [← hmeanSum]
      unfold meanResonantCoefficientSum
      simp only [neg_zero]
      exact
        (zeroRatio_mean_resonant_sum
          (generalQuadraticBlochCoefficient
            q 0 (l : ℝ) α 0 D B) l).symm
    have hplusExtract :=
      cesaroMeanAt_plusMomentSeries_tendsto
        (fun n ↦
          quadraticMomentInitialTwist 0 α 0 1 *
            generalQuadraticBlochCoefficient
              q 0 (l : ℝ) α 0 D B n)
        hsumPlus hΩ 0 (l : ℝ) hT
    have hplusEq :
        quadraticMomentInitialTwist 0 α 0 1 *
          (generalQuadraticBlochCoefficient
              q 0 (l : ℝ) α 0 D B (1 - l) +
            generalQuadraticBlochCoefficient
              q 0 (l : ℝ) α 0 D B (-1 - l)) =
          2 * jacobiGaussianCoefficient q 1 := by
      have hsumEq :=
        tendsto_nhds_unique hplusExtract hplus
      simp only [sub_zero] at hsumEq
      rw [zeroRatio_plus_resonant_sum
        (fun n ↦
          quadraticMomentInitialTwist 0 α 0 1 *
            generalQuadraticBlochCoefficient
              q 0 (l : ℝ) α 0 D B n) l] at hsumEq
      simpa only [mul_add] using hsumEq
    obtain ⟨hD, hBone⟩ :=
      zeroRatio_normalization_of_equations
        q α D B hB l hmeanEq hplusEq
    exact integral_trace_eq_canonical
      q 0 α 0 Ω D B hB l hD hBone

end HGAS.Modular
