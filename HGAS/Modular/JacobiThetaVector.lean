import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Tactic

/-!
# Four two-variable Jacobi theta functions and their common level-two multiplier

Mathlib's `jacobiTheta₂ z τ` is Jacobi's `θ₃(z|τ)` in the normalization

```
  θ₃(z|τ) = ∑ n : ℤ, exp(π i n² τ + 2 π i n z).
```

The other three characteristics are obtained by half-period shifts.  This
file fixes those definitions once and proves the common automorphy factor
under the doubled lattice `2ℤ + 2τℤ`.  That factor is equation (8.15) in
the written proof and is needed both for the projective theta map and for
the quantitative nonreal-Bloch escape argument.

The key reusable lemma is first proved for arbitrary integer lattice
translations of Mathlib's theta function:

```
 θ₃(z + m + nτ | τ)
   = exp(-π i n²τ - 2π i nz) θ₃(z|τ).
```

All calculations are termwise reindexings of an absolutely convergent
theta series; no product formula or choice of logarithm is used.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real

noncomputable section

/-- Integer-lattice automorphy of Mathlib's two-variable Jacobi theta
function. -/
theorem jacobiTheta₂_add_int_lattice
    (z τ : ℂ) (m n : ℤ) :
    jacobiTheta₂
        (z + (m : ℂ) + (n : ℂ) * τ) τ =
      cexp
          (-π * I * (n : ℂ) ^ 2 * τ -
            2 * π * I * (n : ℂ) * z) *
        jacobiTheta₂ z τ := by
  conv_rhs =>
    rw [jacobiTheta₂, ← tsum_mul_left,
      ← (Equiv.addRight n).tsum_eq]
  refine tsum_congr (fun k ↦ ?_)
  simp only [jacobiTheta₂_term, Equiv.coe_addRight,
    Int.cast_add]
  rw [← Complex.exp_add]
  calc
    cexp
        (2 * π * I * (k : ℂ) *
              (z + (m : ℂ) + (n : ℂ) * τ) +
            π * I * (k : ℂ) ^ 2 * τ) =
      cexp
        ((-π * I * (n : ℂ) ^ 2 * τ -
              2 * π * I * (n : ℂ) * z) +
            (2 * π * I * ((k : ℂ) + (n : ℂ)) * z +
              π * I * ((k : ℂ) + (n : ℂ)) ^ 2 * τ) +
          ((k * m : ℤ) : ℂ) * (2 * π * I)) := by
        congr 1
        push_cast
        ring
    _ =
      cexp
        ((-π * I * (n : ℂ) ^ 2 * τ -
              2 * π * I * (n : ℂ) * z) +
            (2 * π * I * ((k : ℂ) + (n : ℂ)) * z +
              π * I * ((k : ℂ) + (n : ℂ)) ^ 2 * τ)) := by
        rw [Complex.exp_add,
          Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Adding an integral multiple of `2πi` does not change the complex
exponential. -/
theorem cexp_add_int_two_pi_I
    (w : ℂ) (k : ℤ) :
    cexp (w + (k : ℂ) * (2 * π * I)) = cexp w := by
  rw [Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Jacobi's `θ₃`, exactly Mathlib's two-variable theta function. -/
def jacobiTheta3 (z τ : ℂ) : ℂ :=
  jacobiTheta₂ z τ

/-- Jacobi's `θ₄`, obtained by translating `θ₃` by the real
half-period. -/
def jacobiTheta4 (z τ : ℂ) : ℂ :=
  jacobiTheta₂ (z + 1 / 2) τ

/-- Jacobi's `θ₂`, obtained by translating `θ₃` by the imaginary
half-period and restoring the standard exponential factor. -/
def jacobiTheta2 (z τ : ℂ) : ℂ :=
  cexp (π * I * (τ / 4 + z)) *
    jacobiTheta₂ (z + τ / 2) τ

/-- Jacobi's odd theta function.  This convention is chosen so that
`θ₁(z) = -θ₂(z+1/2)` and the half-period identity used by the compiler has
the sign printed in equation (7.3). -/
def jacobiTheta1 (z τ : ℂ) : ℂ :=
  -jacobiTheta2 (z + 1 / 2) τ

/-- The four theta coordinates, indexed in the human order
`θ₁,θ₂,θ₃,θ₄`. -/
def jacobiThetaVector (z τ : ℂ) : Fin 4 → ℂ :=
  ![jacobiTheta1 z τ, jacobiTheta2 z τ,
    jacobiTheta3 z τ, jacobiTheta4 z τ]

/-- Joint continuity of Mathlib's theta function when the modular
parameter is restricted to the upper half-plane. -/
theorem continuous_jacobiTheta₂_upperHalfPlane :
    Continuous
      (fun p : ℂ × ℍ ↦
        jacobiTheta₂ p.1 (p.2 : ℂ)) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hp :
      ContinuousAt
        (fun q : ℂ × ℍ ↦
          (q.1, (q.2 : ℂ))) p := by
    fun_prop
  simpa only [Function.comp_apply] using
    (continuousAt_jacobiTheta₂
      p.1 p.2.im_pos).comp
        (f := fun q : ℂ × ℍ ↦
          (q.1, (q.2 : ℂ))) hp

theorem continuous_jacobiTheta3_upperHalfPlane :
    Continuous
      (fun p : ℂ × ℍ ↦
        jacobiTheta3 p.1 (p.2 : ℂ)) := by
  simpa only [jacobiTheta3] using
    continuous_jacobiTheta₂_upperHalfPlane

theorem continuous_jacobiTheta4_upperHalfPlane :
    Continuous
      (fun p : ℂ × ℍ ↦
        jacobiTheta4 p.1 (p.2 : ℂ)) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hp :
      ContinuousAt
        (fun q : ℂ × ℍ ↦
          (q.1 + 1 / 2, (q.2 : ℂ))) p := by
    fun_prop
  simpa only [jacobiTheta4, Function.comp_apply] using
    (continuousAt_jacobiTheta₂
      (p.1 + 1 / 2) p.2.im_pos).comp
        (f := fun q : ℂ × ℍ ↦
          (q.1 + 1 / 2, (q.2 : ℂ))) hp

theorem continuous_jacobiTheta2_upperHalfPlane :
    Continuous
      (fun p : ℂ × ℍ ↦
        jacobiTheta2 p.1 (p.2 : ℂ)) := by
  have htheta :
      Continuous
        (fun p : ℂ × ℍ ↦
          jacobiTheta₂
            (p.1 + (p.2 : ℂ) / 2)
            (p.2 : ℂ)) := by
    rw [continuous_iff_continuousAt]
    intro p
    have hp :
        ContinuousAt
          (fun q : ℂ × ℍ ↦
            (q.1 + (q.2 : ℂ) / 2,
              (q.2 : ℂ))) p := by
      fun_prop
    simpa only [Function.comp_apply] using
      (continuousAt_jacobiTheta₂
        (p.1 + (p.2 : ℂ) / 2)
        p.2.im_pos).comp
          (f := fun q : ℂ × ℍ ↦
            (q.1 + (q.2 : ℂ) / 2,
              (q.2 : ℂ))) hp
  rw [show
      (fun p : ℂ × ℍ ↦
        jacobiTheta2 p.1 (p.2 : ℂ)) =
      fun p ↦
        cexp
            (π * I *
              ((p.2 : ℂ) / 4 + p.1)) *
          jacobiTheta₂
            (p.1 + (p.2 : ℂ) / 2)
            (p.2 : ℂ) by
    funext p
    rfl]
  exact
    (Complex.continuous_exp.comp (by fun_prop)).mul
      htheta

theorem continuous_jacobiTheta1_upperHalfPlane :
    Continuous
      (fun p : ℂ × ℍ ↦
        jacobiTheta1 p.1 (p.2 : ℂ)) := by
  have hcomp :=
    continuous_jacobiTheta2_upperHalfPlane.comp
      (show
        Continuous
          (fun p : ℂ × ℍ ↦
            (p.1 + 1 / 2, p.2)) by
        fun_prop)
  simpa only [jacobiTheta1, Function.comp_apply] using
    hcomp.neg

/-- Joint continuity of the four-coordinate theta vector on
`ℂ × ℍ`. -/
theorem continuous_jacobiThetaVector_upperHalfPlane :
    Continuous
      (fun p : ℂ × ℍ ↦
        jacobiThetaVector p.1 (p.2 : ℂ)) := by
  apply continuous_pi
  intro k
  fin_cases k
  · simpa only [jacobiThetaVector, Matrix.cons_val_zero] using
      continuous_jacobiTheta1_upperHalfPlane
  · simpa only [jacobiThetaVector, Matrix.cons_val_one,
      Matrix.cons_val_zero] using
      continuous_jacobiTheta2_upperHalfPlane
  · simpa only [jacobiThetaVector, Matrix.cons_val_one,
      Matrix.cons_val_zero] using
      continuous_jacobiTheta3_upperHalfPlane
  · simpa only [jacobiThetaVector, Matrix.cons_val_one,
      Matrix.cons_val_zero] using
      continuous_jacobiTheta4_upperHalfPlane

/-- Compactness upgrades pointwise nonvanishing of the theta vector to a
uniform positive lower bound.  The remaining analytic input in applications
is therefore isolated cleanly as the no-common-zero statement. -/
theorem exists_uniform_pos_le_norm_jacobiThetaVector
    {K : Set (ℂ × ℍ)}
    (hK : IsCompact K)
    (hKne : K.Nonempty)
    (hzero :
      ∀ p ∈ K,
        jacobiThetaVector p.1 (p.2 : ℂ) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧
      ∀ p ∈ K, c ≤
        ‖jacobiThetaVector p.1 (p.2 : ℂ)‖ := by
  let f : ℂ × ℍ → ℝ :=
    fun p ↦
      ‖jacobiThetaVector p.1 (p.2 : ℂ)‖
  have hf : Continuous f :=
    continuous_norm.comp
      continuous_jacobiThetaVector_upperHalfPlane
  obtain ⟨p, hpK, hpmin⟩ :=
    hK.exists_isMinOn hKne hf.continuousOn
  refine ⟨f p, ?_, fun q hqK ↦ hpmin hqK⟩
  exact norm_pos_iff.mpr (hzero p hpK)

/-- Common multiplier of all four theta characteristics under the
level-two translation `z ↦ z + 2m + 2nτ`. -/
def levelTwoThetaMultiplier
    (n : ℤ) (z τ : ℂ) : ℂ :=
  cexp
    (-4 * π * I * (n : ℂ) ^ 2 * τ -
      4 * π * I * (n : ℂ) * z)

theorem levelTwoThetaMultiplier_ne_zero
    (n : ℤ) (z τ : ℂ) :
    levelTwoThetaMultiplier n z τ ≠ 0 :=
  Complex.exp_ne_zero _

/-- Exact logarithmic modulus of the level-two multiplier. -/
theorem norm_levelTwoThetaMultiplier
    (n : ℤ) (z τ : ℂ) :
    ‖levelTwoThetaMultiplier n z τ‖ =
      Real.exp
        (4 * π * (n : ℝ) ^ 2 * τ.im +
          4 * π * (n : ℝ) * z.im) := by
  rw [levelTwoThetaMultiplier, Complex.norm_exp]
  congr 1
  simp [pow_two, Complex.mul_re, Complex.mul_im]

theorem jacobiTheta3_add_levelTwo_lattice
    (z τ : ℂ) (m n : ℤ) :
    jacobiTheta3
        (z + 2 * (m : ℂ) + 2 * (n : ℂ) * τ) τ =
      levelTwoThetaMultiplier n z τ *
        jacobiTheta3 z τ := by
  rw [jacobiTheta3, jacobiTheta3]
  have h :=
    jacobiTheta₂_add_int_lattice z τ (2 * m) (2 * n)
  rw [show
      z + 2 * (m : ℂ) + 2 * (n : ℂ) * τ =
        z + ((2 * m : ℤ) : ℂ) +
          ((2 * n : ℤ) : ℂ) * τ by
      push_cast
      ring,
    h, levelTwoThetaMultiplier]
  congr 2
  push_cast
  ring

theorem jacobiTheta4_add_levelTwo_lattice
    (z τ : ℂ) (m n : ℤ) :
    jacobiTheta4
        (z + 2 * (m : ℂ) + 2 * (n : ℂ) * τ) τ =
      levelTwoThetaMultiplier n z τ *
        jacobiTheta4 z τ := by
  rw [jacobiTheta4]
  have h :=
    jacobiTheta₂_add_int_lattice
      (z + 1 / 2) τ (2 * m) (2 * n)
  rw [show
      z + 2 * (m : ℂ) + 2 * (n : ℂ) * τ + 1 / 2 =
        (z + 1 / 2) + ((2 * m : ℤ) : ℂ) +
          ((2 * n : ℤ) : ℂ) * τ by
      push_cast
      ring]
  rw [h]
  congr 1
  rw [levelTwoThetaMultiplier]
  calc
    cexp
        (-π * I * ((2 * n : ℤ) : ℂ) ^ 2 * τ -
          2 * π * I * ((2 * n : ℤ) : ℂ) *
            (z + 1 / 2)) =
      cexp
        ((-4 * π * I * (n : ℂ) ^ 2 * τ -
            4 * π * I * (n : ℂ) * z) +
          ((-n : ℤ) : ℂ) * (2 * π * I)) := by
            congr 1
            push_cast
            ring
    _ =
      cexp
        (-4 * π * I * (n : ℂ) ^ 2 * τ -
          4 * π * I * (n : ℂ) * z) :=
      cexp_add_int_two_pi_I _ (-n)

theorem jacobiTheta2_add_levelTwo_lattice
    (z τ : ℂ) (m n : ℤ) :
    jacobiTheta2
        (z + 2 * (m : ℂ) + 2 * (n : ℂ) * τ) τ =
      levelTwoThetaMultiplier n z τ *
        jacobiTheta2 z τ := by
  rw [jacobiTheta2, jacobiTheta2]
  have h :=
    jacobiTheta₂_add_int_lattice
      (z + τ / 2) τ (2 * m) (2 * n)
  rw [show
      z + 2 * (m : ℂ) + 2 * (n : ℂ) * τ + τ / 2 =
        (z + τ / 2) + ((2 * m : ℤ) : ℂ) +
          ((2 * n : ℤ) : ℂ) * τ by
      push_cast
      ring]
  rw [h, ← mul_assoc, ← Complex.exp_add,
    levelTwoThetaMultiplier, ← mul_assoc,
    ← Complex.exp_add]
  congr 1
  calc
    cexp
        (π * I *
            (τ / 4 +
              (z + 2 * (m : ℂ) +
                2 * (n : ℂ) * τ)) +
          (-π * I * ((2 * n : ℤ) : ℂ) ^ 2 * τ -
            2 * π * I * ((2 * n : ℤ) : ℂ) *
              (z + τ / 2))) =
      cexp
        (((-4 * π * I * (n : ℂ) ^ 2 * τ -
              4 * π * I * (n : ℂ) * z) +
            π * I * (τ / 4 + z)) +
          (m : ℂ) * (2 * π * I)) := by
            congr 1
            push_cast
            ring
    _ =
      cexp
        ((-4 * π * I * (n : ℂ) ^ 2 * τ -
            4 * π * I * (n : ℂ) * z) +
          π * I * (τ / 4 + z)) :=
      cexp_add_int_two_pi_I _ m

theorem jacobiTheta1_add_levelTwo_lattice
    (z τ : ℂ) (m n : ℤ) :
    jacobiTheta1
        (z + 2 * (m : ℂ) + 2 * (n : ℂ) * τ) τ =
      levelTwoThetaMultiplier n z τ *
        jacobiTheta1 z τ := by
  rw [jacobiTheta1, jacobiTheta1,
    show
      z + 2 * (m : ℂ) + 2 * (n : ℂ) * τ + 1 / 2 =
        (z + 1 / 2) + 2 * (m : ℂ) +
          2 * (n : ℂ) * τ by ring,
    jacobiTheta2_add_levelTwo_lattice]
  rw [mul_neg]
  congr 2
  rw [levelTwoThetaMultiplier, levelTwoThetaMultiplier]
  calc
    cexp
        (-4 * π * I * (n : ℂ) ^ 2 * τ -
          4 * π * I * (n : ℂ) * (z + 1 / 2)) =
      cexp
        ((-4 * π * I * (n : ℂ) ^ 2 * τ -
            4 * π * I * (n : ℂ) * z) +
          ((-n : ℤ) : ℂ) * (2 * π * I)) := by
            congr 1
            push_cast
            ring
    _ =
      cexp
        (-4 * π * I * (n : ℂ) ^ 2 * τ -
          4 * π * I * (n : ℂ) * z) :=
      cexp_add_int_two_pi_I _ (-n)

/-- **Common doubled-period multiplier**, equation (8.15).

The four-coordinate theta vector changes only by one common nonzero
scalar under every translation by `2m+2nτ`. -/
theorem jacobiThetaVector_add_levelTwo_lattice
    (z τ : ℂ) (m n : ℤ) :
    jacobiThetaVector
        (z + 2 * (m : ℂ) + 2 * (n : ℂ) * τ) τ =
      levelTwoThetaMultiplier n z τ •
        jacobiThetaVector z τ := by
  funext k
  fin_cases k
  · simpa [jacobiThetaVector] using
      jacobiTheta1_add_levelTwo_lattice z τ m n
  · simpa [jacobiThetaVector] using
      jacobiTheta2_add_levelTwo_lattice z τ m n
  · simpa [jacobiThetaVector] using
      jacobiTheta3_add_levelTwo_lattice z τ m n
  · simpa [jacobiThetaVector] using
      jacobiTheta4_add_levelTwo_lattice z τ m n

/-- Norm form of the common multiplier identity. -/
theorem norm_jacobiThetaVector_add_levelTwo_lattice
    (z τ : ℂ) (m n : ℤ) :
    ‖jacobiThetaVector
        (z + 2 * (m : ℂ) + 2 * (n : ℂ) * τ) τ‖ =
      Real.exp
          (4 * π * (n : ℝ) ^ 2 * τ.im +
            4 * π * (n : ℝ) * z.im) *
        ‖jacobiThetaVector z τ‖ := by
  rw [jacobiThetaVector_add_levelTwo_lattice,
    norm_smul, norm_levelTwoThetaMultiplier]

/-- The half-period identity used to turn the compiler's zero-free
`θ₃` output into the rational reciprocal `θ₁` chart, equation (7.3). -/
theorem jacobiTheta3_eq_halfPeriod_jacobiTheta1
    (z τ : ℂ) :
    jacobiTheta3 z τ =
      cexp (π * I * (z + τ / 4)) *
        jacobiTheta1
          (z + (1 + τ) / 2) τ := by
  rw [jacobiTheta3, jacobiTheta1, jacobiTheta2]
  have h :=
    jacobiTheta₂_add_int_lattice z τ 1 1
  rw [show
      z + (1 + τ) / 2 + 1 / 2 + τ / 2 =
        z + ((1 : ℤ) : ℂ) +
          ((1 : ℤ) : ℂ) * τ by
      norm_num
      ring,
    h]
  rw [mul_neg, ← mul_assoc, ← mul_assoc,
    ← Complex.exp_add, ← Complex.exp_add]
  have hexp :
      cexp
        (π * I * (z + τ / 4) +
          π * I *
            (τ / 4 +
              (z + (1 + τ) / 2 + 1 / 2)) +
          (-π * I * ((1 : ℤ) : ℂ) ^ 2 * τ -
            2 * π * I * ((1 : ℤ) : ℂ) * z)) = -1 := by
    rw [show
        π * I * (z + τ / 4) +
            π * I *
              (τ / 4 +
                (z + (1 + τ) / 2 + 1 / 2)) +
            (-π * I * ((1 : ℤ) : ℂ) ^ 2 * τ -
              2 * π * I * ((1 : ℤ) : ℂ) * z) =
          π * I by ring,
      Complex.exp_pi_mul_I]
  rw [hexp]
  ring

end

end HGAS.Modular
