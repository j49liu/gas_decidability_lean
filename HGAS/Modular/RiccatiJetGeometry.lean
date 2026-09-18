import HGAS.Modular.HorizontalTrajectory
import HGAS.Modular.RiccatiJetAsymptotics
import Mathlib.Tactic

/-!
# Euclidean geometry of a global modular Riccati lift

The exact integration of the Riccati jet

```
                    u' = -u²,   v' = -2uv,   T' = v
```

has only two global geometric shapes inside the upper half-plane.

* If `u(t₀)=0`, then `T` is affine.  An affine line which remains in the
  upper half-plane for every real time has real velocity, so it is a
  horizontal line.
* If `u(t₀)≠0`, write

```
                 ξ = T(t₀) + v(t₀)/u(t₀).
```

  When `ξ` lies on the real axis, global positivity forces the
  fractional-linear arc to be a Euclidean circle tangent to the real
  axis at `ξ`.

The second assertion is proved by an explicit invariant.  If
`y₀ = Im T(t₀)` and

```
                 R = |T(t₀)-ξ|²/(2y₀),
```

then every point of the trajectory satisfies

```
                 |T(t)-(ξ+iR)|² = R².
```

Thus the proof contains no appeal to an informal picture of Möbius
transformations: the centre and radius of the horocycle are both visible
in the theorem statement.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open scoped ComplexConjugate

noncomputable section

/-- A real affine function which is strictly positive on the whole real
line has zero slope. -/
private theorem slope_eq_zero_of_forall_pos
    (a b : ℝ) (h : ∀ s : ℝ, 0 < a + b * s) :
    b = 0 := by
  by_contra hb
  have hzero := h (-a / b)
  field_simp [hb] at hzero
  norm_num at hzero

/-- The elementary imaginary-part numerator for the fractional-linear
expression `-A/(1+U s)`.  Multiplying by the positive squared norm of
the denominator turns it into a real affine function of `s`. -/
private theorem neg_div_one_add_mul_im_mul_normSq
    (A U : ℂ) (s : ℝ)
    (hden : 1 + U * (s : ℂ) ≠ 0) :
    (-A / (1 + U * (s : ℂ))).im *
        Complex.normSq (1 + U * (s : ℂ)) =
      -A.im - (A * conj U).im * s := by
  rw [Complex.div_im]
  field_simp [Complex.normSq_eq_zero, hden]
  simp only [Complex.neg_re, Complex.neg_im, Complex.add_re,
    Complex.add_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

namespace IsRiccatiJetTrajectory

variable {u v T : ℝ → ℂ}

/-- Subtracting the finite endpoint puts the non-affine solution in the
particularly simple form `-(v₀/u₀)/d(t)`. -/
theorem T_sub_fractionalLinearEndpoint
    (h : IsRiccatiJetTrajectory u v T)
    (t₀ t : ℝ) (hu : u t₀ ≠ 0) :
    T t - fractionalLinearEndpoint u v T t₀ =
      -(v t₀ / u t₀) / denominator u t₀ t := by
  rw [h.T_eq_fractionalLinearCandidate t₀ t]
  unfold fractionalLinearCandidate fractionalLinearEndpoint
  have hden :
      1 + u t₀ * (((t - t₀ : ℝ) : ℝ) : ℂ) ≠ 0 := by
    simpa only [denominator] using
      h.denominator_ne_zero t₀ t
  simp only [denominator]
  apply (eq_div_iff hden).2
  rw [sub_mul, add_mul, add_mul,
    div_mul_cancel₀ _ hden]
  field_simp [hu]
  ring

/-- The finite endpoint of a non-affine trajectory contained in the
closed upper half-plane also lies in that closed half-plane.  This is
the small topological half of the recurrent endpoint argument: the
explicit Riccati formula supplies convergence, and nonnegativity passes
to the limit. -/
theorem fractionalLinearEndpoint_im_nonneg
    (h : IsRiccatiJetTrajectory u v T)
    (t₀ : ℝ) (hu : u t₀ ≠ 0)
    (hupper : ∀ t : ℝ, 0 ≤ (T t).im) :
    0 ≤ (fractionalLinearEndpoint u v T t₀).im := by
  have hlimit :=
    h.T_tendsto_fractionalLinearEndpoint_atTop t₀ hu
  have himlimit :
      Filter.Tendsto (fun t ↦ (T t).im) Filter.atTop
        (nhds (fractionalLinearEndpoint u v T t₀).im) :=
    (Complex.continuous_im.tendsto
      (fractionalLinearEndpoint u v T t₀)).comp hlimit
  exact
    ge_of_tendsto himlimit
      (Filter.Eventually.of_forall hupper)

/-- If the finite endpoint is real and the whole fractional-linear
trajectory lies above the real axis, its one possible transverse
coefficient vanishes.  This is the algebraic tangency condition. -/
theorem fractionalLinear_tangency_coefficient
    (h : IsRiccatiJetTrajectory u v T)
    (t₀ : ℝ) (hu : u t₀ ≠ 0)
    (hupper : ∀ t : ℝ, 0 < (T t).im)
    (hendpoint :
      (fractionalLinearEndpoint u v T t₀).im = 0) :
    ((v t₀ / u t₀) * conj (u t₀)).im = 0 := by
  let A : ℂ := v t₀ / u t₀
  let U : ℂ := u t₀
  let ξ : ℂ := fractionalLinearEndpoint u v T t₀
  have hpositive :
      ∀ s : ℝ,
        0 <
          -A.im - (A * conj U).im * s := by
    intro s
    let t := t₀ + s
    have hden :
        1 + U * (s : ℂ) ≠ 0 := by
      simpa only [U, denominator, t, add_sub_cancel_left] using
        h.denominator_ne_zero t₀ t
    have hshape :
        T t - ξ = -A / (1 + U * (s : ℂ)) := by
      simpa only [A, U, ξ, denominator, t, add_sub_cancel_left] using
        h.T_sub_fractionalLinearEndpoint t₀ t hu
    have him :
        (T t - ξ).im = (T t).im := by
      simp only [Complex.sub_im, ξ, hendpoint, sub_zero]
    have hnorm :
        0 < Complex.normSq (1 + U * (s : ℂ)) :=
      Complex.normSq_pos.mpr hden
    have hproduct :
        0 <
          (T t - ξ).im *
            Complex.normSq (1 + U * (s : ℂ)) :=
      mul_pos (by simpa only [him] using hupper t) hnorm
    rw [hshape,
      neg_div_one_add_mul_im_mul_normSq A U s hden] at hproduct
    exact hproduct
  have hslope :
      -(A * conj U).im = 0 :=
    slope_eq_zero_of_forall_pos (-A.im)
      (-(A * conj U).im)
        (by simpa only [neg_mul] using hpositive)
  simpa only [neg_eq_zero] using hslope

/-- The cross-multiplied circle invariant.  This form avoids division by
the initial height and is often the most convenient reusable statement:

```
 Im(T₀) |T(t)-ξ|² = |T₀-ξ|² Im(T(t)).
```
-/
theorem fractionalLinear_horocycle_invariant
    (h : IsRiccatiJetTrajectory u v T)
    (t₀ t : ℝ) (hu : u t₀ ≠ 0)
    (hupper : ∀ q : ℝ, 0 < (T q).im)
    (hendpoint :
      (fractionalLinearEndpoint u v T t₀).im = 0) :
    (T t₀).im *
        Complex.normSq
          (T t - fractionalLinearEndpoint u v T t₀) =
      Complex.normSq
          (T t₀ - fractionalLinearEndpoint u v T t₀) *
        (T t).im := by
  let A : ℂ := v t₀ / u t₀
  let U : ℂ := u t₀
  let ξ : ℂ := fractionalLinearEndpoint u v T t₀
  let D : ℂ := denominator u t₀ t
  have hD : D ≠ 0 := h.denominator_ne_zero t₀ t
  have hshape :
      T t - ξ = -A / D := by
    simpa only [A, ξ, D] using
      h.T_sub_fractionalLinearEndpoint t₀ t hu
  have hshape₀ : T t₀ - ξ = -A := by
    rw [h.T_sub_fractionalLinearEndpoint t₀ t₀ hu]
    simp only [A, denominator, sub_self, Complex.ofReal_zero,
      mul_zero, add_zero, div_one]
  have htangent :
      (A * conj U).im = 0 := by
    simpa only [A, U] using
      h.fractionalLinear_tangency_coefficient
        t₀ hu hupper hendpoint
  have hbaseIm : (T t₀).im = -A.im := by
    have him := congrArg Complex.im hshape₀
    simpa only [Complex.sub_im, ξ, hendpoint, sub_zero,
      Complex.neg_im] using him
  have hcurrentIm :
      (T t).im * Complex.normSq D = -A.im := by
    have him :
        (T t - ξ).im = (T t).im := by
      simp only [Complex.sub_im, ξ, hendpoint, sub_zero]
    have hformula :=
      neg_div_one_add_mul_im_mul_normSq
        A U (t - t₀) (by simpa only [U, D, denominator] using hD)
    rw [htangent, zero_mul, sub_zero] at hformula
    rw [← him, hshape]
    simpa only [U, D, denominator] using hformula
  rw [hshape, hshape₀, Complex.normSq_div, hbaseIm]
  simp only [Complex.normSq_neg]
  have hnormD : Complex.normSq D ≠ 0 :=
    (Complex.normSq_pos.mpr hD).ne'
  calc
    -A.im * (Complex.normSq A / Complex.normSq D) =
        Complex.normSq A *
          (-A.im / Complex.normSq D) := by ring
    _ = Complex.normSq A * (T t).im := by
      congr 1
      exact (div_eq_iff hnormD).2 hcurrentIm.symm

end IsRiccatiJetTrajectory

/-- The radius of the Euclidean horocycle based at `ξ` and passing
through the upper-half-plane point `z`. -/
def horocycleRadius (z ξ : ℂ) : ℝ :=
  Complex.normSq (z - ξ) / (2 * z.im)

/-- The Euclidean centre of the horocycle based at `ξ` and passing
through `z`.  When `ξ` is real, the centre lies vertically above `ξ`. -/
def horocycleCenter (z ξ : ℂ) : ℂ :=
  ξ + (horocycleRadius z ξ : ℂ) * Complex.I

/-- The horocycle radius is positive when `z` is in the upper half-plane
and the real base point `ξ` differs from `z`. -/
theorem horocycleRadius_pos
    (z ξ : ℂ) (hz : 0 < z.im) (hξ : ξ.im = 0) :
    0 < horocycleRadius z ξ := by
  unfold horocycleRadius
  apply div_pos
  · rw [Complex.normSq_pos]
    intro heq
    have him := congrArg Complex.im heq
    simp only [Complex.sub_im, hξ, sub_zero, Complex.zero_im] at him
    exact hz.ne' him
  · positivity

/-- The cross-multiplied invariant is exactly the usual Euclidean circle
equation with centre `ξ+iR` and radius `R`. -/
theorem normSq_sub_horocycleCenter_eq_sq
    (z₀ ξ z : ℂ)
    (hz₀ : 0 < z₀.im)
    (hξ : ξ.im = 0)
    (hinvariant :
      z₀.im * Complex.normSq (z - ξ) =
        Complex.normSq (z₀ - ξ) * z.im) :
    Complex.normSq (z - horocycleCenter z₀ ξ) =
      horocycleRadius z₀ ξ ^ 2 := by
  have hz₀ne : z₀.im ≠ 0 := hz₀.ne'
  unfold horocycleCenter horocycleRadius
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
    add_zero, zero_add, hξ]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    hξ, sub_zero] at hinvariant
  field_simp [hz₀ne]
  nlinarith [hinvariant]

/-- **Global Riccati geometry, affine branch.**  If the Riccati value
vanishes at `t₀`, an upper-half-plane lift is literally a horizontal
line.  The chosen horizontal-line origin makes the formula valid with
the original time parameter, without translating time. -/
theorem riccatiLift_eq_horizontalLine_of_u_eq_zero_at
    {u v : ℝ → ℂ} {T : ℝ → ℍ}
    (h :
      IsRiccatiJetTrajectory u v
        (fun t ↦ (T t : ℂ)))
    (t₀ : ℝ) (hu : u t₀ = 0) :
    ∀ t : ℝ,
      T t =
        horizontalLine
          ((T t₀).re - (v t₀).re * t₀)
          (T t₀).im (v t₀).re (T t₀).im_pos t := by
  have haffine :
      ∀ t : ℝ,
        (T t : ℂ) =
          (T t₀ : ℂ) +
            v t₀ * (((t - t₀ : ℝ) : ℝ) : ℂ) :=
    h.T_eq_affine_of_u_eq_zero_at t₀ hu
  have hvim : (v t₀).im = 0 :=
    affineUpperHalfPlane_velocity_im_eq_zero
      T t₀ (v t₀) haffine
  intro t
  apply UpperHalfPlane.coe_injective
  apply Complex.ext
  · have hre := congrArg Complex.re (haffine t)
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero,
      UpperHalfPlane.coe_re] at hre
    simp only [UpperHalfPlane.coe_re, horizontalLine_re]
    rw [hre]
    ring
  · have him := congrArg Complex.im (haffine t)
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, hvim, mul_zero,
      horizontalLine_im, UpperHalfPlane.coe_im] at him ⊢
    exact him

/-- **Global Riccati geometry, non-affine branch.**  If the finite
endpoint lies on the real axis, then the entire upper-half-plane
trajectory lies on the Euclidean circle of positive radius

```
             |T(t₀)-ξ|² / (2 Im T(t₀))
```

whose centre is `ξ+iR`.  This circle is tangent to the real axis at
`ξ`; hence it is precisely a horocycle based at `ξ`. -/
theorem riccatiLift_mem_horocycle_of_endpoint_im_eq_zero
    {u v : ℝ → ℂ} {T : ℝ → ℍ}
    (h :
      IsRiccatiJetTrajectory u v
        (fun t ↦ (T t : ℂ)))
    (t₀ : ℝ) (hu : u t₀ ≠ 0)
    (hendpoint :
      (IsRiccatiJetTrajectory.fractionalLinearEndpoint
        u v (fun t ↦ (T t : ℂ)) t₀).im = 0) :
    let ξ :=
      IsRiccatiJetTrajectory.fractionalLinearEndpoint
        u v (fun t ↦ (T t : ℂ)) t₀
    let R := horocycleRadius (T t₀ : ℂ) ξ
    0 < R ∧
      ∀ t : ℝ,
        Complex.normSq
            ((T t : ℂ) - horocycleCenter (T t₀ : ℂ) ξ) =
          R ^ 2 := by
  dsimp only
  let ξ :=
    IsRiccatiJetTrajectory.fractionalLinearEndpoint
      u v (fun t ↦ (T t : ℂ)) t₀
  have hR : 0 < horocycleRadius (T t₀ : ℂ) ξ :=
    horocycleRadius_pos (T t₀ : ℂ) ξ (T t₀).im_pos hendpoint
  refine ⟨hR, ?_⟩
  intro t
  apply normSq_sub_horocycleCenter_eq_sq
    (T t₀ : ℂ) ξ (T t : ℂ) (T t₀).im_pos hendpoint
  exact
    h.fractionalLinear_horocycle_invariant
      t₀ t hu (fun q ↦ (T q).im_pos) hendpoint

end

end HGAS.Modular
