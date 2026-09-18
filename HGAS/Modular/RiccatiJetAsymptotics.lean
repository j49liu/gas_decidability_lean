import HGAS.Modular.RiccatiJetIntegration
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.SpecificLimits.RCLike
import Mathlib.Topology.Bornology.BoundedOperation
import Mathlib.Tactic

/-!
# The two global alternatives for a Riccati jet

The exact integration theorem in `RiccatiJetIntegration` writes every
globally defined solution of

```
                  u' = -u²,   v' = -2uv,   T' = v
```

relative to a base time `t₀` in terms of

```
                  d(t) = 1 + u(t₀)(t-t₀).
```

This file records the elementary global dichotomy and its asymptotics.

* If `u(t₀)=0`, then `u` vanishes identically, `v` is constant, and `T`
  is an affine line.
* If `u(t₀)≠0`, then `d(t)⁻¹`, `u(t)`, and `v(t)` tend to zero as
  `t → +∞`, while

```
                  T(t) → T(t₀) + v(t₀)/u(t₀).
```

The proof of the second alternative is deliberately topological rather
than coordinate-heavy.  The real ray `t-t₀`, viewed in `ℂ`, tends to the
cobounded filter.  Multiplication by a nonzero complex number and
translation preserve that filter, and inversion carries it to zero.

We also prove a geometric fact used later: an affine complex line which
lies in the upper half-plane for every real time must have real velocity.
-/

namespace HGAS.Modular

open Filter Topology
open UpperHalfPlane hiding I

noncomputable section

namespace IsRiccatiJetTrajectory

variable {u v T : ℝ → ℂ}

/-- The prospective finite endpoint of the fractional-linear branch. -/
def fractionalLinearEndpoint
    (u v T : ℝ → ℂ) (t₀ : ℝ) : ℂ :=
  T t₀ + v t₀ / u t₀

/-- The real displacement `t-t₀`, embedded in `ℂ`, escapes every bounded
set as `t → +∞`. -/
theorem tendsto_complexDisplacement_cobounded (t₀ : ℝ) :
    Tendsto
      (fun t : ℝ ↦ (((t - t₀ : ℝ) : ℝ) : ℂ))
      atTop (Bornology.cobounded ℂ) := by
  have hreal :
      Tendsto (fun t : ℝ ↦ t - t₀) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-t₀) tendsto_id
  exact
    (RCLike.tendsto_ofReal_atTop_cobounded ℂ).comp hreal

/-- On the non-affine branch, the inverse affine denominator tends to
zero. -/
theorem tendsto_denominator_inv_atTop
    (t₀ : ℝ) (hu : u t₀ ≠ 0) :
    Tendsto
      (fun t ↦ (denominator u t₀ t)⁻¹)
      atTop (𝓝 0) := by
  have hmul :
      Tendsto
        (fun t : ℝ ↦
          u t₀ * (((t - t₀ : ℝ) : ℝ) : ℂ))
        atTop (Bornology.cobounded ℂ) :=
    (Filter.tendsto_mul_left_cobounded hu).comp
      (tendsto_complexDisplacement_cobounded t₀)
  have hadd :
      Tendsto
        (fun t : ℝ ↦
          1 + u t₀ * (((t - t₀ : ℝ) : ℝ) : ℂ))
        atTop (Bornology.cobounded ℂ) :=
    (tendsto_const_add_cobounded (1 : ℂ)).comp hmul
  exact
    Filter.tendsto_inv₀_cobounded.comp
      (by simpa only [denominator] using hadd)

/-- On the non-affine branch, the Riccati coordinate tends to zero. -/
theorem u_tendsto_zero_atTop
    (h : IsRiccatiJetTrajectory u v T)
    (t₀ : ℝ) (hu : u t₀ ≠ 0) :
    Tendsto u atTop (𝓝 0) := by
  have hinv :
      Tendsto
        (fun t ↦ (denominator u t₀ t)⁻¹)
        atTop (𝓝 0) :=
    tendsto_denominator_inv_atTop t₀ hu
  have hlim :
      Tendsto
        (fun t ↦ u t₀ * (denominator u t₀ t)⁻¹)
        atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℝ ↦ u t₀) atTop (𝓝 (u t₀))).mul hinv
  apply hlim.congr'
  filter_upwards with t
  rw [h.u_eq_div_denominator t₀ t, div_eq_mul_inv]

/-- On the non-affine branch, the scale velocity tends to zero. -/
theorem v_tendsto_zero_atTop
    (h : IsRiccatiJetTrajectory u v T)
    (t₀ : ℝ) (hu : u t₀ ≠ 0) :
    Tendsto v atTop (𝓝 0) := by
  have hinv :
      Tendsto
        (fun t ↦ (denominator u t₀ t)⁻¹)
        atTop (𝓝 0) :=
    tendsto_denominator_inv_atTop t₀ hu
  have hlim :
      Tendsto
        (fun t ↦
          v t₀ * (denominator u t₀ t)⁻¹ ^ 2)
        atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℝ ↦ v t₀) atTop (𝓝 (v t₀))).mul
          (hinv.pow 2)
  apply hlim.congr'
  filter_upwards with t
  rw [h.v_eq_div_denominator_sq t₀ t, div_eq_mul_inv,
    inv_pow]

/-- On the non-affine branch, the lifted parameter has the finite
fractional-linear endpoint `T(t₀)+v(t₀)/u(t₀)`. -/
theorem T_tendsto_fractionalLinearEndpoint_atTop
    (h : IsRiccatiJetTrajectory u v T)
    (t₀ : ℝ) (hu : u t₀ ≠ 0) :
    Tendsto T atTop
      (𝓝 (fractionalLinearEndpoint u v T t₀)) := by
  have hinv :
      Tendsto
        (fun t ↦ (denominator u t₀ t)⁻¹)
        atTop (𝓝 0) :=
    tendsto_denominator_inv_atTop t₀ hu
  have hvanish :
      Tendsto
        (fun t ↦
          (v t₀ / u t₀) *
            (denominator u t₀ t)⁻¹)
        atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℝ ↦ v t₀ / u t₀)
          atTop (𝓝 (v t₀ / u t₀))).mul hinv
  have hlimit :
      Tendsto
        (fun t ↦
          fractionalLinearEndpoint u v T t₀ -
            (v t₀ / u t₀) *
              (denominator u t₀ t)⁻¹)
        atTop
        (𝓝 (fractionalLinearEndpoint u v T t₀)) := by
    simpa using
      (tendsto_const_nhds :
        Tendsto
          (fun _ : ℝ ↦
            fractionalLinearEndpoint u v T t₀)
          atTop
          (𝓝 (fractionalLinearEndpoint u v T t₀))).sub
        hvanish
  apply hlimit.congr'
  filter_upwards with t
  rw [h.T_eq_fractionalLinearCandidate t₀ t]
  unfold fractionalLinearCandidate fractionalLinearEndpoint
  field_simp [hu, h.denominator_ne_zero t₀ t]
  simp only [denominator]
  ring

/-- If the Riccati coordinate vanishes at one base time, it vanishes
everywhere. -/
theorem u_eq_zero_of_eq_zero_at
    (h : IsRiccatiJetTrajectory u v T)
    (t₀ : ℝ) (hu : u t₀ = 0) :
    ∀ t, u t = 0 := by
  intro t
  rw [h.u_eq_div_denominator t₀ t, hu]
  simp

/-- On the affine branch, the velocity `v` is constant. -/
theorem v_eq_base_of_u_eq_zero_at
    (h : IsRiccatiJetTrajectory u v T)
    (t₀ : ℝ) (hu : u t₀ = 0) :
    ∀ t, v t = v t₀ := by
  intro t
  rw [h.v_eq_div_denominator_sq t₀ t]
  simp [denominator, hu]

/-- On the affine branch, `T` is exactly a complex affine line. -/
theorem T_eq_affine_of_u_eq_zero_at
    (h : IsRiccatiJetTrajectory u v T)
    (t₀ : ℝ) (hu : u t₀ = 0) :
    ∀ t,
      T t =
        T t₀ + v t₀ * (((t - t₀ : ℝ) : ℝ) : ℂ) := by
  intro t
  rw [h.T_eq_fractionalLinear t₀ t]
  simp [hu]

end IsRiccatiJetTrajectory

/-- An affine complex line contained in the upper half-plane at every
real time has zero imaginary velocity.  Evaluating at the time at which a
nonhorizontal affine line would meet the real axis gives the contradiction
directly. -/
theorem affineUpperHalfPlane_velocity_im_eq_zero
    (T : ℝ → ℍ) (t₀ : ℝ) (w : ℂ)
    (hT : ∀ t,
      (T t : ℂ) =
        (T t₀ : ℂ) +
          w * (((t - t₀ : ℝ) : ℝ) : ℂ)) :
    w.im = 0 := by
  by_contra hw
  let t : ℝ := t₀ - (T t₀).im / w.im
  have him := congrArg Complex.im (hT t)
  have himzero : (T t).im = 0 := by
    rw [← UpperHalfPlane.coe_im]
    rw [him]
    simp only [Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      UpperHalfPlane.coe_im]
    dsimp only [t]
    field_simp [hw]
    ring
  exact (ne_of_gt (T t).im_pos) himzero

/-- Every finite complex limit of points in the open upper half-plane lies
in its closure.  This tiny lemma supplies the other inequality in the
recurrent endpoint theorem. -/
theorem upperHalfPlane_limit_im_nonneg
    {α : Type*} [TopologicalSpace α]
    {l : Filter α} [l.NeBot]
    (T : α → ℍ) (L : ℂ)
    (hT :
      Tendsto (fun x ↦ (T x : ℂ)) l (𝓝 L)) :
    0 ≤ L.im := by
  have him :
      Tendsto (fun x ↦ (T x).im) l (𝓝 L.im) := by
    simpa only [UpperHalfPlane.coe_im] using
      Complex.continuous_im.continuousAt.tendsto.comp hT
  exact ge_of_tendsto' him fun x ↦ (T x).im_pos.le

end

end HGAS.Modular
