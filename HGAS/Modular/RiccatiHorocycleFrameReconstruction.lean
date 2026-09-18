import HGAS.Modular.GammaTwoFrameQuotient
import HGAS.Modular.HorizontalTrajectory
import HGAS.Modular.RiccatiJetGeometry
import Mathlib.Tactic

/-!
# Reconstructing an exact frame horocycle from a Riccati lift

The geometric statement that a curve lies on a Euclidean circle tangent
to the real axis is not, by itself, enough to invoke a horocycle
equidistribution theorem: the curve could traverse that circle with an
arbitrary time change.  The Riccati equations retain the missing
parametrization.

This file proves the exact statement needed later.  If

```
  u' = -u²,       v' = -2uv,       T' = v
```

is a globally defined Riccati jet in the upper half-plane, `u(t₀) ≠ 0`,
and its finite endpoint is real, then there are a real frame `g` and a
nonzero real speed `σ` such that

```
                  T(t) = (g u(σt)) · i
```

for every real `t`.  Consequently its class in
`Γ(2) \ SL(2,ℝ)` is literally a scaled right-horocycle orbit.

The proof first applies the real Möbius transformation
`z ↦ -1/(z-ξ)`, which sends the tangency point `ξ` to infinity.  The
fractional-linear Riccati formula then becomes an affine line.  Since that
line stays in the upper half-plane for all real time, its velocity is
real, so it is a horizontal line with its original time parameter.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I

noncomputable section

/-- The determinant-one real matrix inducing `z ↦ -1/(z-ξ)`. -/
def boundaryInversionFrame (ξ : ℝ) : RealModularFrame :=
  ⟨!![0, -1; 1, -ξ], by
    simp [Matrix.det_fin_two]⟩

/-- The explicit Möbius formula for `boundaryInversionFrame`. -/
theorem coe_boundaryInversionFrame_smul
    (ξ : ℝ) (z : ℍ) :
    ((boundaryInversionFrame ξ • z : ℍ) : ℂ) =
      -1 / ((z : ℂ) - (ξ : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [boundaryInversionFrame, sub_eq_add_neg]

/-- The standard positive-affine frame based at `x+iy`. -/
def horizontalBaseFrame
    (x y : ℝ) (hy : 0 < y) : RealModularFrame :=
  (horizontalLine x y 0 hy 0).toSL2R

/-- Right upper-unipotent motion of the standard frame is a horizontal
line, with the exact conversion between frame time and Euclidean speed. -/
theorem horizontalBaseFrame_upperUnipotent_basePoint
    (x y s t : ℝ) (hy : 0 < y) :
    realModularFrameBasePoint
        (horizontalBaseFrame x y hy *
          upperUnipotent ((s / y) * t)) =
      horizontalLine x y s hy t := by
  apply UpperHalfPlane.coe_injective
  simp only [realModularFrameBasePoint, mul_smul]
  rw [UpperHalfPlane.coe_specialLinearGroup_apply,
    UpperHalfPlane.coe_specialLinearGroup_apply]
  apply Complex.ext <;>
    simp [horizontalBaseFrame, horizontalLine,
      UpperHalfPlane.toSL2R_apply, upperUnipotent] <;>
    field_simp [ne_of_gt hy]
  all_goals rw [Real.sq_sqrt hy.le]
  all_goals ring

/-- Exact frame reconstruction for the non-affine, real-endpoint branch of
a global Riccati trajectory. -/
theorem IsRiccatiJetTrajectory.exists_exact_scaledHorocycleFrame
    {u v : ℝ → ℂ} {T : ℝ → ℍ}
    (h :
      IsRiccatiJetTrajectory u v
        (fun t ↦ (T t : ℂ)))
    (t₀ : ℝ) (hu : u t₀ ≠ 0)
    (hendpoint :
      (IsRiccatiJetTrajectory.fractionalLinearEndpoint
        u v (fun t ↦ (T t : ℂ)) t₀).im = 0) :
    ∃ g : RealModularFrame, ∃ σ : ℝ,
      σ ≠ 0 ∧
      ∀ t : ℝ,
        T t =
          realModularFrameBasePoint
            (g * upperUnipotent (σ * t)) := by
  let ξ : ℂ :=
    IsRiccatiJetTrajectory.fractionalLinearEndpoint
      u v (fun t ↦ (T t : ℂ)) t₀
  let A : ℂ := v t₀ / u t₀
  have hshape₀ :
      (T t₀ : ℂ) - ξ = -A := by
    rw [h.T_sub_fractionalLinearEndpoint t₀ t₀ hu,
      IsRiccatiJetTrajectory.denominator_at_base, div_one]
  have hA : A ≠ 0 := by
    intro hAzero
    have hTξ : (T t₀ : ℂ) = ξ := by
      apply sub_eq_zero.mp
      rw [hshape₀, hAzero, neg_zero]
    have him := congrArg Complex.im hTξ
    simp only [ξ, hendpoint] at him
    exact (ne_of_gt (T t₀).im_pos) him
  let M : RealModularFrame := boundaryInversionFrame ξ.re
  let S : ℝ → ℍ := fun t ↦ M • T t
  have hξreal : (ξ.re : ℂ) = ξ := by
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using hendpoint.symm
  have hScoefficient :
      ∀ t : ℝ,
        (S t : ℂ) =
          (S t₀ : ℂ) +
            (u t₀ / A) *
              (((t - t₀ : ℝ) : ℝ) : ℂ) := by
    intro t
    have hshape :
        (T t : ℂ) - ξ =
          -A /
            IsRiccatiJetTrajectory.denominator u t₀ t := by
      simpa only [ξ, A] using
        h.T_sub_fractionalLinearEndpoint t₀ t hu
    have hden :
        IsRiccatiJetTrajectory.denominator u t₀ t ≠ 0 :=
      h.denominator_ne_zero t₀ t
    simp only [S, M, coe_boundaryInversionFrame_smul,
      hξreal]
    rw [hshape, hshape₀]
    field_simp [hA, hden]
    rfl
  have hvelocityReal : (u t₀ / A).im = 0 :=
    affineUpperHalfPlane_velocity_im_eq_zero
      S t₀ (u t₀ / A) hScoefficient
  let speed : ℝ := (u t₀ / A).re
  have hvelocity :
      u t₀ / A = (speed : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using hvelocityReal
  let x : ℝ := (S t₀).re - speed * t₀
  let y : ℝ := (S t₀).im
  have hy : 0 < y := (S t₀).im_pos
  have hS :
      ∀ t : ℝ, S t = horizontalLine x y speed hy t := by
    intro t
    apply UpperHalfPlane.coe_injective
    apply Complex.ext
    · have hre := congrArg Complex.re (hScoefficient t)
      simp only [hvelocity, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero, UpperHalfPlane.coe_re] at hre
      change (S t).re = x + speed * t
      dsimp only [x]
      rw [hre]
      ring
    · have him := congrArg Complex.im (hScoefficient t)
      simp only [hvelocity, Complex.add_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        add_zero, UpperHalfPlane.coe_im] at him
      change (S t).im = y
      dsimp only [y]
      simpa using him
  have hspeed : speed ≠ 0 := by
    intro hs
    apply hu
    have hquot : u t₀ / A = 0 := by
      rw [hvelocity, hs]
      norm_num
    exact (div_eq_zero_iff.mp hquot).resolve_right hA
  let σ : ℝ := speed / y
  have hσ : σ ≠ 0 := div_ne_zero hspeed (ne_of_gt hy)
  let g : RealModularFrame :=
    M⁻¹ * horizontalBaseFrame x y hy
  refine ⟨g, σ, hσ, ?_⟩
  intro t
  have hbase :
      realModularFrameBasePoint
          (horizontalBaseFrame x y hy *
            upperUnipotent (σ * t)) =
        S t := by
    rw [hS]
    exact
      horizontalBaseFrame_upperUnipotent_basePoint
        x y speed t hy
  apply smul_left_cancel M
  rw [show M • T t = S t by rfl]
  rw [show
      M • realModularFrameBasePoint
          (g * upperUnipotent (σ * t)) =
        realModularFrameBasePoint
          (M * (g * upperUnipotent (σ * t))) by
      simp only [realModularFrameBasePoint, mul_smul]]
  have hframe :
      M * (g * upperUnipotent (σ * t)) =
        horizontalBaseFrame x y hy *
          upperUnipotent (σ * t) := by
    dsimp only [g]
    group
  rw [hframe]
  exact hbase.symm

/-- Quotient form of the exact reconstruction: the lifted modular curve
is the base projection of a literal scaled `Γ(2)` horocycle orbit. -/
theorem IsRiccatiJetTrajectory.exists_exact_scaledGammaTwoHorocycle
    {u v : ℝ → ℂ} {T : ℝ → ℍ}
    (h :
      IsRiccatiJetTrajectory u v
        (fun t ↦ (T t : ℂ)))
    (t₀ : ℝ) (hu : u t₀ ≠ 0)
    (hendpoint :
      (IsRiccatiJetTrajectory.fractionalLinearEndpoint
        u v (fun t ↦ (T t : ℂ)) t₀).im = 0) :
    ∃ q : GammaTwoFrameQuotient, ∃ σ : ℝ,
      σ ≠ 0 ∧
      ∀ t : ℝ,
        lambdaModularQuotientMk (T t) =
          gammaTwoFrameBaseProjection
            (scaledGammaTwoHorocycleFlow σ t q) := by
  obtain ⟨g, σ, hσ, hg⟩ :=
    h.exists_exact_scaledHorocycleFrame t₀ hu hendpoint
  refine
    ⟨gammaTwoFrameQuotientMk g, σ, hσ, ?_⟩
  intro t
  rw [hg t]
  rfl

end

end HGAS.Modular
