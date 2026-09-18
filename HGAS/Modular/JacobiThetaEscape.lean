import HGAS.Analysis.AffineLatticeReduction
import HGAS.Analysis.AffineComplexExponential
import HGAS.Analysis.ComplexLevelTwoReduction
import HGAS.Dynamics.Recurrence
import HGAS.Modular.JacobiThetaHorizontalReduction
import Mathlib.Tactic

/-!
# Quantitative escape from a level-two Jacobi lattice

This module packages the analytic heart of equation (8.16), after lattice
reduction has supplied an integer index with nonzero linear slope.

Suppose

```
  ξ(t) = ξ₀(t) + 2 m(t) + 2 n(t) τ(t),
  Im τ(t) = γ > 0,
  |Im ξ₀(t)| ≤ γ,
  n(t) = a t + O(1),       a ≠ 0.
```

The exact doubled-period law gives a multiplier with logarithmic modulus

```
  4 π γ n(t)² + 4 π n(t) Im ξ₀(t)
      ≥ 4 π γ n(t)² - 4 π γ |n(t)|.
```

Thus the positive quadratic term beats both this linear loss and any
additional exponential scale loss `exp (-scale * (1+t))`.  A uniform
positive lower bound for the reduced theta vector then forces the original
scaled theta vector to leave every bounded set.

The reusable core theorem takes the reduced theta lower bound as an
explicit hypothesis.  The final reduced-coordinate corollary discharges
that hypothesis internally from the global no-common-zero theorem and
compactness of the standard reduced box.
-/

namespace HGAS.Modular

open Filter
open Complex Real
open UpperHalfPlane hiding I

noncomputable section

/-- Exact theta-multiplier escape from an already reduced level-two lattice.

The hypotheses deliberately separate:

* the exact lattice identity (`hξ`);
* compact reduced-coordinate estimates (`hτim`, `hξ₀im`, `hbase`);
* the asymptotic lattice-index estimate (`hn`);
* a possible common-scale loss (`hscale`).

This makes the result reusable independently of how a particular flow
constructs its lattice reduction. -/
theorem scaled_jacobiThetaVector_tendsto_atTop_of_levelTwo_reduction
    {τ ξ ξ₀ S : ℝ → ℂ}
    {m n : ℝ → ℤ}
    {γ slope err lower scale : ℝ}
    (hγ : 0 < γ)
    (hslope : slope ≠ 0)
    (hlower : 0 < lower)
    (hτim : ∀ t, (τ t).im = γ)
    (hξ :
      ∀ t,
        ξ t =
          ξ₀ t + 2 * (m t : ℂ) +
            2 * (n t : ℂ) * τ t)
    (hξ₀im : ∀ t, |(ξ₀ t).im| ≤ γ)
    (hbase :
      ∀ t,
        lower ≤
          ‖jacobiThetaVector (ξ₀ t) (τ t)‖)
    (hn :
      ∀ᶠ t in atTop,
        |(n t : ℝ) - slope * t| ≤ err)
    (hscale :
      ∀ᶠ t in atTop,
        Real.exp (-scale * (1 + t)) ≤ ‖S t‖) :
    Tendsto
      (fun t : ℝ ↦
        ‖S t • jacobiThetaVector (ξ t) (τ t)‖)
      atTop atTop := by
  let exponent : ℝ → ℝ :=
    fun t ↦
      4 * π * γ * (n t : ℝ) ^ 2 -
        4 * π * γ * |(n t : ℝ)| -
        scale * (1 + t)
  have hexponent :
      Tendsto exponent atTop atTop := by
    simpa only [exponent] using
      HGAS.Analysis.affine_boundedError_quadratic_escape
        (n := fun t ↦ (n t : ℝ))
        (a := slope)
        (gamma := 4 * π * γ)
        (loss := 4 * π * γ)
        (scale := scale)
        (err := err)
        hslope
        (by positivity)
        (by positivity)
        hn
  have hlowerTend :
      Tendsto
        (fun t ↦ lower * Real.exp (exponent t))
        atTop atTop := by
    simpa only [Function.comp_apply] using
      (Real.tendsto_exp_atTop.comp hexponent).const_mul_atTop
        hlower
  apply Filter.tendsto_atTop_mono' atTop _ hlowerTend
  filter_upwards [hscale] with t htScale
  let nr : ℝ := n t
  let multiplierExponent : ℝ :=
    4 * π * nr ^ 2 * (τ t).im +
      4 * π * nr * (ξ₀ t).im
  have hlinear :
      -(|nr| * γ) ≤ nr * (ξ₀ t).im := by
    apply neg_le_of_abs_le
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (hξ₀im t) (abs_nonneg nr)
  have hmultiplier :
      4 * π * γ * nr ^ 2 -
          4 * π * γ * |nr| ≤
        multiplierExponent := by
    dsimp [multiplierExponent, nr]
    rw [hτim t]
    have hfourpi : 0 < 4 * π := by positivity
    have hlinearScaled :=
      mul_le_mul_of_nonneg_left hlinear hfourpi.le
    nlinarith
  have hExpMultiplier :
      Real.exp
          (4 * π * γ * nr ^ 2 -
            4 * π * γ * |nr|) ≤
        Real.exp multiplierExponent :=
    Real.exp_le_exp.mpr hmultiplier
  have hproduct :
      lower * Real.exp (exponent t) ≤
        ‖S t‖ *
          (Real.exp multiplierExponent *
            ‖jacobiThetaVector (ξ₀ t) (τ t)‖) := by
    rw [show
        exponent t =
          -scale * (1 + t) +
            (4 * π * γ * nr ^ 2 -
              4 * π * γ * |nr|) by
          dsimp [exponent, nr]
          ring,
      Real.exp_add]
    calc
      lower *
          (Real.exp (-scale * (1 + t)) *
            Real.exp
              (4 * π * γ * nr ^ 2 -
                4 * π * γ * |nr|)) =
          Real.exp (-scale * (1 + t)) *
            Real.exp
              (4 * π * γ * nr ^ 2 -
                4 * π * γ * |nr|) *
            lower := by ring
      _ ≤
          ‖S t‖ * Real.exp multiplierExponent *
            ‖jacobiThetaVector (ξ₀ t) (τ t)‖ := by
        have hfirst :
            Real.exp (-scale * (1 + t)) *
                Real.exp
                  (4 * π * γ * nr ^ 2 -
                    4 * π * γ * |nr|) ≤
              ‖S t‖ * Real.exp multiplierExponent :=
          mul_le_mul htScale hExpMultiplier
            (Real.exp_pos _).le (norm_nonneg _)
        exact mul_le_mul hfirst (hbase t)
          hlower.le
          (mul_nonneg (norm_nonneg _)
            (Real.exp_pos _).le)
      _ =
          ‖S t‖ *
            (Real.exp multiplierExponent *
              ‖jacobiThetaVector (ξ₀ t) (τ t)‖) := by
        ring
  rw [hξ t, norm_smul,
    norm_jacobiThetaVector_add_levelTwo_lattice]
  simpa only [multiplierExponent, nr] using hproduct

/-- The preceding escape theorem with the lattice index chosen canonically
by nearest-integer reduction of `Im ξ / (2γ)`.

Only the horizontal real-period index `m(t)` remains as input.  The reduced
imaginary-coordinate bound and the affine estimate for the vertical index
are consequences, not hypotheses. -/
theorem scaled_jacobiThetaVector_tendsto_atTop_of_nearest_reduction
    {τ ξ ξ₀ S : ℝ → ℂ}
    {m : ℝ → ℤ}
    {γ verticalSlope err lower scale : ℝ}
    (hγ : 0 < γ)
    (hverticalSlope : verticalSlope ≠ 0)
    (hlower : 0 < lower)
    (hτim : ∀ t, (τ t).im = γ)
    (hξ :
      ∀ t,
        ξ t =
          ξ₀ t + 2 * (m t : ℂ) +
            2 *
              (HGAS.Analysis.verticalLatticeIndex
                γ (fun s ↦ (ξ s).im) t : ℂ) *
              τ t)
    (hbase :
      ∀ t,
        lower ≤
          ‖jacobiThetaVector (ξ₀ t) (τ t)‖)
    (hξim :
      ∀ᶠ t in atTop,
        |(ξ t).im - verticalSlope * t| ≤ err)
    (hscale :
      ∀ᶠ t in atTop,
        Real.exp (-scale * (1 + t)) ≤ ‖S t‖) :
    Tendsto
      (fun t : ℝ ↦
        ‖S t • jacobiThetaVector (ξ t) (τ t)‖)
      atTop atTop := by
  let n : ℝ → ℤ :=
    fun t ↦
      HGAS.Analysis.verticalLatticeIndex
        γ (fun s ↦ (ξ s).im) t
  have hn :
      ∀ᶠ t in atTop,
        |(n t : ℝ) -
            (verticalSlope / (2 * γ)) * t| ≤
          (1 : ℝ) / 2 + err / (2 * γ) := by
    simpa only [n, HGAS.Analysis.verticalLatticeIndexReal] using
      HGAS.Analysis.verticalLatticeIndexReal_boundedError
        hγ hξim
  have hξ₀im : ∀ t, |(ξ₀ t).im| ≤ γ := by
    intro t
    have hremainder :=
      HGAS.Analysis.abs_verticalLatticeRemainder_le
        hγ (fun s ↦ (ξ s).im) t
    have himaginary :
        (ξ₀ t).im =
          (ξ t).im -
            2 *
              HGAS.Analysis.verticalLatticeIndexReal
                γ (fun s ↦ (ξ s).im) t *
              γ := by
      have heq :
          (ξ t).im =
            (ξ₀ t).im +
              2 *
                (HGAS.Analysis.verticalLatticeIndex
                  γ (fun s ↦ (ξ s).im) t : ℝ) *
                γ := by
        simpa [hτim t] using
          congr_arg Complex.im (hξ t)
      dsimp [HGAS.Analysis.verticalLatticeIndexReal]
      linarith
    rw [himaginary]
    exact hremainder
  apply
    scaled_jacobiThetaVector_tendsto_atTop_of_levelTwo_reduction
      (m := m)
      (n := n)
      (γ := γ)
      (slope := verticalSlope / (2 * γ))
      (err := (1 : ℝ) / 2 + err / (2 * γ))
      (lower := lower)
      (scale := scale)
      hγ
      (div_ne_zero hverticalSlope (by positivity))
      hlower
      hτim
      (by simpa only [n] using hξ)
      hξ₀im hbase hn hscale

/-- Fully analytic escape theorem on the standard reduced compact domain.

Global theta nonvanishing and compactness now supply the positive lower
bound internally.  The remaining hypotheses are exactly the concrete
lattice-reduction, affine-slope, and scale estimates that must be read off
from a classified Bloch trajectory. -/
theorem scaled_jacobiThetaVector_tendsto_atTop_of_reduced_coordinates
    {τ : ℝ → ℍ} {ξ ξ₀ S : ℝ → ℂ}
    {m : ℝ → ℤ}
    {γ verticalSlope err scale : ℝ}
    (hγ : 0 < γ)
    (hverticalSlope : verticalSlope ≠ 0)
    (hτim : ∀ t, (τ t).im = γ)
    (hτre : ∀ t, |(τ t).re| ≤ 1)
    (hξ :
      ∀ t,
        ξ t =
          ξ₀ t + 2 * (m t : ℂ) +
            2 *
              (HGAS.Analysis.verticalLatticeIndex
                γ (fun s ↦ (ξ s).im) t : ℂ) *
              (τ t : ℂ))
    (hξ₀re : ∀ t, |(ξ₀ t).re| ≤ 1)
    (hξ₀im : ∀ t, |(ξ₀ t).im| ≤ γ)
    (hξim :
      ∀ᶠ t in atTop,
        |(ξ t).im - verticalSlope * t| ≤ err)
    (hscale :
      ∀ᶠ t in atTop,
        Real.exp (-scale * (1 + t)) ≤ ‖S t‖) :
    Tendsto
      (fun t : ℝ ↦
        ‖S t •
          jacobiThetaVector (ξ t) (τ t : ℂ)‖)
      atTop atTop := by
  obtain ⟨lower, hlower, hLowerBound⟩ :=
    exists_uniform_pos_le_norm_jacobiThetaVector_reduced_global
      γ hγ
  apply
    scaled_jacobiThetaVector_tendsto_atTop_of_nearest_reduction
      (τ := fun t ↦ (τ t : ℂ))
      (ξ := ξ) (ξ₀ := ξ₀) (S := S) (m := m)
      (γ := γ) (verticalSlope := verticalSlope)
      (err := err) (lower := lower) (scale := scale)
      hγ hverticalSlope hlower
      hτim hξ
  · intro t
    exact hLowerBound (ξ₀ t) (τ t)
      (hξ₀re t) (hξ₀im t) (hτre t) (hτim t)
  · exact hξim
  · exact hscale

/-- Escape on a fixed-height horizontal line with no hypothesis on
`Re τ`.  Horizontal level-two norm invariance reduces `τ` internally,
while the elliptic coordinate is still reduced by its two lattice
indices. -/
theorem scaled_jacobiThetaVector_tendsto_atTop_of_fixedHeight_coordinates
    {τ : ℝ → ℍ} {ξ ξ₀ S : ℝ → ℂ}
    {m : ℝ → ℤ}
    {γ verticalSlope err scale : ℝ}
    (hγ : 0 < γ)
    (hverticalSlope : verticalSlope ≠ 0)
    (hτim : ∀ t, (τ t).im = γ)
    (hξ :
      ∀ t,
        ξ t =
          ξ₀ t + 2 * (m t : ℂ) +
            2 *
              (HGAS.Analysis.verticalLatticeIndex
                γ (fun s ↦ (ξ s).im) t : ℂ) *
              (τ t : ℂ))
    (hξ₀re : ∀ t, |(ξ₀ t).re| ≤ 1)
    (hξ₀im : ∀ t, |(ξ₀ t).im| ≤ γ)
    (hξim :
      ∀ᶠ t in atTop,
        |(ξ t).im - verticalSlope * t| ≤ err)
    (hscale :
      ∀ᶠ t in atTop,
        Real.exp (-scale * (1 + t)) ≤ ‖S t‖) :
    Tendsto
      (fun t : ℝ ↦
        ‖S t •
          jacobiThetaVector (ξ t) (τ t : ℂ)‖)
      atTop atTop := by
  obtain ⟨lower, hlower, hLowerBound⟩ :=
    exists_uniform_pos_le_norm_jacobiThetaVector_fixed_height
      γ hγ
  apply
    scaled_jacobiThetaVector_tendsto_atTop_of_nearest_reduction
      (τ := fun t ↦ (τ t : ℂ))
      (ξ := ξ) (ξ₀ := ξ₀) (S := S) (m := m)
      (γ := γ) (verticalSlope := verticalSlope)
      (err := err) (lower := lower) (scale := scale)
      hγ hverticalSlope hlower
      hτim hξ
  · intro t
    exact hLowerBound (ξ₀ t) (τ t)
      (hξ₀re t) (hξ₀im t) (hτim t)
  · exact hξim
  · exact hscale

/-- The complete canonical lattice-reduction form.  Both lattice indices
and the reduced elliptic coordinate are constructed internally from
`ξ(t)` and `τ(t)`. -/
theorem scaled_jacobiThetaVector_tendsto_atTop_of_fixedHeight
    {τ : ℝ → ℍ} {ξ S : ℝ → ℂ}
    {γ verticalSlope err scale : ℝ}
    (hγ : 0 < γ)
    (hverticalSlope : verticalSlope ≠ 0)
    (hτim : ∀ t, (τ t).im = γ)
    (hξim :
      ∀ᶠ t in atTop,
        |(ξ t).im - verticalSlope * t| ≤ err)
    (hscale :
      ∀ᶠ t in atTop,
        Real.exp (-scale * (1 + t)) ≤ ‖S t‖) :
    Tendsto
      (fun t : ℝ ↦
        ‖S t •
          jacobiThetaVector (ξ t) (τ t : ℂ)‖)
      atTop atTop := by
  let τc : ℝ → ℂ := fun t ↦ (τ t : ℂ)
  let ξ₀ : ℝ → ℂ :=
    fun t ↦
      HGAS.Analysis.complexLevelTwoReducedCoordinate
        γ ξ τc t
  let m : ℝ → ℤ :=
    fun t ↦
      HGAS.Analysis.complexLevelTwoHorizontalIndex
        γ ξ τc t
  apply
    scaled_jacobiThetaVector_tendsto_atTop_of_fixedHeight_coordinates
      (τ := τ) (ξ := ξ) (ξ₀ := ξ₀) (S := S)
      (m := m) (γ := γ)
      (verticalSlope := verticalSlope) (err := err)
      (scale := scale)
      hγ hverticalSlope hτim
  · intro t
    simpa only [ξ₀, m, τc,
      HGAS.Analysis.complexLevelTwoVerticalIndex] using
      HGAS.Analysis.complexLevelTwo_decomposition
        γ ξ τc t
  · intro t
    exact
      HGAS.Analysis.abs_complexLevelTwoReducedCoordinate_re_le_one
        γ ξ τc t
  · intro t
    exact
      HGAS.Analysis.abs_complexLevelTwoReducedCoordinate_im_le
        hγ ξ τc (by
          intro s
          exact hτim s) t
  · exact hξim
  · exact hscale

/-- The reduced-coordinate escape theorem when the common Bloch scale is
given explicitly as a nonzero constant times an affine complex
exponential.  The exponential lower bound is then a theorem rather than
an application-side hypothesis. -/
theorem scaled_affineExp_jacobiThetaVector_tendsto_atTop_of_reduced_coordinates
    {τ : ℝ → ℍ} {ξ ξ₀ : ℝ → ℂ}
    {m : ℝ → ℤ}
    {C a b : ℂ}
    {γ verticalSlope err : ℝ}
    (hγ : 0 < γ)
    (hverticalSlope : verticalSlope ≠ 0)
    (hC : C ≠ 0)
    (hτim : ∀ t, (τ t).im = γ)
    (hτre : ∀ t, |(τ t).re| ≤ 1)
    (hξ :
      ∀ t,
        ξ t =
          ξ₀ t + 2 * (m t : ℂ) +
            2 *
              (HGAS.Analysis.verticalLatticeIndex
                γ (fun s ↦ (ξ s).im) t : ℂ) *
              (τ t : ℂ))
    (hξ₀re : ∀ t, |(ξ₀ t).re| ≤ 1)
    (hξ₀im : ∀ t, |(ξ₀ t).im| ≤ γ)
    (hξim :
      ∀ᶠ t in atTop,
        |(ξ t).im - verticalSlope * t| ≤ err) :
    Tendsto
      (fun t : ℝ ↦
        ‖(C * Complex.exp (a + (t : ℂ) * b)) •
          jacobiThetaVector (ξ t) (τ t : ℂ)‖)
      atTop atTop := by
  apply
    scaled_jacobiThetaVector_tendsto_atTop_of_reduced_coordinates
      (τ := τ) (ξ := ξ) (ξ₀ := ξ₀)
      (S := fun t ↦
        C * Complex.exp (a + (t : ℂ) * b))
      (m := m) (γ := γ)
      (verticalSlope := verticalSlope) (err := err)
      (scale :=
        HGAS.Analysis.affineComplexExponentialLoss C a b)
      hγ hverticalSlope hτim hτre hξ hξ₀re hξ₀im hξim
  exact
    HGAS.Analysis.eventually_exp_neg_affineComplexExponentialLoss_one_add_le_norm
      hC

/-- Fully reduced Bloch escape with an affine-exponential scale and no
bound on the real part of the horizontal modular parameter. -/
theorem scaled_affineExp_jacobiThetaVector_tendsto_atTop_of_fixedHeight_coordinates
    {τ : ℝ → ℍ} {ξ ξ₀ : ℝ → ℂ}
    {m : ℝ → ℤ}
    {C a b : ℂ}
    {γ verticalSlope err : ℝ}
    (hγ : 0 < γ)
    (hverticalSlope : verticalSlope ≠ 0)
    (hC : C ≠ 0)
    (hτim : ∀ t, (τ t).im = γ)
    (hξ :
      ∀ t,
        ξ t =
          ξ₀ t + 2 * (m t : ℂ) +
            2 *
              (HGAS.Analysis.verticalLatticeIndex
                γ (fun s ↦ (ξ s).im) t : ℂ) *
              (τ t : ℂ))
    (hξ₀re : ∀ t, |(ξ₀ t).re| ≤ 1)
    (hξ₀im : ∀ t, |(ξ₀ t).im| ≤ γ)
    (hξim :
      ∀ᶠ t in atTop,
        |(ξ t).im - verticalSlope * t| ≤ err) :
    Tendsto
      (fun t : ℝ ↦
        ‖(C * Complex.exp (a + (t : ℂ) * b)) •
          jacobiThetaVector (ξ t) (τ t : ℂ)‖)
      atTop atTop := by
  apply
    scaled_jacobiThetaVector_tendsto_atTop_of_fixedHeight_coordinates
      (τ := τ) (ξ := ξ) (ξ₀ := ξ₀)
      (S := fun t ↦
        C * Complex.exp (a + (t : ℂ) * b))
      (m := m) (γ := γ)
      (verticalSlope := verticalSlope) (err := err)
      (scale :=
        HGAS.Analysis.affineComplexExponentialLoss C a b)
      hγ hverticalSlope hτim hξ hξ₀re hξ₀im hξim
  exact
    HGAS.Analysis.eventually_exp_neg_affineComplexExponentialLoss_one_add_le_norm
      hC

/-- Final analytic nonreal-Bloch escape interface: fixed modular height,
nonzero affine imaginary slope, and an explicit nonzero affine-exponential
common scale suffice.  All horizontal and elliptic lattice reductions and
all compact theta lower bounds are now internal. -/
theorem scaled_affineExp_jacobiThetaVector_tendsto_atTop_of_fixedHeight
    {τ : ℝ → ℍ} {ξ : ℝ → ℂ}
    {C a b : ℂ}
    {γ verticalSlope err : ℝ}
    (hγ : 0 < γ)
    (hverticalSlope : verticalSlope ≠ 0)
    (hC : C ≠ 0)
    (hτim : ∀ t, (τ t).im = γ)
    (hξim :
      ∀ᶠ t in atTop,
        |(ξ t).im - verticalSlope * t| ≤ err) :
    Tendsto
      (fun t : ℝ ↦
        ‖(C * Complex.exp (a + (t : ℂ) * b)) •
          jacobiThetaVector (ξ t) (τ t : ℂ)‖)
      atTop atTop := by
  apply
    scaled_jacobiThetaVector_tendsto_atTop_of_fixedHeight
      (τ := τ) (ξ := ξ)
      (S := fun t ↦
        C * Complex.exp (a + (t : ℂ) * b))
      (γ := γ) (verticalSlope := verticalSlope)
      (err := err)
      (scale :=
        HGAS.Analysis.affineComplexExponentialLoss C a b)
      hγ hverticalSlope hτim hξim
  exact
    HGAS.Analysis.eventually_exp_neg_affineComplexExponentialLoss_one_add_le_norm
      hC

/-- Every hypothesis of the nearest-reduction theorem also rules out
forward recurrence of the scaled theta-vector trajectory at every time. -/
theorem scaled_jacobiThetaVector_not_forwardRecurrentAt_of_nearest_reduction
    {τ ξ ξ₀ S : ℝ → ℂ}
    {m : ℝ → ℤ}
    {γ verticalSlope err lower scale t₀ : ℝ}
    (hγ : 0 < γ)
    (hverticalSlope : verticalSlope ≠ 0)
    (hlower : 0 < lower)
    (hτim : ∀ t, (τ t).im = γ)
    (hξ :
      ∀ t,
        ξ t =
          ξ₀ t + 2 * (m t : ℂ) +
            2 *
              (HGAS.Analysis.verticalLatticeIndex
                γ (fun s ↦ (ξ s).im) t : ℂ) *
              τ t)
    (hbase :
      ∀ t,
        lower ≤
          ‖jacobiThetaVector (ξ₀ t) (τ t)‖)
    (hξim :
      ∀ᶠ t in atTop,
        |(ξ t).im - verticalSlope * t| ≤ err)
    (hscale :
      ∀ᶠ t in atTop,
        Real.exp (-scale * (1 + t)) ≤ ‖S t‖) :
    ¬ HGAS.ForwardRecurrentAt
        (fun t : ℝ ↦
          S t • jacobiThetaVector (ξ t) (τ t))
        t₀ :=
  HGAS.not_forwardRecurrentAt_of_norm_tendsto_atTop
    (scaled_jacobiThetaVector_tendsto_atTop_of_nearest_reduction
      hγ hverticalSlope hlower hτim hξ hbase hξim hscale)

end

end HGAS.Modular
