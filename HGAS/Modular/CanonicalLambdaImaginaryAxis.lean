import HGAS.Modular.CanonicalLambdaDeck
import HGAS.Modular.ThetaAsymptotics
import Mathlib.Topology.Order.IntermediateValue

/-!
# Canonical lambda on the positive imaginary axis

This file develops an elementary global slice of the modular-lambda
uniformization theorem.  It uses only the defining theta series, their cusp
limits, and the already proved `S`-transformation.

For `y > 0`, all summands defining the three even theta constants at `iy`
are real.  Their fourth powers are therefore positive (zero-freeness rules
out equality).  Consequently

```
                 0 < Λ(iy) < 1.
```

At the top cusp `Λ(iy) → 0`; applying `S : iy ↦ i/y` gives the bottom-cusp
limit `Λ(iy) → 1`.  The intermediate value theorem then shows that every
real number strictly between zero and one has a canonical-lambda preimage
on the positive imaginary axis.

This is not yet the full complex uniformization theorem, but it supplies a
whole real seam of unconditional base points for analytic continuation and
path lifting.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real Filter Topology
open scoped Real Topology

noncomputable section

/-- The point `iy` of the upper half-plane, for `y > 0`. -/
def imaginaryAxisPoint (y : ℝ) (hy : 0 < y) : ℍ :=
  ⟨Complex.I * y, by simpa using hy⟩

@[simp]
theorem imaginaryAxisPoint_coe (y : ℝ) (hy : 0 < y) :
    (imaginaryAxisPoint y hy : ℂ) = Complex.I * y :=
  rfl

@[simp]
theorem imaginaryAxisPoint_im (y : ℝ) (hy : 0 < y) :
    (imaginaryAxisPoint y hy).im = y := by
  simp [imaginaryAxisPoint]

/-- Every summand of `θ₂(iy)` is real. -/
theorem theta₂Term_imaginaryAxis_im
    (n : ℤ) (y : ℝ) (hy : 0 < y) :
    (theta₂Term n (imaginaryAxisPoint y hy)).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  rw [theta₂Term, ← Complex.exp_conj]
  congr 1
  simp only [one_div, imaginaryAxisPoint_coe, map_mul,
    conj_ofReal, conj_I, mul_neg, map_pow, map_add,
    map_intCast, map_inv₀, neg_mul, neg_neg,
    mul_eq_mul_right_iff, mul_eq_mul_left_iff,
    mul_eq_zero, ofReal_eq_zero, pi_ne_zero,
    I_ne_zero, or_self, or_false, false_or]
  exact Or.inl (by simp only [map_ofNat])

/-- Every summand of `θ₃(iy)` is real. -/
theorem theta₃Term_imaginaryAxis_im
    (n : ℤ) (y : ℝ) (hy : 0 < y) :
    (theta₃Term n (imaginaryAxisPoint y hy)).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  rw [theta₃Term, ← Complex.exp_conj]
  congr 1
  simp [imaginaryAxisPoint]

/-- Every summand of `θ₄(iy)` is real. -/
theorem theta₄Term_imaginaryAxis_im
    (n : ℤ) (y : ℝ) (hy : 0 < y) :
    (theta₄Term n (imaginaryAxisPoint y hy)).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  rw [theta₄Term, map_mul, ← Complex.exp_conj]
  congr 1
  · calc
      (starRingEnd ℂ) ((-1 : ℂ) ^ n) =
          ((starRingEnd ℂ) (-1 : ℂ)) ^ n :=
        map_zpow₀ (starRingEnd ℂ) (-1 : ℂ) n
      _ = (-1 : ℂ) ^ n := by norm_num
  · congr 1
    simp [imaginaryAxisPoint]

/-- `θ₂` is real on the positive imaginary axis. -/
theorem theta₂_imaginaryAxis_im
    (y : ℝ) (hy : 0 < y) :
    (theta₂ (imaginaryAxisPoint y hy)).im = 0 := by
  rw [theta₂, Complex.im_tsum]
  · simp [theta₂Term_imaginaryAxis_im]
  · have h :=
      (summable_jacobiTheta₂_term_iff
        ((imaginaryAxisPoint y hy : ℂ) / 2)
        (imaginaryAxisPoint y hy)).mpr
          (imaginaryAxisPoint y hy).im_pos
    simpa only [theta₂Term_eq_jacobiTheta₂_term] using
      h.mul_left
        (cexp
          (π * I * (imaginaryAxisPoint y hy : ℂ) / 4))

/-- `θ₃` is real on the positive imaginary axis. -/
theorem theta₃_imaginaryAxis_im
    (y : ℝ) (hy : 0 < y) :
    (theta₃ (imaginaryAxisPoint y hy)).im = 0 := by
  rw [theta₃, Complex.im_tsum]
  · simp [theta₃Term_imaginaryAxis_im]
  · simpa only [theta₃Term_eq_jacobiTheta₂_term] using
      (summable_jacobiTheta₂_term_iff
        0 (imaginaryAxisPoint y hy)).mpr
          (imaginaryAxisPoint y hy).im_pos

/-- `θ₄` is real on the positive imaginary axis. -/
theorem theta₄_imaginaryAxis_im
    (y : ℝ) (hy : 0 < y) :
    (theta₄ (imaginaryAxisPoint y hy)).im = 0 := by
  rw [theta₄, Complex.im_tsum]
  · simp [theta₄Term_imaginaryAxis_im]
  · simpa only [theta₄Term_eq_jacobiTheta₂_term] using
      (summable_jacobiTheta₂_term_iff
        (1 / 2 : ℂ) (imaginaryAxisPoint y hy)).mpr
          (imaginaryAxisPoint y hy).im_pos

/-- On the imaginary axis `H₂` is the real fourth power of `Re θ₂`. -/
theorem H₂_imaginaryAxis_eq_ofReal
    (y : ℝ) (hy : 0 < y) :
    H₂ (imaginaryAxisPoint y hy) =
      ((theta₂ (imaginaryAxisPoint y hy)).re ^ 4 : ℝ) := by
  have hconj :
      (starRingEnd ℂ)
          (theta₂ (imaginaryAxisPoint y hy)) =
        theta₂ (imaginaryAxisPoint y hy) :=
    Complex.conj_eq_iff_im.mpr
      (theta₂_imaginaryAxis_im y hy)
  have hreal :
      ((theta₂ (imaginaryAxisPoint y hy)).re : ℂ) =
        theta₂ (imaginaryAxisPoint y hy) :=
    Complex.conj_eq_iff_re.mp hconj
  unfold H₂
  calc
    theta₂ (imaginaryAxisPoint y hy) ^ 4 =
        ((theta₂ (imaginaryAxisPoint y hy)).re : ℂ) ^ 4 :=
      congrArg (fun z : ℂ ↦ z ^ 4) hreal.symm
    _ = (((theta₂ (imaginaryAxisPoint y hy)).re ^ 4 : ℝ) : ℂ) :=
      (ofReal_pow _ 4).symm

/-- On the imaginary axis `H₃` is the real fourth power of `Re θ₃`. -/
theorem H₃_imaginaryAxis_eq_ofReal
    (y : ℝ) (hy : 0 < y) :
    H₃ (imaginaryAxisPoint y hy) =
      ((theta₃ (imaginaryAxisPoint y hy)).re ^ 4 : ℝ) := by
  have hconj :
      (starRingEnd ℂ)
          (theta₃ (imaginaryAxisPoint y hy)) =
        theta₃ (imaginaryAxisPoint y hy) :=
    Complex.conj_eq_iff_im.mpr
      (theta₃_imaginaryAxis_im y hy)
  have hreal :
      ((theta₃ (imaginaryAxisPoint y hy)).re : ℂ) =
        theta₃ (imaginaryAxisPoint y hy) :=
    Complex.conj_eq_iff_re.mp hconj
  unfold H₃
  calc
    theta₃ (imaginaryAxisPoint y hy) ^ 4 =
        ((theta₃ (imaginaryAxisPoint y hy)).re : ℂ) ^ 4 :=
      congrArg (fun z : ℂ ↦ z ^ 4) hreal.symm
    _ = (((theta₃ (imaginaryAxisPoint y hy)).re ^ 4 : ℝ) : ℂ) :=
      (ofReal_pow _ 4).symm

/-- On the imaginary axis `H₄` is the real fourth power of `Re θ₄`. -/
theorem H₄_imaginaryAxis_eq_ofReal
    (y : ℝ) (hy : 0 < y) :
    H₄ (imaginaryAxisPoint y hy) =
      ((theta₄ (imaginaryAxisPoint y hy)).re ^ 4 : ℝ) := by
  have hconj :
      (starRingEnd ℂ)
          (theta₄ (imaginaryAxisPoint y hy)) =
        theta₄ (imaginaryAxisPoint y hy) :=
    Complex.conj_eq_iff_im.mpr
      (theta₄_imaginaryAxis_im y hy)
  have hreal :
      ((theta₄ (imaginaryAxisPoint y hy)).re : ℂ) =
        theta₄ (imaginaryAxisPoint y hy) :=
    Complex.conj_eq_iff_re.mp hconj
  unfold H₄
  calc
    theta₄ (imaginaryAxisPoint y hy) ^ 4 =
        ((theta₄ (imaginaryAxisPoint y hy)).re : ℂ) ^ 4 :=
      congrArg (fun z : ℂ ↦ z ^ 4) hreal.symm
    _ = (((theta₄ (imaginaryAxisPoint y hy)).re ^ 4 : ℝ) : ℂ) :=
      (ofReal_pow _ 4).symm

/-- The real value of `H₂(iy)` is strictly positive. -/
theorem H₂_imaginaryAxis_re_pos
    (y : ℝ) (hy : 0 < y) :
    0 < (H₂ (imaginaryAxisPoint y hy)).re := by
  rw [H₂_imaginaryAxis_eq_ofReal]
  have hre :
      (theta₂ (imaginaryAxisPoint y hy)).re ≠ 0 := by
    intro hre
    apply H₂_ne_zero (imaginaryAxisPoint y hy)
    rw [H₂_imaginaryAxis_eq_ofReal, hre]
    norm_num
  simp only [ofReal_re]
  positivity

/-- The real value of `H₃(iy)` is strictly positive. -/
theorem H₃_imaginaryAxis_re_pos
    (y : ℝ) (hy : 0 < y) :
    0 < (H₃ (imaginaryAxisPoint y hy)).re := by
  rw [H₃_imaginaryAxis_eq_ofReal]
  have hre :
      (theta₃ (imaginaryAxisPoint y hy)).re ≠ 0 := by
    intro hre
    apply H₃_ne_zero (imaginaryAxisPoint y hy)
    rw [H₃_imaginaryAxis_eq_ofReal, hre]
    norm_num
  simp only [ofReal_re]
  positivity

/-- The real value of `H₄(iy)` is strictly positive. -/
theorem H₄_imaginaryAxis_re_pos
    (y : ℝ) (hy : 0 < y) :
    0 < (H₄ (imaginaryAxisPoint y hy)).re := by
  rw [H₄_imaginaryAxis_eq_ofReal]
  have hre :
      (theta₄ (imaginaryAxisPoint y hy)).re ≠ 0 := by
    intro hre
    apply H₄_ne_zero (imaginaryAxisPoint y hy)
    rw [H₄_imaginaryAxis_eq_ofReal, hre]
    norm_num
  simp only [ofReal_re]
  positivity

/-- Canonical lambda is real on the positive imaginary axis. -/
theorem canonicalLambda_imaginaryAxis_im
    (y : ℝ) (hy : 0 < y) :
    (canonicalLambda (imaginaryAxisPoint y hy)).im = 0 := by
  rw [canonicalLambda,
    H₂_imaginaryAxis_eq_ofReal,
    H₃_imaginaryAxis_eq_ofReal]
  rw [← ofReal_div, ofReal_im]

/-- Canonical lambda is positive on the positive imaginary axis. -/
theorem canonicalLambda_imaginaryAxis_re_pos
    (y : ℝ) (hy : 0 < y) :
    0 < (canonicalLambda
      (imaginaryAxisPoint y hy)).re := by
  rw [canonicalLambda,
    H₂_imaginaryAxis_eq_ofReal,
    H₃_imaginaryAxis_eq_ofReal]
  rw [← ofReal_div, ofReal_re]
  exact div_pos
    (by
      simpa only [H₂_imaginaryAxis_eq_ofReal,
        ofReal_re] using
          H₂_imaginaryAxis_re_pos y hy)
    (by
      simpa only [H₃_imaginaryAxis_eq_ofReal,
        ofReal_re] using
          H₃_imaginaryAxis_re_pos y hy)

/-- Canonical lambda is less than one on the positive imaginary axis. -/
theorem canonicalLambda_imaginaryAxis_re_lt_one
    (y : ℝ) (hy : 0 < y) :
    (canonicalLambda (imaginaryAxisPoint y hy)).re < 1 := by
  have hcomplement :
      0 <
        (1 - canonicalLambda
          (imaginaryAxisPoint y hy)).re := by
    rw [one_sub_canonicalLambda,
      H₄_imaginaryAxis_eq_ofReal,
      H₃_imaginaryAxis_eq_ofReal]
    rw [← ofReal_div, ofReal_re]
    exact div_pos
      (by
        simpa only [H₄_imaginaryAxis_eq_ofReal,
          ofReal_re] using
            H₄_imaginaryAxis_re_pos y hy)
      (by
        simpa only [H₃_imaginaryAxis_eq_ofReal,
          ofReal_re] using
            H₃_imaginaryAxis_re_pos y hy)
  rw [sub_re, one_re] at hcomplement
  linarith

/-- Inversion across the unit semicircle exchanges heights `y` and `1/y`
on the positive imaginary axis. -/
theorem modularSPoint_imaginaryAxisPoint
    (y : ℝ) (hy : 0 < y) :
    modularSPoint (imaginaryAxisPoint y hy) =
      imaginaryAxisPoint (1 / y)
        (one_div_pos.mpr hy) := by
  ext
  simp [modularSPoint, imaginaryAxisPoint,
    Complex.ext_iff]

/-- The fixed point of the `S`-action is the point `i`. -/
theorem modularSPoint_I :
    modularSPoint UpperHalfPlane.I =
      UpperHalfPlane.I := by
  ext
  norm_num [modularSPoint, Complex.ext_iff]

/-- The central value of canonical lambda is exactly `Λ(i)=1/2`. -/
theorem canonicalLambda_I :
    canonicalLambda UpperHalfPlane.I = 1 / 2 := by
  have h :=
    canonicalLambda_modularSPoint
      UpperHalfPlane.I
  rw [modularSPoint_I] at h
  linear_combination h / 2

/-- The positive-imaginary-axis parametrization at height one is `i`. -/
theorem imaginaryAxisPoint_one :
    imaginaryAxisPoint 1 zero_lt_one =
      UpperHalfPlane.I := by
  ext
  simp [imaginaryAxisPoint]

/-- Canonical lambda tends to zero at the top cusp. -/
theorem canonicalLambda_tendsto_atImInfty :
    Tendsto canonicalLambda atImInfty (𝓝 0) := by
  unfold canonicalLambda
  simpa using
    H₂_tendsto_atImInfty.div
      H₃_tendsto_atImInfty one_ne_zero

/-- A total parametrization of the imaginary axis.  At positive heights
this is literally `iy`; the total definition is convenient for filters and
the intermediate value theorem. -/
def imaginaryAxisMap (y : ℝ) : ℍ :=
  UpperHalfPlane.ofComplex (Complex.I * y)

/-- At positive heights the total parametrization agrees with
`imaginaryAxisPoint`. -/
theorem imaginaryAxisMap_eq_point
    (y : ℝ) (hy : 0 < y) :
    imaginaryAxisMap y =
      imaginaryAxisPoint y hy := by
  apply UpperHalfPlane.coe_injective
  change
    (UpperHalfPlane.ofComplex
        (Complex.I * (y : ℂ)) : ℂ) =
      Complex.I * (y : ℂ)
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos]
  simpa

/-- The total imaginary-axis parametrization approaches the top cusp as
the height tends to infinity. -/
theorem imaginaryAxisMap_tendsto_atTop :
    Tendsto imaginaryAxisMap atTop atImInfty := by
  apply UpperHalfPlane.tendsto_comap_im_ofComplex.comp
  rw [tendsto_comap_iff]
  convert
    (tendsto_id :
      Tendsto (fun y : ℝ ↦ y) atTop atTop) using 1
  ext y
  simp

/-- The real lambda coordinate along the total imaginary-axis map. -/
def imaginaryAxisLambda (y : ℝ) : ℝ :=
  (canonicalLambda (imaginaryAxisMap y)).re

/-- Along positive heights, the total real coordinate is the usual
canonical-lambda value at `iy`. -/
theorem imaginaryAxisLambda_eq
    (y : ℝ) (hy : 0 < y) :
    imaginaryAxisLambda y =
      (canonicalLambda
        (imaginaryAxisPoint y hy)).re := by
  rw [imaginaryAxisLambda,
    imaginaryAxisMap_eq_point y hy]

/-- The imaginary-axis lambda coordinate tends to zero at the top cusp. -/
theorem imaginaryAxisLambda_tendsto_atTop :
    Tendsto imaginaryAxisLambda atTop (𝓝 0) := by
  have h :=
    canonicalLambda_tendsto_atImInfty.comp
      imaginaryAxisMap_tendsto_atTop
  have hre :=
    Complex.continuous_re.continuousAt.tendsto.comp h
  simpa only [Function.comp_apply, zero_re,
    imaginaryAxisLambda] using hre

/-- The `S`-transformation becomes the elementary reflection formula
`L(1/y)=1-L(y)` for the real imaginary-axis coordinate. -/
theorem imaginaryAxisLambda_one_div
    (y : ℝ) (hy : 0 < y) :
    imaginaryAxisLambda (1 / y) =
      1 - imaginaryAxisLambda y := by
  have h :=
    congrArg Complex.re
      (canonicalLambda_modularSPoint
        (imaginaryAxisPoint y hy))
  rw [modularSPoint_imaginaryAxisPoint,
    sub_re, one_re] at h
  rw [imaginaryAxisLambda_eq
      (1 / y) (one_div_pos.mpr hy),
    imaginaryAxisLambda_eq y hy]
  exact h

/-- The total imaginary-axis parametrization is continuous at every
positive height. -/
theorem imaginaryAxisMap_continuousOn_pos :
    ContinuousOn imaginaryAxisMap (Set.Ioi 0) := by
  unfold imaginaryAxisMap
  refine
    UpperHalfPlane.ofComplex.continuousOn.comp
      (by fun_prop) ?_
  intro y hy
  simpa [UpperHalfPlane.ofComplex] using hy

/-- The real canonical-lambda coordinate is continuous on positive
heights. -/
theorem imaginaryAxisLambda_continuousOn_pos :
    ContinuousOn imaginaryAxisLambda (Set.Ioi 0) := by
  unfold imaginaryAxisLambda
  exact
    Complex.continuous_re.comp_continuousOn
      (canonicalLambda_mdifferentiable.continuous
        |>.comp_continuousOn
          imaginaryAxisMap_continuousOn_pos)

/-- The upper-half-plane path `y ↦ iy` has velocity `i` at every positive
height. -/
theorem imaginaryAxisMap_hasDerivAt
    (y : ℝ) (hy : 0 < y) :
    HasDerivAt
      (fun s : ℝ ↦ (imaginaryAxisMap s : ℂ))
      Complex.I y := by
  have hlinear :
      HasDerivAt
        (fun s : ℝ ↦ Complex.I * (s : ℂ))
        Complex.I y := by
    convert
      (Complex.ofRealCLM.hasDerivAt
        (x := y)).const_mul Complex.I using 1
    norm_num [Complex.ofRealCLM_apply]
  apply hlinear.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hy] with s hs
  rw [imaginaryAxisMap_eq_point s hs]
  rfl

/-- Exact derivative of the real imaginary-axis lambda coordinate.
The four factors on the right have signs `-,+,+,+`. -/
theorem imaginaryAxisLambda_hasDerivAt
    (y : ℝ) (hy : 0 < y) :
    HasDerivAt imaginaryAxisLambda
      (-Real.pi *
        (H₃ (imaginaryAxisPoint y hy)).re *
        (canonicalLambda
          (imaginaryAxisPoint y hy)).re *
        (1 - (canonicalLambda
          (imaginaryAxisPoint y hy)).re)) y := by
  have hc :=
    canonicalLambda_comp_hasDerivAt
      imaginaryAxisMap y
      (imaginaryAxisMap_hasDerivAt y hy)
  have hre :=
    Complex.reCLM.hasFDerivAt.comp y
      hc.hasFDerivAt
  rw [hasFDerivAt_iff_hasDerivAt] at hre
  have hre' :
      HasDerivAt imaginaryAxisLambda
        (modularIndependentVariableClock * Complex.I *
          H₃ (imaginaryAxisMap y) *
          canonicalLambda (imaginaryAxisMap y) *
          (1 - canonicalLambda
            (imaginaryAxisMap y))).re y := by
    simpa only [Function.comp_apply,
      Complex.reCLM_apply, imaginaryAxisLambda,
      ContinuousLinearMap.coe_comp',
      ContinuousLinearMap.toSpanSingleton_apply_one] using
        hre
  convert hre' using 1
  rw [imaginaryAxisMap_eq_point y hy]
  rw [H₃_imaginaryAxis_eq_ofReal]
  have hreal :
      canonicalLambda (imaginaryAxisPoint y hy) =
        ((canonicalLambda
          (imaginaryAxisPoint y hy)).re : ℂ) := by
    exact
      (Complex.conj_eq_iff_re.mp
        (Complex.conj_eq_iff_im.mpr
          (canonicalLambda_imaginaryAxis_im
            y hy))).symm
  rw [hreal]
  simp [modularIndependentVariableClock]

/-- The imaginary-axis lambda coordinate has strictly negative derivative
at every positive height. -/
theorem imaginaryAxisLambda_deriv_neg
    (y : ℝ) (hy : 0 < y) :
    deriv imaginaryAxisLambda y < 0 := by
  rw [(imaginaryAxisLambda_hasDerivAt y hy).deriv]
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos
        (neg_lt_zero.mpr Real.pi_pos)
        (H₃_imaginaryAxis_re_pos y hy))
      (canonicalLambda_imaginaryAxis_re_pos y hy))
    (sub_pos.mpr
      (canonicalLambda_imaginaryAxis_re_lt_one
        y hy))

/-- Canonical lambda is strictly decreasing from `1` to `0` along the
positive imaginary axis. -/
theorem imaginaryAxisLambda_strictAntiOn :
    StrictAntiOn imaginaryAxisLambda
      (Set.Ioi (0 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg
    (convex_Ioi (𝕜 := ℝ) (0 : ℝ))
    imaginaryAxisLambda_continuousOn_pos
  intro y hy
  rw [interior_Ioi] at hy
  exact imaginaryAxisLambda_deriv_neg y hy

/-- Fiber separation on the imaginary axis: a canonical-lambda value has
at most one positive imaginary height. -/
theorem canonicalLambda_imaginaryAxis_injective
    {y₁ y₂ : ℝ} (hy₁ : 0 < y₁) (hy₂ : 0 < y₂)
    (h :
      canonicalLambda (imaginaryAxisPoint y₁ hy₁) =
        canonicalLambda (imaginaryAxisPoint y₂ hy₂)) :
    y₁ = y₂ := by
  apply
    imaginaryAxisLambda_strictAntiOn.injOn
      hy₁ hy₂
  rw [imaginaryAxisLambda_eq y₁ hy₁,
    imaginaryAxisLambda_eq y₂ hy₂, h]

/-- **Real-seam surjectivity.**  Every `r ∈ (0,1)` is attained by
canonical lambda at a point of the positive imaginary axis. -/
theorem exists_imaginaryAxisPoint_canonicalLambda_eq
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ y : ℝ, ∃ hy : 0 < y,
      canonicalLambda (imaginaryAxisPoint y hy) = r := by
  let ε : ℝ := min r (1 - r)
  have hε : 0 < ε := by
    exact lt_min hr0 (sub_pos.mpr hr1)
  have hevent :
      ∀ᶠ y : ℝ in atTop,
        imaginaryAxisLambda y ∈ Metric.ball 0 ε :=
    imaginaryAxisLambda_tendsto_atTop.eventually
      (Metric.ball_mem_nhds 0 hε)
  obtain ⟨Y, hY⟩ :=
    Filter.eventually_atTop.mp hevent
  let B : ℝ := max Y 2
  have hYB : Y ≤ B :=
    le_max_left Y 2
  have hBtwo : 2 ≤ B :=
    le_max_right Y 2
  have hBpos : 0 < B :=
    (by norm_num : (0 : ℝ) < 2).trans_le hBtwo
  have hsmallBall :
      imaginaryAxisLambda B ∈
        Metric.ball 0 ε :=
    hY B hYB
  have hsmallNorm :
      |imaginaryAxisLambda B| < ε := by
    simpa only [Metric.mem_ball, dist_zero_right,
      Real.norm_eq_abs] using hsmallBall
  have hsmall :
      imaginaryAxisLambda B < ε :=
    (le_abs_self _).trans_lt hsmallNorm
  have hBr :
      imaginaryAxisLambda B < r :=
    hsmall.trans_le (min_le_left _ _)
  have hBoneSub :
      imaginaryAxisLambda B < 1 - r :=
    hsmall.trans_le (min_le_right _ _)
  have hreciprocal :
      r < imaginaryAxisLambda (1 / B) := by
    rw [imaginaryAxisLambda_one_div B hBpos]
    linarith
  have hab : 1 / B ≤ B := by
    rw [div_le_iff₀ hBpos]
    nlinarith
  have hintervalPos :
      Set.Icc (1 / B) B ⊆ Set.Ioi (0 : ℝ) := by
    intro y hy
    exact (one_div_pos.mpr hBpos).trans_le hy.1
  have hcont :
      ContinuousOn imaginaryAxisLambda
        (Set.Icc (1 / B) B) :=
    imaginaryAxisLambda_continuousOn_pos.mono
      hintervalPos
  have hrange :=
    intermediate_value_Icc' hab hcont
      (show r ∈
        Set.Icc (imaginaryAxisLambda B)
          (imaginaryAxisLambda (1 / B)) from
        ⟨hBr.le, hreciprocal.le⟩)
  obtain ⟨y, hyIcc, hyr⟩ := hrange
  have hy : 0 < y :=
    hintervalPos hyIcc
  refine ⟨y, hy, ?_⟩
  apply Complex.ext
  · simpa only [imaginaryAxisLambda_eq y hy] using
      hyr
  · simp only [canonicalLambda_imaginaryAxis_im,
      ofReal_im]

/-- The punctured canonical-lambda map is surjective over the entire open
real seam `(0,1)`. -/
theorem canonicalLambdaPunctured_realSeam_surjective
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ z : ℍ,
      canonicalLambdaPunctured z =
        ⟨(r : ℂ), by
          constructor
          · exact ofReal_ne_zero.mpr hr0.ne'
          · exact ofReal_ne_one.mpr hr1.ne⟩ := by
  obtain ⟨y, hy, hlambda⟩ :=
    exists_imaginaryAxisPoint_canonicalLambda_eq
      r hr0 hr1
  refine ⟨imaginaryAxisPoint y hy, ?_⟩
  apply Subtype.ext
  simpa only [canonicalLambdaPunctured_coe] using
    hlambda

/-- Every negative real number is a canonical-lambda value.  Translation
by one sends the seam coordinate `s ∈ (0,1)` to `s/(s-1) ∈ (-∞,0)`. -/
theorem exists_canonicalLambda_eq_of_neg
    (r : ℝ) (hr : r < 0) :
    ∃ z : ℍ, canonicalLambda z = (r : ℂ) := by
  let s : ℝ := r / (r - 1)
  have hden : r - 1 < 0 := by
    linarith
  have hs0 : 0 < s :=
    div_pos_of_neg_of_neg hr hden
  have hs1 : s < 1 :=
    (div_lt_one_of_neg hden).2 (by linarith)
  obtain ⟨y, hy, hlambda⟩ :=
    exists_imaginaryAxisPoint_canonicalLambda_eq
      s hs0 hs1
  refine
    ⟨(1 : ℝ) +ᵥ imaginaryAxisPoint y hy, ?_⟩
  rw [canonicalLambda_vadd_one, hlambda]
  have hr1 : r - 1 ≠ 0 := by
    linarith
  have hsEq : s / (s - 1) = r := by
    unfold s
    field_simp [hr1]
    ring
  exact_mod_cast hsEq

/-- Every real number greater than one is a canonical-lambda value.
Translation by one followed by inversion sends the seam coordinate `s` to
`1-s/(s-1)=1/(1-s)`. -/
theorem exists_canonicalLambda_eq_of_one_lt
    (r : ℝ) (hr : 1 < r) :
    ∃ z : ℍ, canonicalLambda z = (r : ℂ) := by
  let s : ℝ := 1 - 1 / r
  have hrpos : 0 < r :=
    zero_lt_one.trans hr
  have hs0 : 0 < s :=
    sub_pos.mpr ((div_lt_one hrpos).2 hr)
  have hs1 : s < 1 :=
    sub_lt_self 1 (one_div_pos.mpr hrpos)
  obtain ⟨y, hy, hlambda⟩ :=
    exists_imaginaryAxisPoint_canonicalLambda_eq
      s hs0 hs1
  refine
    ⟨modularSPoint
      ((1 : ℝ) +ᵥ imaginaryAxisPoint y hy), ?_⟩
  rw [canonicalLambda_modularSPoint,
    canonicalLambda_vadd_one, hlambda]
  have hr0 : r ≠ 0 :=
    hrpos.ne'
  have hsEq : 1 - s / (s - 1) = r := by
    unfold s
    field_simp [hr0]
    ring
  exact_mod_cast hsEq

/-- **Punctured-real-line surjectivity.**  Every real value other than
zero and one occurs as a canonical-lambda value. -/
theorem canonicalLambda_realLine_surjective
    (r : ℝ) (hr0 : r ≠ 0) (hr1 : r ≠ 1) :
    ∃ z : ℍ, canonicalLambda z = (r : ℂ) := by
  rcases lt_trichotomy r 0 with hrneg | hrzero | hrpos
  · exact exists_canonicalLambda_eq_of_neg r hrneg
  · exact (hr0 hrzero).elim
  · rcases lt_trichotomy r 1 with hrlt | hrone | hrgt
    · obtain ⟨y, hy, hlambda⟩ :=
        exists_imaginaryAxisPoint_canonicalLambda_eq
          r hrpos hrlt
      exact ⟨imaginaryAxisPoint y hy, hlambda⟩
    · exact (hr1 hrone).elim
    · exact exists_canonicalLambda_eq_of_one_lt r hrgt

/-- The punctured canonical-lambda map is surjective over the full real
punctured line `ℝ ∖ {0,1}`. -/
theorem canonicalLambdaPunctured_realLine_surjective
    (r : ℝ) (hr0 : r ≠ 0) (hr1 : r ≠ 1) :
    ∃ z : ℍ,
      canonicalLambdaPunctured z =
        ⟨(r : ℂ), by
          constructor
          · exact ofReal_ne_zero.mpr hr0
          · exact ofReal_ne_one.mpr hr1⟩ := by
  obtain ⟨z, hz⟩ :=
    canonicalLambda_realLine_surjective
      r hr0 hr1
  refine ⟨z, ?_⟩
  apply Subtype.ext
  simpa only [canonicalLambdaPunctured_coe] using hz

end

end HGAS.Modular
