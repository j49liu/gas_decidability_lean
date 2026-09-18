import HGAS.Modular.JacobiThetaInitialRank
import HGAS.Topology.ComplexProjectiveLine
import Mathlib.Tactic

/-!
# The `[θ₁:θ₂]` projection of the Jacobi theta curve

For fixed `τ ∈ ℍ`, the first two Jacobi theta coordinates have no common
zero and hence define a map

```
                 ℂ ⟶ ℂP¹,       z ↦ [θ₁(z):θ₂(z)].
```

This file proves that map surjective.  The proof is elementary and avoids
both schemes and a pre-existing topology on algebraic projective space.

* `ℂP¹` is modeled by `OnePoint ℂ`.
* The two theta functions are entire and are not constant multiples of
  one another, so the complex open mapping theorem makes the projective
  ratio open.  Ramification is allowed.
* Doubled-period automorphy reduces the complete image to a compact
  fundamental rectangle.
* A nonempty subset of connected `ℂP¹` which is both open and closed is
  the whole space.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real Filter Topology
open scoped OnePoint Topology

noncomputable section

/-! ## The first two coordinates never vanish together -/

/-- The pair `(θ₁(z),θ₂(z))` has no common zero. -/
theorem jacobiTheta12_pair_ne_zero
    (z : ℂ) (τ : ℍ) :
    (jacobiTheta1 z (τ : ℂ),
      jacobiTheta2 z (τ : ℂ)) ≠ 0 := by
  intro hpair
  have h0 :
      jacobiThetaVector z (τ : ℂ) 0 = 0 := by
    simpa [jacobiThetaVector] using
      congrArg Prod.fst hpair
  have h1 :
      jacobiThetaVector z (τ : ℂ) 1 = 0 := by
    simpa [jacobiThetaVector] using
      congrArg Prod.snd hpair
  have hp :=
    canonicalUnaryRoots_p_product_ne_zero τ
  have hp2 :
      (canonicalUnaryRoots τ).p2 ≠ 0 := by
    intro hp2
    apply hp
    rw [hp2, zero_mul]
    exact zero_mul _
  have hQ1 :=
    canonical_jacobiResidualQ1_jacobiThetaVector z τ
  have hQ2 :=
    canonical_jacobiResidualQ2_jacobiThetaVector z τ
  have h2 :
      jacobiThetaVector z (τ : ℂ) 2 = 0 := by
    change
      (canonicalUnaryRoots τ).p2 *
            jacobiThetaVector z (τ : ℂ) 2 ^ 2 -
          (canonicalUnaryRoots τ).p3 *
            jacobiThetaVector z (τ : ℂ) 1 ^ 2 -
        (canonicalUnaryRoots τ).p4 *
            jacobiThetaVector z (τ : ℂ) 0 ^ 2 =
        0 at hQ2
    simp only [h0, h1, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, sub_zero] at hQ2
    exact
      sq_eq_zero_iff.mp
        ((mul_eq_zero.mp hQ2).resolve_left hp2)
  have h3 :
      jacobiThetaVector z (τ : ℂ) 3 = 0 := by
    change
      (canonicalUnaryRoots τ).p2 *
            jacobiThetaVector z (τ : ℂ) 3 ^ 2 -
          (canonicalUnaryRoots τ).p4 *
            jacobiThetaVector z (τ : ℂ) 1 ^ 2 -
        (canonicalUnaryRoots τ).p3 *
            jacobiThetaVector z (τ : ℂ) 0 ^ 2 =
        0 at hQ1
    simp only [h0, h1, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, sub_zero] at hQ1
    exact
      sq_eq_zero_iff.mp
        ((mul_eq_zero.mp hQ1).resolve_left hp2)
  apply jacobiThetaVector_ne_zero z τ
  funext k
  fin_cases k <;> assumption

/-- The projective-line theta ratio.  A finite value is `θ₂/θ₁`; a zero
of `θ₁` maps to infinity. -/
def jacobiTheta12Projective
    (τ : ℍ) : ℂ → OnePoint ℂ :=
  complexProjectiveRatioMap
    (fun z => jacobiTheta1 z (τ : ℂ))
    (fun z => jacobiTheta2 z (τ : ℂ))
    (fun z => jacobiTheta12_pair_ne_zero z τ)

theorem jacobiTheta12Projective_apply
    (z : ℂ) (τ : ℍ) :
    jacobiTheta12Projective τ z =
      if jacobiTheta1 z (τ : ℂ) = 0 then ∞
      else
        ((jacobiTheta2 z (τ : ℂ) /
          jacobiTheta1 z (τ : ℂ) : ℂ) :
          OnePoint ℂ) := rfl

/-! ## Entirety and nonproportionality -/

theorem analyticOnNhd_jacobiTheta1_fixed
    (τ : ℍ) :
    AnalyticOnNhd ℂ
      (fun z => jacobiTheta1 z (τ : ℂ))
      Set.univ := by
  rw [analyticOnNhd_univ_iff_differentiable]
  intro z
  exact
    (hasDerivAt_jacobiTheta1 z (τ : ℂ)
      τ.im_pos).differentiableAt

theorem analyticOnNhd_jacobiTheta2_fixed
    (τ : ℍ) :
    AnalyticOnNhd ℂ
      (fun z => jacobiTheta2 z (τ : ℂ))
      Set.univ := by
  rw [analyticOnNhd_univ_iff_differentiable]
  intro z
  exact
    (hasDerivAt_jacobiTheta2 z (τ : ℂ)
      τ.im_pos).differentiableAt

/-- The common quasiperiodic scalar for a shift by `τ`. -/
def thetaTauMultiplier (z τ : ℂ) : ℂ :=
  cexp (-π * I * τ - 2 * π * I * z)

theorem thetaTauMultiplier_ne_zero
    (z τ : ℂ) :
    thetaTauMultiplier z τ ≠ 0 :=
  Complex.exp_ne_zero _

/-- `θ₃(z+τ)` quasiperiodicity. -/
theorem jacobiTheta3_add_tau
    (z τ : ℂ) :
    jacobiTheta3 (z + τ) τ =
      thetaTauMultiplier z τ *
        jacobiTheta3 z τ := by
  simpa [jacobiTheta3, thetaTauMultiplier] using
    jacobiTheta₂_add_int_lattice z τ 0 1

/-- `θ₄(z+τ)` has the opposite sign. -/
theorem jacobiTheta4_add_tau
    (z τ : ℂ) :
    jacobiTheta4 (z + τ) τ =
      -thetaTauMultiplier z τ *
        jacobiTheta4 z τ := by
  rw [jacobiTheta4]
  have h :=
    jacobiTheta₂_add_int_lattice
      (z + 1 / 2) τ 0 1
  norm_num at h
  rw [show z + τ + 1 / 2 =
      (z + 1 / 2) + (0 : ℂ) + (1 : ℂ) * τ by
        ring]
  norm_num only [zero_add, add_zero, one_mul]
  rw [h]
  rw [thetaTauMultiplier]
  calc
    cexp
          (-(π * I * τ) -
            2 * π * I * (z + 1 / 2)) *
        jacobiTheta₂ (z + 1 / 2) τ =
      cexp
          ((-π * I * τ - 2 * π * I * z) +
            -(π * I)) *
        jacobiTheta₂ (z + 1 / 2) τ := by
          congr 2
          ring
    _ =
      -cexp (-π * I * τ - 2 * π * I * z) *
        jacobiTheta₂ (z + 1 / 2) τ := by
      rw [Complex.exp_add, Complex.exp_neg,
        Complex.exp_pi_mul_I]
      ring

/-- `θ₂(z+τ)` quasiperiodicity. -/
theorem jacobiTheta2_add_tau
    (z τ : ℂ) :
    jacobiTheta2 (z + τ) τ =
      thetaTauMultiplier z τ *
        jacobiTheta2 z τ := by
  rw [jacobiTheta2, jacobiTheta2]
  have h :=
    jacobiTheta₂_add_int_lattice
      (z + τ / 2) τ 0 1
  norm_num at h
  rw [show z + τ + τ / 2 =
      (z + τ / 2) + (0 : ℂ) + (1 : ℂ) * τ by
        ring]
  norm_num only [zero_add, add_zero, one_mul]
  rw [h, thetaTauMultiplier]
  rw [← mul_assoc, ← Complex.exp_add,
    ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- The odd theta coordinate changes by the opposite scalar. -/
theorem jacobiTheta1_add_tau
    (z τ : ℂ) :
    jacobiTheta1 (z + τ) τ =
      -thetaTauMultiplier z τ *
        jacobiTheta1 z τ := by
  rw [jacobiTheta1, jacobiTheta1,
    show z + τ + 1 / 2 =
      (z + 1 / 2) + τ by ring,
    jacobiTheta2_add_tau]
  rw [thetaTauMultiplier, thetaTauMultiplier]
  have hexp :
      cexp
          (-π * I * τ -
            2 * π * I * (z + 1 / 2)) =
        -cexp
          (-π * I * τ - 2 * π * I * z) := by
    calc
      cexp
          (-π * I * τ -
            2 * π * I * (z + 1 / 2)) =
        cexp
          ((-π * I * τ - 2 * π * I * z) +
            -(π * I)) := by
          congr 1
          ring
      _ = _ := by
        rw [Complex.exp_add, Complex.exp_neg,
          Complex.exp_pi_mul_I]
        ring
  rw [hexp]
  ring

/-- Pointwise nonvanishing of the even theta constant `θ₂(0|τ)`. -/
theorem jacobiTheta2_zero_ne_zero
    (τ : ℍ) :
    jacobiTheta2 0 (τ : ℂ) ≠ 0 := by
  rw [jacobiTheta2_zero_eq_theta₂]
  intro hzero
  apply H₂_ne_zero τ
  simp [H₂, hzero]

/-- The odd theta function is nonzero at the opposite half-period. -/
theorem jacobiTheta1_oppositeHalfPeriod_ne_zero
    (τ : ℍ) :
    jacobiTheta1
      ((1 + (τ : ℂ)) / 2) (τ : ℂ) ≠ 0 := by
  intro hzero
  have hhalf :=
    jacobiTheta3_eq_halfPeriod_jacobiTheta1
      0 (τ : ℂ)
  have hzero' :
      jacobiTheta1
        (0 + (1 + (τ : ℂ)) / 2) (τ : ℂ) = 0 := by
    simpa only [zero_add] using hzero
  rw [hzero', mul_zero] at hhalf
  have htheta3 :
      jacobiTheta3 0 (τ : ℂ) ≠ 0 := by
    rw [jacobiTheta3_zero_eq_theta₃]
    intro hz
    apply H₃_ne_zero τ
    simp [H₃, hz]
  exact htheta3 hhalf

theorem jacobiTheta2_not_const_mul_jacobiTheta1
    (τ : ℍ) :
    ¬ ∃ c : ℂ, ∀ z : ℂ,
      jacobiTheta2 z (τ : ℂ) =
        c * jacobiTheta1 z (τ : ℂ) := by
  rintro ⟨c, hc⟩
  let a := thetaTauMultiplier 0 (τ : ℂ)
  have ha : a ≠ 0 :=
    thetaTauMultiplier_ne_zero 0 (τ : ℂ)
  have h0 := hc 0
  have hτ :
      a * jacobiTheta2 0 (τ : ℂ) =
        c * (-a * jacobiTheta1 0 (τ : ℂ)) := by
    calc
      a * jacobiTheta2 0 (τ : ℂ) =
          jacobiTheta2 (0 + (τ : ℂ)) (τ : ℂ) := by
        exact
          (jacobiTheta2_add_tau 0 (τ : ℂ)).symm
      _ = c *
          jacobiTheta1 (0 + (τ : ℂ)) (τ : ℂ) :=
        hc (0 + (τ : ℂ))
      _ = c * (-a *
          jacobiTheta1 0 (τ : ℂ)) := by
        rw [jacobiTheta1_add_tau]
  have h2 := jacobiTheta2_zero_ne_zero τ
  have hτ' :
      a * jacobiTheta2 0 (τ : ℂ) =
        -(a * jacobiTheta2 0 (τ : ℂ)) := by
    calc
      a * jacobiTheta2 0 (τ : ℂ) =
          c * (-a * jacobiTheta1 0 (τ : ℂ)) :=
        hτ
      _ = -(a *
          jacobiTheta2 0 (τ : ℂ)) := by
        rw [h0]
        ring
  have hzero :
      a * jacobiTheta2 0 (τ : ℂ) = 0 := by
    linear_combination (1 / 2 : ℂ) * hτ'
  exact (mul_ne_zero ha h2) hzero

theorem jacobiTheta1_not_const_mul_jacobiTheta2
    (τ : ℍ) :
    ¬ ∃ c : ℂ, ∀ z : ℂ,
      jacobiTheta1 z (τ : ℂ) =
        c * jacobiTheta2 z (τ : ℂ) := by
  rintro ⟨c, hc⟩
  let z0 : ℂ := (1 + (τ : ℂ)) / 2
  let a := thetaTauMultiplier z0 (τ : ℂ)
  have ha : a ≠ 0 :=
    thetaTauMultiplier_ne_zero z0 (τ : ℂ)
  have hz := hc z0
  have hzτ :
      -a * jacobiTheta1 z0 (τ : ℂ) =
        c * (a * jacobiTheta2 z0 (τ : ℂ)) := by
    calc
      -a * jacobiTheta1 z0 (τ : ℂ) =
          jacobiTheta1 (z0 + (τ : ℂ)) (τ : ℂ) := by
        exact
          (jacobiTheta1_add_tau z0 (τ : ℂ)).symm
      _ = c *
          jacobiTheta2 (z0 + (τ : ℂ)) (τ : ℂ) :=
        hc (z0 + (τ : ℂ))
      _ = c * (a *
          jacobiTheta2 z0 (τ : ℂ)) := by
        rw [jacobiTheta2_add_tau]
  have h1 :
      jacobiTheta1 z0 (τ : ℂ) ≠ 0 := by
    simpa only [z0] using
      jacobiTheta1_oppositeHalfPeriod_ne_zero τ
  have hzτ' :
      -(a * jacobiTheta1 z0 (τ : ℂ)) =
        a * jacobiTheta1 z0 (τ : ℂ) := by
    calc
      -(a * jacobiTheta1 z0 (τ : ℂ)) =
          -a * jacobiTheta1 z0 (τ : ℂ) := by ring
      _ = c * (a *
          jacobiTheta2 z0 (τ : ℂ)) := hzτ
      _ = a * jacobiTheta1 z0 (τ : ℂ) := by
        rw [hz]
        ring
  have hzero :
      a * jacobiTheta1 z0 (τ : ℂ) = 0 := by
    linear_combination (-1 / 2 : ℂ) * hzτ'
  exact (mul_ne_zero ha h1) hzero

/-- The projective theta ratio is continuous. -/
theorem continuous_jacobiTheta12Projective
    (τ : ℍ) :
    Continuous (jacobiTheta12Projective τ) := by
  apply continuous_complexProjectiveRatioMap
  · exact
      (analyticOnNhd_jacobiTheta1_fixed τ).continuous
  · exact
      (analyticOnNhd_jacobiTheta2_fixed τ).continuous

/-- The projective theta ratio is open.  This is an application of the
complex open mapping theorem, so it remains valid at branch points. -/
theorem isOpenMap_jacobiTheta12Projective
    (τ : ℍ) :
    IsOpenMap (jacobiTheta12Projective τ) := by
  exact
    isOpenMap_complexProjectiveRatioMap
      (fun z => jacobiTheta12_pair_ne_zero z τ)
      (analyticOnNhd_jacobiTheta1_fixed τ)
      (analyticOnNhd_jacobiTheta2_fixed τ)
      (jacobiTheta2_not_const_mul_jacobiTheta1 τ)
      (jacobiTheta1_not_const_mul_jacobiTheta2 τ)

/-! ## Compact level-two reduction -/

/-- The real parameter box for a level-two elliptic fundamental
rectangle. -/
def ellipticThetaParameterBox
    (τ : ℍ) : Set (ℝ × ℝ) :=
  Set.Icc (-1) 1 ×ˢ
    Set.Icc (-τ.im) τ.im

/-- Identify real coordinates with a complex elliptic coordinate. -/
def ellipticThetaParam
    (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) + (p.2 : ℂ) * I

/-- A compact rectangle containing one representative of every class
modulo `2ℤ+2τℤ`. -/
def ellipticThetaFundamentalRectangle
    (τ : ℍ) : Set ℂ :=
  ellipticThetaParam ''
    ellipticThetaParameterBox τ

theorem continuous_ellipticThetaParam :
    Continuous ellipticThetaParam := by
  unfold ellipticThetaParam
  fun_prop

theorem isCompact_ellipticThetaFundamentalRectangle
    (τ : ℍ) :
    IsCompact
      (ellipticThetaFundamentalRectangle τ) := by
  exact
    (isCompact_Icc.prod isCompact_Icc).image
      continuous_ellipticThetaParam

/-- First reduce the imaginary coordinate modulo `2 Im τ`. -/
def ellipticThetaImagIndex
    (z : ℂ) (τ : ℍ) : ℤ :=
  round (z.im / (2 * τ.im))

/-- Intermediate reduction after removing the imaginary lattice
coordinate. -/
def ellipticThetaAfterImag
    (z : ℂ) (τ : ℍ) : ℂ :=
  z - 2 * (ellipticThetaImagIndex z τ : ℂ) *
    (τ : ℂ)

/-- Then reduce the real coordinate modulo `2`. -/
def ellipticThetaRealIndex
    (z : ℂ) (τ : ℍ) : ℤ :=
  round ((ellipticThetaAfterImag z τ).re / 2)

/-- Canonical representative in the compact rectangle. -/
def ellipticThetaReduce
    (z : ℂ) (τ : ℍ) : ℂ :=
  ellipticThetaAfterImag z τ -
    2 * (ellipticThetaRealIndex z τ : ℂ)

theorem ellipticThetaReduce_reconstruction
    (z : ℂ) (τ : ℍ) :
    z =
      ellipticThetaReduce z τ +
        2 * (ellipticThetaRealIndex z τ : ℂ) +
        2 * (ellipticThetaImagIndex z τ : ℂ) *
          (τ : ℂ) := by
  unfold ellipticThetaReduce ellipticThetaAfterImag
  ring

theorem abs_ellipticThetaReduce_re_le_one
    (z : ℂ) (τ : ℍ) :
    |(ellipticThetaReduce z τ).re| ≤ 1 := by
  have hround :=
    abs_sub_round
      ((ellipticThetaAfterImag z τ).re / 2)
  have hre :
      (ellipticThetaReduce z τ).re =
        2 *
          ((ellipticThetaAfterImag z τ).re / 2 -
            (ellipticThetaRealIndex z τ : ℝ)) := by
    simp [ellipticThetaReduce]
    ring
  rw [hre, abs_mul, abs_of_nonneg
    (show (0 : ℝ) ≤ 2 by norm_num)]
  simpa only [ellipticThetaRealIndex] using
    (show
      2 *
          |(ellipticThetaAfterImag z τ).re / 2 -
            (round
              ((ellipticThetaAfterImag z τ).re / 2) :
                ℝ)| ≤
        1 by nlinarith)

theorem abs_ellipticThetaReduce_im_le
    (z : ℂ) (τ : ℍ) :
    |(ellipticThetaReduce z τ).im| ≤ τ.im := by
  have hround :=
    abs_sub_round (z.im / (2 * τ.im))
  have hτpos : 0 < 2 * τ.im := by
    positivity
  have hτne : 2 * τ.im ≠ 0 :=
    ne_of_gt hτpos
  have him :
      (ellipticThetaReduce z τ).im =
        (2 * τ.im) *
          (z.im / (2 * τ.im) -
            (ellipticThetaImagIndex z τ : ℝ)) := by
    rw [ellipticThetaReduce, Complex.sub_im]
    have hm :
        (2 *
          (ellipticThetaRealIndex z τ : ℂ)).im = 0 := by
      norm_num [Complex.mul_im]
    rw [hm, sub_zero, ellipticThetaAfterImag,
      Complex.sub_im]
    have hn :
        (2 * (ellipticThetaImagIndex z τ : ℂ) *
          (τ : ℂ)).im =
            2 *
              (ellipticThetaImagIndex z τ : ℝ) *
                τ.im := by
      norm_num [Complex.mul_im]
    rw [hn]
    rw [div_eq_mul_inv]
    field_simp
  rw [him, abs_mul, abs_of_pos hτpos]
  have hround' :
      |z.im / (2 * τ.im) -
        (ellipticThetaImagIndex z τ : ℝ)| ≤
          (1 : ℝ) / 2 := by
    simpa only [ellipticThetaImagIndex] using hround
  nlinarith

theorem ellipticThetaReduce_mem_fundamentalRectangle
    (z : ℂ) (τ : ℍ) :
    ellipticThetaReduce z τ ∈
      ellipticThetaFundamentalRectangle τ := by
  refine
    ⟨((ellipticThetaReduce z τ).re,
        (ellipticThetaReduce z τ).im), ?_, ?_⟩
  · exact
      ⟨abs_le.mp
          (abs_ellipticThetaReduce_re_le_one z τ),
        abs_le.mp
          (abs_ellipticThetaReduce_im_le z τ)⟩
  · apply Complex.ext
    · simp [ellipticThetaParam]
    · simp [ellipticThetaParam]

/-- The projective ratio is invariant under the doubled period
lattice. -/
theorem jacobiTheta12Projective_add_levelTwo_lattice
    (z : ℂ) (τ : ℍ) (m n : ℤ) :
    jacobiTheta12Projective τ
        (z + 2 * (m : ℂ) +
          2 * (n : ℂ) * (τ : ℂ)) =
      jacobiTheta12Projective τ z := by
  have h1 :=
    jacobiTheta1_add_levelTwo_lattice
      z (τ : ℂ) m n
  have h2 :=
    jacobiTheta2_add_levelTwo_lattice
      z (τ : ℂ) m n
  have hc :
      levelTwoThetaMultiplier n z (τ : ℂ) ≠ 0 :=
    levelTwoThetaMultiplier_ne_zero n z (τ : ℂ)
  rw [jacobiTheta12Projective_apply,
    jacobiTheta12Projective_apply, h1, h2]
  by_cases hz : jacobiTheta1 z (τ : ℂ) = 0
  · simp [hz]
  · have hcz :
        levelTwoThetaMultiplier n z (τ : ℂ) *
            jacobiTheta1 z (τ : ℂ) ≠
          0 :=
      mul_ne_zero hc hz
    simp only [hcz, hz, if_false]
    congr 1
    field_simp

theorem jacobiTheta12Projective_compact_reduction
    (z : ℂ) (τ : ℍ) :
    ∃ w ∈ ellipticThetaFundamentalRectangle τ,
      jacobiTheta12Projective τ w =
        jacobiTheta12Projective τ z := by
  let w := ellipticThetaReduce z τ
  let m := ellipticThetaRealIndex z τ
  let n := ellipticThetaImagIndex z τ
  refine
    ⟨w, ellipticThetaReduce_mem_fundamentalRectangle
      z τ, ?_⟩
  have hreconstruct :
      z =
        w + 2 * (m : ℂ) +
          2 * (n : ℂ) * (τ : ℂ) :=
    ellipticThetaReduce_reconstruction z τ
  rw [hreconstruct,
    jacobiTheta12Projective_add_levelTwo_lattice]

/-- **Surjectivity of the first-two-coordinate projection.**

Every point of `ℂP¹` is `[θ₁(z):θ₂(z)]` for some elliptic coordinate
`z`.  No Wronskian or algebraic-geometric connectedness theorem is
needed. -/
theorem jacobiTheta12Projective_surjective
    (τ : ℍ) :
    Function.Surjective
      (jacobiTheta12Projective τ) := by
  exact
    surjective_to_complexProjectiveLine_of_compact_reduction
      (continuous_jacobiTheta12Projective τ)
      (isOpenMap_jacobiTheta12Projective τ)
      (isCompact_ellipticThetaFundamentalRectangle τ)
      (fun z =>
        jacobiTheta12Projective_compact_reduction z τ)

end

end HGAS.Modular
