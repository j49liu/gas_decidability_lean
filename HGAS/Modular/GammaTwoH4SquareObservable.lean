import HGAS.Modular.ExplicitGammaTwoHaarCusp
import HGAS.Modular.GammaTwoThetaSquareAutomorphy
import HGAS.Modular.HaarExclusion
import Mathlib.Tactic

/-!
# A continuous cusp observable on the full level-two frame quotient

The upper-half-plane expression

```
                         Im(τ)² H₄(τ)²
```

is not merely a function of the base point modulo `Γ(2)`: its automorphy
factor also remembers the frame.  The intrinsic frame expression is the
weight-four slash value

```
                    ((H₄ * H₄) |₄ g)(i).
```

By exact `Γ(2)` invariance of `H₄²`, proved in
`GammaTwoThetaSquareAutomorphy`, this is invariant under left deck
translations and hence descends to `Γ(2) \\ SL(2,ℝ)`.

Taking its norm and an arbitrary natural power gives a continuous,
nonnegative real observable.  Its value is exactly

```
                 (Im(g·i) * ‖H₄(g·i)‖)^(2K).
```

This is the quotient-intrinsic version of the cusp coordinate used in
the Haar-divergence argument.
-/

namespace HGAS.Modular

open Complex Matrix
open UpperHalfPlane hiding I
open ModularForm SlashAction
open scoped ENNReal NNReal MatrixGroups ModularForm

noncomputable section

/-- The weight-four `H₄²` coordinate of a real modular frame. -/
def realFrameH4SquareCoordinate
    (g : RealModularFrame) : ℂ :=
  ((H₄ * H₄) ∣[(4 : ℤ)]
      Matrix.SpecialLinearGroup.toGL g) UpperHalfPlane.I

/-- Explicit slash formula for the frame coordinate. -/
theorem realFrameH4SquareCoordinate_apply
    (g : RealModularFrame) :
    realFrameH4SquareCoordinate g =
      (H₄ (realModularFrameBasePoint g) *
          H₄ (realModularFrameBasePoint g)) *
        UpperHalfPlane.denom
            (Matrix.SpecialLinearGroup.toGL g)
            UpperHalfPlane.I ^ (-4 : ℤ) := by
  have hgl :
      Matrix.SpecialLinearGroup.toGL g =
        Matrix.SpecialLinearGroup.mapGL ℝ g := by
    ext i j
    rfl
  have hbase :
      Matrix.SpecialLinearGroup.toGL g • UpperHalfPlane.I =
        g • UpperHalfPlane.I := by
    change
      Matrix.SpecialLinearGroup.toGL g • UpperHalfPlane.I =
        Matrix.SpecialLinearGroup.mapGL ℝ g • UpperHalfPlane.I
    rw [hgl]
  simp only [realFrameH4SquareCoordinate,
    ModularForm.slash_apply, Pi.mul_apply]
  simp only [realModularFrameBasePoint]
  simp only [map_mul, Matrix.SpecialLinearGroup.coeToGL_det,
    Units.val_one, abs_one, ofReal_one, Int.reduceSub,
    one_zpow, mul_one, UpperHalfPlane.coe_I, Int.reduceNeg,
    zpow_neg, mul_eq_mul_right_iff, inv_eq_zero]
  left
  simpa only [hbase] using
    congrArg (fun z : ℂ ↦ z * z)
      (show
        UpperHalfPlane.σ
            (Matrix.SpecialLinearGroup.toGL g)
            (H₄
              (Matrix.SpecialLinearGroup.toGL g •
                UpperHalfPlane.I)) =
          H₄ (g • UpperHalfPlane.I) by
        simp only [UpperHalfPlane.σ,
          Matrix.SpecialLinearGroup.coeToGL_det,
          Units.val_one, zero_lt_one, if_pos,
          ContinuousAlgEquiv.refl_apply, hbase])

/-- The frame coordinate varies continuously with the real frame. -/
theorem continuous_realFrameH4SquareCoordinate :
    Continuous realFrameH4SquareCoordinate := by
  rw [show
    realFrameH4SquareCoordinate =
      fun g : RealModularFrame ↦
        (H₄ (realModularFrameBasePoint g) *
            H₄ (realModularFrameBasePoint g)) *
          UpperHalfPlane.denom
              (Matrix.SpecialLinearGroup.toGL g)
              UpperHalfPlane.I ^ (-4 : ℤ) by
      funext g
      exact realFrameH4SquareCoordinate_apply g]
  have htheta :
      Continuous
        (fun g : RealModularFrame ↦
          H₄ (realModularFrameBasePoint g)) :=
    H₄_mdifferentiable.continuous.comp
      realModularFrameBasePoint_continuous
  have hdenom :
      Continuous
        (fun g : RealModularFrame ↦
          UpperHalfPlane.denom
            (Matrix.SpecialLinearGroup.toGL g)
            UpperHalfPlane.I) :=
    UpperHalfPlane.denom_continuous.comp
      (Matrix.SpecialLinearGroup.continuous_toGL.prodMk
        continuous_const)
  exact
    (htheta.mul htheta).mul
      (hdenom.zpow₀ (-4) (fun g ↦
        Or.inl
          (UpperHalfPlane.denom_ne_zero
            (Matrix.SpecialLinearGroup.toGL g)
            UpperHalfPlane.I)))

/-- Left translation by a level-two integral frame does not change the
frame coordinate. -/
theorem realFrameH4SquareCoordinate_gammaTwo_smul
    (γ : GammaTwo) (g : RealModularFrame) :
    realFrameH4SquareCoordinate (γ • g) =
      realFrameH4SquareCoordinate g := by
  have hcast :
      Matrix.SpecialLinearGroup.toGL
          (gammaTwoToRealFrame γ) =
        Matrix.SpecialLinearGroup.mapGL ℝ γ.1 := by
    ext i j
    rfl
  unfold realFrameH4SquareCoordinate
  simp only [gammaTwo_smul_realFrame, map_mul, hcast,
    SlashAction.slash_mul]
  change
    (((H₄ * H₄) ∣[(4 : ℤ)] γ.1) ∣[(4 : ℤ)]
        Matrix.SpecialLinearGroup.toGL g) UpperHalfPlane.I =
      ((H₄ * H₄) ∣[(4 : ℤ)]
        Matrix.SpecialLinearGroup.toGL g) UpperHalfPlane.I
  rw [H₄_sq_smul_of_mem_Gamma_two γ.property]

/-- The invariant frame coordinate descended to
`Γ(2) \\ SL(2,ℝ)`. -/
def gammaTwoH4SquareCoordinate :
    GammaTwoFrameQuotient → ℂ :=
  Quotient.lift
    realFrameH4SquareCoordinate
    (by
      intro g h hgh
      change g ∈ MulAction.orbit GammaTwo h at hgh
      obtain ⟨γ, rfl⟩ := hgh
      exact
        realFrameH4SquareCoordinate_gammaTwo_smul γ h)

@[simp]
theorem gammaTwoH4SquareCoordinate_mk
    (g : RealModularFrame) :
    gammaTwoH4SquareCoordinate
        (gammaTwoFrameQuotientMk g) =
      realFrameH4SquareCoordinate g :=
  rfl

/-- Continuity survives descent through the quotient. -/
theorem continuous_gammaTwoH4SquareCoordinate :
    Continuous gammaTwoH4SquareCoordinate :=
  Continuous.quotient_lift
    continuous_realFrameH4SquareCoordinate
    (by
      intro g h hgh
      change g ∈ MulAction.orbit GammaTwo h at hgh
      obtain ⟨γ, rfl⟩ := hgh
      exact
        realFrameH4SquareCoordinate_gammaTwo_smul γ h)

/-- The nonnegative real observable obtained by taking the `K`-th power
of the norm of the descended `H₄²` coordinate. -/
def gammaTwoH4SquareNormPower
    (K : ℕ) :
    C(GammaTwoFrameQuotient, ℝ) :=
  ⟨fun q ↦ ‖gammaTwoH4SquareCoordinate q‖ ^ K,
    continuous_gammaTwoH4SquareCoordinate.norm.pow K⟩

@[simp]
theorem gammaTwoH4SquareNormPower_apply
    (K : ℕ) (q : GammaTwoFrameQuotient) :
    gammaTwoH4SquareNormPower K q =
      ‖gammaTwoH4SquareCoordinate q‖ ^ K :=
  rfl

theorem gammaTwoH4SquareNormPower_nonneg
    (K : ℕ) (q : GammaTwoFrameQuotient) :
    0 ≤ gammaTwoH4SquareNormPower K q :=
  pow_nonneg (norm_nonneg _) K

/-- The norm of the frame coordinate is the square of the elementary
Iwasawa expression `height * ‖H₄‖`. -/
theorem norm_realFrameH4SquareCoordinate
    (g : RealModularFrame) :
    ‖realFrameH4SquareCoordinate g‖ =
      (realModularFrameHeight g *
        ‖H₄ (realModularFrameBasePoint g)‖) ^ 2 := by
  let d : ℂ :=
    UpperHalfPlane.denom
      (Matrix.SpecialLinearGroup.toGL g)
      UpperHalfPlane.I
  have hd : d ≠ 0 := by
    exact
      UpperHalfPlane.denom_ne_zero
        (Matrix.SpecialLinearGroup.toGL g)
        UpperHalfPlane.I
  have hgl :
      Matrix.SpecialLinearGroup.toGL g =
        Matrix.SpecialLinearGroup.mapGL ℝ g := by
    ext i j
    rfl
  have hbase :
      Matrix.SpecialLinearGroup.toGL g • UpperHalfPlane.I =
        realModularFrameBasePoint g := by
    unfold realModularFrameBasePoint
    change
      Matrix.SpecialLinearGroup.toGL g • UpperHalfPlane.I =
        Matrix.SpecialLinearGroup.mapGL ℝ g • UpperHalfPlane.I
    rw [hgl]
  have hheight :
      realModularFrameHeight g =
        1 / Complex.normSq d := by
    have him :=
      UpperHalfPlane.im_smul_eq_div_normSq
        (Matrix.SpecialLinearGroup.toGL g)
        UpperHalfPlane.I
    have hdet :
        |((Matrix.SpecialLinearGroup.toGL g).det.val : ℝ)| =
          1 := by
      simp
    unfold realModularFrameHeight
    rw [← hbase]
    rw [hdet] at him
    simpa only [UpperHalfPlane.I_im, mul_one,
      one_div, d] using him
  rw [realFrameH4SquareCoordinate_apply,
    norm_mul, norm_mul, norm_zpow, hheight,
    Complex.normSq_eq_norm_sq]
  have hnorm : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr hd
  change
    ‖H₄ (realModularFrameBasePoint g)‖ *
          ‖H₄ (realModularFrameBasePoint g)‖ *
          ‖d‖ ^ (-4 : ℤ) =
      ((1 / ‖d‖ ^ 2) *
          ‖H₄ (realModularFrameBasePoint g)‖) ^ 2
  field_simp [hnorm]

/-- Representative formula for the descended power observable. -/
theorem gammaTwoH4SquareNormPower_mk
    (K : ℕ) (g : RealModularFrame) :
    gammaTwoH4SquareNormPower K
        (gammaTwoFrameQuotientMk g) =
      (realModularFrameHeight g *
          ‖H₄ (realModularFrameBasePoint g)‖) ^ (2 * K) := by
  rw [gammaTwoH4SquareNormPower_apply,
    gammaTwoH4SquareCoordinate_mk,
    norm_realFrameH4SquareCoordinate]
  exact (pow_mul _ 2 K).symm

/-- The norm of the paper's canonical cusp coordinate at unit scale. -/
theorem norm_canonicalHaarCuspCoordinate_one
    (τ : ℍ) :
    ‖canonicalHaarCuspCoordinate 1 τ‖ =
      τ.im * ‖H₄ τ‖ := by
  rw [canonicalHaarCuspCoordinate, norm_mul]
  simp only [one_mul, norm_real, Real.norm_eq_abs,
    abs_of_pos τ.im_pos]

/-- On the explicit translated cusp chart, the quotient observable is
exactly the even power of the canonical cusp coordinate after undoing the
fixed deck translation. -/
theorem gammaTwoH4SquareNormPower_cuspChart
    (K : ℕ) {Y : ℝ}
    (g : gammaTwoTranslatedFrameCusp Y) :
    gammaTwoH4SquareNormPower K
        (gammaTwoCuspChartMap Y g) =
      ‖canonicalHaarCuspCoordinate 1
          (realModularFrameBasePoint
            (gammaTwoIdentityDeckFactor⁻¹ • g.1))‖ ^
        (2 * K) := by
  let h : RealModularFrame :=
    gammaTwoIdentityDeckFactor⁻¹ • g.1
  have hquot :
      gammaTwoCuspChartMap Y g =
        gammaTwoFrameQuotientMk h := by
    change
      gammaTwoFrameQuotientMk g.1 =
        gammaTwoFrameQuotientMk h
    apply Quotient.sound
    exact
      ⟨gammaTwoIdentityDeckFactor, by
        simp only [h, smul_smul, mul_inv_cancel,
          one_smul]⟩
  rw [hquot, gammaTwoH4SquareNormPower_mk,
    norm_canonicalHaarCuspCoordinate_one]
  rfl

/-- The fixed positive cusp-growth constant supplied by
`‖H₄(τ)‖ ≥ 1/2` sufficiently high in the cusp. -/
def gammaTwoThetaCuspHalf : ℝ≥0 :=
  ⟨(1 / 2 : ℝ), by norm_num⟩

theorem gammaTwoThetaCuspHalf_ne_zero :
    gammaTwoThetaCuspHalf ≠ 0 := by
  exact ne_of_gt (by
    change (0 : ℝ) < 1 / 2
    norm_num)

/-- The continuous quotient observable has the uniform cusp lower bound
required by the compact-test theorem.

The threshold is enlarged to be positive.  This matters only off the
explicit cusp chart: there the extended height is zero, so the positive
tail indicator vanishes identically. -/
theorem exists_gammaTwoH4SquareNormPower_cuspLowerBound
    {Y : ℝ} (hY : 1 < Y) (K : ℕ) :
    ∃ Ytail : ℝ, 0 < Ytail ∧
      ∀ q : GammaTwoFrameQuotient,
        (gammaTwoThetaCuspHalf : ℝ≥0∞) ^ (2 * K) *
            HGAS.Dynamics.cuspTailHeightPower
              Ytail (2 * K)
              (gammaTwoExplicitCuspHeight Y q) ≤
          ENNReal.ofReal
            (gammaTwoH4SquareNormPower K q) := by
  obtain ⟨Y₀, hY₀⟩ :=
    exists_cuspHeight_scaledPower_le_canonicalCoordinatePower
      (s := 1) (by norm_num) (2 * K)
  let Ytail : ℝ := max Y₀ 1
  have hYtail_pos : 0 < Ytail :=
    zero_lt_one.trans_le (le_max_right Y₀ 1)
  have hcanonical :
      ∀ τ : ℍ,
        ENNReal.ofReal (1 / 2) ^ (2 * K) *
            HGAS.Dynamics.cuspTailHeightPower
              Ytail (2 * K) τ.im ≤
          ENNReal.ofReal
            ‖canonicalHaarCuspCoordinate 1 τ‖ ^ (2 * K) := by
    intro τ
    by_cases hτ : Ytail ≤ τ.im
    · have hτ₀ : Y₀ ≤ τ.im :=
        (le_max_left Y₀ 1).trans hτ
      have hold := hY₀ τ
      simpa only [
        HGAS.Dynamics.cuspTailHeightPower,
        Set.indicator_of_mem
          (show τ.im ∈ Set.Ici Ytail from hτ),
        Set.indicator_of_mem
          (show τ.im ∈ Set.Ici Y₀ from hτ₀)] using hold
    · simp only [
        HGAS.Dynamics.cuspTailHeightPower,
        Set.indicator_of_notMem
          (show τ.im ∉ Set.Ici Ytail from hτ),
        mul_zero]
      exact bot_le
  refine ⟨Ytail, hYtail_pos, ?_⟩
  intro q
  by_cases hq :
      ∃ g : gammaTwoTranslatedFrameCusp Y,
        gammaTwoCuspChartMap Y g = q
  · obtain ⟨g, rfl⟩ := hq
    let τ : ℍ :=
      realModularFrameBasePoint
        (gammaTwoIdentityDeckFactor⁻¹ • g.1)
    have hlower := hcanonical τ
    rw [gammaTwoExplicitCuspHeight_chart hY,
      gammaTwoH4SquareNormPower_cuspChart]
    change
      (gammaTwoThetaCuspHalf : ℝ≥0∞) ^ (2 * K) *
            HGAS.Dynamics.cuspTailHeightPower
              Ytail (2 * K) τ.im ≤
        ENNReal.ofReal
          (‖canonicalHaarCuspCoordinate 1 τ‖ ^ (2 * K))
    rw [ENNReal.ofReal_pow (norm_nonneg _) (2 * K)]
    have hhalf :
        (gammaTwoThetaCuspHalf : ℝ≥0∞) =
          ENNReal.ofReal (1 / 2) := by
      rw [ENNReal.coe_nnreal_eq]
      rfl
    rw [hhalf]
    exact hlower
  · have hheight :
        gammaTwoExplicitCuspHeight Y q = 0 := by
      unfold gammaTwoExplicitCuspHeight
      simpa using
        (Function.extend_apply'
          (f := gammaTwoCuspChartMap Y)
          (gammaTwoCuspChartHeight Y)
          (0 : GammaTwoFrameQuotient → ℝ) q hq)
    rw [hheight]
    simp only [HGAS.Dynamics.cuspTailHeightPower,
      Set.indicator_of_notMem
        (show (0 : ℝ) ∉ Set.Ici Ytail by
          simpa only [Set.mem_Ici, not_le] using hYtail_pos),
      mul_zero]
    exact bot_le

end

end HGAS.Modular
