import HGAS.Dynamics.CuspMeasureDivergence
import HGAS.Modular.StandardFundamentalDomainVolume
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# The height marginal of a rectangular hyperbolic cusp

This file gives a reusable, coordinate-level calculation for the
upper-half-plane measure.  On a rectangle of Euclidean width one and
height at least `Y > 0`, hyperbolic area is

```
  dx dy / y²,
```

so its push-forward by the height coordinate is exactly the measure
`cuspHeightMeasure Y`.

Keeping this calculation separate from the modular quotient makes the
later quotient argument transparent: quotient geometry is used only to
embed one such rectangle, while all analytic content is here.
-/

namespace HGAS.Modular

open Complex MeasureTheory Set UpperHalfPlane
open scoped ENNReal NNReal

noncomputable section

/-- The open, width-one horizontal interval used in the standard cusp. -/
def standardCuspHorizontalInterval : Set ℝ :=
  Ioo (-(1 / 2 : ℝ)) (1 / 2 : ℝ)

/-- A rectangular cusp in the upper half-plane. -/
def upperHalfPlaneCuspRectangle (Y : ℝ) : Set UpperHalfPlane :=
  {τ | τ.re ∈ standardCuspHorizontalInterval ∧ Y ≤ τ.im}

theorem measurableSet_upperHalfPlaneCuspRectangle (Y : ℝ) :
    MeasurableSet (upperHalfPlaneCuspRectangle Y) := by
  exact
    (measurableSet_Ioo.prod measurableSet_Ici).preimage
      (Complex.measurableEquivRealProd.measurable.comp
        UpperHalfPlane.measurable_coe)

theorem upperHalfPlaneCuspRectangle_subset_fdo
    {Y : ℝ} (hY : 1 < Y) :
    upperHalfPlaneCuspRectangle Y ⊆ ModularGroup.fdo := by
  intro τ hτ
  constructor
  · have him : 1 < τ.im := hY.trans_le hτ.2
    have him' : (1 : ℝ) < (τ : ℂ).im := by
      simpa only [UpperHalfPlane.coe_im] using him
    have himsq : (1 : ℝ) ^ 2 < (τ : ℂ).im ^ 2 :=
      (sq_lt_sq₀ (by norm_num) (le_of_lt τ.im_pos)).2 him'
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg (τ : ℂ).re]
  · simpa only [standardCuspHorizontalInterval, mem_Ioo, abs_lt]
      using hτ.1

/-- The complex-plane version of the hyperbolic density. -/
def complexHyperbolicDensity (z : ℂ) : ℝ≥0∞ :=
  ↑((1 / ‖z.im‖₊) ^ 2 : ℝ≥0)

theorem measurable_complexHyperbolicDensity :
    Measurable complexHyperbolicDensity := by
  unfold complexHyperbolicDensity
  fun_prop

private theorem complexHyperbolicDensity_eq_cuspDensity
    {y : ℝ} (hy : 0 < y) :
    complexHyperbolicDensity (Complex.ofReal 0 + Complex.I * y) =
      ENNReal.ofReal ((y ^ 2)⁻¹) := by
  unfold complexHyperbolicDensity
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul,
    zero_add]
  rw [ENNReal.ofReal_eq_coe_nnreal
    (inv_nonneg.mpr (sq_nonneg y))]
  congr 1
  apply NNReal.eq
  simp [Real.nnnorm_of_nonneg hy.le, sq]

private theorem complexHyperbolicDensity_realProd
    {p : ℝ × ℝ} (hp : 0 < p.2) :
    complexHyperbolicDensity
        (Complex.measurableEquivRealProd.symm p) =
      ENNReal.ofReal ((p.2 ^ 2)⁻¹) := by
  unfold complexHyperbolicDensity
  rw [ENNReal.ofReal_eq_coe_nnreal
    (inv_nonneg.mpr (sq_nonneg p.2))]
  congr 1
  apply NNReal.eq
  simp [Complex.measurableEquivRealProd_symm_apply,
    Real.nnnorm_of_nonneg hp.le, sq]

private theorem measurable_cuspDensity :
    Measurable (fun y : ℝ ↦ ENNReal.ofReal ((y ^ 2)⁻¹)) := by
  fun_prop

/-- A width-one complex rectangle with the hyperbolic density has
exactly the standard `dy / y²` height marginal. -/
theorem map_im_restrict_complexHyperbolicMeasure
    (Y : ℝ) (hY : 0 < Y) :
    Measure.map Complex.im
        ((volume.withDensity complexHyperbolicDensity).restrict
          {z : ℂ |
            z.re ∈ standardCuspHorizontalInterval ∧ Y ≤ z.im}) =
      HGAS.Dynamics.cuspHeightMeasure Y := by
  ext A hA
  have hrectangle :
      MeasurableSet
        {z : ℂ |
          z.re ∈ standardCuspHorizontalInterval ∧ Y ≤ z.im} :=
    (measurableSet_Ioo.prod measurableSet_Ici).preimage
      Complex.measurableEquivRealProd.measurable
  have hintersection :
      MeasurableSet
        (Complex.im ⁻¹' A ∩
          {z : ℂ |
            z.re ∈ standardCuspHorizontalInterval ∧ Y ≤ z.im}) :=
    (measurable_im hA).inter hrectangle
  rw [Measure.map_apply measurable_im hA,
    Measure.restrict_apply (measurable_im hA),
    withDensity_apply _ hintersection]
  let X : Set ℝ := standardCuspHorizontalInterval
  let T : Set ℝ := A ∩ Ici Y
  have hX : MeasurableSet X := measurableSet_Ioo
  have hT : MeasurableSet T := hA.inter measurableSet_Ici
  have hset :
      Complex.im ⁻¹' A ∩
          {z : ℂ |
            z.re ∈ standardCuspHorizontalInterval ∧ Y ≤ z.im} =
        Complex.measurableEquivRealProd ⁻¹' (X ×ˢ T) := by
    ext z
    simp [X, T, standardCuspHorizontalInterval, and_left_comm,
      and_assoc, and_comm]
  rw [hset]
  calc
    (∫⁻ z in
        Complex.measurableEquivRealProd ⁻¹' (X ×ˢ T),
        complexHyperbolicDensity z ∂volume) =
        ∫⁻ p in X ×ˢ T,
          complexHyperbolicDensity
            (Complex.measurableEquivRealProd.symm p)
          ∂(volume.prod volume) := by
      simpa using
        Complex.volume_preserving_equiv_real_prod
          |>.setLIntegral_comp_preimage_emb
            Complex.measurableEquivRealProd.measurableEmbedding
            (fun p : ℝ × ℝ ↦
              complexHyperbolicDensity
                (Complex.measurableEquivRealProd.symm p))
            (X ×ˢ T)
    _ = ∫⁻ x in X, ∫⁻ y in T,
          complexHyperbolicDensity
            (Complex.measurableEquivRealProd.symm (x, y)) := by
      rw [setLIntegral_prod]
      exact
        (measurable_complexHyperbolicDensity.comp
          Complex.measurableEquivRealProd.symm.measurable).aemeasurable
    _ = ∫⁻ x in X, ∫⁻ y in T,
          ENNReal.ofReal ((y ^ 2)⁻¹) := by
      congr 1
      funext x
      apply setLIntegral_congr_fun hT
      intro y hy
      exact complexHyperbolicDensity_realProd
        (hY.trans_le hy.2)
    _ = ∫⁻ y in T, ENNReal.ofReal ((y ^ 2)⁻¹) := by
      rw [setLIntegral_const]
      have hvolumeX : volume X = 1 := by
        dsimp [X, standardCuspHorizontalInterval]
        rw [Real.volume_Ioo]
        norm_num
      rw [hvolumeX, mul_one]
    _ = HGAS.Dynamics.cuspHeightMeasure Y A := by
      rw [HGAS.Dynamics.cuspHeightMeasure,
        withDensity_apply _ hA]
      change
        (∫⁻ y, ENNReal.ofReal ((y ^ 2)⁻¹)
          ∂volume.restrict T) =
        ∫⁻ y, ENNReal.ofReal ((y ^ 2)⁻¹)
          ∂(volume.restrict (Ici Y)).restrict A
      rw [Measure.restrict_restrict hA]

/-- The height marginal of a width-one rectangular cusp in `ℍ` is
exactly the standard one-dimensional cusp measure. -/
theorem map_im_restrict_upperHalfPlaneCuspRectangle
    (Y : ℝ) (hY : 0 < Y) :
    Measure.map (fun τ : UpperHalfPlane ↦ τ.im)
        ((volume : Measure UpperHalfPlane).restrict
          (upperHalfPlaneCuspRectangle Y)) =
      HGAS.Dynamics.cuspHeightMeasure Y := by
  ext A hA
  rw [Measure.map_apply (by fun_prop) hA,
    Measure.restrict_apply (hA.preimage (by fun_prop))]
  rw [UpperHalfPlane.volume_eq_lintegral]
  have himage :
      UpperHalfPlane.coe ''
          ((fun τ : UpperHalfPlane ↦ τ.im) ⁻¹' A ∩
            upperHalfPlaneCuspRectangle Y) =
        Complex.im ⁻¹' A ∩
          {z : ℂ |
            z.re ∈ standardCuspHorizontalInterval ∧ Y ≤ z.im} := by
    ext z
    constructor
    · rintro ⟨τ, ⟨hAτ, hτ⟩, rfl⟩
      exact ⟨hAτ, hτ⟩
    · intro hz
      have hzpos : 0 < z.im := hY.trans_le hz.2.2
      refine ⟨⟨z, hzpos⟩, ?_, rfl⟩
      exact ⟨hz.1, hz.2⟩
  rw [himage]
  have hcomplex :=
    congrArg (fun μ : Measure ℝ ↦ μ A)
      (map_im_restrict_complexHyperbolicMeasure Y hY)
  change
    (Measure.map Complex.im
      ((volume.withDensity complexHyperbolicDensity).restrict
        {z : ℂ |
          z.re ∈ standardCuspHorizontalInterval ∧ Y ≤ z.im})) A =
      HGAS.Dynamics.cuspHeightMeasure Y A at hcomplex
  have hrectangle :
      MeasurableSet
        {z : ℂ |
          z.re ∈ standardCuspHorizontalInterval ∧ Y ≤ z.im} :=
    (measurableSet_Ioo.prod measurableSet_Ici).preimage
      Complex.measurableEquivRealProd.measurable
  have hintersection :
      MeasurableSet
        (Complex.im ⁻¹' A ∩
          {z : ℂ |
            z.re ∈ standardCuspHorizontalInterval ∧ Y ≤ z.im}) :=
    (measurable_im hA).inter hrectangle
  rw [Measure.map_apply measurable_im hA,
    Measure.restrict_apply (measurable_im hA),
    withDensity_apply _ hintersection] at hcomplex
  exact hcomplex

end

end HGAS.Modular
