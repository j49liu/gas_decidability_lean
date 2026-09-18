import HGAS.Wrapper.UnitSpherePolynomialWrapper
import Mathlib.Tactic

/-!
# The two normalized chart sheets of the polynomial wrapper

`UnitSpherePolynomialWrapper` constructs the complete sparse polynomial
field and proves its radius-cleanup identities.  This file identifies its
intended full stratum with two copies of the original product of spheres.

For `L=k+1`, a normalized chart point has the form

```
v = (z, z y),       L z² = 1.
```

If each source block of `y` has squared norm one, every scaled ambient
radius is one and `v` lies on the Euclidean unit sphere.  If the source
field is tangent to those source blocks, the raw wrapper velocity is

```
B(v) = (0, z P(y)).
```

Consequently the quotient coordinate `y=x/z` has velocity exactly `P(y)`
on *both* sheets.  The odd chart degree is essential: the rational factor
`L^((D-1)/2)` makes the negative sheet have the same time orientation.
The wrapper reward simultaneously reduces to the source reward.
-/

namespace HGAS

open _root_.MvPolynomial
open scoped BigOperators

noncomputable section

namespace UnitSpherePolynomialWrapper

variable {n k : ℕ}

/-- Squared norm of source block `i`. -/
def sourceBlockNormSq
    (sourceBlock : Fin n → Fin k)
    (y : Fin n → ℝ) (i : Fin k) : ℝ :=
  ∑ j, if sourceBlock j = i then y j ^ 2 else 0

/-- Source block dot product `yᵢ·Pᵢ(y)`. -/
def sourceBlockDot
    (sourceBlock : Fin n → Fin k)
    (y p : Fin n → ℝ) (i : Fin k) : ℝ :=
  ∑ j, if sourceBlock j = i then y j * p j else 0

/-- The source product of unit spheres. -/
def OnSourceProductSpheres
    (sourceBlock : Fin n → Fin k) (y : Fin n → ℝ) : Prop :=
  ∀ i, sourceBlockNormSq sourceBlock y i = 1

/-- Pointwise tangency of a source velocity to every source sphere block. -/
def SourceTangentAt
    (sourceBlock : Fin n → Fin k)
    (y p : Fin n → ℝ) : Prop :=
  ∀ i, sourceBlockDot sourceBlock y p i = 0

/-- The singleton chart block has scaled radius `Lz²`. -/
theorem scaledBlockRadius_chart_zero
    (sourceBlock : Fin n → Fin k)
    (z : ℝ) (y : Fin n → ℝ) :
    scaledBlockRadius sourceBlock
        (PolynomialCode.unitChartPoint z (z • y)) 0 =
      (k + 1 : ℝ) * z ^ 2 := by
  rw [scaledBlockRadius, rawBlockNormSq, Fin.sum_univ_succ]
  simp [Fin.succ_ne_zero, pow_two]

/-- A source block has scaled radius `Lz²‖yᵢ‖²`. -/
theorem scaledBlockRadius_chart_succ
    (sourceBlock : Fin n → Fin k)
    (z : ℝ) (y : Fin n → ℝ) (i : Fin k) :
    scaledBlockRadius sourceBlock
        (PolynomialCode.unitChartPoint z (z • y)) i.succ =
      (k + 1 : ℝ) * z ^ 2 *
        sourceBlockNormSq sourceBlock y i := by
  simp only [scaledBlockRadius, rawBlockNormSq, sourceBlockNormSq]
  rw [Fin.sum_univ_succ]
  have hzero : ¬(0 : Fin (k + 1)) = i.succ :=
    (Fin.succ_ne_zero i).symm
  simp only [ambientBlock_zero, hzero, ↓reduceIte, zero_add,
    PolynomialCode.unitChartPoint_succ, Pi.smul_apply, smul_eq_mul,
    ambientBlock_succ, Fin.succ_inj]
  calc
    (k + 1 : ℝ) *
        (∑ j, if sourceBlock j = i then (z * y j) ^ 2 else 0) =
      (∑ j, (k + 1 : ℝ) *
        (if sourceBlock j = i then (z * y j) ^ 2 else 0)) := by
          rw [Finset.mul_sum]
    _ = (∑ j, (k + 1 : ℝ) * z ^ 2 *
        (if sourceBlock j = i then y j ^ 2 else 0)) := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hj : sourceBlock j = i
          · simp [hj]
            ring
          · simp [hj]
    _ = (k + 1 : ℝ) * z ^ 2 *
        (∑ j, if sourceBlock j = i then y j ^ 2 else 0) := by
          rw [Finset.mul_sum]

/-- Every ambient scaled radius is one on either intended sheet. -/
theorem scaledBlockRadius_eq_one_on_chart
    (sourceBlock : Fin n → Fin k)
    (z : ℝ) (hz : (k + 1 : ℝ) * z ^ 2 = 1)
    (y : Fin n → ℝ)
    (hy : OnSourceProductSpheres sourceBlock y) :
    ∀ b,
      scaledBlockRadius sourceBlock
        (PolynomialCode.unitChartPoint z (z • y)) b = 1 := by
  intro b
  refine Fin.cases ?_ (fun i ↦ ?_) b
  · exact scaledBlockRadius_chart_zero sourceBlock z y |>.trans hz
  · rw [scaledBlockRadius_chart_succ, hz, one_mul, hy i]

/-- The two intended sheets lie on the ordinary Euclidean unit sphere. -/
theorem normSq_chart_eq_one
    (sourceBlock : Fin n → Fin k)
    (z : ℝ) (hz : (k + 1 : ℝ) * z ^ 2 = 1)
    (y : Fin n → ℝ)
    (hy : OnSourceProductSpheres sourceBlock y) :
    normSq (PolynomialCode.unitChartPoint z (z • y)) = 1 := by
  let v := PolynomialCode.unitChartPoint z (z • y)
  have hradii :
      ∀ b, scaledBlockRadius sourceBlock v b = 1 :=
    scaledBlockRadius_eq_one_on_chart sourceBlock z hz y hy
  have hsum := sum_scaledBlockRadius sourceBlock v
  simp only [hradii, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  norm_num at hsum
  have hL : (0 : ℝ) < k + 1 := by positivity
  nlinarith

/-- The chart field has zero dot product in its singleton chart block. -/
theorem blockDotValue_chartField_zero
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (x : Fin (n + 1) → ℝ) :
    blockDotValue sourceBlock x
      (PolynomialFieldCode.realize (chartFieldCode k D P) x) 0 = 0 := by
  rw [blockDotValue, Fin.sum_univ_succ]
  simp only [ambientBlock_zero, ↓reduceIte,
    eval_chartFieldCode_zero, mul_zero, zero_add, ambientBlock_succ]
  apply Finset.sum_eq_zero
  intro j _
  simp [Fin.succ_ne_zero]

/-- On a scaled chart point, a source block dot product is a scalar
multiple of the original source block dot product. -/
theorem blockDotValue_chartField_succ_scaled
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j))
    (z : ℝ) (y : Fin n → ℝ) (i : Fin k) :
    blockDotValue sourceBlock
        (PolynomialCode.unitChartPoint z (z • y))
        (PolynomialFieldCode.realize (chartFieldCode k D P)
          (PolynomialCode.unitChartPoint z (z • y))) i.succ =
      (chartScale k D : ℝ) * z ^ (D + 1) *
        sourceBlockDot sourceBlock y
          (PolynomialFieldCode.realize P y) i := by
  simp only [blockDotValue, sourceBlockDot]
  rw [Fin.sum_univ_succ]
  have hzero : ¬(0 : Fin (k + 1)) = i.succ :=
    (Fin.succ_ne_zero i).symm
  simp only [ambientBlock_zero, hzero, ↓reduceIte, zero_add,
    ambientBlock_succ, Fin.succ_inj,
    PolynomialCode.unitChartPoint_succ, Pi.smul_apply, smul_eq_mul,
    eval_chartFieldCode_succ_scaled D P hP]
  calc
    (∑ j, if sourceBlock j = i then
        z * y j *
          ((chartScale k D : ℝ) * z ^ D *
            PolynomialFieldCode.realize P y j)
      else 0) =
      ∑ j, (chartScale k D : ℝ) * z ^ (D + 1) *
        (if sourceBlock j = i then
          y j * PolynomialFieldCode.realize P y j else 0) := by
            apply Finset.sum_congr rfl
            intro j _
            by_cases hj : sourceBlock j = i
            · simp [hj, pow_succ]
              ring
            · simp [hj]
    _ = (chartScale k D : ℝ) * z ^ (D + 1) *
        ∑ j, if sourceBlock j = i then
          y j * PolynomialFieldCode.realize P y j else 0 := by
            rw [Finset.mul_sum]

/-- Source tangency makes every ambient chart-field block dot vanish. -/
theorem blockDotValue_chartField_eq_zero_on_chart
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j))
    (z : ℝ) (y : Fin n → ℝ)
    (htangent :
      SourceTangentAt sourceBlock y
        (PolynomialFieldCode.realize P y)) :
    ∀ b,
      blockDotValue sourceBlock
        (PolynomialCode.unitChartPoint z (z • y))
        (PolynomialFieldCode.realize (chartFieldCode k D P)
          (PolynomialCode.unitChartPoint z (z • y))) b = 0 := by
  intro b
  refine Fin.cases ?_ (fun i ↦ ?_) b
  · exact blockDotValue_chartField_zero sourceBlock D P _
  · rw [blockDotValue_chartField_succ_scaled
      sourceBlock D P hP z y i, htangent i, mul_zero]

/-- If every scaled radius is one, the cleanup deviation is zero. -/
theorem radiusDeviation_eq_zero_of_all_one
    (s : Fin (k + 1) → ℝ) (hs : ∀ i, s i = 1) (i : Fin (k + 1)) :
    radiusDeviation (k + 1 : ℝ) s i = 0 := by
  simp [radiusDeviation, radiusAverage, hs]

/-- **Pointwise two-sheet dynamics.**

On either intended sheet, the raw wrapper velocity is precisely
`(0,zP(y))`. -/
theorem realize_rawWrapperFieldCode_on_chart
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (hDodd : D % 2 = 1)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j))
    (z : ℝ) (hz : (k + 1 : ℝ) * z ^ 2 = 1)
    (y : Fin n → ℝ)
    (hy : OnSourceProductSpheres sourceBlock y)
    (htangent :
      SourceTangentAt sourceBlock y
        (PolynomialFieldCode.realize P y)) :
    PolynomialFieldCode.realize
        (rawWrapperFieldCode sourceBlock D P)
        (PolynomialCode.unitChartPoint z (z • y)) =
      PolynomialCode.unitChartPoint 0
        (z • PolynomialFieldCode.realize P y) := by
  let v := PolynomialCode.unitChartPoint z (z • y)
  have hradii :
      ∀ b, scaledBlockRadius sourceBlock v b = 1 :=
    scaledBlockRadius_eq_one_on_chart sourceBlock z hz y hy
  have hdots :
      ∀ b,
        blockDotValue sourceBlock v
          (PolynomialFieldCode.realize (chartFieldCode k D P) v) b = 0 :=
    blockDotValue_chartField_eq_zero_on_chart
      sourceBlock D P hP z y htangent
  have hdev :
      ∀ b,
        radiusDeviation (k + 1 : ℝ)
          (fun i ↦ scaledBlockRadius sourceBlock v i) b = 0 :=
    radiusDeviation_eq_zero_of_all_one
      (fun i ↦ scaledBlockRadius sourceBlock v i) hradii
  funext j
  refine Fin.cases ?_ (fun q ↦ ?_) j
  · rw [eval_rawWrapperFieldCode, eval_tangentFieldCode]
    rw [hradii, hdots, hdev]
    simp only [one_mul, zero_mul, mul_zero, sub_zero, add_zero,
      PolynomialCode.unitChartPoint_zero]
    exact eval_chartFieldCode_zero D P _
  · rw [eval_rawWrapperFieldCode, eval_tangentFieldCode]
    rw [hradii, hdots, hdev]
    simp only [one_mul, zero_mul, mul_zero, sub_zero,
      PolynomialCode.unitChartPoint_succ, Pi.smul_apply, smul_eq_mul]
    simpa only [PolynomialFieldCode.realize_apply, add_zero] using
      eval_chartFieldCode_succ_on_sheet
        D hDodd P hP z hz y q

/-- The raw wrapper reward is exactly the source reward on both sheets. -/
theorem eval_rawWrapperRewardCode_on_chart
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (hDodd : D % 2 = 1)
    (a : PolynomialCode n)
    (ha : PolynomialCode.TermsDegreeLE (D - 1) a)
    (z : ℝ) (hz : (k + 1 : ℝ) * z ^ 2 = 1)
    (y : Fin n → ℝ)
    (hy : OnSourceProductSpheres sourceBlock y) :
    eval₂Hom (algebraMap ℚ ℝ)
        (PolynomialCode.unitChartPoint z (z • y))
        (PolynomialCode.decode
          (rawWrapperRewardCode sourceBlock D a)) =
      eval₂Hom (algebraMap ℚ ℝ) y
        (PolynomialCode.decode a) := by
  rw [eval_rawWrapperRewardCode]
  rw [wrapperReward_eq_source
    (fun b ↦ scaledBlockRadius sourceBlock
      (PolynomialCode.unitChartPoint z (z • y)) b)
    _ (scaledBlockRadius_eq_one_on_chart
      sourceBlock z hz y hy)]
  exact eval_chartRewardCode_on_sheet D hDodd a ha z hz y

/-- The homogeneous angular field has the same two-sheet dynamics. -/
theorem realize_homogeneousAngularCode_on_chart
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (hDodd : D % 2 = 1)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j))
    (z : ℝ) (hz : (k + 1 : ℝ) * z ^ 2 = 1)
    (y : Fin n → ℝ)
    (hy : OnSourceProductSpheres sourceBlock y)
    (htangent :
      SourceTangentAt sourceBlock y
        (PolynomialFieldCode.realize P y)) :
    PolynomialFieldCode.realize
        (homogeneousAngularCode sourceBlock D P)
        (PolynomialCode.unitChartPoint z (z • y)) =
      PolynomialCode.unitChartPoint 0
        (z • PolynomialFieldCode.realize P y) := by
  rw [realize_homogeneousAngularCode_of_normSq_one
    sourceBlock D P _ (normSq_chart_eq_one sourceBlock z hz y hy)]
  exact realize_rawWrapperFieldCode_on_chart
    sourceBlock D hDodd P hP z hz y hy htangent

/-- The homogeneous radial reward is the source reward on both sheets. -/
theorem eval_homogeneousRewardCode_on_chart
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (hDodd : D % 2 = 1)
    (a : PolynomialCode n)
    (ha : PolynomialCode.TermsDegreeLE (D - 1) a)
    (z : ℝ) (hz : (k + 1 : ℝ) * z ^ 2 = 1)
    (y : Fin n → ℝ)
    (hy : OnSourceProductSpheres sourceBlock y) :
    eval₂Hom (algebraMap ℚ ℝ)
        (PolynomialCode.unitChartPoint z (z • y))
        (PolynomialCode.decode
          (homogeneousRewardCode sourceBlock D a)) =
      eval₂Hom (algebraMap ℚ ℝ) y
        (PolynomialCode.decode a) := by
  rw [eval_homogeneousRewardCode_of_normSq_one
    sourceBlock D a _ (normSq_chart_eq_one sourceBlock z hz y hy)]
  exact eval_rawWrapperRewardCode_on_chart
    sourceBlock D hDodd a ha z hz y hy

end UnitSpherePolynomialWrapper

end

end HGAS
