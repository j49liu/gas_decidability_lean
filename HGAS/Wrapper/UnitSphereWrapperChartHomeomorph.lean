import HGAS.Wrapper.UnitSphereWrapperSheetInvariant
import Mathlib.Tactic

/-!
# Homeomorphisms from the source product sphere to the two chart sheets

Let `L=k+1` and `z₊=1/√L`, `z₋=-z₊`.  The maps

```
y ↦ (z₊, z₊y),       y ↦ (z₋, z₋y)
```

are homeomorphisms from the source product of spheres onto the positive
and negative full sheets.  The inverse is the chart quotient `x/z`.

This file contains only topology and exact coordinate algebra.  Dynamical
and invariant-measure transport is built on top of these homeomorphisms in
the subsequent module.
-/

namespace HGAS

open Function Metric Set
open scoped BigOperators BoundedContinuousFunction RealInnerProductSpace

noncomputable section

namespace UnitSpherePolynomialWrapper

variable {n k : ℕ}

/-- The compact source phase set as a subtype. -/
abbrev SourceProductSphere
    (sourceBlock : Fin n → Fin k) :=
  {y : Fin n → ℝ // OnSourceProductSpheres sourceBlock y}

/-- Positive normalized chart scalar `1/√(k+1)`. -/
noncomputable def positiveChartScalar (k : ℕ) : ℝ :=
  (Real.sqrt (k + 1 : ℝ))⁻¹

/-- Negative normalized chart scalar. -/
noncomputable def negativeChartScalar (k : ℕ) : ℝ :=
  -positiveChartScalar k

theorem positiveChartScalar_pos :
    0 < positiveChartScalar k := by
  unfold positiveChartScalar
  exact inv_pos.mpr (Real.sqrt_pos.2 (by positivity))

theorem positiveChartScalar_ne_zero :
    positiveChartScalar k ≠ 0 :=
  (positiveChartScalar_pos (k := k)).ne'

theorem positiveChartScalar_sheet :
    (k + 1 : ℝ) * positiveChartScalar k ^ 2 = 1 := by
  let L : ℝ := k + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hsqrt : Real.sqrt L ^ 2 = L :=
    Real.sq_sqrt hL.le
  unfold positiveChartScalar
  change L * (Real.sqrt L)⁻¹ ^ 2 = 1
  field_simp [Real.sqrt_ne_zero'.2 hL]
  nlinarith

theorem negativeChartScalar_neg :
    negativeChartScalar k < 0 := by
  unfold negativeChartScalar
  exact neg_neg_of_pos positiveChartScalar_pos

theorem negativeChartScalar_ne_zero :
    negativeChartScalar k ≠ 0 :=
  (negativeChartScalar_neg (k := k)).ne

theorem negativeChartScalar_sheet :
    (k + 1 : ℝ) * negativeChartScalar k ^ 2 = 1 := by
  rw [negativeChartScalar, neg_sq]
  exact positiveChartScalar_sheet

/-- A positive solution of the normalized sheet equation is the canonical
positive chart scalar. -/
theorem eq_positiveChartScalar_of_sheet_of_pos
    (z : ℝ) (hz : (k + 1 : ℝ) * z ^ 2 = 1)
    (hzpos : 0 < z) :
    z = positiveChartScalar k := by
  have hcpos := positiveChartScalar_pos (k := k)
  have hcsheet := positiveChartScalar_sheet (k := k)
  have hL : 0 < (k + 1 : ℝ) := by positivity
  nlinarith

/-- A negative solution of the normalized sheet equation is the canonical
negative chart scalar. -/
theorem eq_negativeChartScalar_of_sheet_of_neg
    (z : ℝ) (hz : (k + 1 : ℝ) * z ^ 2 = 1)
    (hzneg : z < 0) :
    z = negativeChartScalar k := by
  have hcneg := negativeChartScalar_neg (k := k)
  have hcsheet := negativeChartScalar_sheet (k := k)
  have hL : 0 < (k + 1 : ℝ) := by positivity
  nlinarith

/-- Raw normalized chart point at a chosen sheet scalar. -/
def normalizedRawChartPoint
    (z : ℝ) (y : Fin n → ℝ) : RawWrapperSpace n :=
  PolynomialCode.unitChartPoint z (z • y)

/-- Genuine Euclidean chart point. -/
noncomputable def normalizedEuclideanChartPoint
    (sourceBlock : Fin n → Fin k)
    (z : ℝ) (hz : (k + 1 : ℝ) * z ^ 2 = 1)
    (y : SourceProductSphere sourceBlock) :
    EuclideanUnitSphere (EuclideanWrapperSpace n) :=
  ⟨wrapperEuclideanEquiv (normalizedRawChartPoint z y.1), by
    change dist
      (wrapperEuclideanEquiv (normalizedRawChartPoint z y.1)) 0 = 1
    rw [dist_zero_right]
    apply (norm_wrapperEuclideanEquiv_eq_one_iff _).2
    exact normSq_chart_eq_one sourceBlock z hz y.1 y.2⟩

@[simp]
theorem normalizedEuclideanChartPoint_raw
    (sourceBlock : Fin n → Fin k)
    (z : ℝ) (hz : (k + 1 : ℝ) * z ^ 2 = 1)
    (y : SourceProductSphere sourceBlock) :
    wrapperEuclideanEquiv.symm
        (normalizedEuclideanChartPoint sourceBlock z hz y).1 =
      normalizedRawChartPoint z y.1 := by
  simp [normalizedEuclideanChartPoint]

/-- Positive chart map, with codomain restricted to the positive full
sheet. -/
noncomputable def sourceToPositiveSheet
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    SourceProductSphere sourceBlock →
      positiveFullSheet sourceBlock D P a :=
  fun y ↦
    ⟨normalizedEuclideanChartPoint sourceBlock
      (positiveChartScalar k) positiveChartScalar_sheet y,
      by
        refine ⟨?_, ?_⟩
        · intro b
          change
            (radiusCleanupFlowCertificate
              sourceBlock D P a).radii b
                (normalizedEuclideanChartPoint sourceBlock
                  (positiveChartScalar k)
                  positiveChartScalar_sheet y) = 1
          rw [radiusCleanupFlowCertificate_radii_apply,
            normalizedEuclideanChartPoint_raw]
          exact scaledBlockRadius_eq_one_on_chart
            sourceBlock (positiveChartScalar k)
            positiveChartScalar_sheet y.1 y.2 b
        · rw [normalizedEuclideanChartPoint_raw]
          exact positiveChartScalar_pos⟩

/-- Negative chart map, with codomain restricted to the negative full
sheet. -/
noncomputable def sourceToNegativeSheet
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    SourceProductSphere sourceBlock →
      negativeFullSheet sourceBlock D P a :=
  fun y ↦
    ⟨normalizedEuclideanChartPoint sourceBlock
      (negativeChartScalar k) negativeChartScalar_sheet y,
      by
        refine ⟨?_, ?_⟩
        · intro b
          change
            (radiusCleanupFlowCertificate
              sourceBlock D P a).radii b
                (normalizedEuclideanChartPoint sourceBlock
                  (negativeChartScalar k)
                  negativeChartScalar_sheet y) = 1
          rw [radiusCleanupFlowCertificate_radii_apply,
            normalizedEuclideanChartPoint_raw]
          exact scaledBlockRadius_eq_one_on_chart
            sourceBlock (negativeChartScalar k)
            negativeChartScalar_sheet y.1 y.2 b
        · rw [normalizedEuclideanChartPoint_raw]
          exact negativeChartScalar_neg⟩

/-- Fixed-scalar chart inverse. -/
def fixedScalarChartInverse
    (sourceBlock : Fin n → Fin k)
    (z : ℝ)
    (u : EuclideanUnitSphere (EuclideanWrapperSpace n))
    (hu :
      OnSourceProductSpheres sourceBlock
        (fun j ↦ wrapperEuclideanEquiv.symm u.1 j.succ / z)) :
    SourceProductSphere sourceBlock :=
  ⟨fun j ↦ wrapperEuclideanEquiv.symm u.1 j.succ / z, hu⟩

/-- The raw chart coordinate of a point on the positive sheet is the
canonical positive scalar. -/
theorem positiveSheet_chartCoordinate
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (u : positiveFullSheet sourceBlock D P a) :
    wrapperEuclideanEquiv.symm u.1.1 0 =
      positiveChartScalar k := by
  have hradii :
      ∀ b, scaledBlockRadius sourceBlock
        (wrapperEuclideanEquiv.symm u.1.1) b = 1 := by
    intro b
    have hb := u.2.1 b
    simpa only [radiusCleanupFlowCertificate_radii_apply] using hb
  exact eq_positiveChartScalar_of_sheet_of_pos
    _ (chartCoordinate_sheet_of_all_radii_one
      sourceBlock _ hradii) u.2.2

/-- The raw chart coordinate of a point on the negative sheet is the
canonical negative scalar. -/
theorem negativeSheet_chartCoordinate
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (u : negativeFullSheet sourceBlock D P a) :
    wrapperEuclideanEquiv.symm u.1.1 0 =
      negativeChartScalar k := by
  have hradii :
      ∀ b, scaledBlockRadius sourceBlock
        (wrapperEuclideanEquiv.symm u.1.1) b = 1 := by
    intro b
    have hb := u.2.1 b
    simpa only [radiusCleanupFlowCertificate_radii_apply] using hb
  exact eq_negativeChartScalar_of_sheet_of_neg
    _ (chartCoordinate_sheet_of_all_radii_one
      sourceBlock _ hradii) u.2.2

/-- Positive-sheet inverse. -/
noncomputable def positiveSheetToSource
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    positiveFullSheet sourceBlock D P a →
      SourceProductSphere sourceBlock :=
  fun u ↦
    ⟨fun j ↦
      wrapperEuclideanEquiv.symm u.1.1 j.succ /
        positiveChartScalar k,
      by
        have hradii :
            ∀ b, scaledBlockRadius sourceBlock
              (wrapperEuclideanEquiv.symm u.1.1) b = 1 := by
          intro b
          have hb := u.2.1 b
          simpa only [radiusCleanupFlowCertificate_radii_apply] using hb
        have hy :=
          chartQuotient_onSourceProductSpheres
            sourceBlock (wrapperEuclideanEquiv.symm u.1.1) hradii
        rw [show
          (fun j ↦ wrapperEuclideanEquiv.symm u.1.1 j.succ /
            positiveChartScalar k) =
            chartQuotient (wrapperEuclideanEquiv.symm u.1.1) by
          funext j
          rw [chartQuotient,
            positiveSheet_chartCoordinate sourceBlock D P a u]]
        exact hy⟩

/-- Negative-sheet inverse. -/
noncomputable def negativeSheetToSource
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    negativeFullSheet sourceBlock D P a →
      SourceProductSphere sourceBlock :=
  fun u ↦
    ⟨fun j ↦
      wrapperEuclideanEquiv.symm u.1.1 j.succ /
        negativeChartScalar k,
      by
        have hradii :
            ∀ b, scaledBlockRadius sourceBlock
              (wrapperEuclideanEquiv.symm u.1.1) b = 1 := by
          intro b
          have hb := u.2.1 b
          simpa only [radiusCleanupFlowCertificate_radii_apply] using hb
        have hy :=
          chartQuotient_onSourceProductSpheres
            sourceBlock (wrapperEuclideanEquiv.symm u.1.1) hradii
        rw [show
          (fun j ↦ wrapperEuclideanEquiv.symm u.1.1 j.succ /
            negativeChartScalar k) =
            chartQuotient (wrapperEuclideanEquiv.symm u.1.1) by
          funext j
          rw [chartQuotient,
            negativeSheet_chartCoordinate sourceBlock D P a u]]
        exact hy⟩

theorem positiveSheetToSource_sourceToPositiveSheet
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (y : SourceProductSphere sourceBlock) :
    positiveSheetToSource sourceBlock D P a
        (sourceToPositiveSheet sourceBlock D P a y) = y := by
  apply Subtype.ext
  funext j
  change
    wrapperEuclideanEquiv.symm
        (normalizedEuclideanChartPoint sourceBlock
          (positiveChartScalar k) positiveChartScalar_sheet y).1
        j.succ / positiveChartScalar k = y.1 j
  rw [normalizedEuclideanChartPoint_raw]
  simp [normalizedRawChartPoint, positiveChartScalar_ne_zero]

theorem sourceToPositiveSheet_positiveSheetToSource
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (u : positiveFullSheet sourceBlock D P a) :
    sourceToPositiveSheet sourceBlock D P a
        (positiveSheetToSource sourceBlock D P a u) = u := by
  apply Subtype.ext
  apply Subtype.ext
  apply wrapperEuclideanEquiv.symm.injective
  change
    wrapperEuclideanEquiv.symm
        (normalizedEuclideanChartPoint sourceBlock
          (positiveChartScalar k) positiveChartScalar_sheet
          (positiveSheetToSource sourceBlock D P a u)).1 =
      wrapperEuclideanEquiv.symm u.1.1
  rw [normalizedEuclideanChartPoint_raw]
  let x := wrapperEuclideanEquiv.symm u.1.1
  have hx0 :
      x 0 = positiveChartScalar k :=
    positiveSheet_chartCoordinate sourceBlock D P a u
  funext j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · exact hx0.symm
  · change
      positiveChartScalar k *
          (u.1.1 i.succ / positiveChartScalar k) =
        u.1.1 i.succ
    field_simp [positiveChartScalar_ne_zero (k := k)]

theorem negativeSheetToSource_sourceToNegativeSheet
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (y : SourceProductSphere sourceBlock) :
    negativeSheetToSource sourceBlock D P a
        (sourceToNegativeSheet sourceBlock D P a y) = y := by
  apply Subtype.ext
  funext j
  change
    wrapperEuclideanEquiv.symm
        (normalizedEuclideanChartPoint sourceBlock
          (negativeChartScalar k) negativeChartScalar_sheet y).1
        j.succ / negativeChartScalar k = y.1 j
  rw [normalizedEuclideanChartPoint_raw]
  simp [normalizedRawChartPoint, negativeChartScalar_ne_zero]

theorem sourceToNegativeSheet_negativeSheetToSource
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (u : negativeFullSheet sourceBlock D P a) :
    sourceToNegativeSheet sourceBlock D P a
        (negativeSheetToSource sourceBlock D P a u) = u := by
  apply Subtype.ext
  apply Subtype.ext
  apply wrapperEuclideanEquiv.symm.injective
  change
    wrapperEuclideanEquiv.symm
        (normalizedEuclideanChartPoint sourceBlock
          (negativeChartScalar k) negativeChartScalar_sheet
          (negativeSheetToSource sourceBlock D P a u)).1 =
      wrapperEuclideanEquiv.symm u.1.1
  rw [normalizedEuclideanChartPoint_raw]
  let x := wrapperEuclideanEquiv.symm u.1.1
  have hx0 :
      x 0 = negativeChartScalar k :=
    negativeSheet_chartCoordinate sourceBlock D P a u
  funext j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · exact hx0.symm
  · change
      negativeChartScalar k *
          (u.1.1 i.succ / negativeChartScalar k) =
        u.1.1 i.succ
    field_simp [negativeChartScalar_ne_zero (k := k)]

/-- Continuity of a fixed-scalar source chart map. -/
theorem continuous_normalizedEuclideanChartPoint
    (sourceBlock : Fin n → Fin k)
    (z : ℝ) (hz : (k + 1 : ℝ) * z ^ 2 = 1) :
    Continuous
      (normalizedEuclideanChartPoint sourceBlock z hz) := by
  apply Continuous.subtype_mk
  apply wrapperEuclideanEquiv.continuous.comp
  unfold normalizedRawChartPoint
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · exact continuous_const
  · simp only [PolynomialCode.unitChartPoint_succ,
      Pi.smul_apply, smul_eq_mul]
    exact continuous_const.mul
      ((continuous_apply i).comp continuous_subtype_val)

theorem continuous_sourceToPositiveSheet
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    Continuous (sourceToPositiveSheet sourceBlock D P a) := by
  apply Continuous.subtype_mk
  exact continuous_normalizedEuclideanChartPoint
    sourceBlock (positiveChartScalar k) positiveChartScalar_sheet

theorem continuous_sourceToNegativeSheet
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    Continuous (sourceToNegativeSheet sourceBlock D P a) := by
  apply Continuous.subtype_mk
  exact continuous_normalizedEuclideanChartPoint
    sourceBlock (negativeChartScalar k) negativeChartScalar_sheet

theorem continuous_positiveSheetToSource
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    Continuous (positiveSheetToSource sourceBlock D P a) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  change Continuous (fun u :
      positiveFullSheet sourceBlock D P a ↦
    wrapperEuclideanEquiv.symm u.1.1 j.succ /
      positiveChartScalar k)
  fun_prop

theorem continuous_negativeSheetToSource
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    Continuous (negativeSheetToSource sourceBlock D P a) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  change Continuous (fun u :
      negativeFullSheet sourceBlock D P a ↦
    wrapperEuclideanEquiv.symm u.1.1 j.succ /
      negativeChartScalar k)
  fun_prop

/-- Homeomorphism from the source product sphere to the positive sheet. -/
noncomputable def positiveSheetHomeomorph
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    SourceProductSphere sourceBlock ≃ₜ
      positiveFullSheet sourceBlock D P a where
  toFun := sourceToPositiveSheet sourceBlock D P a
  invFun := positiveSheetToSource sourceBlock D P a
  left_inv :=
    positiveSheetToSource_sourceToPositiveSheet
      sourceBlock D P a
  right_inv :=
    sourceToPositiveSheet_positiveSheetToSource
      sourceBlock D P a
  continuous_toFun :=
    continuous_sourceToPositiveSheet sourceBlock D P a
  continuous_invFun :=
    continuous_positiveSheetToSource sourceBlock D P a

/-- Homeomorphism from the source product sphere to the negative sheet. -/
noncomputable def negativeSheetHomeomorph
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    SourceProductSphere sourceBlock ≃ₜ
      negativeFullSheet sourceBlock D P a where
  toFun := sourceToNegativeSheet sourceBlock D P a
  invFun := negativeSheetToSource sourceBlock D P a
  left_inv :=
    negativeSheetToSource_sourceToNegativeSheet
      sourceBlock D P a
  right_inv :=
    sourceToNegativeSheet_negativeSheetToSource
      sourceBlock D P a
  continuous_toFun :=
    continuous_sourceToNegativeSheet sourceBlock D P a
  continuous_invFun :=
    continuous_negativeSheetToSource sourceBlock D P a

end UnitSpherePolynomialWrapper

end

end HGAS
