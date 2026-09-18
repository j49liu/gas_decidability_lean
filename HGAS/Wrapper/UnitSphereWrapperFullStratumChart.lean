import HGAS.Wrapper.UnitSphereWrapperFullStratum
import Mathlib.Tactic

/-!
# Exact chart description of the full stratum

This file proves the converse to the chart lemmas in
`UnitSphereWrapperChart`: every point whose scaled block radii are all one
has a nonzero chart coordinate and is uniquely of the form

```
(z, z y),    (k+1) z² = 1,
```

with `y` on the source product of unit spheres.  Consequently the full
stratum is exactly the disjoint union of its positive and negative chart
sheets.  This is the set-theoretic input needed for the final
invariant-measure conjugacy.
-/

namespace HGAS

open Function Metric Set
open scoped BigOperators BoundedContinuousFunction RealInnerProductSpace

noncomputable section

namespace UnitSpherePolynomialWrapper

variable {n k : ℕ}

/-- At an arbitrary raw point, the singleton chart block has scaled radius
`(k+1)x₀²`. -/
theorem scaledBlockRadius_zero
    (sourceBlock : Fin n → Fin k)
    (x : RawWrapperSpace n) :
    scaledBlockRadius sourceBlock x 0 =
      (k + 1 : ℝ) * x 0 ^ 2 := by
  unfold scaledBlockRadius rawBlockNormSq
  rw [Fin.sum_univ_succ]
  simp [Fin.succ_ne_zero]

/-- At an arbitrary raw point, source block `i` consists exactly of the
shifted source coordinates assigned to `i`. -/
theorem scaledBlockRadius_succ
    (sourceBlock : Fin n → Fin k)
    (x : RawWrapperSpace n) (i : Fin k) :
    scaledBlockRadius sourceBlock x i.succ =
      (k + 1 : ℝ) *
        ∑ j : Fin n,
          if sourceBlock j = i then x j.succ ^ 2 else 0 := by
  unfold scaledBlockRadius rawBlockNormSq
  rw [Fin.sum_univ_succ]
  have hzero : ¬(0 : Fin (k + 1)) = i.succ :=
    (Fin.succ_ne_zero i).symm
  simp only [ambientBlock_zero, hzero, ↓reduceIte, zero_add,
    ambientBlock_succ, Fin.succ_inj]

/-- Quotient source coordinates associated with a nonzero chart
coordinate. -/
def chartQuotient (x : RawWrapperSpace n) : Fin n → ℝ :=
  fun j ↦ x j.succ / x 0

/-- Reconstructing a point from its chart quotient is exact whenever the
chart coordinate is nonzero. -/
theorem unitChartPoint_chartQuotient
    (x : RawWrapperSpace n) (hx0 : x 0 ≠ 0) :
    PolynomialCode.unitChartPoint (x 0)
        (x 0 • chartQuotient x) = x := by
  funext j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · rfl
  · dsimp [chartQuotient]
    field_simp [hx0]

/-- If all scaled radii are one, the chart coordinate lies on one of the
two normalized sheets. -/
theorem chartCoordinate_sheet_of_all_radii_one
    (sourceBlock : Fin n → Fin k)
    (x : RawWrapperSpace n)
    (hradii : ∀ b, scaledBlockRadius sourceBlock x b = 1) :
    (k + 1 : ℝ) * x 0 ^ 2 = 1 := by
  rw [← scaledBlockRadius_zero sourceBlock x]
  exact hradii 0

/-- A full-stratum point never lies on the projective hyperplane `z=0`. -/
theorem chartCoordinate_ne_zero_of_all_radii_one
    (sourceBlock : Fin n → Fin k)
    (x : RawWrapperSpace n)
    (hradii : ∀ b, scaledBlockRadius sourceBlock x b = 1) :
    x 0 ≠ 0 := by
  intro hx
  have hsheet :=
    chartCoordinate_sheet_of_all_radii_one
      sourceBlock x hradii
  rw [hx] at hsheet
  norm_num at hsheet

/-- The chart quotient of a full-stratum point lies on every source unit
sphere. -/
theorem chartQuotient_onSourceProductSpheres
    (sourceBlock : Fin n → Fin k)
    (x : RawWrapperSpace n)
    (hradii : ∀ b, scaledBlockRadius sourceBlock x b = 1) :
    OnSourceProductSpheres sourceBlock (chartQuotient x) := by
  intro i
  have hsheet :=
    chartCoordinate_sheet_of_all_radii_one
      sourceBlock x hradii
  have hx0 :=
    chartCoordinate_ne_zero_of_all_radii_one
      sourceBlock x hradii
  have hblock := hradii i.succ
  rw [scaledBlockRadius_succ] at hblock
  unfold sourceBlockNormSq chartQuotient
  have hdivision :
      (∑ j : Fin n,
        if sourceBlock j = i then
          (x j.succ / x 0) ^ 2 else 0) =
        (x 0 ^ 2)⁻¹ *
          ∑ j : Fin n,
            if sourceBlock j = i then x j.succ ^ 2 else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : sourceBlock j = i
    · simp [hj, div_pow]
      field_simp [hx0]
    · simp [hj]
  rw [hdivision]
  have hL : (k + 1 : ℝ) ≠ 0 := by positivity
  have hzsq : x 0 ^ 2 = (k + 1 : ℝ)⁻¹ := by
    field_simp [hL]
    nlinarith
  rw [hzsq, inv_inv]
  nlinarith

/-- Complete raw-coordinate characterization of the full stratum. -/
theorem all_radii_one_iff_exists_chart
    (sourceBlock : Fin n → Fin k)
    (x : RawWrapperSpace n) :
    (∀ b, scaledBlockRadius sourceBlock x b = 1) ↔
      ∃ z : ℝ, ∃ y : Fin n → ℝ,
        (k + 1 : ℝ) * z ^ 2 = 1 ∧
        OnSourceProductSpheres sourceBlock y ∧
        x = PolynomialCode.unitChartPoint z (z • y) := by
  constructor
  · intro hradii
    refine ⟨x 0, chartQuotient x,
      chartCoordinate_sheet_of_all_radii_one
        sourceBlock x hradii,
      chartQuotient_onSourceProductSpheres
        sourceBlock x hradii, ?_⟩
    exact (unitChartPoint_chartQuotient x
      (chartCoordinate_ne_zero_of_all_radii_one
        sourceBlock x hradii)).symm
  · rintro ⟨z, y, hz, hy, rfl⟩
    exact scaledBlockRadius_eq_one_on_chart
      sourceBlock z hz y hy

/-- A normalized chart coordinate has one of the two signs. -/
theorem chartCoordinate_pos_or_neg_of_sheet
    (z : ℝ) (hz : (k + 1 : ℝ) * z ^ 2 = 1) :
    0 < z ∨ z < 0 := by
  have hz0 : z ≠ 0 := by
    intro hzero
    rw [hzero] at hz
    norm_num at hz
  exact lt_or_gt_of_ne hz0.symm

/-- Positive part of the concrete full stratum. -/
def positiveFullSheet
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    Set (EuclideanUnitSphere (EuclideanWrapperSpace n)) :=
  {u |
    u ∈ (radiusCleanupFlowCertificate
      sourceBlock D P a).fullStratum ∧
    0 < wrapperEuclideanEquiv.symm u.1 0}

/-- Negative part of the concrete full stratum. -/
def negativeFullSheet
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    Set (EuclideanUnitSphere (EuclideanWrapperSpace n)) :=
  {u |
    u ∈ (radiusCleanupFlowCertificate
      sourceBlock D P a).fullStratum ∧
    wrapperEuclideanEquiv.symm u.1 0 < 0}

/-- The full stratum is exactly the disjoint union of its positive and
negative normalized chart sheets. -/
theorem mem_fullStratum_iff_mem_positive_or_negative
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (u : EuclideanUnitSphere (EuclideanWrapperSpace n)) :
    u ∈ (radiusCleanupFlowCertificate
        sourceBlock D P a).fullStratum ↔
      u ∈ positiveFullSheet sourceBlock D P a ∨
      u ∈ negativeFullSheet sourceBlock D P a := by
  constructor
  · intro hu
    have hradii :
        ∀ b, scaledBlockRadius sourceBlock
          (wrapperEuclideanEquiv.symm u.1) b = 1 := by
      intro b
      have hb := hu b
      simpa only [radiusCleanupFlowCertificate_radii_apply] using hb
    rcases chartCoordinate_pos_or_neg_of_sheet
        (wrapperEuclideanEquiv.symm u.1 0)
        (chartCoordinate_sheet_of_all_radii_one
          sourceBlock _ hradii) with hpos | hneg
    · exact Or.inl ⟨hu, hpos⟩
    · exact Or.inr ⟨hu, hneg⟩
  · rintro (⟨hu, _⟩ | ⟨hu, _⟩)
    · exact hu
    · exact hu

/-- The two chart sheets are disjoint. -/
theorem disjoint_positiveFullSheet_negativeFullSheet
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    Disjoint
      (positiveFullSheet sourceBlock D P a)
      (negativeFullSheet sourceBlock D P a) := by
  rw [Set.disjoint_left]
  rintro u ⟨_, hpos⟩ ⟨_, hneg⟩
  linarith

end UnitSpherePolynomialWrapper

end

end HGAS
