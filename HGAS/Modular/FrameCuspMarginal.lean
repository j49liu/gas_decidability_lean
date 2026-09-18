import HGAS.Modular.SL2ZFrameFundamentalDomain
import HGAS.Modular.UpperHalfPlaneCuspMarginal
import Mathlib.Tactic

/-!
# A positive cusp marginal in the integral frame domain

The frame fundamental domain uses the standard modular base domain and
one measurable half of each central pair `{g, -g}`.  This file proves
that its high-cusp part has a positive constant multiple of
`dy / y²` as height marginal.

There are two independent constants in the calculation:

* ambient Haar measure projects to `b` times hyperbolic area, with
  `b > 0`;
* the sign convention keeps exactly one half of every pair
  `{g, -g}`.

Thus the final transverse constant is `b / 2`, and in particular is
nonzero.
-/

namespace HGAS.Modular

open Function Matrix _root_.MeasureTheory
  _root_.MeasureTheory.Measure Set
open scoped ENNReal NNReal

noncomputable section

private theorem continuous_neg_realModularFrame :
    Continuous (fun g : RealModularFrame ↦ -g) := by
  exact (continuous_subtype_val.neg).subtype_mk _

/-- The complementary measurable frame half. -/
def negativeFrameHalf : Set RealModularFrame :=
  {g | -g ∈ positiveFrameHalf}

theorem measurableSet_negativeFrameHalf :
    MeasurableSet negativeFrameHalf := by
  exact
    measurableSet_positiveFrameHalf.preimage
      continuous_neg_realModularFrame.measurable

theorem positiveFrameHalf_union_negativeFrameHalf :
    positiveFrameHalf ∪ negativeFrameHalf = Set.univ := by
  ext g
  simp only [mem_union, mem_univ, iff_true,
    negativeFrameHalf, mem_setOf_eq]
  exact mem_positiveFrameHalf_or_neg g

theorem positiveFrameHalf_disjoint_negativeFrameHalf :
    Disjoint positiveFrameHalf negativeFrameHalf := by
  rw [Set.disjoint_left]
  intro g hg hneg
  exact not_mem_positiveFrameHalf_neg_of_mem hg hneg

/-- Frames above the standard rectangular cusp, with the positive
central sign convention. -/
def frameCuspRectangle (Y : ℝ) : Set RealModularFrame :=
  realModularFrameBasePoint ⁻¹'
      upperHalfPlaneCuspRectangle Y ∩
    positiveFrameHalf

theorem measurableSet_frameCuspRectangle (Y : ℝ) :
    MeasurableSet (frameCuspRectangle Y) :=
  ((measurableSet_upperHalfPlaneCuspRectangle Y).preimage
      realModularFrameBasePoint_continuous.measurable).inter
    measurableSet_positiveFrameHalf

theorem frameCuspRectangle_subset_integralFrameFundamentalDomain
    {Y : ℝ} (hY : 1 < Y) :
    frameCuspRectangle Y ⊆ integralFrameFundamentalDomain := by
  intro g hg
  exact
    ⟨upperHalfPlaneCuspRectangle_subset_fdo hY hg.1,
      hg.2⟩

/-- The height coordinate on frames. -/
def realModularFrameHeight (g : RealModularFrame) : ℝ :=
  (realModularFrameBasePoint g).im

theorem measurable_realModularFrameHeight :
    Measurable realModularFrameHeight := by
  unfold realModularFrameHeight
  exact
    UpperHalfPlane.continuous_im.measurable.comp
      realModularFrameBasePoint_continuous.measurable

@[simp]
theorem realModularFrameBasePoint_neg
    (g : RealModularFrame) :
    realModularFrameBasePoint (-g) =
      realModularFrameBasePoint g := by
  unfold realModularFrameBasePoint
  change
    (Matrix.SpecialLinearGroup.mapGL ℝ (-g)) • UpperHalfPlane.I =
      (Matrix.SpecialLinearGroup.mapGL ℝ g) • UpperHalfPlane.I
  rw [show
    Matrix.SpecialLinearGroup.mapGL ℝ (-g) =
      -(Matrix.SpecialLinearGroup.mapGL ℝ g) by
        ext i j
        simp [Matrix.SpecialLinearGroup.mapGL]]
  exact UpperHalfPlane.neg_smul _ _

@[simp]
theorem realModularFrameHeight_neg
    (g : RealModularFrame) :
    realModularFrameHeight (-g) =
      realModularFrameHeight g := by
  simp [realModularFrameHeight]

private theorem map_neg_haar :
    Measure.map (fun g : RealModularFrame ↦ -g)
        (Measure.haar : Measure RealModularFrame) =
      (Measure.haar : Measure RealModularFrame) := by
  have hfun :
      (fun g : RealModularFrame ↦ -g) =
        fun g ↦ (-1 : RealModularFrame) * g := by
    funext g
    apply Subtype.ext
    simp
  rw [hfun]
  exact
    map_mul_left_eq_self
      (Measure.haar : Measure RealModularFrame)
      (-1 : RealModularFrame)

private theorem neg_preimage_negativeFrameHalf :
    (fun g : RealModularFrame ↦ -g) ⁻¹'
        negativeFrameHalf =
      positiveFrameHalf := by
  ext g
  simp [negativeFrameHalf]

private def negativeFrameCuspRectangle
    (Y : ℝ) : Set RealModularFrame :=
  realModularFrameBasePoint ⁻¹'
      upperHalfPlaneCuspRectangle Y ∩
    negativeFrameHalf

private theorem measurableSet_negativeFrameCuspRectangle
    (Y : ℝ) :
    MeasurableSet (negativeFrameCuspRectangle Y) :=
  ((measurableSet_upperHalfPlaneCuspRectangle Y).preimage
      realModularFrameBasePoint_continuous.measurable).inter
    measurableSet_negativeFrameHalf

private theorem frameCuspRectangle_union_negative
    (Y : ℝ) :
    frameCuspRectangle Y ∪
        negativeFrameCuspRectangle Y =
      realModularFrameBasePoint ⁻¹'
        upperHalfPlaneCuspRectangle Y := by
  rw [frameCuspRectangle, negativeFrameCuspRectangle,
    ← inter_union_distrib_left,
    positiveFrameHalf_union_negativeFrameHalf,
    inter_univ]

private theorem frameCuspRectangle_disjoint_negative
    (Y : ℝ) :
    Disjoint (frameCuspRectangle Y)
      (negativeFrameCuspRectangle Y) :=
  positiveFrameHalf_disjoint_negativeFrameHalf.mono
    inter_subset_right inter_subset_right

private theorem neg_preimage_negativeFrameCuspRectangle
    (Y : ℝ) :
    (fun g : RealModularFrame ↦ -g) ⁻¹'
        negativeFrameCuspRectangle Y =
      frameCuspRectangle Y := by
  ext g
  simp [negativeFrameCuspRectangle, frameCuspRectangle,
    negativeFrameHalf]

private theorem map_height_negativeFrameCuspRectangle
    (Y : ℝ) :
    Measure.map realModularFrameHeight
        ((Measure.haar : Measure RealModularFrame).restrict
          (negativeFrameCuspRectangle Y)) =
      Measure.map realModularFrameHeight
        ((Measure.haar : Measure RealModularFrame).restrict
          (frameCuspRectangle Y)) := by
  have hrestrict :
      (Measure.haar : Measure RealModularFrame).restrict
          (negativeFrameCuspRectangle Y) =
        Measure.map (fun g : RealModularFrame ↦ -g)
          ((Measure.haar : Measure RealModularFrame).restrict
            (frameCuspRectangle Y)) := by
    calc
      (Measure.haar : Measure RealModularFrame).restrict
          (negativeFrameCuspRectangle Y) =
          (Measure.map (fun g : RealModularFrame ↦ -g)
            (Measure.haar : Measure RealModularFrame)).restrict
              (negativeFrameCuspRectangle Y) := by
            rw [map_neg_haar]
      _ =
          Measure.map (fun g : RealModularFrame ↦ -g)
            ((Measure.haar : Measure RealModularFrame).restrict
              ((fun g : RealModularFrame ↦ -g) ⁻¹'
                negativeFrameCuspRectangle Y)) := by
            rw [Measure.restrict_map
              continuous_neg_realModularFrame.measurable
              (measurableSet_negativeFrameCuspRectangle Y)]
      _ =
          Measure.map (fun g : RealModularFrame ↦ -g)
            ((Measure.haar : Measure RealModularFrame).restrict
              (frameCuspRectangle Y)) := by
            rw [neg_preimage_negativeFrameCuspRectangle]
  rw [hrestrict,
    Measure.map_map measurable_realModularFrameHeight
      continuous_neg_realModularFrame.measurable]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall
    realModularFrameHeight_neg

/-- The full frame preimage of a rectangular cusp has the same height
marginal as the projected Haar measure on the base. -/
private theorem map_height_restrict_baseCusp
    (Y : ℝ) (hY : 0 < Y) :
    ∃ b : ℝ≥0, b ≠ 0 ∧
      Measure.map realModularFrameHeight
          ((Measure.haar : Measure RealModularFrame).restrict
            (realModularFrameBasePoint ⁻¹'
              upperHalfPlaneCuspRectangle Y)) =
        b • HGAS.Dynamics.cuspHeightMeasure Y := by
  obtain ⟨b, hb⟩ :=
    frameBaseProjectionMeasure_eq_smul_volume
      (Measure.haar : Measure RealModularFrame)
  have hb0 : b ≠ 0 := by
    intro hbzero
    apply
      frameBaseProjectionMeasure_ne_zero
        (Measure.haar : Measure RealModularFrame)
    rw [hb, hbzero, zero_smul]
  refine ⟨b, hb0, ?_⟩
  calc
    Measure.map realModularFrameHeight
        ((Measure.haar : Measure RealModularFrame).restrict
          (realModularFrameBasePoint ⁻¹'
            upperHalfPlaneCuspRectangle Y)) =
        Measure.map (fun τ : UpperHalfPlane ↦ τ.im)
          (Measure.map realModularFrameBasePoint
            ((Measure.haar : Measure RealModularFrame).restrict
              (realModularFrameBasePoint ⁻¹'
                upperHalfPlaneCuspRectangle Y))) := by
          rw [Measure.map_map (by fun_prop)
            realModularFrameBasePoint_continuous.measurable]
          rfl
    _ =
        Measure.map (fun τ : UpperHalfPlane ↦ τ.im)
          ((Measure.map realModularFrameBasePoint
              (Measure.haar : Measure RealModularFrame)).restrict
            (upperHalfPlaneCuspRectangle Y)) := by
          rw [Measure.restrict_map
            realModularFrameBasePoint_continuous.measurable
            (measurableSet_upperHalfPlaneCuspRectangle Y)]
    _ =
        Measure.map (fun τ : UpperHalfPlane ↦ τ.im)
          ((b • (volume : Measure UpperHalfPlane)).restrict
            (upperHalfPlaneCuspRectangle Y)) := by
          rw [show
            Measure.map realModularFrameBasePoint
                (Measure.haar : Measure RealModularFrame) =
              b • (volume : Measure UpperHalfPlane) from hb]
    _ =
        b • Measure.map (fun τ : UpperHalfPlane ↦ τ.im)
          ((volume : Measure UpperHalfPlane).restrict
            (upperHalfPlaneCuspRectangle Y)) := by
          rw [Measure.restrict_smul, Measure.map_smul]
    _ = b • HGAS.Dynamics.cuspHeightMeasure Y := by
          rw [map_im_restrict_upperHalfPlaneCuspRectangle Y hY]

/-- The positive-sign part of the integral frame domain has a positive
standard cusp-height marginal. -/
theorem exists_positive_frameCuspRectangle_heightMarginal
    (Y : ℝ) (hY : 0 < Y) :
    ∃ c : ℝ≥0, c ≠ 0 ∧
      Measure.map realModularFrameHeight
          ((Measure.haar : Measure RealModularFrame).restrict
            (frameCuspRectangle Y)) =
        c • HGAS.Dynamics.cuspHeightMeasure Y := by
  obtain ⟨b, hb0, hfull⟩ :=
    map_height_restrict_baseCusp Y hY
  let P : Measure ℝ :=
    Measure.map realModularFrameHeight
      ((Measure.haar : Measure RealModularFrame).restrict
        (frameCuspRectangle Y))
  have hdecompose :
      (Measure.haar : Measure RealModularFrame).restrict
          (realModularFrameBasePoint ⁻¹'
            upperHalfPlaneCuspRectangle Y) =
        (Measure.haar : Measure RealModularFrame).restrict
            (frameCuspRectangle Y) +
          (Measure.haar : Measure RealModularFrame).restrict
            (negativeFrameCuspRectangle Y) := by
    rw [← Measure.restrict_union
      (frameCuspRectangle_disjoint_negative Y)
      (measurableSet_negativeFrameCuspRectangle Y),
      frameCuspRectangle_union_negative]
  have htwice :
      b • HGAS.Dynamics.cuspHeightMeasure Y =
        (2 : ℝ≥0) • P := by
    rw [← hfull, hdecompose,
      Measure.map_add _ _ measurable_realModularFrameHeight,
      map_height_negativeFrameCuspRectangle]
    simp only [P, two_smul]
  let c : ℝ≥0 := b / 2
  have hc0 : c ≠ 0 := div_ne_zero hb0 (by norm_num)
  refine ⟨c, hc0, ?_⟩
  have hscaled :=
    congrArg
      (fun μ : Measure ℝ ↦ (1 / 2 : ℝ≥0) • μ)
      htwice
  have htwo : (2 / 2 : ℝ≥0) = 1 := by
    norm_num
  simpa only [P, smul_smul, c, one_div, inv_mul_cancel₀,
    one_smul, inv_mul_eq_div, htwo] using hscaled.symm

end

end HGAS.Modular
