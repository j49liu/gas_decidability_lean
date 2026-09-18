import HGAS.Modular.GammaTwoFrameQuotient
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Tactic

/-!
# Projecting Haar measure to the upper half-plane

The orbit map

`SL(2, ℝ) → ℍ,  g ↦ g • I`

has compact fibres and is proper.  Consequently the push-forward of a
Haar measure is a nonzero locally finite invariant measure on `ℍ`.

This is the exact measure-theoretic bridge needed to compare Haar
measure on frames with hyperbolic area on the base.  The remaining
comparison is uniqueness, up to scale, of locally finite invariant
measures on the homogeneous space `SL(2, ℝ) / SO(2)`.
-/

namespace HGAS.Modular

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

noncomputable section

/-- The push-forward of an ambient frame measure by the base-point
map. -/
def frameBaseProjectionMeasure
    (m : Measure RealModularFrame) :
    Measure UpperHalfPlane :=
  m.map realModularFrameBasePoint

@[simp]
theorem frameBaseProjectionMeasure_apply
    (m : Measure RealModularFrame)
    {A : Set UpperHalfPlane} (hA : MeasurableSet A) :
    frameBaseProjectionMeasure m A =
      m (realModularFrameBasePoint ⁻¹' A) := by
  rw [frameBaseProjectionMeasure,
    Measure.map_apply
      realModularFrameBasePoint_continuous.measurable hA]

/-- Properness of the base-point map makes the projected Haar measure
finite on compact subsets of `ℍ`. -/
theorem frameBaseProjectionMeasure_isFiniteMeasureOnCompacts
    (m : Measure RealModularFrame) [IsHaarMeasure m] :
    IsFiniteMeasureOnCompacts
      (frameBaseProjectionMeasure m) := by
  constructor
  intro K hK
  rw [frameBaseProjectionMeasure_apply m hK.measurableSet]
  exact
    (UpperHalfPlane.isProperMap_smul_I.isCompact_preimage hK).measure_lt_top

/-- Left invariance of Haar measure descends to invariance of its
base-point projection under `SL(2, ℝ)`. -/
theorem frameBaseProjectionMeasure_smulInvariant
    (m : Measure RealModularFrame) [IsHaarMeasure m] :
    SMulInvariantMeasure RealModularFrame UpperHalfPlane
      (frameBaseProjectionMeasure m) := by
  unfold frameBaseProjectionMeasure
  apply smulInvariantMeasure_map m
  · intro a g
    change (a * g) • UpperHalfPlane.I =
      a • (g • UpperHalfPlane.I)
    exact mul_smul a g UpperHalfPlane.I
  · exact realModularFrameBasePoint_continuous.measurable

/-- The projected Haar measure is nonzero. -/
theorem frameBaseProjectionMeasure_ne_zero
    (m : Measure RealModularFrame) [IsHaarMeasure m] :
    frameBaseProjectionMeasure m ≠ 0 := by
  rw [← measure_univ_pos]
  rw [frameBaseProjectionMeasure_apply m MeasurableSet.univ]
  simp only [preimage_univ]
  exact
    pos_iff_ne_zero.mpr
      (isOpen_univ.measure_ne_zero m univ_nonempty)

/-- Package the three structural facts about the projected Haar
measure without installing global typeclass instances. -/
theorem exists_nonzero_locallyFinite_invariant_base_measure :
    ∃ μ : Measure UpperHalfPlane,
      μ ≠ 0 ∧
      IsFiniteMeasureOnCompacts μ ∧
      SMulInvariantMeasure RealModularFrame UpperHalfPlane μ := by
  let m : Measure RealModularFrame := Measure.haar
  refine ⟨frameBaseProjectionMeasure m,
    frameBaseProjectionMeasure_ne_zero m,
    frameBaseProjectionMeasure_isFiniteMeasureOnCompacts m,
    frameBaseProjectionMeasure_smulInvariant m⟩

end

end HGAS.Modular
