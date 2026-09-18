import HGAS.Modular.StandardFundamentalDomainVolume
import HGAS.Modular.UpperHalfPlanePositiveAffine

/-!
# Haar volume above the standard modular domain

This file combines two independent ingredients:

* finite hyperbolic area of the standard modular fundamental domain;
* uniqueness, up to scale, of locally finite invariant measures on the
  upper half-plane.

It follows that the set of real modular frames whose base point lies in
the standard modular domain has finite Haar measure.
-/

namespace HGAS.Modular

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal NNReal

noncomputable section

/-- The push-forward to `ℍ` of any Haar measure on `SL(2, ℝ)` is a
scalar multiple of hyperbolic area. -/
theorem frameBaseProjectionMeasure_eq_smul_volume
    (m : Measure RealModularFrame) [IsHaarMeasure m] :
    ∃ c : ℝ≥0,
      frameBaseProjectionMeasure m =
        c • (volume : Measure UpperHalfPlane) := by
  letI :
      IsFiniteMeasureOnCompacts
        (frameBaseProjectionMeasure m) :=
    frameBaseProjectionMeasure_isFiniteMeasureOnCompacts m
  letI :
      SMulInvariantMeasure RealModularFrame UpperHalfPlane
        (frameBaseProjectionMeasure m) :=
    frameBaseProjectionMeasure_smulInvariant m
  exact
    locallyFinite_invariant_eq_smul_upperHalfPlaneVolume
      (frameBaseProjectionMeasure m)

/-- The inverse image of the standard modular domain under the frame
base-point map has finite Haar measure. -/
theorem haar_basePoint_preimage_modular_fd_ne_top :
    (Measure.haar : Measure RealModularFrame)
        (realModularFrameBasePoint ⁻¹' ModularGroup.fd) ≠ ∞ := by
  rw [← frameBaseProjectionMeasure_apply
    (Measure.haar : Measure RealModularFrame)
    ModularGroup.isClosed_fd.measurableSet]
  obtain ⟨c, hc⟩ :=
    frameBaseProjectionMeasure_eq_smul_volume
      (Measure.haar : Measure RealModularFrame)
  rw [hc]
  exact ENNReal.nnreal_smul_ne_top modular_fd_volume_ne_top

end

end HGAS.Modular
