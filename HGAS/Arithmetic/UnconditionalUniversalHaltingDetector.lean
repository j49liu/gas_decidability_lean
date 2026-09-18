import HGAS.Arithmetic.UnconditionalMRDP
import HGAS.Arithmetic.UniversalHaltingDetector

/-!
# Unconditional universal-halting detector

Specialization of the arithmetic-to-Fourier-detector bridge to the proved
primitive-recursive MRDP theorem.
-/

namespace HGAS

open MeasureTheory

noncomputable section

local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs
    (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs
    (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Positivity of the fixed-parameter detector integral is exactly
universal halting. -/
theorem unconditionalUniversalHalting_halfDetectorIntegral_re_pos_iff
    (input : ℕ) :
    0 < (∫ phase,
      expandedDetector (1 / 2 : ℝ) (1 / 2 : ℝ)
        (UniversalHalting.unconditionalUniversalHaltingDQL input)
        phase).re ↔
      UniversalHalting.Predicate input := by
  simpa [UniversalHalting.unconditionalUniversalHaltingDQL] using
    universalHalting_halfDetectorIntegral_re_pos_iff
      UniversalHalting.binaryPrimitiveRecursiveRelationsAreDiophantine
      input

/-- Consequently, fixed-parameter detector positivity is undecidable. -/
theorem unconditionalUniversalHalting_halfDetectorIntegral_not_computable :
    ¬ComputablePred
      (fun input : ℕ ↦
        0 < (∫ phase,
          expandedDetector (1 / 2 : ℝ) (1 / 2 : ℝ)
            (UniversalHalting.unconditionalUniversalHaltingDQL input)
            phase).re) := by
  simpa [UniversalHalting.unconditionalUniversalHaltingDQL] using
    universalHalting_halfDetectorIntegral_not_computable
      UniversalHalting.binaryPrimitiveRecursiveRelationsAreDiophantine

end

end HGAS
