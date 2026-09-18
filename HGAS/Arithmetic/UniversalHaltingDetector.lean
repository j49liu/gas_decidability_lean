import HGAS.Arithmetic.DetectorFourier
import HGAS.Arithmetic.UniversalHaltingDiophantineGap
import Mathlib.Tactic

/-!
# Universal halting as a positive detector integral

This module records the exact point at which the finite arithmetic
compiler meets the analytic constant-term detector.

Assume the binary primitive-recursive closure case of DPRM used in
`UniversalHaltingDiophantineGap`.  For an input natural number, that module
produces a finite diagonal--quadratic--linear system whose solvability is
equivalent to halting of the fixed universal interpreter.  The detector
theorem then turns solvability into strict positivity of one normalized
Haar integral.

The numerical parameters are fixed once and for all at `1/2`.  Thus no
choice of an analytic convergence parameter depends on the input.

This is still not a reduction to a polynomial vector field: constructing
the clocked modular source, proving its all-state invariant-measure
classification, and applying the compact wrapper are separate downstream
obligations.
-/

namespace HGAS

open MeasureTheory

noncomputable section

/-! Use the same normalized Haar instance as `DetectorFourier`. -/

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

/-- For every finite DQL system, the detector with the fixed parameters
`lambda = eta = 1/2` has positive real Haar average exactly when the system
has an integer solution. -/
theorem halfDetectorIntegral_re_pos_iff_solvable
    {eqs vars : ℕ} (I : DQLSystem eqs vars) :
    0 < (∫ phase : UnitAddTorus (DetectorPhase eqs vars),
      expandedDetector (1 / 2 : ℝ) (1 / 2 : ℝ) I phase).re ↔
        I.Solvable := by
  exact integral_expandedDetector_re_pos_iff_solvable
    (lambda := (1 / 2 : ℝ)) (eta := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) I

/-- **Arithmetic-to-detector bridge.**  Subject only to the stated DPRM
closure theorem, positivity of the fixed-parameter detector integral for
the compiled instance is equivalent to universal halting. -/
theorem universalHalting_halfDetectorIntegral_re_pos_iff
    (closure :
      UniversalHalting.BinaryPrimitiveRecursiveRelationsAreDiophantine)
    (input : ℕ) :
    0 < (∫ phase,
      expandedDetector (1 / 2 : ℝ) (1 / 2 : ℝ)
        (UniversalHalting.universalHaltingDQL closure input)
        phase).re ↔
      UniversalHalting.Predicate input := by
  exact
    (halfDetectorIntegral_re_pos_iff_solvable
      (UniversalHalting.universalHaltingDQL closure input)).trans
        (UniversalHalting.universalHaltingDQL_solvable_iff
          closure input)

/-- Consequently, a decision procedure for the detector-positivity
predicate would decide the universal interpreter's halting predicate. -/
theorem universalHalting_halfDetectorIntegral_not_computable
    (closure :
      UniversalHalting.BinaryPrimitiveRecursiveRelationsAreDiophantine) :
    ¬ComputablePred
      (fun input : ℕ ↦
        0 < (∫ phase,
          expandedDetector (1 / 2 : ℝ) (1 / 2 : ℝ)
            (UniversalHalting.universalHaltingDQL closure input)
            phase).re) := by
  intro hcomputable
  apply UniversalHalting.predicate_not_computable
  exact ComputablePred.of_eq hcomputable fun input ↦
    universalHalting_halfDetectorIntegral_re_pos_iff closure input

end

end HGAS
