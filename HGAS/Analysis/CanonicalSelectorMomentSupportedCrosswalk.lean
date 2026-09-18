import HGAS.Arithmetic.CorrectedCanonicalFixedDetectorMomentFourierCrosswalk
import HGAS.Arithmetic.CorrectedFixedDetectorMomentSemantics
import Mathlib.Tactic

/-!
# Uniform supported-family crosswalk for the seven selector moments

The analytic crosswalk proves the seven corrected moment identities one
at a time.  The finite-graph construction needs one family selected by a
runtime moment index.  This file packages the seven cases into a single
dependent interface and then flattens the variable/moment pair in exactly
the order used by `CorrectedFixedDetectorMomentCode`.
-/

noncomputable section

namespace HGAS.Analysis.CanonicalSelectorMomentSupportedCrosswalk

open HGAS
open HGAS.Analysis.CanonicalSelectorMomentAggregatedFamilies
open HGAS.CorrectedCanonicalFixedDetectorMomentFourierCrosswalk

variable {eqs vars : ℕ}

/-- The centered family belonging to one of the seven local selector
moments. -/
def localFamily
    (I : DQLSystem eqs vars)
    (j : Fin vars)
    (r : Fin CorrectedFixedDetectorMomentCode.localMomentCount) :
    RawCenteredFamily eqs vars :=
  ![
    unaryMean I j,
    unaryFirst I j,
    rootP4 j,
    rootP2 j,
    jacobiMean I j,
    jacobiPlus I j,
    jacobiMinus I j
  ] r

/-- One harmless radicand used only to invoke ordinary coefficient
summability from the stronger weighted theorem. -/
def harmlessRadicand :
    Fin (vars + eqs) → ℕ :=
  fun _ ↦ 2

/-- Uniform raw-series form of the seven explicit crosswalk theorems. -/
theorem localMomentValue_eq_rawSeries
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Clocks.Controller.ControllerState ℝ)
    (t : ℝ)
    (j : Fin vars)
    (r : Fin CorrectedFixedDetectorMomentCode.localMomentCount) :
    CorrectedFixedDetectorMomentCode.localMomentValue I j
        (canonicalState parameters I controller t) r =
      torusFourierSeries
        (localFamily I j r).coefficient
        (localFamily I j r).flatExponent
        (phase parameters controller t) := by
  fin_cases r
  · simpa [localFamily] using
      localMomentValue_zero_eq_unaryMean_series
        parameters I controller t j
  · simpa [localFamily] using
      localMomentValue_one_eq_unaryFirst_series
        parameters I controller t j
  · simpa [localFamily] using
      localMomentValue_two_eq_rootP4_series
        parameters I controller t j
  · simpa [localFamily] using
      localMomentValue_three_eq_rootP2_series
        parameters I controller t j
  · simpa [localFamily] using
      localMomentValue_four_eq_jacobiMean_series
        parameters I controller t j
  · simpa [localFamily] using
      localMomentValue_five_eq_jacobiPlus_series
        parameters I controller t j
  · simpa [localFamily] using
      localMomentValue_six_eq_jacobiMinus_series
        parameters I controller t j

/-- Uniform supported-series form.  Equal exponents have been collected,
zero coefficients discarded, and no analytic value has changed. -/
theorem localMomentValue_eq_supportedSeries
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Clocks.Controller.ControllerState ℝ)
    (t : ℝ)
    (j : Fin vars)
    (r : Fin CorrectedFixedDetectorMomentCode.localMomentCount) :
    CorrectedFixedDetectorMomentCode.localMomentValue I j
        (canonicalState parameters I controller t) r =
      torusFourierSeries
        (localFamily I j r).supportedCoefficient
        (localFamily I j r).supportedExponent
        (phase parameters controller t) := by
  rw [(localFamily I j r).torusFourierSeries_supported
    (harmlessRadicand (eqs := eqs) (vars := vars))]
  exact
    localMomentValue_eq_rawSeries parameters I controller t j r

/-- Family selected by the compiler's flattened complex-moment index. -/
def momentFamily
    (I : DQLSystem eqs vars)
    (k : Fin (CorrectedFixedDetectorMomentCode.momentCount vars)) :
    RawCenteredFamily eqs vars :=
  let jr := finProdFinEquiv.symm k
  localFamily I jr.1 jr.2

/-- The flattened semantic complex moment equals its selected supported
Fourier family on the canonical orbit. -/
theorem momentValue_eq_supportedSeries
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Clocks.Controller.ControllerState ℝ)
    (t : ℝ)
    (k : Fin (CorrectedFixedDetectorMomentCode.momentCount vars)) :
    CorrectedFixedDetectorMomentCode.momentValue I
        (canonicalState parameters I controller t) k =
      torusFourierSeries
        (momentFamily I k).supportedCoefficient
        (momentFamily I k).supportedExponent
        (phase parameters controller t) := by
  let jr := finProdFinEquiv.symm k
  change
    CorrectedFixedDetectorMomentCode.localMomentValue I jr.1
        (canonicalState parameters I controller t) jr.2 =
      torusFourierSeries
        (localFamily I jr.1 jr.2).supportedCoefficient
        (localFamily I jr.1 jr.2).supportedExponent
        (phase parameters controller t)
  exact
    localMomentValue_eq_supportedSeries
      parameters I controller t jr.1 jr.2

end HGAS.Analysis.CanonicalSelectorMomentSupportedCrosswalk
