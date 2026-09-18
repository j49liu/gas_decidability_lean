import HGAS.Dynamics.PoincareRecurrence
import HGAS.Modular.RecurrentMeasureClassification
import HGAS.Modular.SL2ZFrameFundamentalDomain

/-!
# Consequences of finite volume for the level-two frame quotient

The explicit finite-Haar fundamental domain constructed in
`SL2ZFrameFundamentalDomain` supplies a canonical choice of normalized
right-invariant frame probability.  This file packages that witness,
its horocycle invariance, and Poincaré recurrence.

It also sharpens the remaining classification trust boundary: finite
volume is now unconditional, so the only input still needed for the full
`GammaTwoDaniSmillieTheorem` is the genuinely dynamical
periodic-or-Haar dichotomy.
-/

namespace HGAS.Modular

open Filter _root_.MeasureTheory Set Topology

noncomputable section

/-- A fixed normalized right-Haar probability on the level-two frame
quotient, chosen from the explicit finite-volume construction. -/
def gammaTwoFrameHaarProbability :
    ProbabilityMeasure GammaTwoFrameQuotient :=
  gammaTwoHasFiniteFrameVolume.choose

/-- The chosen frame probability is invariant under every descended
right translation. -/
theorem gammaTwoFrameHaarProbability_rightInvariant :
    IsRightInvariantFrameProbability
      gammaTwoFrameHaarProbability :=
  gammaTwoHasFiniteFrameVolume.choose_spec

/-- In particular, the chosen frame probability is invariant under the
unit-speed horocycle flow. -/
theorem gammaTwoFrameHaarProbability_horocycleInvariant :
    Dynamics.IsInvariantProbability gammaTwoHorocycleFlow
      gammaTwoFrameHaarProbability :=
  gammaTwoFrameHaarProbability_rightInvariant.horocycleInvariant

/-- Package the chosen Haar probability as an invariant probability
measure for the horocycle flow. -/
def gammaTwoFrameHaarInvariantProbability :
    Dynamics.InvariantProbabilityMeasure
      gammaTwoHorocycleFlow :=
  ⟨gammaTwoFrameHaarProbability,
    gammaTwoFrameHaarProbability_horocycleInvariant⟩

/-- Haar-almost every frame class is forward recurrent for the
horocycle flow. -/
theorem gammaTwoFrameHaarProbability_ae_forwardRecurrent :
    ∀ᵐ q ∂(gammaTwoFrameHaarProbability :
        Measure GammaTwoFrameQuotient),
      HGAS.ForwardRecurrentAt
        (fun t : ℝ ↦ gammaTwoHorocycleFlow t q) 0 := by
  letI : MetricSpace GammaTwoFrameQuotient :=
    TopologicalSpace.metrizableSpaceMetric
      GammaTwoFrameQuotient
  exact
    gammaTwoFrameHaarInvariantProbability
      |>.ae_forwardRecurrentAt_zero

/-- Consequently there exists a forward-recurrent frame class. -/
theorem exists_gammaTwoFrameHaar_forwardRecurrent :
    ∃ q : GammaTwoFrameQuotient,
      HGAS.ForwardRecurrentAt
        (fun t : ℝ ↦ gammaTwoHorocycleFlow t q) 0 := by
  letI : MetricSpace GammaTwoFrameQuotient :=
    TopologicalSpace.metrizableSpaceMetric
      GammaTwoFrameQuotient
  exact
    gammaTwoFrameHaarInvariantProbability
      |>.exists_forwardRecurrentAt_zero

/-- The chosen Haar probability is invariant under every constant
rescaling of the horocycle flow. -/
theorem gammaTwoFrameHaarProbability_scaledInvariant
    (s : ℝ) :
    Dynamics.IsInvariantProbability
      (scaledGammaTwoHorocycleFlow s)
      gammaTwoFrameHaarProbability :=
  gammaTwoFrameHaarProbability_rightInvariant
    |>.scaledHorocycleInvariant s

/-- Poincaré recurrence also holds for every constant rescaling of the
horocycle flow. -/
theorem gammaTwoFrameHaarProbability_ae_scaledForwardRecurrent
    (s : ℝ) :
    ∀ᵐ q ∂(gammaTwoFrameHaarProbability :
        Measure GammaTwoFrameQuotient),
      HGAS.ForwardRecurrentAt
        (fun t : ℝ ↦
          scaledGammaTwoHorocycleFlow s t q) 0 := by
  letI : MetricSpace GammaTwoFrameQuotient :=
    TopologicalSpace.metrizableSpaceMetric
      GammaTwoFrameQuotient
  let μ :
      Dynamics.InvariantProbabilityMeasure
        (scaledGammaTwoHorocycleFlow s) :=
    ⟨gammaTwoFrameHaarProbability,
      gammaTwoFrameHaarProbability_scaledInvariant s⟩
  exact μ.ae_forwardRecurrentAt_zero

/-- Once the genuine Dani--Smillie periodic-or-Haar dichotomy is
supplied, no further finite-volume hypothesis is needed: the full
classification interface consumed by the recurrent-measure bridge
follows unconditionally from the explicit domain above. -/
theorem gammaTwoDaniSmillieTheorem_of_ergodicHorocycleDichotomy
    (hdynamics : GammaTwoErgodicHorocycleDichotomy) :
    GammaTwoDaniSmillieTheorem :=
  gammaTwoHasFiniteHaarFundamentalDomain
    |>.daniSmillie_of_dichotomy hdynamics

/-- A version of the preceding theorem using the fixed Haar
probability chosen in this file. -/
theorem gammaTwoFrameHaarProbability_daniSmillieClassification
    (hdynamics : GammaTwoErgodicHorocycleDichotomy) :
    DaniSmillieClassification
      gammaTwoFrameHaarProbability := by
  refine
    ⟨gammaTwoFrameHaarProbability_rightInvariant, ?_⟩
  exact
    hdynamics gammaTwoFrameHaarProbability
      gammaTwoFrameHaarProbability_rightInvariant

end

end HGAS.Modular
