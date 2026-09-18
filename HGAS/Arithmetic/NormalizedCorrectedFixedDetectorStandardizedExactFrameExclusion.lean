import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorStandardizedUnitSpeedHaarExclusion
import HGAS.Modular.GammaTwoOffPeriodicUnique
import HGAS.Modular.GammaTwoScaledPointwiseEquidistribution
import Mathlib.Tactic

/-!
# Excluding the Haar-generic exact-frame branch

This file is the direct composition layer between two independent pieces
of the detector argument.

* Exact signed column standardization gives a canonical-lambda lift which
  is either a horizontal line or a literal real-frame horocycle
  `g * u(σt)`, with `σ ≠ 0`.
* The compact-cusp estimate proves that such a literal frame orbit cannot
  be forward generic for frame Haar probability.

The first theorem below packages those facts without changing either
interface.  A separate reusable proposition records signed-speed
pointwise equidistribution.  The final theorem does not need to assume
that proposition: inverse-speed reparametrization transports the detector
estimate itself to the positive unit-speed flow, so the existing
unconditional Dani--Smillie theorem applies directly.
-/

namespace
  HGAS.NormalizedCorrectedFixedDetectorStandardizedExactFrameExclusion

open HGAS
open HGAS.Modular
open _root_.MeasureTheory
open UpperHalfPlane hiding I
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorBidirectionalValidityOrbit
open NormalizedCorrectedFixedDetectorColumnStandardization
open
  NormalizedCorrectedFixedDetectorColumnStandardization.SelectedBidirectionalValidityOrbit
open
  NormalizedCorrectedFixedDetectorStandardizedHaarExclusion.SelectedBidirectionalValidityOrbit
open
  NormalizedFixedDetectorUnitSpeedHaarExclusion.SelectedBidirectionalValidityOrbit

noncomputable section

variable {eqs vars : ℕ}
variable
  {u :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      eqs vars}

/-- The signed-speed pointwise Dani--Smillie interface which is exactly
needed by a literal exact-frame reconstruction.

The periodicity hypothesis is stated for unit speed because periodicity
is already known to be independent of every nonzero scale. -/
def GammaTwoSignedNonzeroOrbitEquidistribution
    (ν : ProbabilityMeasure GammaTwoFrameQuotient) : Prop :=
  ∀ (σ : ℝ), σ ≠ 0 →
    ∀ q : GammaTwoFrameQuotient,
      ¬ IsPeriodicHorocyclePoint 1 q →
        IsForwardGenericFor
          (scaledGammaTwoHorocycleFlow σ) ν q

/-- The existing unconditional pointwise theorem gives precisely the
unit-speed instance of the signed-speed interface. -/
theorem gammaTwoUnitSpeed_nonperiodicOrbitEquidistribution :
    ∀ q : GammaTwoFrameQuotient,
      ¬ IsPeriodicHorocyclePoint 1 q →
        IsForwardGenericFor
          gammaTwoHorocycleFlow
          gammaTwoFrameHaarProbability q :=
  gammaTwoPointwiseHorocycleEquidistribution_unconditional
    gammaTwoFrameHaarProbability
    gammaTwoFrameHaarProbability_rightInvariant

/-- The signed-speed interface is also available unconditionally.  This
gives an independent route to the periodic detector conclusion. -/
theorem gammaTwoSignedNonzeroOrbitEquidistribution_unconditional :
    GammaTwoSignedNonzeroOrbitEquidistribution
      gammaTwoFrameHaarProbability := by
  intro σ hσ q hq
  exact
    gammaTwoPointwiseScaledHorocycleEquidistribution_unconditional
      gammaTwoFrameHaarProbability
      gammaTwoFrameHaarProbability_rightInvariant
      q hq hσ

namespace SelectedBidirectionalValidityOrbit

variable (O : SelectedBidirectionalValidityOrbit u)

private abbrev B :
    SelectedTwoSidedValidityOrbit u :=
  O.toSelectedTwoSidedValidityOrbit

/-- Every selected standardized detector column has a lift which is
horizontal or is a literal exact real-frame horocycle which is *not*
forward generic for frame Haar probability.

This is unconditional and stronger than merely excluding a
nonperiodic/Haar-generic conjunction: periodicity is not used in the
compact-cusp contradiction. -/
theorem
    standardizedUnaryColumn_hasHorizontalOrExactNonHaarFrameLift
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (j : Fin vars) :
    ∃ T : ℝ → ℍ,
      Continuous T ∧
      (∀ t,
        UnaryModularState.lambdaCoordinate
            (standardizedUnaryColumn (B O) j t) =
          canonicalLambda (T t)) ∧
      ((∃ x y s : ℝ, ∃ hy : 0 < y,
          ∀ t,
            T t = horizontalLine x y s hy t) ∨
        ∃ g : RealModularFrame, ∃ σ : ℝ,
          σ ≠ 0 ∧
          (∀ t : ℝ,
            T t =
              realModularFrameBasePoint
                (g * upperUnipotent (σ * t))) ∧
          ¬ IsForwardGenericFor
              (scaledGammaTwoHorocycleFlow σ)
              gammaTwoFrameHaarProbability
              (gammaTwoFrameQuotientMk g)) := by
  obtain ⟨T, hT, hlambda, hhorizontal | hexact⟩ :=
    standardizedUnaryColumn_hasHorizontalOrExactHorocycleFrameLift
      O hscale hp j
  · exact ⟨T, hT, hlambda, Or.inl hhorizontal⟩
  · obtain ⟨g, σ, hσ, hframe⟩ := hexact
    refine
      ⟨T, hT, hlambda, Or.inr
        ⟨g, σ, hσ, hframe, ?_⟩⟩
    intro hgeneric
    exact
      not_haarGeneric_of_standardizedExactFrameBranch
        O hscale hp j T hlambda g σ hσ hframe hgeneric

/-- There is no nonperiodic exact-frame branch which is Haar generic.

The theorem is stated separately because this conjunction is the exact
shape produced when one tries to compose the detector reconstruction
with a pointwise Dani--Smillie dichotomy. -/
theorem
    not_exists_nonperiodic_exactRealFrameHaarGenericBranch
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (j : Fin vars) :
    ¬ ∃ (T : ℝ → ℍ) (g : RealModularFrame) (σ : ℝ),
        (∀ t,
          UnaryModularState.lambdaCoordinate
              (standardizedUnaryColumn (B O) j t) =
            canonicalLambda (T t)) ∧
        σ ≠ 0 ∧
        (∀ t : ℝ,
          T t =
            realModularFrameBasePoint
              (g * upperUnipotent (σ * t))) ∧
        ¬ IsPeriodicHorocyclePoint 1
            (gammaTwoFrameQuotientMk g) ∧
        IsForwardGenericFor
          (scaledGammaTwoHorocycleFlow σ)
          gammaTwoFrameHaarProbability
          (gammaTwoFrameQuotientMk g) := by
  rintro ⟨T, g, σ, hlambda, hσ, hframe, _hnonperiodic,
    hgeneric⟩
  exact
    not_haarGeneric_of_standardizedExactFrameBranch
      O hscale hp j T hlambda g σ hσ hframe hgeneric

/-- If pointwise Dani--Smillie equidistribution is supplied at every
signed nonzero speed, the exact-frame branch of every selected detector
column is necessarily periodic.

This theorem is retained as a reusable abstract composition statement.
The unconditional theorem below bypasses its stronger signed-genericity
hypothesis by reparametrizing the detector estimate to unit speed. -/
theorem standardizedUnaryColumn_hasHorizontalOrPeriodicExactFrameLift
    (hDS :
      GammaTwoSignedNonzeroOrbitEquidistribution
        gammaTwoFrameHaarProbability)
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (j : Fin vars) :
    ∃ T : ℝ → ℍ,
      Continuous T ∧
      (∀ t,
        UnaryModularState.lambdaCoordinate
            (standardizedUnaryColumn (B O) j t) =
          canonicalLambda (T t)) ∧
      ((∃ x y s : ℝ, ∃ hy : 0 < y,
          ∀ t,
            T t = horizontalLine x y s hy t) ∨
        ∃ g : RealModularFrame, ∃ σ : ℝ,
          σ ≠ 0 ∧
          (∀ t : ℝ,
            T t =
              realModularFrameBasePoint
                (g * upperUnipotent (σ * t))) ∧
          IsPeriodicHorocyclePoint 1
            (gammaTwoFrameQuotientMk g)) := by
  obtain ⟨T, hT, hlambda, hhorizontal | hexact⟩ :=
    standardizedUnaryColumn_hasHorizontalOrExactNonHaarFrameLift
      O hscale hp j
  · exact ⟨T, hT, hlambda, Or.inl hhorizontal⟩
  · obtain ⟨g, σ, hσ, hframe, hnotgeneric⟩ := hexact
    refine
      ⟨T, hT, hlambda, Or.inr
        ⟨g, σ, hσ, hframe, ?_⟩⟩
    by_contra hnonperiodic
    exact hnotgeneric
      (hDS σ hσ (gammaTwoFrameQuotientMk g)
        hnonperiodic)

/-- Independent unconditional specialization using the signed pointwise
Dani--Smillie theorem directly. -/
theorem
    standardizedUnaryColumn_hasHorizontalOrPeriodicFrame_viaSignedDS
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (j : Fin vars) :
    ∃ T : ℝ → ℍ,
      Continuous T ∧
      (∀ t,
        UnaryModularState.lambdaCoordinate
            (standardizedUnaryColumn (B O) j t) =
          canonicalLambda (T t)) ∧
      ((∃ x y s : ℝ, ∃ hy : 0 < y,
          ∀ t,
            T t = horizontalLine x y s hy t) ∨
        ∃ g : RealModularFrame, ∃ σ : ℝ,
          σ ≠ 0 ∧
          (∀ t : ℝ,
            T t =
              realModularFrameBasePoint
                (g * upperUnipotent (σ * t))) ∧
          IsPeriodicHorocyclePoint 1
            (gammaTwoFrameQuotientMk g)) :=
  standardizedUnaryColumn_hasHorizontalOrPeriodicExactFrameLift
    O gammaTwoSignedNonzeroOrbitEquidistribution_unconditional
      hscale hp j

/-- **Unconditional direct composition.**  Every selected standardized
detector column has a canonical-lambda lift which is horizontal or a
literal exact real-frame horocycle whose quotient orbit is periodic.

The exact branch may initially have either sign and any nonzero speed.
Inverse-speed reparametrization of the detector estimate reduces it to
the positive unit-speed Dani--Smillie theorem. -/
theorem
    standardizedUnaryColumn_hasHorizontalOrPeriodicExactFrameLift_unconditional
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (j : Fin vars) :
    ∃ T : ℝ → ℍ,
      Continuous T ∧
      (∀ t,
        UnaryModularState.lambdaCoordinate
            (standardizedUnaryColumn (B O) j t) =
          canonicalLambda (T t)) ∧
      ((∃ x y s : ℝ, ∃ hy : 0 < y,
          ∀ t,
            T t = horizontalLine x y s hy t) ∨
        ∃ g : RealModularFrame, ∃ σ : ℝ,
          σ ≠ 0 ∧
          (∀ t : ℝ,
            T t =
              realModularFrameBasePoint
                (g * upperUnipotent (σ * t))) ∧
          IsPeriodicHorocyclePoint 1
            (gammaTwoFrameQuotientMk g)) := by
  obtain ⟨T, hT, hlambda, hhorizontal | hexact⟩ :=
    standardizedUnaryColumn_hasHorizontalOrExactHorocycleFrameLift
      O hscale hp j
  · exact ⟨T, hT, hlambda, Or.inl hhorizontal⟩
  · obtain ⟨g, σ, hσ, hframe⟩ := hexact
    exact
      ⟨T, hT, hlambda, Or.inr
        ⟨g, σ, hσ, hframe,
          periodic_of_standardizedExactFrameBranch
            O hscale hp j T hlambda g σ hσ hframe⟩⟩

end SelectedBidirectionalValidityOrbit

end

end
  HGAS.NormalizedCorrectedFixedDetectorStandardizedExactFrameExclusion
