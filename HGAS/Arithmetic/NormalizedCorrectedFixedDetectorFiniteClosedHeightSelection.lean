import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorColumnCharacters
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorFiniteClosedBranchSelection
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorRawColumnFirstMoment
import HGAS.Modular.HorizontalThetaSignedFirstMoment
import Mathlib.Tactic

/-!
# The exact height of a finite closed detector branch

The finite-cusp selector identifies an actual standardized detector
column with the infinity-cusp theta branch and forces its horizontal
speed to be one.  It remains to determine the height.

The compiler's first centered moment supplies, in physical time,

```text
  Cesàro(Y χ₁) → 1/128.
```

If `a = π/ω` is the possibly signed standardization scale and
`b = a⁻¹`, then physical time sees

```text
  Y(t)  = θ₃(x + b t + i y),
  χ₁(t) = η exp(-π i b t),      ‖η‖ = 1.
```

The signed-speed resonance theorem therefore applies directly, without
converting a forward average into a backward one.  It forces
`exp(-π y)=1/256`, hence `y = log(256)/π`.
-/

namespace
  HGAS.NormalizedCorrectedFixedDetectorFiniteClosedHeightSelection

open HGAS
open Filter
open HGAS.Clocks.ControllerPhaseProductCharacterCode
open HGAS.Modular
open UpperHalfPlane hiding I
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorBidirectionalValidityOrbit
open NormalizedCorrectedFixedDetectorColumnTrajectory
open NormalizedCorrectedFixedDetectorColumnStandardization
open NormalizedCorrectedFixedDetectorColumnCharacters
open NormalizedCorrectedFixedDetectorRawColumnMeans
open NormalizedCorrectedFixedDetectorRawColumnFirstMoment
open NormalizedCorrectedFixedDetectorFiniteClosedBranchSelection
open NormalizedCorrectedFixedDetectorTwoSidedPhysicalMomentAverages
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit.SelectedTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorColumnTrajectory.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorColumnStandardization.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorColumnStandardization.SelectedBidirectionalValidityOrbit
open
  NormalizedCorrectedFixedDetectorColumnCharacters.SelectedBidirectionalValidityOrbit
open
  NormalizedCorrectedFixedDetectorRawColumnMeans.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorRawColumnFirstMoment.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorFiniteClosedBranchSelection.SelectedBidirectionalValidityOrbit
open scoped Topology

noncomputable section

variable {eqs vars : ℕ}
variable
  {u :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      eqs vars}

namespace SelectedBidirectionalValidityOrbit

variable (O : SelectedBidirectionalValidityOrbit u)

/-- Once the branch selector has identified the infinity cusp and the
quartic amplitude as one, the standardized horizontal speed is one. -/
theorem closedChartSpeed_eq_one_of_selection
    (j : Fin vars)
    (T : ℝ → UpperHalfPlane)
    (c :
      ClosedUnaryHorocycleChart
        (standardizedUnaryColumn
          O.toSelectedTwoSidedValidityOrbit j) T)
    (selection :
      FiniteClosedCuspMeanSelection
        c.cuspLabel
        (standardizedLinkedColumn
          O.toSelectedTwoSidedValidityOrbit j)
        (closedChartX c)
        (closedChartHeight c)
        (closedChartSpeed c)
        (closedChartHeight_pos c)
        (closedChartAmplitude c)) :
    closedChartSpeed c = 1 := by
  have hcomplex :
      ((closedChartSpeed c : ℝ) : ℂ) = 1 := by
    simpa [
      closedChartAmplitude, cuspQuarticAmplitude,
      selection.cusp_eq_infinity] using
      selection.q_eq_one
  exact_mod_cast hcomplex

/-- Every finite closed branch of an actual selected detector column has
the canonical theta-gauge height. -/
theorem standardizedFiniteClosedBranch_height_eq_thetaGaugeHeight
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
    (j : Fin vars)
    (T : ℝ → UpperHalfPlane)
    (c :
      ClosedUnaryHorocycleChart
        (standardizedUnaryColumn
          O.toSelectedTwoSidedValidityOrbit j) T)
    (hlambda :
      ∀ t,
        UnaryModularState.lambdaCoordinate
            (standardizedUnaryColumn
              O.toSelectedTwoSidedValidityOrbit j t) =
          canonicalLambda (T t))
    (hTdiff :
      ∀ t, ∃ v : ℂ,
        HasDerivAt (fun s : ℝ ↦ (T s : ℂ)) v t) :
    closedChartHeight c = thetaGaugeHeight := by
  let B := O.toSelectedTwoSidedValidityOrbit
  let a := columnStandardScale B j
  let b := a⁻¹
  let η := unaryFirstInitialPhase O j
  obtain ⟨selection⟩ :=
    standardizedFiniteClosedBranch_selection
      O hscale hp j T c hlambda hTdiff
  have ha : a ≠ 0 := by
    exact columnStandardScale_ne_zero B hscale hp j
  have hb : b ≠ 0 :=
    inv_ne_zero ha
  have hsOne : closedChartSpeed c = 1 :=
    closedChartSpeed_eq_one_of_selection O j T c selection
  have hYphysical :
      ∀ t,
        (linkedColumn B j t).unary.Y =
          theta₃
            (horizontalLine
              (closedChartX c) (closedChartHeight c) b
              (closedChartHeight_pos c) t) := by
    intro t
    calc
      (linkedColumn B j t).unary.Y =
          (standardizedLinkedColumn B j (b * t)).unary.Y := by
            rw [
              standardizedLinkedColumn_invScale
                B hscale hp j t]
      _ =
          theta₃
            (horizontalLine
              (closedChartX c) (closedChartHeight c)
              (closedChartSpeed c)
              (closedChartHeight_pos c) (b * t)) :=
        selection.Y_eq_theta₃ (b * t)
      _ =
          theta₃
            (horizontalLine
              (closedChartX c) (closedChartHeight c)
              (closedChartSpeed c * b)
              (closedChartHeight_pos c) t) := by
        rw [horizontalLine_mul_time]
      _ =
          theta₃
            (horizontalLine
              (closedChartX c) (closedChartHeight c) b
              (closedChartHeight_pos c) t) := by
        rw [hsOne, one_mul]
  have hcharacter :
      ∀ t,
        characterValue
            (FixedDetectorMomentCode.unaryFirstHarmonicExponent j)
            (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
              B.physicalPoint t).base.base.source.controllers =
          η * standardUnaryFirstCharacter (b * t) := by
    intro t
    have h :=
      unaryFirstCharacter_standardized
        O hscale hp j (b * t)
    have hab : a * (b * t) = t := by
      rw [← mul_assoc]
      simp only [b, mul_inv_cancel₀ ha, one_mul]
    simpa only [B, a, hab, η] using h
  have hraw :=
    unaryFirstRawObservable_cesaroMean_tendsto
      B hscale j
  have hobservable :
      unaryFirstRawObservable B j =
        fun t ↦
          theta₃
              (horizontalLine
                (closedChartX c) (closedChartHeight c) b
                (closedChartHeight_pos c) t) *
            (η * standardUnaryFirstCharacter (b * t)) := by
    funext t
    unfold unaryFirstRawObservable
    rw [hYphysical t, hcharacter t]
  have htheta :
      Tendsto
        (fun n ↦
          HGAS.Analysis.cesaroMeanAt
            (fun t ↦
              theta₃
                  (horizontalLine
                    (closedChartX c) (closedChartHeight c) b
                    (closedChartHeight_pos c) t) *
                (η * standardUnaryFirstCharacter (b * t)))
            (physicalHorizon B n))
        atTop (nhds (1 / 128 : ℂ)) := by
    rw [← hobservable]
    exact hraw
  apply thetaGaugeHeight_of_horizontal_signed_firstMoment
    (closedChartX c) (closedChartHeight c) b
    (closedChartHeight_pos c) hb η
    (norm_unaryFirstInitialPhase O hscale j)
    (rawMeanPhysicalHorizon_tendsto B)
  exact htheta

end SelectedBidirectionalValidityOrbit

end

end
  HGAS.NormalizedCorrectedFixedDetectorFiniteClosedHeightSelection
