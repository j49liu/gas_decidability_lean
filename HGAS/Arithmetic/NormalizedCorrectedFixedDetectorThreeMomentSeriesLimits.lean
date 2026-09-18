import HGAS.Arithmetic.FixedDetectorNormalizedForwardClassifiedSeries
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorRawColumnMeans
import Mathlib.Tactic

/-!
# The three corrected detector moments give the three Bloch-series limits

`FixedDetectorNormalizedForwardClassifiedSeries` identifies the three
literal corrected moment rows with quadratic Bloch series on nonnegative
physical time.  Independently,
`NormalizedCorrectedFixedDetectorTwoSidedPhysicalMomentAverages` proves
that every corrected moment has zero Cesàro mean along one common
unbounded sequence of physical horizons.

This file joins those two interfaces.  It deliberately keeps the
analytic normalization of the resulting series separate; the live
reusable target-value rigidity step is in
`Modular.JacobiThreeMomentTargetRigidity`.
-/

namespace HGAS.NormalizedCorrectedFixedDetectorThreeMomentSeriesLimits

open HGAS
open Filter MeasureTheory Topology
open HGAS.Modular
open HGAS.Clocks
open HGAS.Clocks.ControllerPhaseProductCharacterCode
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit.SelectedTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorColumnGenericity
open NormalizedCorrectedFixedDetectorColumnGenericity.SelectedTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorTwoSidedPhysicalMomentAverages
open NormalizedCorrectedFixedDetectorRawColumnMeans
open FixedDetectorNormalizedForwardClassifiedSeries
open scoped Interval

noncomputable section

variable {eqs vars : ℕ}
variable
  {u :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      eqs vars}

namespace SelectedTwoSidedValidityOrbit

variable (O : SelectedTwoSidedValidityOrbit u)

set_option linter.style.longLine false in
/-- The common sequence of physical horizons diverges. -/
private theorem physicalHorizon_tendsto :
    Tendsto (physicalHorizon O) atTop atTop :=
  _root_.HGAS.NormalizedCorrectedFixedDetectorTwoSidedPhysicalMomentAverages.physicalHorizon_tendsto_atTop O

/-- Equality on the nonnegative ray gives eventual equality of Cesàro
means along any horizon tending to `+∞`. -/
private theorem eventually_cesaroMeanAt_eq_of_eqOn_nonnegative
    {f g : ℝ → ℂ} {T : ℕ → ℝ}
    (hT : Tendsto T atTop atTop)
    (hfg : ∀ t, 0 ≤ t → f t = g t) :
    (fun n ↦ HGAS.Analysis.cesaroMeanAt f (T n)) =ᶠ[atTop]
      fun n ↦ HGAS.Analysis.cesaroMeanAt g (T n) := by
  have hTpos : ∀ᶠ n in atTop, 0 < T n :=
    hT.eventually (eventually_gt_atTop 0)
  filter_upwards [hTpos] with n hn
  unfold HGAS.Analysis.cesaroMeanAt
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hn.le] at ht
  exact hfg t ht.1

/-- Semantic form of local corrected moment `4`, the centered Jacobi
mean row. -/
theorem jacobiMean_momentValue
    (j : Fin vars) (t : ℝ) :
    CorrectedFixedDetectorMomentCode.momentValue
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
        (O.physicalState t)
        (columnMomentIndex j (4 : Fin 7)) =
      evalPair (FixedDetectorMomentCode.jacobiMeanCode j)
        (O.physicalPoint t) := by
  rw [momentValue_columnMomentIndex]
  symm
  simpa only [FixedDetectorPolynomialCode.point_state] using
    (FixedDetectorMomentCode.evalPair_jacobiMeanCode
      j (FixedDetectorPolynomialCode.state (O.physicalPoint t)))

/-- Semantic form of local corrected moment `5`. -/
theorem jacobiPlus_momentValue
    (j : Fin vars) (t : ℝ) :
    CorrectedFixedDetectorMomentCode.momentValue
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
        (O.physicalState t)
        (columnMomentIndex j (5 : Fin 7)) =
      evalPair
        (CorrectedFixedDetectorMomentCode.jacobiPlusMeanCode
          (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j)
        (O.physicalPoint t) := by
  rw [momentValue_columnMomentIndex]
  symm
  simpa only [FixedDetectorPolynomialCode.point_state] using
    (CorrectedFixedDetectorMomentCode.evalPair_jacobiPlusMeanCode
      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j
      (FixedDetectorPolynomialCode.state (O.physicalPoint t)))

/-- Semantic form of local corrected moment `6`. -/
theorem jacobiMinus_momentValue
    (j : Fin vars) (t : ℝ) :
    CorrectedFixedDetectorMomentCode.momentValue
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
        (O.physicalState t)
        (columnMomentIndex j (6 : Fin 7)) =
      evalPair
        (CorrectedFixedDetectorMomentCode.jacobiMinusMeanCode
          (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j)
        (O.physicalPoint t) := by
  rw [momentValue_columnMomentIndex]
  symm
  simpa only [FixedDetectorPolynomialCode.point_state] using
    (CorrectedFixedDetectorMomentCode.evalPair_jacobiMinusMeanCode
      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j
      (FixedDetectorPolynomialCode.state (O.physicalPoint t)))

variable
  (controller :
    Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
      Controller.ControllerState ℝ)
  (phase₀ :
    Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
  (x₀ : Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
  (j : Fin vars)
  (p : AffineBlochParameters)
  (d : ℂ)
  (t₀ : ℝ)

/-- The centered mean row has zero average, so the uncentered classified
quadratic series has limit one. -/
theorem meanSeries_cesaro_tendsto_one
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (h :
      ClassifiedSeed
        (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
        O.physicalPoint x₀ controller phase₀ j p d t₀) :
    Tendsto
      (fun n ↦
        HGAS.Analysis.cesaroMeanAt
          (quadraticMomentSeries
            (p.gaugedBlochCoefficient d)
            (CanonicalFixedDetectorTrajectory.omegaFrequency
              (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
              controller j)
            (CanonicalFixedDetectorTrajectory.numberFrequency
                (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
                controller j /
              CanonicalFixedDetectorTrajectory.omegaFrequency
                (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                controller j)
            p.a0.re 0)
          (physicalHorizon O n))
      atTop (nhds 1) := by
  let centered : ℝ → ℂ := fun t ↦
    CorrectedFixedDetectorMomentCode.momentValue
      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
      (O.physicalState t)
      (columnMomentIndex j (4 : Fin 7))
  let raw : ℝ → ℂ := fun t ↦ centered t + 1
  have hcentered :
      Tendsto
        (fun n ↦ HGAS.Analysis.cesaroMeanAt centered
          (physicalHorizon O n))
        atTop (nhds 0) := by
    simpa only [centered] using
      (momentComplexAverage_tendsto_zero
        O hscale.ne' (columnMomentIndex j (4 : Fin 7)))
  have hraw :
      Tendsto
        (fun n ↦ HGAS.Analysis.cesaroMeanAt raw
          (physicalHorizon O n))
        atTop (nhds 1) := by
    apply
      HGAS.Analysis.tendsto_cesaroMeanAt_of_sub_const_tendsto_zero
        ((continuous_momentValue_physical O
          (columnMomentIndex j (4 : Fin 7))).add continuous_const)
        1
        (physicalHorizon_tendsto O)
    simpa only [raw, centered, Pi.add_apply, add_sub_cancel_right] using hcentered
  apply hraw.congr'
  apply
    (eventually_cesaroMeanAt_eq_of_eqOn_nonnegative
      (physicalHorizon_tendsto O) ?_).symm
  intro t ht
  dsimp only [raw, centered]
  rw [jacobiMean_momentValue O j t]
  have hseries :=
    mean_eq_quadraticMomentSeries
      (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
      O.physicalPoint x₀ controller phase₀ j p d t₀ h t ht
  calc
    quadraticMomentSeries
          (p.gaugedBlochCoefficient d)
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
            controller j)
          (CanonicalFixedDetectorTrajectory.numberFrequency
              (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
              (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
              controller j /
            CanonicalFixedDetectorTrajectory.omegaFrequency
              (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
              controller j)
          p.a0.re 0 t =
        (quadraticMomentSeries
            (p.gaugedBlochCoefficient d)
            (CanonicalFixedDetectorTrajectory.omegaFrequency
              (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
              controller j)
            (CanonicalFixedDetectorTrajectory.numberFrequency
                (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
                controller j /
              CanonicalFixedDetectorTrajectory.omegaFrequency
                (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                controller j)
            p.a0.re 0 t - 1) + 1 := by ring
    _ = evalPair (FixedDetectorMomentCode.jacobiMeanCode j)
          (O.physicalPoint t) + 1 := by rw [← hseries]

/-- The corrected positive selector row has zero average, so its
uncentered classified series has the conditional selector center as its
limit. -/
theorem plusSeries_cesaro_tendsto_selectorCenter
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (h :
      ClassifiedSeed
        (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
        O.physicalPoint x₀ controller phase₀ j p d t₀) :
    let c :=
      characterValue
        (FixedDetectorMomentCode.jacobiPlusExponent
          (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j)
        (CanonicalFixedDetectorTrajectory.clockPath
          (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
          controller phase₀ 0)
    Tendsto
      (fun n ↦
        HGAS.Analysis.cesaroMeanAt
          (quadraticMomentSeries
            (fun k ↦ c * p.gaugedBlochCoefficient d k)
            (CanonicalFixedDetectorTrajectory.omegaFrequency
              (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
              controller j)
            (CanonicalFixedDetectorTrajectory.numberFrequency
                (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
                controller j /
              CanonicalFixedDetectorTrajectory.omegaFrequency
                (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                controller j)
            p.a0.re 1)
          (physicalHorizon O n))
      atTop
      (nhds
        (CorrectedJacobiSelectorCentering.selectorCenter
          (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j)) := by
  dsimp only
  let center : ℂ :=
    CorrectedJacobiSelectorCentering.selectorCenter
      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j
  let centered : ℝ → ℂ := fun t ↦
    CorrectedFixedDetectorMomentCode.momentValue
      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
      (O.physicalState t)
      (columnMomentIndex j (5 : Fin 7))
  let raw : ℝ → ℂ := fun t ↦ centered t + center
  have hcentered :
      Tendsto
        (fun n ↦ HGAS.Analysis.cesaroMeanAt centered
          (physicalHorizon O n))
        atTop (nhds 0) := by
    simpa only [centered] using
      (momentComplexAverage_tendsto_zero
        O hscale.ne' (columnMomentIndex j (5 : Fin 7)))
  have hraw :
      Tendsto
        (fun n ↦ HGAS.Analysis.cesaroMeanAt raw
          (physicalHorizon O n))
        atTop (nhds center) := by
    apply
      HGAS.Analysis.tendsto_cesaroMeanAt_of_sub_const_tendsto_zero
        ((continuous_momentValue_physical O
          (columnMomentIndex j (5 : Fin 7))).add continuous_const)
        center
        (physicalHorizon_tendsto O)
    simpa only [raw, centered, center, Pi.add_apply, add_sub_cancel_right] using
      hcentered
  apply hraw.congr'
  apply
    (eventually_cesaroMeanAt_eq_of_eqOn_nonnegative
      (physicalHorizon_tendsto O) ?_).symm
  intro t ht
  dsimp only [raw, centered, center]
  rw [jacobiPlus_momentValue O j t]
  have hseries :=
    plus_eq_quadraticMomentSeries
      (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
      O.physicalPoint x₀ controller phase₀ j p d t₀ h t ht
  calc
    quadraticMomentSeries
          (fun k ↦
            characterValue
                (FixedDetectorMomentCode.jacobiPlusExponent
                  (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
                  j)
                (CanonicalFixedDetectorTrajectory.clockPath
                  (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                  controller phase₀ 0) *
              p.gaugedBlochCoefficient d k)
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
            controller j)
          (CanonicalFixedDetectorTrajectory.numberFrequency
              (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
              (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
              controller j /
            CanonicalFixedDetectorTrajectory.omegaFrequency
              (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
              controller j)
          p.a0.re 1 t =
        (quadraticMomentSeries
            (fun k ↦
              characterValue
                  (FixedDetectorMomentCode.jacobiPlusExponent
                    (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
                    j)
                  (CanonicalFixedDetectorTrajectory.clockPath
                    (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                    controller phase₀ 0) *
                p.gaugedBlochCoefficient d k)
            (CanonicalFixedDetectorTrajectory.omegaFrequency
              (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
              controller j)
            (CanonicalFixedDetectorTrajectory.numberFrequency
                (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
                controller j /
              CanonicalFixedDetectorTrajectory.omegaFrequency
                (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                controller j)
            p.a0.re 1 t -
          CorrectedJacobiSelectorCentering.selectorCenter
            (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j) +
          CorrectedJacobiSelectorCentering.selectorCenter
            (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j := by ring
    _ = evalPair
          (CorrectedFixedDetectorMomentCode.jacobiPlusMeanCode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j)
          (O.physicalPoint t) +
        CorrectedJacobiSelectorCentering.selectorCenter
          (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j := by
      rw [← hseries]

/-- The negative selector row gives the same conditional center. -/
theorem minusSeries_cesaro_tendsto_selectorCenter
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (h :
      ClassifiedSeed
        (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
        (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
        O.physicalPoint x₀ controller phase₀ j p d t₀) :
    let c :=
      characterValue
        (FixedDetectorMomentCode.jacobiMinusExponent
          (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j)
        (CanonicalFixedDetectorTrajectory.clockPath
          (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
          controller phase₀ 0)
    Tendsto
      (fun n ↦
        HGAS.Analysis.cesaroMeanAt
          (quadraticMomentSeries
            (fun k ↦ c * p.gaugedBlochCoefficient d k)
            (CanonicalFixedDetectorTrajectory.omegaFrequency
              (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
              controller j)
            (CanonicalFixedDetectorTrajectory.numberFrequency
                (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
                controller j /
              CanonicalFixedDetectorTrajectory.omegaFrequency
                (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                controller j)
            p.a0.re (-1))
          (physicalHorizon O n))
      atTop
      (nhds
        (CorrectedJacobiSelectorCentering.selectorCenter
          (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j)) := by
  dsimp only
  let center : ℂ :=
    CorrectedJacobiSelectorCentering.selectorCenter
      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j
  let centered : ℝ → ℂ := fun t ↦
    CorrectedFixedDetectorMomentCode.momentValue
      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
      (O.physicalState t)
      (columnMomentIndex j (6 : Fin 7))
  let raw : ℝ → ℂ := fun t ↦ centered t + center
  have hcentered :
      Tendsto
        (fun n ↦ HGAS.Analysis.cesaroMeanAt centered
          (physicalHorizon O n))
        atTop (nhds 0) := by
    simpa only [centered] using
      (momentComplexAverage_tendsto_zero
        O hscale.ne' (columnMomentIndex j (6 : Fin 7)))
  have hraw :
      Tendsto
        (fun n ↦ HGAS.Analysis.cesaroMeanAt raw
          (physicalHorizon O n))
        atTop (nhds center) := by
    apply
      HGAS.Analysis.tendsto_cesaroMeanAt_of_sub_const_tendsto_zero
        ((continuous_momentValue_physical O
          (columnMomentIndex j (6 : Fin 7))).add continuous_const)
        center
        (physicalHorizon_tendsto O)
    simpa only [raw, centered, center, Pi.add_apply, add_sub_cancel_right] using
      hcentered
  apply hraw.congr'
  apply
    (eventually_cesaroMeanAt_eq_of_eqOn_nonnegative
      (physicalHorizon_tendsto O) ?_).symm
  intro t ht
  dsimp only [raw, centered, center]
  rw [jacobiMinus_momentValue O j t]
  have hseries :=
    minus_eq_quadraticMomentSeries
      (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
      O.physicalPoint x₀ controller phase₀ j p d t₀ h t ht
  calc
    quadraticMomentSeries
          (fun k ↦
            characterValue
                (FixedDetectorMomentCode.jacobiMinusExponent
                  (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
                  j)
                (CanonicalFixedDetectorTrajectory.clockPath
                  (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                  controller phase₀ 0) *
              p.gaugedBlochCoefficient d k)
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
            controller j)
          (CanonicalFixedDetectorTrajectory.numberFrequency
              (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
              (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
              controller j /
            CanonicalFixedDetectorTrajectory.omegaFrequency
              (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
              controller j)
          p.a0.re (-1) t =
        (quadraticMomentSeries
            (fun k ↦
              characterValue
                  (FixedDetectorMomentCode.jacobiMinusExponent
                    (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
                    j)
                  (CanonicalFixedDetectorTrajectory.clockPath
                    (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                    controller phase₀ 0) *
                p.gaugedBlochCoefficient d k)
            (CanonicalFixedDetectorTrajectory.omegaFrequency
              (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
              controller j)
            (CanonicalFixedDetectorTrajectory.numberFrequency
                (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
                controller j /
              CanonicalFixedDetectorTrajectory.omegaFrequency
                (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
                controller j)
            p.a0.re (-1) t -
          CorrectedJacobiSelectorCentering.selectorCenter
            (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j) +
          CorrectedJacobiSelectorCentering.selectorCenter
            (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j := by ring
    _ = evalPair
          (CorrectedFixedDetectorMomentCode.jacobiMinusMeanCode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j)
          (O.physicalPoint t) +
        CorrectedJacobiSelectorCentering.selectorCenter
          (NormalizedCorrectedFixedDetectorCompactSourceCode.system u) j := by
      rw [← hseries]

end SelectedTwoSidedValidityOrbit

end

end HGAS.NormalizedCorrectedFixedDetectorThreeMomentSeriesLimits
