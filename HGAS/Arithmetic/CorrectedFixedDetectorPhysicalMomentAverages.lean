import HGAS.Analysis.CesaroExponentialSeriesArbitraryHorizon
import HGAS.Arithmetic.CorrectedFixedDetectorValidityOrbit
import Mathlib.Tactic

/-!
# Corrected selector moments along the selected physical orbit

Every scalar drift coordinate has zero physical-time average along one
common unbounded sequence of clock horizons.  This file identifies those
coordinates with the real and imaginary parts of the corrected complex
selector moments and with the final arithmetic detector.
-/

namespace HGAS.CorrectedFixedDetectorPhysicalMomentAverages

open HGAS
open Filter MeasureTheory Topology
open scoped Interval

noncomputable section

open CorrectedFixedDetectorValidityOrbit
open CorrectedFixedDetectorValidityOrbit.SelectedValidityOrbit

variable {eqs vars : ℕ}
variable
  {u : CorrectedFixedDetectorCompactSourceCode.CompilerInput eqs vars}
  (O : SelectedValidityOrbit u)

/-- Common physical horizons produced by the compactification clock. -/
def physicalHorizon (q : ℕ) : ℝ :=
  integralClock
    (stateClockWeight
      (CompactAccumulatorPipelineCode.AllAffineCompactSourceChart.affineSpeed
        (speedExponent
          (CorrectedFixedDetectorCompactSourceCode.system u)))
      (affineCurve u O.point))
    (positiveIntegerHorizon q)

theorem physicalHorizon_tendsto_atTop :
    Tendsto (physicalHorizon O) atTop atTop := by
  simpa only [physicalHorizon] using
    CorrectedFixedDetectorValidityOrbit.SelectedValidityOrbit.physicalHorizon_tendsto_atTop
      O

/-- Scalar physical Cesàro average. -/
def scalarAverage
  (f : ℝ → ℝ) (q : ℕ) : ℝ :=
  (physicalHorizon O q)⁻¹ *
    ∫ t in (0 : ℝ)..physicalHorizon O q, f t

/-- Complex Cesàro mean reconstructed from the scalar real and imaginary
means used by the compiler. -/
def complexAverage
    (f : ℝ → ℂ) (q : ℕ) : ℂ :=
  (scalarAverage O (fun t ↦ (f t).re) q : ℂ) +
    (scalarAverage O (fun t ↦ (f t).im) q : ℂ) * Complex.I

/-- The reconstructed complex average is the ordinary complex interval
average. -/
theorem complexAverage_eq_cesaroMeanAt
    (f : ℝ → ℂ) (hf : Continuous f) (q : ℕ) :
    complexAverage O f q =
      Analysis.cesaroMeanAt f (physicalHorizon O q) := by
  let T := physicalHorizon O q
  have hint : IntervalIntegrable f volume 0 T :=
    hf.intervalIntegrable 0 T
  have hre :=
    intervalIntegral.intervalIntegral_re hint
  have him :=
    intervalIntegral.intervalIntegral_im hint
  have hre' :
      (∫ t in (0 : ℝ)..T, (f t).re) =
        (∫ t in (0 : ℝ)..T, f t).re := by
    simpa only [RCLike.re_to_real] using hre
  have him' :
      (∫ t in (0 : ℝ)..T, (f t).im) =
        (∫ t in (0 : ℝ)..T, f t).im := by
    simpa only [RCLike.im_to_real] using him
  unfold complexAverage scalarAverage Analysis.cesaroMeanAt
  change
    ((T⁻¹ * ∫ t in (0 : ℝ)..T, (f t).re : ℝ) : ℂ) +
        ((T⁻¹ * ∫ t in (0 : ℝ)..T, (f t).im : ℝ) : ℂ) *
          Complex.I =
      ((T : ℂ)⁻¹) * ∫ t in (0 : ℝ)..T, f t
  rw [hre', him']
  push_cast
  calc
    (T : ℂ)⁻¹ * ((∫ t in (0 : ℝ)..T, f t).re : ℂ) +
          (T : ℂ)⁻¹ * ((∫ t in (0 : ℝ)..T, f t).im : ℂ) *
            Complex.I =
        (T : ℂ)⁻¹ *
          (((∫ t in (0 : ℝ)..T, f t).re : ℂ) +
            ((∫ t in (0 : ℝ)..T, f t).im : ℂ) * Complex.I) := by
      ring
    _ = (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, f t := by
      rw [Complex.re_add_im]

/-- Adjacent scalar index containing the real part of complex moment
`k`. -/
def momentRealScalarIndex
    (k : Fin (CorrectedFixedDetectorMomentCode.momentCount vars)) :
    Fin (CorrectedFixedDetectorMomentCode.scalarMomentCount vars) :=
  finProdFinEquiv (k, (0 : Fin 2))

/-- Adjacent scalar index containing the imaginary part of complex moment
`k`. -/
def momentImagScalarIndex
    (k : Fin (CorrectedFixedDetectorMomentCode.momentCount vars)) :
    Fin (CorrectedFixedDetectorMomentCode.scalarMomentCount vars) :=
  finProdFinEquiv (k, (1 : Fin 2))

@[simp]
theorem scalarMomentValue_real
    (k : Fin (CorrectedFixedDetectorMomentCode.momentCount vars))
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    CorrectedFixedDetectorMomentCode.scalarMomentValue
        (CorrectedFixedDetectorCompactSourceCode.system u) z
        (momentRealScalarIndex k) =
      (CorrectedFixedDetectorMomentCode.momentValue
        (CorrectedFixedDetectorCompactSourceCode.system u) z k).re := by
  simp [CorrectedFixedDetectorMomentCode.scalarMomentValue,
    momentRealScalarIndex]

@[simp]
theorem scalarMomentValue_imag
    (k : Fin (CorrectedFixedDetectorMomentCode.momentCount vars))
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    CorrectedFixedDetectorMomentCode.scalarMomentValue
        (CorrectedFixedDetectorCompactSourceCode.system u) z
        (momentImagScalarIndex k) =
      (CorrectedFixedDetectorMomentCode.momentValue
        (CorrectedFixedDetectorCompactSourceCode.system u) z k).im := by
  simp [CorrectedFixedDetectorMomentCode.scalarMomentValue,
    momentImagScalarIndex]

/-- Exact physical evaluation of the real part of one corrected complex
moment. -/
theorem eval_sourceDrift_momentReal
    (k : Fin (CorrectedFixedDetectorMomentCode.momentCount vars))
    (t : ℝ) :
    _root_.MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (O.physicalPoint t)
        (PolynomialCode.decode
          (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode
            (CorrectedFixedDetectorCompactSourceCode.system u)
            (CorrectedFixedDetectorDriftCode.momentIndex
              (momentRealScalarIndex k)))) =
      (CorrectedFixedDetectorMomentCode.momentValue
        (CorrectedFixedDetectorCompactSourceCode.system u)
        (O.physicalState t) k).re := by
  simpa [CorrectedFixedDetectorCompactSourceCode.sourceDriftCode] using
    (CorrectedFixedDetectorDriftCode.eval_driftCode_momentIndex
      (CorrectedFixedDetectorCompactSourceCode.system u)
      (momentRealScalarIndex k) (O.physicalState t))

/-- Exact physical evaluation of the imaginary part of one corrected
complex moment. -/
theorem eval_sourceDrift_momentImag
    (k : Fin (CorrectedFixedDetectorMomentCode.momentCount vars))
    (t : ℝ) :
    _root_.MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (O.physicalPoint t)
        (PolynomialCode.decode
          (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode
            (CorrectedFixedDetectorCompactSourceCode.system u)
            (CorrectedFixedDetectorDriftCode.momentIndex
              (momentImagScalarIndex k)))) =
      (CorrectedFixedDetectorMomentCode.momentValue
        (CorrectedFixedDetectorCompactSourceCode.system u)
        (O.physicalState t) k).im := by
  simpa [CorrectedFixedDetectorCompactSourceCode.sourceDriftCode] using
    (CorrectedFixedDetectorDriftCode.eval_driftCode_momentIndex
      (CorrectedFixedDetectorCompactSourceCode.system u)
      (momentImagScalarIndex k) (O.physicalState t))

/-- Every corrected complex moment is continuous along the physical
detector trajectory. -/
theorem continuous_momentValue_physical
    (k : Fin (CorrectedFixedDetectorMomentCode.momentCount vars)) :
    Continuous
      (fun t ↦
        CorrectedFixedDetectorMomentCode.momentValue
          (CorrectedFixedDetectorCompactSourceCode.system u)
          (O.physicalState t) k) := by
  let code :=
    CorrectedFixedDetectorMomentCode.momentCode
      (CorrectedFixedDetectorCompactSourceCode.system u) k
  have hre :
      Continuous
        (fun t ↦
          _root_.MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
            (O.physicalPoint t)
            (PolynomialCode.decode code.1)) := by
    have hp :=
      _root_.MvPolynomial.continuous_eval
        (_root_.MvPolynomial.map (algebraMap ℚ ℝ)
          (PolynomialCode.decode code.1))
    simpa only [_root_.MvPolynomial.eval_map] using
      hp.comp
        (CorrectedFixedDetectorValidityOrbit.SelectedValidityOrbit.continuous_physicalPoint
          O)
  have him :
      Continuous
        (fun t ↦
          _root_.MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
            (O.physicalPoint t)
            (PolynomialCode.decode code.2)) := by
    have hp :=
      _root_.MvPolynomial.continuous_eval
        (_root_.MvPolynomial.map (algebraMap ℚ ℝ)
          (PolynomialCode.decode code.2))
    simpa only [_root_.MvPolynomial.eval_map] using
      hp.comp
        (CorrectedFixedDetectorValidityOrbit.SelectedValidityOrbit.continuous_physicalPoint
          O)
  have hpair :
      Continuous
        (fun t ↦
          Clocks.ControllerPhaseProductCharacterCode.evalPair
            code (O.physicalPoint t)) := by
    exact
      Complex.equivRealProdCLM.symm.continuous.comp
        (hre.prodMk him)
  have heq :
      (fun t ↦
        CorrectedFixedDetectorMomentCode.momentValue
          (CorrectedFixedDetectorCompactSourceCode.system u)
          (O.physicalState t) k) =
        fun t ↦
          Clocks.ControllerPhaseProductCharacterCode.evalPair
            code (O.physicalPoint t) := by
    funext t
    symm
    rw [←
      CorrectedFixedDetectorValidityOrbit.SelectedValidityOrbit.point_physicalState
        O t]
    exact
      CorrectedFixedDetectorMomentCode.evalPair_momentCode
        (CorrectedFixedDetectorCompactSourceCode.system u)
        k (O.physicalState t)
  rw [heq]
  exact hpair

/-- The real part of every corrected selector moment has zero physical
average along the common clock horizons. -/
theorem momentRealAverage_tendsto_zero
    (hscale :
      ((CorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
          ℝ) ≠ 0)
    (k : Fin (CorrectedFixedDetectorMomentCode.momentCount vars)) :
    Tendsto
      (fun q ↦ scalarAverage O
        (fun t ↦
          (CorrectedFixedDetectorMomentCode.momentValue
            (CorrectedFixedDetectorCompactSourceCode.system u)
            (O.physicalState t) k).re) q)
      atTop (𝓝 0) := by
  simpa only [scalarAverage, physicalHorizon,
    eval_sourceDrift_momentReal] using
    CorrectedFixedDetectorValidityOrbit.SelectedValidityOrbit.physicalDriftAverage_tendsto_zero
      O hscale
      (CorrectedFixedDetectorDriftCode.momentIndex
        (momentRealScalarIndex k))

/-- The imaginary part of every corrected selector moment has zero physical
average along the common clock horizons. -/
theorem momentImagAverage_tendsto_zero
    (hscale :
      ((CorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
          ℝ) ≠ 0)
    (k : Fin (CorrectedFixedDetectorMomentCode.momentCount vars)) :
    Tendsto
      (fun q ↦ scalarAverage O
        (fun t ↦
          (CorrectedFixedDetectorMomentCode.momentValue
            (CorrectedFixedDetectorCompactSourceCode.system u)
            (O.physicalState t) k).im) q)
      atTop (𝓝 0) := by
  simpa only [scalarAverage, physicalHorizon,
    eval_sourceDrift_momentImag] using
    CorrectedFixedDetectorValidityOrbit.SelectedValidityOrbit.physicalDriftAverage_tendsto_zero
      O hscale
      (CorrectedFixedDetectorDriftCode.momentIndex
        (momentImagScalarIndex k))

/-- Every corrected complex selector moment has zero physical Cesàro
average along the common unbounded clock horizons. -/
theorem momentComplexAverage_tendsto_zero
    (hscale :
      ((CorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
          ℝ) ≠ 0)
    (k : Fin (CorrectedFixedDetectorMomentCode.momentCount vars)) :
    Tendsto
      (fun q ↦
        Analysis.cesaroMeanAt
          (fun t ↦
            CorrectedFixedDetectorMomentCode.momentValue
              (CorrectedFixedDetectorCompactSourceCode.system u)
              (O.physicalState t) k)
          (physicalHorizon O q))
      atTop (𝓝 0) := by
  have hre := (momentRealAverage_tendsto_zero O hscale k).ofReal
  have him := (momentImagAverage_tendsto_zero O hscale k).ofReal
  have hsum :
      Tendsto
        (fun q ↦
          (scalarAverage O
            (fun t ↦
              (CorrectedFixedDetectorMomentCode.momentValue
                (CorrectedFixedDetectorCompactSourceCode.system u)
                (O.physicalState t) k).re) q : ℂ) +
            (scalarAverage O
              (fun t ↦
                (CorrectedFixedDetectorMomentCode.momentValue
                  (CorrectedFixedDetectorCompactSourceCode.system u)
                  (O.physicalState t) k).im) q : ℂ) * Complex.I)
        atTop (𝓝 0) := by
    convert hre.add (him.mul_const Complex.I) using 1
    all_goals norm_num
  apply hsum.congr'
  exact Eventually.of_forall fun q ↦ by
    exact complexAverage_eq_cesaroMeanAt O _
      (continuous_momentValue_physical O k) q

/-- Exact physical evaluation of the real detector coordinate. -/
theorem eval_sourceDrift_detectorReal (t : ℝ) :
    _root_.MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (O.physicalPoint t)
        (PolynomialCode.decode
          (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode
            (CorrectedFixedDetectorCompactSourceCode.system u)
            (CorrectedFixedDetectorDriftCode.detectorIndex
              (0 : Fin 2)))) =
      (CorrectedFixedDetectorDriftCode.detectorValue
        (O.physicalState t)).re := by
  simpa [CorrectedFixedDetectorCompactSourceCode.sourceDriftCode] using
    (CorrectedFixedDetectorDriftCode.eval_driftCode_detectorIndex
      (CorrectedFixedDetectorCompactSourceCode.system u)
      (0 : Fin 2) (O.physicalState t))

/-- Exact physical evaluation of the imaginary detector coordinate. -/
theorem eval_sourceDrift_detectorImag (t : ℝ) :
    _root_.MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (O.physicalPoint t)
        (PolynomialCode.decode
          (CorrectedFixedDetectorCompactSourceCode.sourceDriftCode
            (CorrectedFixedDetectorCompactSourceCode.system u)
            (CorrectedFixedDetectorDriftCode.detectorIndex
              (1 : Fin 2)))) =
      (CorrectedFixedDetectorDriftCode.detectorValue
        (O.physicalState t)).im := by
  simpa [CorrectedFixedDetectorCompactSourceCode.sourceDriftCode] using
    (CorrectedFixedDetectorDriftCode.eval_driftCode_detectorIndex
      (CorrectedFixedDetectorCompactSourceCode.system u)
      (1 : Fin 2) (O.physicalState t))

/-- The final complex detector is continuous along the physical orbit. -/
theorem continuous_detectorValue_physical :
    Continuous
      (fun t ↦
        CorrectedFixedDetectorDriftCode.detectorValue
          (O.physicalState t)) := by
  let code :=
    FixedDetectorPolynomialCode.detectorCode
      (eqs := eqs) (vars := vars)
  have hre :
      Continuous
        (fun t ↦
          _root_.MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
            (O.physicalPoint t)
            (PolynomialCode.decode code.1)) := by
    have hp :=
      _root_.MvPolynomial.continuous_eval
        (_root_.MvPolynomial.map (algebraMap ℚ ℝ)
          (PolynomialCode.decode code.1))
    simpa only [_root_.MvPolynomial.eval_map] using
      hp.comp
        (CorrectedFixedDetectorValidityOrbit.SelectedValidityOrbit.continuous_physicalPoint
          O)
  have him :
      Continuous
        (fun t ↦
          _root_.MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
            (O.physicalPoint t)
            (PolynomialCode.decode code.2)) := by
    have hp :=
      _root_.MvPolynomial.continuous_eval
        (_root_.MvPolynomial.map (algebraMap ℚ ℝ)
          (PolynomialCode.decode code.2))
    simpa only [_root_.MvPolynomial.eval_map] using
      hp.comp
        (CorrectedFixedDetectorValidityOrbit.SelectedValidityOrbit.continuous_physicalPoint
          O)
  have hpair :
      Continuous
        (fun t ↦
          Clocks.ControllerPhaseProductCharacterCode.evalPair
            code (O.physicalPoint t)) :=
    Complex.equivRealProdCLM.symm.continuous.comp
      (hre.prodMk him)
  have heq :
      (fun t ↦
        CorrectedFixedDetectorDriftCode.detectorValue
          (O.physicalState t)) =
        fun t ↦
          Clocks.ControllerPhaseProductCharacterCode.evalPair
            code (O.physicalPoint t) := by
    funext t
    symm
    rw [←
      CorrectedFixedDetectorValidityOrbit.SelectedValidityOrbit.point_physicalState
        O t]
    exact
      FixedDetectorDriftCode.evalPair_detectorCode_eq_detectorValue
        (O.physicalState t)
  rw [heq]
  exact hpair

theorem detectorRealAverage_tendsto_zero
    (hscale :
      ((CorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
          ℝ) ≠ 0) :
    Tendsto
      (fun q ↦ scalarAverage O
        (fun t ↦
          (CorrectedFixedDetectorDriftCode.detectorValue
            (O.physicalState t)).re) q)
      atTop (𝓝 0) := by
  simpa only [scalarAverage, physicalHorizon,
    eval_sourceDrift_detectorReal] using
    CorrectedFixedDetectorValidityOrbit.SelectedValidityOrbit.physicalDriftAverage_tendsto_zero
      O hscale
      (CorrectedFixedDetectorDriftCode.detectorIndex (0 : Fin 2))

theorem detectorImagAverage_tendsto_zero
    (hscale :
      ((CorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
          ℝ) ≠ 0) :
    Tendsto
      (fun q ↦ scalarAverage O
        (fun t ↦
          (CorrectedFixedDetectorDriftCode.detectorValue
            (O.physicalState t)).im) q)
      atTop (𝓝 0) := by
  simpa only [scalarAverage, physicalHorizon,
    eval_sourceDrift_detectorImag] using
    CorrectedFixedDetectorValidityOrbit.SelectedValidityOrbit.physicalDriftAverage_tendsto_zero
      O hscale
      (CorrectedFixedDetectorDriftCode.detectorIndex (1 : Fin 2))

/-- The final complex arithmetic detector has zero physical Cesàro
average along the same common clock horizons. -/
theorem detectorComplexAverage_tendsto_zero
    (hscale :
      ((CorrectedFixedDetectorCompactSourceCode.accumulatorScale u).decode :
          ℝ) ≠ 0) :
    Tendsto
      (fun q ↦
        Analysis.cesaroMeanAt
          (fun t ↦
            CorrectedFixedDetectorDriftCode.detectorValue
              (O.physicalState t))
          (physicalHorizon O q))
      atTop (𝓝 0) := by
  have hre := (detectorRealAverage_tendsto_zero O hscale).ofReal
  have him := (detectorImagAverage_tendsto_zero O hscale).ofReal
  have hsum :
      Tendsto
        (fun q ↦
          (scalarAverage O
            (fun t ↦
              (CorrectedFixedDetectorDriftCode.detectorValue
                (O.physicalState t)).re) q : ℂ) +
            (scalarAverage O
              (fun t ↦
                (CorrectedFixedDetectorDriftCode.detectorValue
                  (O.physicalState t)).im) q : ℂ) * Complex.I)
        atTop (𝓝 0) := by
    convert hre.add (him.mul_const Complex.I) using 1
    all_goals norm_num
  apply hsum.congr'
  exact Eventually.of_forall fun q ↦ by
    exact complexAverage_eq_cesaroMeanAt O _
      (continuous_detectorValue_physical O) q

end

end HGAS.CorrectedFixedDetectorPhysicalMomentAverages
