import HGAS.Arithmetic.CanonicalFixedDetectorRawOrbitBound
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorCompactSourceCode
import HGAS.Compactification.PositiveCentralChart
import HGAS.Compiler.CompactAccumulatorPipelineFiniteGraph
import Mathlib.Tactic

/-!
# Uniformly positive central chart for the normalized canonical detector

The analytic canonical detector trajectory is an affine trajectory in the
exact source dimension used by the normalized corrected compact compiler.
`CanonicalFixedDetectorRawOrbitBound` gives a time-independent bound

```text
                         ‖z(t)‖² ≤ B.
```

This file applies the reusable positive central chart to that trajectory.
Its chart scalar is

```text
                  w(t) = (1 + ‖z(t)‖²)^(-1/2),
```

and therefore

```text
        (1 + B)^(-1/2) ≤ w(t),
        (1 + B)^(-1)   ≤ w(t)².
```

The second estimate is also stated in the literal
`baseCentralWeightProduct` vocabulary of the one-block normalized compact
compiler.  It is the quantitative hypothesis required by the finite-graph
reward theorem.
-/

noncomputable section

namespace HGAS.NormalizedCorrectedCanonicalFixedDetectorCentralChart

open HGAS
open HGAS.Clocks
open HGAS.CanonicalFixedDetectorRawOrbitBound
open HGAS.CompactAccumulatorPipelineCode

variable {eqs vars : ℕ}

/-- The affine point on the completely aligned canonical detector orbit. -/
def canonicalAffinePoint
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) :
    Fin (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
      eqs vars) → ℝ :=
  FixedDetectorPolynomialCode.point
    (canonicalRawState parameters I controller t)

/-- The positive finite central-chart point above the canonical affine
state. -/
def canonicalCentralChartPoint
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) :
    FiniteCentralChart
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
        eqs vars) :=
  positiveCentralChartPoint
    (canonicalAffinePoint parameters I controller t)

/-- Explicit positive lower bound for the (unsquared) central weight. -/
def canonicalCentralWeightLowerBound (eqs vars : ℕ) : ℝ :=
  positiveCentralWeightLowerBound
    (canonicalRawNormSqBound eqs vars)

/-- Explicit positive lower bound for the squared central weight. -/
def canonicalCentralWeightSqLowerBound (eqs vars : ℕ) : ℝ :=
  positiveCentralWeightSqLowerBound
    (canonicalRawNormSqBound eqs vars)

theorem canonicalCentralWeightLowerBound_pos :
    0 < canonicalCentralWeightLowerBound eqs vars := by
  exact positiveCentralWeightLowerBound_pos
    canonicalRawNormSqBound_nonneg

theorem canonicalCentralWeightSqLowerBound_pos :
    0 < canonicalCentralWeightSqLowerBound eqs vars := by
  exact positiveCentralWeightSqLowerBound_pos
    canonicalRawNormSqBound_nonneg

/-- The canonical compact chart recovers the original raw detector point. -/
@[simp]
theorem centralChartCoordinate_canonicalCentralChartPoint
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) :
    centralChartCoordinate
        (canonicalCentralChartPoint parameters I controller t) =
      canonicalAffinePoint parameters I controller t := by
  exact centralChartCoordinate_positiveCentralChartPoint _

/-- Uniform positive lower bound for the actual central weight along the
whole canonical orbit. -/
theorem canonicalCentralWeightLowerBound_le
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (t : ℝ) :
    canonicalCentralWeightLowerBound eqs vars ≤
      (canonicalCentralChartPoint parameters I controller t).1.1.2 := by
  exact positiveCentralWeightLowerBound_le
    canonicalRawNormSqBound_nonneg
    (canonicalAffinePoint parameters I controller t)
    (normSq_canonicalRawPoint_le
      parameters I controller hcontroller t)

/-- Uniform positive lower bound for the squared central weight. -/
theorem canonicalCentralWeightSqLowerBound_le
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (t : ℝ) :
    canonicalCentralWeightSqLowerBound eqs vars ≤
      (canonicalCentralChartPoint parameters I controller t).1.1.2 ^ 2 := by
  exact positiveCentralWeightSqLowerBound_le
    canonicalRawNormSqBound_nonneg
    (canonicalAffinePoint parameters I controller t)
    (normSq_canonicalRawPoint_le
      parameters I controller hcontroller t)

/-- The same central point, embedded in the exact one-block compact base
space emitted by the normalized corrected compiler. -/
def canonicalCompactBasePoint
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) :
    BaseSpace
      (NormalizedCorrectedFixedDetectorCompactSourceCode.layout
        (eqs := eqs) (vars := vars)) := by
  let q := canonicalCentralChartPoint parameters I controller t
  let x : Fin
      (NormalizedCorrectedFixedDetectorCompactSourceCode.sourceDimension
        eqs vars) → ℝ := q.1.1.1
  let w : ℝ := q.1.1.2
  refine
    ⟨MixedCentralPolynomialCode.chartPoint x
        (fun _ : Fin 1 ↦ w), ?_⟩
  rw [MixedCentralPolynomialCode.onSourceProductSpheres_targetBlock_iff]
  constructor
  · intro b
    have hb : b = 0 := Subsingleton.elim _ _
    subst b
    have hsphere : normSq x + w ^ 2 = 1 := q.1.2
    simpa only [
      NormalizedCorrectedFixedDetectorCompactSourceCode.layout,
      MixedCentralPolynomialCode.affineBlockNormSq,
      MixedCentralPolynomialCode.oneBlockAllAffineLayout,
      if_pos rfl, normSq, dot, pow_two, x, w] using hsphere
  · intro c
    exact Fin.elim0 c

/-- On the one-block compact base, the abstract central-weight product is
literally the square of the canonical chart weight. -/
theorem baseCentralWeightProduct_canonicalCompactBasePoint
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (t : ℝ) :
    baseCentralWeightProduct
        (NormalizedCorrectedFixedDetectorCompactSourceCode.layout
          (eqs := eqs) (vars := vars))
        (canonicalCompactBasePoint parameters I controller t) =
      (canonicalCentralChartPoint
        parameters I controller t).1.1.2 ^ 2 := by
  simp [baseCentralWeightProduct, canonicalCompactBasePoint]

/-- Compiler-facing uniform lower bound for the central-weight product
along the complete canonical compactified orbit. -/
theorem canonicalCentralWeightSqLowerBound_le_baseCentralWeightProduct
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (hcontroller :
      ∀ i, Controller.controllerRadiusSq (controller i) = 1)
    (t : ℝ) :
    canonicalCentralWeightSqLowerBound eqs vars ≤
      baseCentralWeightProduct
        (NormalizedCorrectedFixedDetectorCompactSourceCode.layout
          (eqs := eqs) (vars := vars))
        (canonicalCompactBasePoint parameters I controller t) := by
  rw [baseCentralWeightProduct_canonicalCompactBasePoint]
  exact canonicalCentralWeightSqLowerBound_le
    parameters I controller hcontroller t

end HGAS.NormalizedCorrectedCanonicalFixedDetectorCentralChart
