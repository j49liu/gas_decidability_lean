import HGAS.Analysis.RadicalTimeChangedTorusComponentFiniteGraph
import HGAS.Arithmetic.CorrectedFixedDetectorCompactSourceCode

/-!
# No-instance finite graphs for the corrected compact compiler

This file specializes the abstract component-graph and radical Fourier
theorems to the exact field and drift emitted by
`CorrectedFixedDetectorCompactSourceCode`.

The conclusions below are literally the type of the `finite_graph` field
of `CanonicalCompactAccumulatorGap` after substituting:

* the one-block corrected detector layout;
* the corrected source degree and clearing exponent;
* the unchanged detector source field;
* the corrected seven-moment drift;
* the runtime accumulator scale and reward margin.

Thus no informal renaming or hidden compatibility premise remains between
the analytic no-instance certificate and the corrected compiler.
-/

noncomputable section

open Function MeasureTheory
open scoped BigOperators BoundedContinuousFunction

namespace HGAS.CorrectedFixedDetectorCompactSourceCode

open HGAS
open HGAS.CompactAccumulatorPipelineCode

variable {eqs vars : ℕ}

/-- A selected component certificate gives the no-instance reward bound
in the exact specialized `finite_graph` type. -/
theorem finite_graph_of_componentFiniteGraphCertificate
    (u : CompilerInput eqs vars)
    (delta : ℝ)
    (componentGraph :
      ¬(system u).Solvable →
        ComponentFiniteGraphCertificate
          layout
          (sourceDegreeBound (system u))
          (clearingExponent (system u))
          (accumulatorScale u)
          (sourceFieldCode (parameters u) (system u))
          (sourceDriftCode (system u)))
    (hdelta :
      ∀ hnot : ¬(system u).Solvable,
        delta ≤
          3 * (componentGraph hnot).wStar / 2 -
            ((rewardMargin u).decode : ℝ)) :
    ¬(system u).Solvable →
      ∃ μ :
          Dynamics.InvariantProbabilityMeasure
            (sourceFlow
              layout
              (sourceDegreeBound (system u))
              (clearingExponent (system u))
              (accumulatorScale u)
              (sourceFieldCode (parameters u) (system u))
              (sourceDriftCode (system u))
              (rewardMargin u)),
        delta ≤
          Dynamics.observableAverage
            (UnitSpherePolynomialWrapper.sourceRewardBCF
              (sourceBlock
                (m := driftDimension vars) layout)
              (rewardCode
                (n := sourceDimension eqs vars)
                (k := affineBlockCount)
                (m := driftDimension vars)
                (rewardMargin u)))
            μ.measure := by
  exact
    CanonicalCompactAccumulatorGap.finite_graph_of_componentFiniteGraphCertificate
        (system u)
        layout
        (sourceDegreeBound (system u))
        (clearingExponent (system u))
        (accumulatorScale u)
        (sourceFieldCode (parameters u) (system u))
        (sourceFieldCode_termsDegreeLE
          (parameters u) (system u))
        (sourceDriftCode (system u))
        (sourceDriftCode_termsDegreeLE (system u))
        (rewardMargin u)
        (baseCompactTangency (parameters u) (system u))
        delta componentGraph hdelta

universe uClock uIndex

variable {d : Type uClock} [Fintype d]
variable
  {ι : Fin (driftDimension vars) → Type uIndex}
  {scale : ℝ}
  {p : d → ℕ}
  {sign : d → ℤ}
  {coefficient :
    ∀ q : Fin (driftDimension vars), ι q → ℂ}
  {exponent :
    ∀ q : Fin (driftDimension vars), ι q → d → ℤ}

/-- A time-changed radical-torus Fourier model of the corrected drift
directly fills the corrected compiler's no-instance `finite_graph`
obligation. -/
theorem finite_graph_of_radicalTimeChangedTorus
    (u : CompilerInput eqs vars)
    (G :
      ¬(system u).Solvable →
        HGAS.Analysis.RadicalTimeChangedTorusFourierComponent.Model
          layout
          (sourceDegreeBound (system u))
          (clearingExponent (system u))
          (accumulatorScale u)
          (sourceFieldCode (parameters u) (system u))
          (sourceDriftCode (system u))
          ι scale p sign coefficient exponent)
    (hscale : scale ≠ 0)
    (hp : ∀ i : d, (p i).Prime)
    (hinjective : Function.Injective p)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (hzero :
      ∀ _hnot : ¬(system u).Solvable,
        ∀ q j, exponent q j = 0 → coefficient q j = 0)
    (hcoefficient :
      ∀ q, Summable fun j ↦ ‖coefficient q j‖)
    (hweighted :
      ∀ q,
        Summable fun j ↦
          ‖coefficient q j‖ *
            HGAS.Clocks.RadicalSmallDivisor.radicalConjugateHeight
                p (exponent q j) ^
              (HGAS.Clocks.RadicalSmallDivisor.radicalDegree p - 1))
    (wStar delta : ℝ)
    (hprimitiveScale :
      4 *
          (∑ q : Fin (driftDimension vars),
            (HGAS.Analysis.primitiveCoordinateBound
              ι coefficient exponent
                (HGAS.Analysis.RadicalTimeChangedTorusFourierComponent.frequency
                  scale p sign) q) ^ 2) ≤
        wStar)
    (hcentral :
      ∀ hnot : ¬(system u).Solvable,
        ∀ b :
            (G hnot).ComponentSpace,
          wStar ≤ baseCentralWeightProduct layout b.1)
    (hdelta :
      delta ≤
        3 * wStar / 2 -
          ((rewardMargin u).decode : ℝ)) :
    ¬(system u).Solvable →
      ∃ μ :
          Dynamics.InvariantProbabilityMeasure
            (sourceFlow
              layout
              (sourceDegreeBound (system u))
              (clearingExponent (system u))
              (accumulatorScale u)
              (sourceFieldCode (parameters u) (system u))
              (sourceDriftCode (system u))
              (rewardMargin u)),
        delta ≤
          Dynamics.observableAverage
            (UnitSpherePolynomialWrapper.sourceRewardBCF
              (sourceBlock
                (m := driftDimension vars) layout)
              (rewardCode
                (n := sourceDimension eqs vars)
                (k := affineBlockCount)
                (m := driftDimension vars)
                (rewardMargin u)))
            μ.measure := by
  exact
    HGAS.Analysis.RadicalTimeChangedTorusFourierComponent.finite_graph
      (system u) G hscale hp hinjective hsign hzero
      hcoefficient hweighted wStar delta hprimitiveScale hcentral
      (sourceFieldCode_termsDegreeLE
        (parameters u) (system u))
      (sourceDriftCode_termsDegreeLE (system u))
      (rewardMargin u)
      (baseCompactTangency (parameters u) (system u))
      hdelta

end HGAS.CorrectedFixedDetectorCompactSourceCode
