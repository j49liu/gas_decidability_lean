import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorFiniteGraphBridge
import Mathlib.Tactic

/-!
# Explicit no-instance gap for the normalized corrected compiler

Let `centralLower > 0` bound the squared central chart weight on the
selected canonical component.  Reserving half of this quantity for the
primitive graph and assuming

```text
       8 * Σ_q primitiveBound(q)^2 ≤ centralLower
```

gives the explicit positive reward gap

```text
                       delta = 3 * centralLower / 8.
```

Every type below is the literal type of the normalized compact compiler.
-/

noncomputable section

open Function MeasureTheory
open scoped BigOperators BoundedContinuousFunction

namespace HGAS.NormalizedCorrectedFixedDetectorCompactSourceCode

open HGAS
open HGAS.CompactAccumulatorPipelineCode

variable {eqs vars : ℕ}

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

def explicitFiniteGraphDelta (centralLower : ℝ) : ℝ :=
  3 * centralLower / 8

theorem explicitFiniteGraphDelta_pos
    {centralLower : ℝ} (hcentralLower : 0 < centralLower) :
    0 < explicitFiniteGraphDelta centralLower := by
  unfold explicitFiniteGraphDelta
  positivity

/-- The explicit positive-gap endpoint for a normalized radical-torus
component. -/
theorem finite_graph_of_radicalTimeChangedTorus_explicitGap
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
    (centralLower : ℝ)
    (hcentralLower : 0 < centralLower)
    (hprimitive :
      8 *
          (∑ q : Fin (driftDimension vars),
            (HGAS.Analysis.primitiveCoordinateBound
              ι coefficient exponent
                (HGAS.Analysis.RadicalTimeChangedTorusFourierComponent.frequency
                  scale p sign) q) ^ 2) ≤
        centralLower)
    (hcentral :
      ∀ hnot : ¬(system u).Solvable,
        ∀ b : (G hnot).ComponentSpace,
          centralLower ≤ baseCentralWeightProduct layout b.1)
    (hmargin :
      ((rewardMargin u).decode : ℝ) ≤
        3 * centralLower / 8) :
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
        explicitFiniteGraphDelta centralLower ≤
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
  apply finite_graph_of_radicalTimeChangedTorus
    u G hscale hp hinjective hsign hzero hcoefficient hweighted
    (centralLower / 2) (explicitFiniteGraphDelta centralLower)
  · have hsum_nonneg :
        0 ≤
          ∑ q : Fin (driftDimension vars),
            (HGAS.Analysis.primitiveCoordinateBound
              ι coefficient exponent
                (HGAS.Analysis.RadicalTimeChangedTorusFourierComponent.frequency
                  scale p sign) q) ^ 2 :=
      Finset.sum_nonneg fun q _ ↦ sq_nonneg _
    nlinarith
  · intro hnot b
    have hhalf : centralLower / 2 ≤ centralLower := by
      linarith
    exact hhalf.trans (hcentral hnot b)
  · unfold explicitFiniteGraphDelta
    linarith

/-- Zero decoded reward-margin specialization. -/
theorem finite_graph_of_radicalTimeChangedTorus_explicitGap_zeroMargin
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
    (centralLower : ℝ)
    (hcentralLower : 0 < centralLower)
    (hprimitive :
      8 *
          (∑ q : Fin (driftDimension vars),
            (HGAS.Analysis.primitiveCoordinateBound
              ι coefficient exponent
                (HGAS.Analysis.RadicalTimeChangedTorusFourierComponent.frequency
                  scale p sign) q) ^ 2) ≤
        centralLower)
    (hcentral :
      ∀ hnot : ¬(system u).Solvable,
        ∀ b : (G hnot).ComponentSpace,
          centralLower ≤ baseCentralWeightProduct layout b.1)
    (hmargin :
      ((rewardMargin u).decode : ℝ) = 0) :
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
        explicitFiniteGraphDelta centralLower ≤
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
  apply finite_graph_of_radicalTimeChangedTorus_explicitGap
    u G hscale hp hinjective hsign hzero hcoefficient hweighted
    centralLower hcentralLower hprimitive hcentral
  rw [hmargin]
  positivity

end HGAS.NormalizedCorrectedFixedDetectorCompactSourceCode
