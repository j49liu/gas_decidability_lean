import HGAS.Modular.GammaTwoHaarProbabilityUnique
import HGAS.Modular.GammaTwoOffPeriodicUnique
import HGAS.Modular.RecurrentMeasureClassification

/-!
# Unconditional closed-horocycle classification for integrable state factors

This file combines two previously independent parts of the level-two
modular argument.

* `gammaTwoDaniSmillieTheorem_unconditional` says that the modular
  marginal of an ergodic state flow is either normalized arclength on a
  closed horocycle or frame Haar probability.
* `gammaTwoHaar_reciprocalSlowdown_lintegral_eq_top` says that a joining
  with frame-Haar marginal has nonintegrable reciprocal projective
  slowdown as soon as one modular affine coordinate has the standard
  linear cusp growth.

Consequently an ergodic state probability satisfying the finite-chart
integrability condition has a normalized closed-horocycle marginal.
This is the exact modular-measure conclusion needed by compactified
detector arguments.  The theorem is deliberately generic in the state
space: a concrete compiler application must still provide its continuous
equivariant frame observation and the elementary finite-chart cusp bound.
-/

namespace HGAS.Modular

open Filter Function _root_.MeasureTheory Set Topology
open scoped ENNReal NNReal

noncomputable section

variable {S : Type*}
  [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  {Ψ : Flow ℝ S}

/-- The Dani--Smillie state-marginal classification is unconditional.

This is the direct no-hypothesis replacement for
`GammaTwoDaniSmillieTheorem.classifyErgodicStateMarginal`. -/
theorem classifyErgodicStateMarginal_unconditional
    {s : ℝ} (hs : s ≠ 0)
    (μ : ProbabilityMeasure S)
    (hμ : Dynamics.IsErgodicInvariantProbability Ψ μ)
    {π : S → GammaTwoFrameQuotient}
    (hπ : IsModularHorocycleFactorMap Ψ s π) :
    ∃ ν : ProbabilityMeasure GammaTwoFrameQuotient,
      DaniSmillieClassification ν ∧
        ((IsNormalizedClosedHorocycleProbability s
              (modularHorocycleMarginal μ hπ) ∧
            IsCarriedOverClosedHorocycle π s μ) ∨
          modularHorocycleMarginal μ hπ = ν) :=
  gammaTwoDaniSmillieTheorem_unconditional
    |>.classifyErgodicStateMarginal hs μ hμ hπ

/-- Every Haar witness returned by the unconditional Dani--Smillie
classification is the project's explicit normalized frame-Haar
probability. -/
theorem daniSmillieHaarWitness_eq_explicit
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : DaniSmillieClassification ν) :
    ν = gammaTwoExplicitFrameHaarProbability :=
  gammaTwoRightInvariantProbability_unique
    ν gammaTwoExplicitFrameHaarProbability
    hν.1 gammaTwoExplicitFrameHaarProbability_rightInvariant

/-- **Integrable state factors have closed modular marginal.**

Let an ergodic state flow continuously factor onto a nonzero rescaling of
the level-two horocycle flow.  Suppose `reciprocalSlowdown` is the inverse
projective clock density.  The hypothesis `hchart` is the pointwise cusp
estimate: above a fixed chart threshold it dominates a nonzero multiple
of the `M`-th power of modular height.  If `M ≥ 2`, frame Haar would make
its lower integral infinite.  Therefore finite integrability excludes
the Haar branch, leaving canonical normalized arclength on a closed
horocycle.  The state probability is simultaneously carried by the
preimage of that orbit.

No choice of Haar witness remains in the statement or proof. -/
theorem normalizedClosedMarginal_of_reciprocalSlowdown_integrable
    {s : ℝ} (hs : s ≠ 0)
    (μ : ProbabilityMeasure S)
    (hμ : Dynamics.IsErgodicInvariantProbability Ψ μ)
    {π : S → GammaTwoFrameQuotient}
    (hπ : IsModularHorocycleFactorMap Ψ s π)
    (reciprocalSlowdown : S → ℝ≥0∞)
    (Y : ℝ) (hY : 1 < Y)
    (Ychart : ℝ)
    (M : ℕ) (hM : 2 ≤ M)
    (κ : ℝ≥0) (hκ : κ ≠ 0)
    (hchart :
      ∀ᵐ x ∂(μ : Measure S),
        (κ : ℝ≥0∞) ^ M *
            Dynamics.cuspTailHeightPower
              Ychart M
              (gammaTwoExplicitCuspHeight Y (π x)) ≤
          reciprocalSlowdown x)
    (hfinite :
      (∫⁻ x, reciprocalSlowdown x ∂(μ : Measure S)) ≠ ∞) :
    IsNormalizedClosedHorocycleProbability s
        (modularHorocycleMarginal μ hπ) ∧
      IsCarriedOverClosedHorocycle π s μ := by
  obtain ⟨ν, hν, hclosed | hhaar⟩ :=
    classifyErgodicStateMarginal_unconditional
      hs μ hμ hπ
  · exact hclosed
  · have hνexplicit :
        ν = gammaTwoExplicitFrameHaarProbability :=
      daniSmillieHaarWitness_eq_explicit hν
    have hmarginalProbability :
        modularHorocycleMarginal μ hπ =
          gammaTwoExplicitFrameHaarProbability := by
      exact hhaar.trans hνexplicit
    have hmarginalMeasure :
        Measure.map π (μ : Measure S) =
          (gammaTwoExplicitFrameHaarProbability :
            Measure GammaTwoFrameQuotient) := by
      have hmeasure :=
        congrArg ProbabilityMeasure.toMeasure
          hmarginalProbability
      change
        Measure.map π (μ : Measure S) =
          (gammaTwoExplicitFrameHaarProbability :
            Measure GammaTwoFrameQuotient) at hmeasure
      exact hmeasure
    have hinfinite :
        (∫⁻ x, reciprocalSlowdown x ∂(μ : Measure S)) = ∞ :=
      explicitGammaTwoHaar_reciprocalSlowdown_lintegral_eq_top
        (μ : Measure S) π hπ.continuous.measurable
        reciprocalSlowdown Y hY Ychart M hM
        hmarginalMeasure κ hκ hchart
    exact False.elim (hfinite hinfinite)

end

end HGAS.Modular
