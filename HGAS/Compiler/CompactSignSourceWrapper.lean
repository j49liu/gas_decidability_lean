import HGAS.Arithmetic.DQL
import HGAS.Accumulator.CompactSignDichotomy
import HGAS.Wrapper.UnitSphereWrapperConcreteReduction
import Mathlib.Tactic

/-!
# The exact compact-sign source interface

The paper does **not** claim that every invariant probability of the final
compact source has Haar clock marginal.  Boundary strata and the
one-point accumulator infinity always carry additional invariant
probabilities.  They are harmless because the specially constructed
reward is uniformly negative there.

Accordingly, the faithful interface between the compact source
construction and the homogeneous wrapper is the strict sign statement

```
  maximalInvariantAverage sourceFlow sourceReward < 0
      ↔ DQL(I).Solvable.
```

This file packages precisely that data.  It is intentionally independent
of how the sign theorem is proved.  The intended constructor combines:

* multi-block central compactification and positive time change;
* exclusion of modular Haar marginals from finite charts;
* the all-state modular--Jacobi selector;
* nonzero-drift escape to stereographic infinity; and
* the positive finite graph in a no-instance.

Once those ingredients yield a `CompactSignSourceCertificate`, the
already-verified polynomial wrapper gives the GAS equivalence in one
line.  Unlike `DetectorSourceCertificate`, this interface exactly matches
the reward and invariant-measure bookkeeping of Sections 10--12.

The completed augmented fixed-resource endpoint instantiates this generic
certificate interface downstream through
`FixedUniversalDQLCompactSignSourceFamily`; this file intentionally remains
independent of that particular construction.
-/

namespace HGAS

open Function MeasureTheory Set
open scoped BoundedContinuousFunction

noncomputable section

namespace Compiler

variable {n k eqs vars : ℕ}

/-- Complete semantic certificate expected from the compact
source/accumulator compiler for one DQL instance. -/
structure CompactSignSourceCertificate
    (sourceBlock : Fin n → Fin k)
    [Nonempty
      (UnitSpherePolynomialWrapper.SourceProductSphere sourceBlock)]
    (I : DQLSystem eqs vars) where
  /-- Odd degree used by the exact homogeneous wrapper. -/
  degree : ℕ
  degree_ge_three : 3 ≤ degree
  degree_odd : degree % 2 = 1
  /-- Rational polynomial field and compact-sign reward. -/
  fieldCode : PolynomialFieldCode n
  field_degree :
    ∀ j, PolynomialCode.TermsDegreeLE degree (fieldCode j)
  rewardCode : PolynomialCode n
  reward_degree :
    PolynomialCode.TermsDegreeLE (degree - 1) rewardCode
  /-- Any block may serve as the wrapper's proper-face witness. -/
  properFaceBlock : Fin k
  /-- Tangency to every sphere factor of the compact source. -/
  tangent :
    ∀ y :
        UnitSpherePolynomialWrapper.SourceProductSphere sourceBlock,
      UnitSpherePolynomialWrapper.SourceTangentAt sourceBlock y.1
        (PolynomialFieldCode.realize fieldCode y.1)
  /-- The compact source flow and its literal polynomial ODE equation. -/
  sourceFlow :
    Flow ℝ
      (UnitSpherePolynomialWrapper.SourceProductSphere sourceBlock)
  sourceFlow_integralCurve :
    ∀ y,
      IsIntegralCurve
        (fun t ↦ (sourceFlow t y).1)
        (fun _ x ↦ PolynomialFieldCode.realize fieldCode x)
  /-- The full compact sign theorem.  Boundary, infinity, finite-chart
  time change, selector, and finite-graph arguments all belong in the
  proof of this field. -/
  sourceMaximum_neg_iff_solvable :
    Dynamics.maximalInvariantAverage sourceFlow
        (UnitSpherePolynomialWrapper.sourceRewardBCF
          sourceBlock rewardCode) < 0 ↔
      I.Solvable

namespace CompactSignSourceCertificate

/-- Construct the faithful source certificate directly from the reusable
compact-accumulator sign theorem.

This declaration is deliberately verbose: each hypothesis corresponds to
one checkable line of the paper's compact-sign proof.  In particular,
`hnonzero` is where the modular/Jacobi classification and Haar exclusion
enter, while `hfiniteGraph` is the canonical no-instance graph.  The
classification is required only for ergodic invariant probabilities:
the compact-sign theorem chooses an ergodic maximizer and never asks for
a no-cancellation theorem for arbitrary invariant mixtures. -/
def ofCompactAccumulatorGap
    {sourceBlock : Fin n → Fin k}
    [Nonempty
      (UnitSpherePolynomialWrapper.SourceProductSphere sourceBlock)]
    (I : DQLSystem eqs vars)
    (degree : ℕ)
    (degree_ge_three : 3 ≤ degree)
    (degree_odd : degree % 2 = 1)
    (fieldCode : PolynomialFieldCode n)
    (field_degree :
      ∀ j, PolynomialCode.TermsDegreeLE degree (fieldCode j))
    (rewardCode : PolynomialCode n)
    (reward_degree :
      PolynomialCode.TermsDegreeLE (degree - 1) rewardCode)
    (properFaceBlock : Fin k)
    (tangent :
      ∀ y :
          UnitSpherePolynomialWrapper.SourceProductSphere sourceBlock,
        UnitSpherePolynomialWrapper.SourceTangentAt sourceBlock y.1
          (PolynomialFieldCode.realize fieldCode y.1))
    (sourceFlow :
      Flow ℝ
        (UnitSpherePolynomialWrapper.SourceProductSphere sourceBlock))
    (sourceFlow_integralCurve :
      ∀ y,
        IsIntegralCurve
          (fun t ↦ (sourceFlow t y).1)
          (fun _ x ↦ PolynomialFieldCode.realize fieldCode x))
    {s : Set
      (UnitSpherePolynomialWrapper.SourceProductSphere sourceBlock)}
    (hs : MeasurableSet s)
    (hinv : IsInvariant sourceFlow s)
    {B : Type*} [TopologicalSpace B]
    [MeasurableSpace B] [BorelSpace B]
    {baseFlow : Flow ℝ B}
    (π : s → B) (hπ : Continuous π)
    (hequiv :
      ∀ t : ℝ,
        Function.Semiconj π ((sourceFlow.restrict hinv) t)
          (baseFlow t))
    {m : ℕ}
    (q : s → FiniteAccumulatorChart m)
    (hq : Continuous q)
    (gb : B →ᵇ FinVector m ℝ)
    (hU :
      ∀ x i t,
        HasDerivAt
          (fun r ↦
            (q ((sourceFlow.restrict hinv) r x)).1.1.1 i)
          (accumulatorUField
            (q ((sourceFlow.restrict hinv) t x)).1.1.1
            (q ((sourceFlow.restrict hinv) t x)).1.1.2
            (gb (π ((sourceFlow.restrict hinv) t x))) i) t)
    (hW :
      ∀ x t,
        HasDerivAt
          (fun r ↦
            (q ((sourceFlow.restrict hinv) r x)).1.1.2)
          (accumulatorWField
            (q ((sourceFlow.restrict hinv) t x)).1.1.1
            (q ((sourceFlow.restrict hinv) t x)).1.1.2
            (gb (π ((sourceFlow.restrict hinv) t x)))) t)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hreward :
      ∀ x, x ∉ s →
        UnitSpherePolynomialWrapper.sourceRewardBCF
            sourceBlock rewardCode x ≤ -ε)
    (hnonzero :
      I.Solvable →
        ∀ μ : Dynamics.InvariantProbabilityMeasure sourceFlow,
          Dynamics.IsErgodicInvariantProbability
              sourceFlow μ.measure →
            ∀ hpos :
              (μ.measure :
                Measure
                  (UnitSpherePolynomialWrapper.SourceProductSphere
                    sourceBlock)) s ≠ 0,
            let ν :=
              μ.restrictToPositiveInvariant hs hpos hinv
            ∃ i : Fin m,
              (∫ b, gb b i
                ∂((ν.mapEquivariant π hπ hequiv).measure :
                  Measure B)) ≠ 0)
    (hfiniteGraph :
      ¬I.Solvable →
        ∃ μ : Dynamics.InvariantProbabilityMeasure sourceFlow,
          δ ≤ Dynamics.observableAverage
            (UnitSpherePolynomialWrapper.sourceRewardBCF
              sourceBlock rewardCode) μ.measure) :
    CompactSignSourceCertificate sourceBlock I where
  degree := degree
  degree_ge_three := degree_ge_three
  degree_odd := degree_odd
  fieldCode := fieldCode
  field_degree := field_degree
  rewardCode := rewardCode
  reward_degree := reward_degree
  properFaceBlock := properFaceBlock
  tangent := tangent
  sourceFlow := sourceFlow
  sourceFlow_integralCurve := sourceFlow_integralCurve
  sourceMaximum_neg_iff_solvable :=
    maximalInvariantAverage_neg_iff_of_compactAccumulatorGap
      hs hinv π hπ hequiv q hq gb hU hW
      (UnitSpherePolynomialWrapper.sourceRewardBCF
        sourceBlock rewardCode)
      I.Solvable hε hδ hreward hnonzero hfiniteGraph

/-- Executable homogeneous rational field emitted from a compact-sign
source certificate. -/
def finalFieldCode
    {sourceBlock : Fin n → Fin k}
    [Nonempty
      (UnitSpherePolynomialWrapper.SourceProductSphere sourceBlock)]
    {I : DQLSystem eqs vars}
    (C : CompactSignSourceCertificate sourceBlock I) :
    PolynomialFieldCode (n + 1) :=
  UnitSpherePolynomialWrapper.finalFieldCode
    sourceBlock C.degree C.fieldCode C.rewardCode

/-- **End-to-end compact-sign composition.**

GAS of the emitted homogeneous field is equivalent to DQL solvability.
No Haar uniqueness assumption is introduced at this final step. -/
theorem finalField_gas_iff_solvable
    {sourceBlock : Fin n → Fin k}
    [Nonempty
      (UnitSpherePolynomialWrapper.SourceProductSphere sourceBlock)]
    {I : DQLSystem eqs vars}
    (C : CompactSignSourceCertificate sourceBlock I) :
    GloballyAsymptoticallyStable
        (PolynomialFieldCode.realize C.finalFieldCode) 0 ↔
      I.Solvable := by
  change
    GloballyAsymptoticallyStable
        (PolynomialFieldCode.realize
          (UnitSpherePolynomialWrapper.finalFieldCode
            sourceBlock C.degree C.fieldCode C.rewardCode)) 0 ↔
      I.Solvable
  rw [
    UnitSpherePolynomialWrapper.realize_finalFieldCode_gas_iff_externalSourceMaximum_neg
        sourceBlock C.degree C.degree_ge_three C.degree_odd
        C.fieldCode C.field_degree C.rewardCode C.reward_degree
        C.properFaceBlock C.tangent C.sourceFlow
        C.sourceFlow_integralCurve]
  exact C.sourceMaximum_neg_iff_solvable

end CompactSignSourceCertificate

end Compiler

end

end HGAS
