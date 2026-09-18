import HGAS.Dynamics.FiniteSkewProductErgodicLift
import HGAS.Dynamics.RecurrenceTransport
import HGAS.Modular.HorocycleMeasureClassification
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Tactic

/-!
# Conditional classification of recurrent modular state measures

## Routing in the completed endpoint

The generic conditional lemmas below remain valid and are retained as a
reusable interface.  The base theorem `classifyErgodicStateMarginal` also
feeds the alternative module `GammaTwoStateMarginalClosed`.  The completed
endpoint does not use the later finite-permutation-cover specializations;
its live classification path instead uses the unconditional level-two and
pointwise route culminating in `GammaTwoOffPeriodicUnique`.

This file is the semantic bridge from a recurrent state flow to the
level-two horocycle quotient.

Suppose a continuous state flow `Ψ` has a continuous observation

```text
       π : state space → Γ(2) \ SL(2,ℝ)
```

which intertwines `Ψ` with a nonzero constant rescaling of the horocycle
flow.  Then:

1. every ergodic `Ψ`-invariant probability has an ergodic modular
   marginal;
2. almost every state is forward recurrent, and its modular observation
   is forward recurrent as well;
3. assuming the explicitly supplied proposition
   `GammaTwoDaniSmillieTheorem`, the marginal is either normalized
   arclength on a closed horocycle or normalized frame Haar measure; and
4. in the closed branch, the original state probability gives full mass
   to the preimage of that closed horocycle.

The result is then specialized to the globally trivial finite-sheet model
from `FiniteSkewProductMeasure`.  Conversely, the single-sheet construction
from `FiniteSkewProductErgodicLift` gives an ergodic recurrent lift of every
ergodic modular probability without changing its marginal.

## Exact trust boundary

`GammaTwoDaniSmillieTheorem` is always an explicit argument below.  It is a
named proposition, not an axiom, instance, or theorem proved in this file.
All reasoning from that proposition to the state-space conclusion is
kernel checked.

The file does **not** construct the paper-specific theta-state map.  To
apply the main theorem to that map one must still prove its continuity and
the exact flow-intertwining equation.  Likewise, a genuinely nontrivial
connected finite cover needs a global measurable lifting theorem; the
finite-sheet corollaries here use the existing honest product model
`X × Fin n`.
-/

noncomputable section

open Filter Function MeasureTheory Set Topology

namespace HGAS.Modular

/-! ## Modular factor maps and marginals -/

variable {S : Type*}
  [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  {Ψ : Flow ℝ S}

/-- The exact data saying that a state observation is a factor map to the
scale-`s` level-two horocycle flow. -/
structure IsModularHorocycleFactorMap
    (Ψ : Flow ℝ S) (s : ℝ)
    (π : S → GammaTwoFrameQuotient) : Prop where
  /-- The modular observation is continuous. -/
  continuous : Continuous π
  /-- State evolution is observed as scaled horocycle evolution. -/
  semiconj :
    ∀ t : ℝ,
      Function.Semiconj π (Ψ t)
        (scaledGammaTwoHorocycleFlow s t)

/-- Push a state probability to its modular horocycle marginal. -/
def modularHorocycleMarginal
    (μ : ProbabilityMeasure S)
    {s : ℝ} {π : S → GammaTwoFrameQuotient}
    (hπ : IsModularHorocycleFactorMap Ψ s π) :
    ProbabilityMeasure GammaTwoFrameQuotient :=
  μ.map hπ.continuous.measurable.aemeasurable

/-- An ergodic state probability has an ergodic modular marginal. -/
theorem IsModularHorocycleFactorMap.ergodicMarginal
    {μ : ProbabilityMeasure S}
    {s : ℝ} {π : S → GammaTwoFrameQuotient}
    (hπ : IsModularHorocycleFactorMap Ψ s π)
    (hμ :
      Dynamics.IsErgodicInvariantProbability Ψ μ) :
    Dynamics.IsErgodicInvariantProbability
      (scaledGammaTwoHorocycleFlow s)
      (modularHorocycleMarginal μ hπ) :=
  hμ.mapEquivariant π hπ.continuous hπ.semiconj

/-- The source probability is carried over a closed modular horocycle.

This is the state-space support statement: it records full mass on the
preimage of one explicitly periodic orbit, rather than merely classifying
the pushforward measure. -/
def IsCarriedOverClosedHorocycle
    (π : S → GammaTwoFrameQuotient) (s : ℝ)
    (μ : ProbabilityMeasure S) : Prop :=
  ∃ q : GammaTwoFrameQuotient,
    ∃ T : ℝ, 0 < T ∧
      scaledGammaTwoHorocycleFlow s T q = q ∧
      (μ : Measure S)
          (π ⁻¹' Flow.orbit
            (scaledGammaTwoHorocycleFlow s) q) = 1

/-- If the modular marginal is canonical normalized arclength on a closed
horocycle, then the state probability gives full mass to the preimage of
that orbit. -/
theorem IsModularHorocycleFactorMap.carriedOverClosed_of_normalizedMarginal
    (μ : ProbabilityMeasure S)
    {s : ℝ} {π : S → GammaTwoFrameQuotient}
    (hπ : IsModularHorocycleFactorMap Ψ s π)
    (hclosed :
      IsNormalizedClosedHorocycleProbability s
        (modularHorocycleMarginal μ hπ)) :
    IsCarriedOverClosedHorocycle π s μ := by
  obtain ⟨q, T, hT, hperiod, hmarginal⟩ := hclosed
  refine ⟨q, T, hT, hperiod, ?_⟩
  let O : Set GammaTwoFrameQuotient :=
    Flow.orbit (scaledGammaTwoHorocycleFlow s) q
  have hO : MeasurableSet O :=
    (Dynamics.isCompact_flow_orbit_of_periodic
      (scaledGammaTwoHorocycleFlow s) q
      hT.ne' hperiod).isClosed.measurableSet
  rw [← Measure.map_apply hπ.continuous.measurable hO]
  change
    ((modularHorocycleMarginal μ hπ :
      ProbabilityMeasure GammaTwoFrameQuotient) :
        Measure GammaTwoFrameQuotient) O = 1
  rw [hmarginal]
  exact
    Dynamics.periodicOrbitInvariantProbability_orbit_mass
      (scaledGammaTwoHorocycleFlow s) q hT hperiod

/-! ## Dani--Smillie classification transported to a state flow -/

/-- **Conditional recurrent-state marginal classification.**

Assuming the stated Dani--Smillie theorem and a nonzero time scale, every
ergodic state probability has one of two modular marginals:

* canonical normalized arclength on a periodic horocycle, with the state
  measure carried over that orbit; or
* normalized frame Haar probability.

The returned `ν` is accompanied by the full
`DaniSmillieClassification ν` certificate, so clients also retain its
right-invariance and unit-speed classification properties. -/
theorem GammaTwoDaniSmillieTheorem.classifyErgodicStateMarginal
    (hDS : GammaTwoDaniSmillieTheorem)
    {s : ℝ} (hs : s ≠ 0)
    (μ : ProbabilityMeasure S)
    (hμ :
      Dynamics.IsErgodicInvariantProbability Ψ μ)
    {π : S → GammaTwoFrameQuotient}
    (hπ : IsModularHorocycleFactorMap Ψ s π) :
    ∃ ν : ProbabilityMeasure GammaTwoFrameQuotient,
      DaniSmillieClassification ν ∧
        ((IsNormalizedClosedHorocycleProbability s
              (modularHorocycleMarginal μ hπ) ∧
            IsCarriedOverClosedHorocycle π s μ) ∨
          modularHorocycleMarginal μ hπ = ν) := by
  obtain ⟨ν, hν⟩ := hDS
  refine ⟨ν, hν, ?_⟩
  rcases hν.classify_exact_at_nonzero_scale hs
      (modularHorocycleMarginal μ hπ)
      (hπ.ergodicMarginal hμ) with
    hclosed | hhaar
  · exact Or.inl
      ⟨hclosed,
        hπ.carriedOverClosed_of_normalizedMarginal
          μ hclosed⟩
  · exact Or.inr hhaar

/-- Version of `classifyErgodicStateMarginal` which also records Poincaré
recurrence almost everywhere upstairs and recurrence of the corresponding
modular observations downstairs. -/
theorem GammaTwoDaniSmillieTheorem.classifyErgodicRecurrentStateMarginal
    {R : Type*}
    [PseudoMetricSpace R] [MeasurableSpace R]
    [BorelSpace R] [SecondCountableTopology R]
    {Θ : Flow ℝ R}
    (hDS : GammaTwoDaniSmillieTheorem)
    {s : ℝ} (hs : s ≠ 0)
    (μ : ProbabilityMeasure R)
    (hμ :
      Dynamics.IsErgodicInvariantProbability Θ μ)
    {π : R → GammaTwoFrameQuotient}
    (hπ : IsModularHorocycleFactorMap Θ s π) :
    (∀ᵐ x ∂(μ : Measure R),
      ForwardRecurrentAt (fun t : ℝ ↦ Θ t x) 0 ∧
      ForwardRecurrentAt
        (fun t : ℝ ↦
          scaledGammaTwoHorocycleFlow s t (π x)) 0) ∧
    ∃ ν : ProbabilityMeasure GammaTwoFrameQuotient,
      DaniSmillieClassification ν ∧
        ((IsNormalizedClosedHorocycleProbability s
              (modularHorocycleMarginal μ hπ) ∧
            IsCarriedOverClosedHorocycle π s μ) ∨
          modularHorocycleMarginal μ hπ = ν) := by
  refine ⟨?_,
    hDS.classifyErgodicStateMarginal hs μ hμ hπ⟩
  have hrec :
      ∀ᵐ x ∂(μ : Measure R),
        ForwardRecurrentAt
          (fun t : ℝ ↦ Θ t x) 0 :=
    @Dynamics.InvariantProbabilityMeasure.ae_forwardRecurrentAt_zero
      R inferInstance inferInstance inferInstance
      inferInstance Θ
      (⟨μ, hμ.invariant⟩ :
        Dynamics.InvariantProbabilityMeasure Θ)
  filter_upwards [hrec] with x hx
  exact
    ⟨hx,
      Dynamics.forwardRecurrentAt_orbit_of_equivariant
        π hπ.continuous hπ.semiconj x 0 hx⟩

/-! ## Globally trivial finite-sheet modular covers -/

/-- The first projection of a finite permutation skew product is a modular
horocycle factor map. -/
def finitePermutationSkewProductModularFactor
    {s : ℝ} (n : ℕ)
    {Φ :
      Flow ℝ (GammaTwoFrameQuotient × Fin n)}
    (σ :
      ℝ → GammaTwoFrameQuotient →
        Equiv.Perm (Fin n))
    (hskew :
      Dynamics.IsFinitePermutationSkewProduct
        n Φ (scaledGammaTwoHorocycleFlow s) σ) :
    IsModularHorocycleFactorMap Φ s Prod.fst where
  continuous := continuous_fst
  semiconj := by
    intro t z
    rcases z with ⟨q, i⟩
    exact congrArg Prod.fst (hskew t q i)

/-- An ergodic probability on a globally trivial finite modular cover has
a closed-horocycle or Haar first marginal.  In the closed case it gives
full mass to the inverse image of the periodic orbit. -/
theorem GammaTwoDaniSmillieTheorem.classifyErgodicFinitePermutationCover
    (hDS : GammaTwoDaniSmillieTheorem)
    {s : ℝ} (hs : s ≠ 0)
    (n : ℕ)
    {Φ :
      Flow ℝ (GammaTwoFrameQuotient × Fin n)}
    (σ :
      ℝ → GammaTwoFrameQuotient →
        Equiv.Perm (Fin n))
    (hskew :
      Dynamics.IsFinitePermutationSkewProduct
        n Φ (scaledGammaTwoHorocycleFlow s) σ)
    (μ :
      ProbabilityMeasure
        (GammaTwoFrameQuotient × Fin n))
    (hμ :
      Dynamics.IsErgodicInvariantProbability Φ μ) :
    let hfactor :=
      finitePermutationSkewProductModularFactor
        n σ hskew
    ∃ ν : ProbabilityMeasure GammaTwoFrameQuotient,
      DaniSmillieClassification ν ∧
        ((IsNormalizedClosedHorocycleProbability s
              (modularHorocycleMarginal μ hfactor) ∧
            IsCarriedOverClosedHorocycle Prod.fst s μ) ∨
          modularHorocycleMarginal μ hfactor = ν) := by
  dsimp only
  exact hDS.classifyErgodicStateMarginal
    hs μ hμ
      (finitePermutationSkewProductModularFactor
        n σ hskew)

/-- The preceding finite-cover classification together with almost-everywhere
recurrence upstairs and downstairs. -/
theorem GammaTwoDaniSmillieTheorem.classifyErgodicRecurrentFinitePermutationCover
    (hDS : GammaTwoDaniSmillieTheorem)
    {s : ℝ} (hs : s ≠ 0)
    (n : ℕ)
    {Φ :
      Flow ℝ (GammaTwoFrameQuotient × Fin n)}
    (σ :
      ℝ → GammaTwoFrameQuotient →
        Equiv.Perm (Fin n))
    (hskew :
      Dynamics.IsFinitePermutationSkewProduct
        n Φ (scaledGammaTwoHorocycleFlow s) σ)
    (μ :
      ProbabilityMeasure
        (GammaTwoFrameQuotient × Fin n))
    (hμ :
      Dynamics.IsErgodicInvariantProbability Φ μ) :
    let hfactor :=
      finitePermutationSkewProductModularFactor
        n σ hskew
    (∀ᵐ z ∂(μ : Measure
        (GammaTwoFrameQuotient × Fin n)),
      ForwardRecurrentAt (fun t : ℝ ↦ Φ t z) 0 ∧
      ForwardRecurrentAt
        (fun t : ℝ ↦
          scaledGammaTwoHorocycleFlow s t z.1) 0) ∧
    ∃ ν : ProbabilityMeasure GammaTwoFrameQuotient,
      DaniSmillieClassification ν ∧
        ((IsNormalizedClosedHorocycleProbability s
              (modularHorocycleMarginal μ hfactor) ∧
            IsCarriedOverClosedHorocycle Prod.fst s μ) ∨
          modularHorocycleMarginal μ hfactor = ν) := by
  dsimp only
  letI : MetricSpace GammaTwoFrameQuotient :=
    TopologicalSpace.metrizableSpaceMetric
      GammaTwoFrameQuotient
  letI : MetricSpace (Fin n) :=
    TopologicalSpace.metrizableSpaceMetric (Fin n)
  exact hDS.classifyErgodicRecurrentStateMarginal
    hs μ hμ
      (finitePermutationSkewProductModularFactor
        n σ hskew)

/-- Conversely, every ergodic modular horocycle probability has an
ergodic, almost-everywhere recurrent lift on each chosen global sheet.
Its first marginal is unchanged, and the explicit Dani--Smillie hypothesis
classifies that marginal.

This theorem is useful when a future theta-state construction supplies a
global finite sheet label. -/
theorem GammaTwoDaniSmillieTheorem.classifyAndLiftErgodicModularProbability
    (hDS : GammaTwoDaniSmillieTheorem)
    {s : ℝ} (hs : s ≠ 0)
    (n : ℕ)
    {Φ :
      Flow ℝ (GammaTwoFrameQuotient × Fin n)}
    (σ :
      ℝ → GammaTwoFrameQuotient →
        Equiv.Perm (Fin n))
    (hskew :
      Dynamics.IsFinitePermutationSkewProduct
        n Φ (scaledGammaTwoHorocycleFlow s) σ)
    (μ : ProbabilityMeasure GammaTwoFrameQuotient)
    (hμ :
      Dynamics.IsErgodicInvariantProbability
        (scaledGammaTwoHorocycleFlow s) μ)
    (i : Fin n) :
    let μi :=
      (⟨μ, hμ.invariant⟩ :
          Dynamics.InvariantProbabilityMeasure
            (scaledGammaTwoHorocycleFlow s))
        |>.liftFinitePermutationSkewProductSheet
          hskew i
    ∃ ν : ProbabilityMeasure GammaTwoFrameQuotient,
      DaniSmillieClassification ν ∧
        Dynamics.IsErgodicInvariantProbability Φ μi.measure ∧
        μi.measure.map measurable_fst.aemeasurable = μ ∧
        (IsNormalizedClosedHorocycleProbability s μ ∨
          μ = ν) ∧
        ∀ᵐ z ∂(μi.measure : Measure
            (GammaTwoFrameQuotient × Fin n)),
          ForwardRecurrentAt (fun t : ℝ ↦ Φ t z) 0 := by
  dsimp only
  obtain ⟨ν, hν⟩ := hDS
  have hμi :
      Dynamics.IsErgodicInvariantProbability Φ
        ((⟨μ, hμ.invariant⟩ :
            Dynamics.InvariantProbabilityMeasure
              (scaledGammaTwoHorocycleFlow s))
          |>.liftFinitePermutationSkewProductSheet
            hskew i).measure :=
    hμ.liftFinitePermutationSkewProductSheet
      hskew i
  refine ⟨ν, hν, hμi, ?_, ?_, ?_⟩
  · exact
      (⟨μ, hμ.invariant⟩ :
          Dynamics.InvariantProbabilityMeasure
            (scaledGammaTwoHorocycleFlow s))
        |>.map_fst_liftFinitePermutationSkewProductSheet
          hskew i
  · exact
      hν.classify_exact_at_nonzero_scale hs μ hμ
  · letI : MetricSpace GammaTwoFrameQuotient :=
      TopologicalSpace.metrizableSpaceMetric
        GammaTwoFrameQuotient
    letI : MetricSpace (Fin n) :=
      TopologicalSpace.metrizableSpaceMetric (Fin n)
    exact
      @Dynamics.InvariantProbabilityMeasure.ae_forwardRecurrentAt_zero
        (GammaTwoFrameQuotient × Fin n)
        inferInstance inferInstance inferInstance
        inferInstance Φ
        (⟨_, hμi.invariant⟩ :
          Dynamics.InvariantProbabilityMeasure Φ)

end HGAS.Modular
