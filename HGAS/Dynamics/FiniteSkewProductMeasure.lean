import HGAS.Dynamics.PoincareRecurrence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic

/-!
# Invariant probabilities on finite permutation skew products

Let `ψ` be a real flow on `X`, and let `Φ` be a flow on the trivial
`n`-sheeted cover `X × Fin n`.  Suppose that every time map has the form

```
Φₜ(x,i) = (ψₜ(x), σₜ,x(i)),
```

where `σₜ,x` is a permutation of the finite fiber.  If `μ` is invariant for
`ψ`, then

```
μ × (normalized counting measure on Fin n)
```

is invariant for `Φ`.

The fiber permutation is allowed to depend on both time and the base point.
No separate measurability hypothesis on `σ` is needed: the skew map is
already assumed to be the time map of the continuous flow `Φ`.

This is the finite-sheet measure-lifting argument used informally in the
manuscript, proved here for a globally trivialized finite cover.  Combining
the lifted invariant probability with the project's Poincaré theorem gives
almost-everywhere forward recurrence upstairs.
-/

noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped BigOperators BoundedContinuousFunction

namespace HGAS.Dynamics

/-- The uniform probability on the nonempty finite type `Fin n`. -/
def uniformFinProbability (n : ℕ) [NeZero n] :
    ProbabilityMeasure (Fin n) :=
  ⟨(PMF.uniformOfFintype (Fin n)).toMeasure, inferInstance⟩

@[simp]
theorem uniformFinProbability_toMeasure
    (n : ℕ) [NeZero n] :
    (uniformFinProbability n : Measure (Fin n)) =
      (PMF.uniformOfFintype (Fin n)).toMeasure :=
  rfl

/-- Integration against uniform counting probability is the ordinary
finite arithmetic mean. -/
theorem integral_uniformFinProbability
    (n : ℕ) [NeZero n] (g : Fin n → ℝ) :
    (∫ i, g i ∂(uniformFinProbability n : Measure (Fin n))) =
      (n : ℝ)⁻¹ * ∑ i, g i := by
  rw [uniformFinProbability_toMeasure,
    PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,
    ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Fintype.card_fin, smul_eq_mul]
  rw [Finset.mul_sum]

/-- Average a bounded continuous observable over the finite fiber. -/
def finiteFiberAverage
    {X : Type*} [TopologicalSpace X]
    (n : ℕ) [NeZero n]
    (f : X × Fin n →ᵇ ℝ) : X →ᵇ ℝ :=
  (n : ℝ)⁻¹ •
    ∑ i : Fin n,
      f.compContinuous
        ⟨(fun x ↦ (x, i)), by fun_prop⟩

@[simp]
theorem finiteFiberAverage_apply
    {X : Type*} [TopologicalSpace X]
    (n : ℕ) [NeZero n]
    (f : X × Fin n →ᵇ ℝ) (x : X) :
    finiteFiberAverage n f x =
      (n : ℝ)⁻¹ * ∑ i, f (x, i) := by
  simp only [finiteFiberAverage,
    BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.coe_sum,
    Finset.sum_apply,
    BoundedContinuousFunction.compContinuous_apply,
    ContinuousMap.coe_mk, smul_eq_mul]

/-- A permutation of the sheets does not change a fiber average. -/
theorem finiteFiberAverage_permutation
    {X : Type*} [TopologicalSpace X]
    (n : ℕ) [NeZero n]
    (f : X × Fin n →ᵇ ℝ) (x : X)
    (e : Equiv.Perm (Fin n)) :
    (n : ℝ)⁻¹ * ∑ i, f (x, e i) =
      finiteFiberAverage n f x := by
  rw [finiteFiberAverage_apply]
  congr 1
  exact Equiv.sum_comp e (fun i ↦ f (x, i))

/-- Product of a base probability and uniform counting probability on the
finite sheet. -/
def finiteProductProbability
    {X : Type*} [MeasurableSpace X]
    (n : ℕ) [NeZero n]
    (μ : ProbabilityMeasure X) :
    ProbabilityMeasure (X × Fin n) :=
  μ.prod (uniformFinProbability n)

@[simp]
theorem finiteProductProbability_toMeasure
    {X : Type*} [MeasurableSpace X]
    (n : ℕ) [NeZero n]
    (μ : ProbabilityMeasure X) :
    (finiteProductProbability n μ : Measure (X × Fin n)) =
      (μ : Measure X).prod
        (uniformFinProbability n : Measure (Fin n)) :=
  rfl

/-- The first marginal of the uniform finite-sheet lift is the original
base probability. -/
@[simp]
theorem finiteProductProbability_map_fst
    {X : Type*} [MeasurableSpace X]
    (n : ℕ) [NeZero n]
    (μ : ProbabilityMeasure X) :
    (finiteProductProbability n μ).map
        measurable_fst.aemeasurable = μ := by
  exact ProbabilityMeasure.map_fst_prod
    μ (uniformFinProbability n)

/-- Fubini's theorem specialized to a uniform finite fiber. -/
theorem integral_finiteProductProbability
    {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (n : ℕ) [NeZero n]
    (μ : ProbabilityMeasure X)
    (f : X × Fin n →ᵇ ℝ) :
    (∫ z, f z
        ∂(finiteProductProbability n μ : Measure (X × Fin n))) =
      ∫ x, finiteFiberAverage n f x ∂(μ : Measure X) := by
  rw [finiteProductProbability_toMeasure,
    integral_prod _ (f.integrable _)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [integral_uniformFinProbability,
    finiteFiberAverage_apply]

/-- A flow on `X × Fin n` is a finite permutation skew product over `ψ`
when its base coordinate is `ψ` and each time map permutes every fiber. -/
def IsFinitePermutationSkewProduct
    {X : Type*} [TopologicalSpace X]
    (n : ℕ)
    (Φ : Flow ℝ (X × Fin n)) (ψ : Flow ℝ X)
    (σ : ℝ → X → Equiv.Perm (Fin n)) : Prop :=
  ∀ t x i, Φ t (x, i) = (ψ t x, σ t x i)

/-- Uniform normalized counting in each sheet lifts a base invariant
probability to a skew-product invariant probability. -/
def InvariantProbabilityMeasure.liftFinitePermutationSkewProduct
    {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (n : ℕ) [NeZero n]
    {Φ : Flow ℝ (X × Fin n)} {ψ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ψ)
    (σ : ℝ → X → Equiv.Perm (Fin n))
    (hskew : IsFinitePermutationSkewProduct n Φ ψ σ) :
    InvariantProbabilityMeasure Φ where
  measure := finiteProductProbability n μ.measure
  invariant := by
    intro t
    apply ProbabilityMeasure.toMeasure_injective
    simp only [timePushforward,
      ProbabilityMeasure.toMeasure_map]
    apply
      ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    rw [integral_map
      (Φ.continuous_toFun t).measurable.aemeasurable
      f.continuous.aestronglyMeasurable]
    let fAfter :
        X × Fin n →ᵇ ℝ :=
      f.compContinuous
        ⟨Φ t, Φ.continuous_toFun t⟩
    calc
      (∫ z, f (Φ t z)
          ∂(finiteProductProbability n μ.measure :
            Measure (X × Fin n))) =
          ∫ x, finiteFiberAverage n fAfter x
            ∂(μ.measure : Measure X) := by
              exact integral_finiteProductProbability
                n μ.measure fAfter
      _ =
          ∫ x, finiteFiberAverage n f (ψ t x)
            ∂(μ.measure : Measure X) := by
              apply integral_congr_ae
              filter_upwards [] with x
              rw [finiteFiberAverage_apply,
                finiteFiberAverage_apply]
              change
                (n : ℝ)⁻¹ *
                    ∑ i, f (Φ t (x, i)) =
                  (n : ℝ)⁻¹ *
                    ∑ i, f (ψ t x, i)
              simp_rw [hskew t x]
              congr 1
              exact
                Equiv.sum_comp (σ t x)
                  (fun i ↦ f (ψ t x, i))
      _ =
          ∫ x, finiteFiberAverage n f x
            ∂(μ.measure : Measure X) :=
              μ.integral_comp_time t
                (finiteFiberAverage n f)
      _ =
          ∫ z, f z
            ∂(finiteProductProbability n μ.measure :
              Measure (X × Fin n)) := by
                exact
                  (integral_finiteProductProbability
                    n μ.measure f).symm

@[simp]
theorem InvariantProbabilityMeasure.liftFinitePermutationSkewProduct_measure
    {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (n : ℕ) [NeZero n]
    {Φ : Flow ℝ (X × Fin n)} {ψ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ψ)
    (σ : ℝ → X → Equiv.Perm (Fin n))
    (hskew : IsFinitePermutationSkewProduct n Φ ψ σ) :
    (μ.liftFinitePermutationSkewProduct n σ hskew).measure =
      finiteProductProbability n μ.measure :=
  rfl

/-- The lifted invariant probability has exactly the prescribed base
marginal. -/
theorem InvariantProbabilityMeasure.map_fst_liftFinitePermutationSkewProduct
    {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (n : ℕ) [NeZero n]
    {Φ : Flow ℝ (X × Fin n)} {ψ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ψ)
    (σ : ℝ → X → Equiv.Perm (Fin n))
    (hskew : IsFinitePermutationSkewProduct n Φ ψ σ) :
    (μ.liftFinitePermutationSkewProduct n σ hskew).measure.map
        measurable_fst.aemeasurable = μ.measure := by
  rw [InvariantProbabilityMeasure.liftFinitePermutationSkewProduct_measure]
  exact finiteProductProbability_map_fst n μ.measure

/-- Poincaré recurrence for the normalized-counting lift: almost every
point of the finite skew product is forward recurrent. -/
theorem InvariantProbabilityMeasure.ae_forwardRecurrentAt_zero_liftFinite
    {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    (n : ℕ) [NeZero n]
    {Φ : Flow ℝ (X × Fin n)} {ψ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ψ)
    (σ : ℝ → X → Equiv.Perm (Fin n))
    (hskew : IsFinitePermutationSkewProduct n Φ ψ σ) :
    ∀ᵐ z
        ∂(finiteProductProbability n μ.measure :
          Measure (X × Fin n)),
      HGAS.ForwardRecurrentAt
        (fun t : ℝ ↦ Φ t z) 0 :=
  by
    letI : MetricSpace (Fin n) :=
      TopologicalSpace.metrizableSpaceMetric (Fin n)
    let ν : InvariantProbabilityMeasure Φ :=
      μ.liftFinitePermutationSkewProduct
        n σ hskew
    change
      ∀ᵐ z ∂(ν.measure : Measure (X × Fin n)),
        HGAS.ForwardRecurrentAt
          (fun t : ℝ ↦ Φ t z) 0
    exact
      @InvariantProbabilityMeasure.ae_forwardRecurrentAt_zero
        (X × Fin n) inferInstance inferInstance
        inferInstance inferInstance Φ ν

/-- In particular, every finite permutation skew product over a base
invariant probability has at least one recurrent point upstairs. -/
theorem InvariantProbabilityMeasure.exists_forwardRecurrentAt_zero_liftFinite
    {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    (n : ℕ) [NeZero n]
    {Φ : Flow ℝ (X × Fin n)} {ψ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ψ)
    (σ : ℝ → X → Equiv.Perm (Fin n))
    (hskew : IsFinitePermutationSkewProduct n Φ ψ σ) :
    ∃ z : X × Fin n,
      HGAS.ForwardRecurrentAt
        (fun t : ℝ ↦ Φ t z) 0 :=
  by
    letI : MetricSpace (Fin n) :=
      TopologicalSpace.metrizableSpaceMetric (Fin n)
    let ν : InvariantProbabilityMeasure Φ :=
      μ.liftFinitePermutationSkewProduct
        n σ hskew
    exact
      @InvariantProbabilityMeasure.exists_forwardRecurrentAt_zero
        (X × Fin n) inferInstance inferInstance
        inferInstance inferInstance Φ ν

end HGAS.Dynamics
