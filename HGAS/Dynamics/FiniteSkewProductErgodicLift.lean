import HGAS.Dynamics.ErgodicFactor
import HGAS.Dynamics.FiniteSkewProductMeasure
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Tactic

/-!
# Ergodic single-sheet lifts for trivial finite covers

`FiniteSkewProductMeasure` constructs the uniform-counting lift of an
invariant probability to a globally trivial finite cover `X × Fin n`.
For a continuous real flow one can say more.

Fix `x : X` and a sheet `i : Fin n`.  The second coordinate of

```text
                     t ↦ Φₜ(x,i)
```

is a continuous map from the connected real line to the discrete finite
space `Fin n`.  It is therefore constant.  Since the time-zero map is the
identity, the sheet label is always `i`.  Thus every continuous real-flow
skew product of the form used in `FiniteSkewProductMeasure` is actually

```text
                     Φₜ(x,i) = (ψₜ(x),i).
```

Consequently each individual sheet carries a copy of every base invariant
probability.  If the base probability is ergodic, its single-sheet lift is
ergodic as well; unlike the uniform lift, it is not a mixture of the
different sheets.  Its first marginal is exactly the original measure, and
Poincaré recurrence holds almost everywhere.

This conclusion is intentionally limited to a *globally trivialized*
cover.  A connected nontrivial finite covering need not admit a global
sheet label, so it requires a separate measurable finite-cover argument.
-/

noncomputable section

open Function MeasureTheory

namespace HGAS.Dynamics

namespace IsFinitePermutationSkewProduct

variable {X : Type*} [TopologicalSpace X]
  {n : ℕ}
  {Φ : Flow ℝ (X × Fin n)} {ψ : Flow ℝ X}
  {σ : ℝ → X → Equiv.Perm (Fin n)}

/-- A continuous real flow cannot move a point between globally discrete
sheets. -/
theorem sheet_eq
    (hskew : IsFinitePermutationSkewProduct n Φ ψ σ)
    (t : ℝ) (x : X) (i : Fin n) :
    σ t x i = i := by
  let sheet : ℝ → Fin n :=
    fun u ↦ (Φ u (x, i)).2
  have hsheet : Continuous sheet := by
    exact continuous_snd.comp
      (Φ.continuous continuous_id continuous_const)
  calc
    σ t x i = sheet t := by
      simpa only [sheet] using
        congrArg Prod.snd (hskew t x i).symm
    _ = sheet 0 :=
      TotallyDisconnectedSpace.eq_of_continuous
        sheet hsheet t 0
    _ = i := by simp [sheet]

/-- Pointwise product form of a continuous finite permutation skew
product over real time. -/
theorem eq_base_prod_sheet
    (hskew : IsFinitePermutationSkewProduct n Φ ψ σ)
    (t : ℝ) (z : X × Fin n) :
    Φ t z = (ψ t z.1, z.2) := by
  rcases z with ⟨x, i⟩
  rw [hskew t x i]
  exact Prod.ext rfl (hskew.sheet_eq t x i)

end IsFinitePermutationSkewProduct

/-! ## Inclusion of one sheet -/

variable {X : Type*} [TopologicalSpace X] {n : ℕ}

/-- Inclusion of the sheet labelled by `i`. -/
def finiteSheetInclusion (i : Fin n) : X → X × Fin n :=
  fun x ↦ (x, i)

/-- A single-sheet inclusion is continuous. -/
theorem finiteSheetInclusion_continuous (i : Fin n) :
    Continuous (finiteSheetInclusion (X := X) i) :=
  continuous_id.prodMk continuous_const

section Measure

variable [MeasurableSpace X] [BorelSpace X]
  {Φ : Flow ℝ (X × Fin n)} {ψ : Flow ℝ X}
  {σ : ℝ → X → Equiv.Perm (Fin n)}

namespace InvariantProbabilityMeasure

/-- Lift a base invariant probability to one chosen global sheet.

Continuity of real time forces that sheet to be invariant, so this is an
equivariant pushforward along `x ↦ (x,i)`. -/
def liftFinitePermutationSkewProductSheet
    (μ : InvariantProbabilityMeasure ψ)
    (hskew : IsFinitePermutationSkewProduct n Φ ψ σ)
    (i : Fin n) :
    InvariantProbabilityMeasure Φ :=
  μ.mapEquivariant
    (finiteSheetInclusion i)
    (finiteSheetInclusion_continuous i)
    (fun t x ↦ by
      symm
      exact hskew.eq_base_prod_sheet t (x, i))

@[simp]
theorem liftFinitePermutationSkewProductSheet_measure
    (μ : InvariantProbabilityMeasure ψ)
    (hskew : IsFinitePermutationSkewProduct n Φ ψ σ)
    (i : Fin n) :
    (μ.liftFinitePermutationSkewProductSheet hskew i).measure =
      μ.measure.map
        (finiteSheetInclusion_continuous i).measurable.aemeasurable :=
  rfl

/-- The first marginal of a single-sheet lift is exactly the base
probability. -/
@[simp]
theorem map_fst_liftFinitePermutationSkewProductSheet
    (μ : InvariantProbabilityMeasure ψ)
    (hskew : IsFinitePermutationSkewProduct n Φ ψ σ)
    (i : Fin n) :
    (μ.liftFinitePermutationSkewProductSheet hskew i).measure.map
        measurable_fst.aemeasurable =
      μ.measure := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [liftFinitePermutationSkewProductSheet_measure,
    ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map
    measurable_fst
    (finiteSheetInclusion_continuous i).measurable]
  simpa only [Function.comp_def, finiteSheetInclusion,
    id_eq] using
      (Measure.map_id :
        Measure.map id (μ.measure : Measure X) =
          (μ.measure : Measure X))

end InvariantProbabilityMeasure

namespace IsErgodicInvariantProbability

/-- An ergodic base probability has an ergodic lift on every individual
global sheet. -/
theorem liftFinitePermutationSkewProductSheet
    {μ : ProbabilityMeasure X}
    (hμ : IsErgodicInvariantProbability ψ μ)
    (hskew : IsFinitePermutationSkewProduct n Φ ψ σ)
    (i : Fin n) :
    IsErgodicInvariantProbability Φ
      ((⟨μ, hμ.invariant⟩ :
          InvariantProbabilityMeasure ψ)
        |>.liftFinitePermutationSkewProductSheet
          hskew i).measure := by
  exact hμ.mapEquivariant
    (finiteSheetInclusion i)
    (finiteSheetInclusion_continuous i)
    (fun t x ↦ by
      symm
      exact hskew.eq_base_prod_sheet t (x, i))

end IsErgodicInvariantProbability

end Measure

/-! ## Poincaré recurrence on one sheet -/

namespace InvariantProbabilityMeasure

variable {Z : Type*} [PseudoMetricSpace Z]
  [MeasurableSpace Z] [BorelSpace Z]
  [SecondCountableTopology Z]
  {m : ℕ}
  {Φ : Flow ℝ (Z × Fin m)} {ψ : Flow ℝ Z}
  {σ : ℝ → Z → Equiv.Perm (Fin m)}

/-- Almost every point of a single-sheet lift is forward recurrent. -/
theorem ae_forwardRecurrentAt_zero_liftFiniteSheet
    (μ : InvariantProbabilityMeasure ψ)
    (hskew : IsFinitePermutationSkewProduct m Φ ψ σ)
    (i : Fin m) :
    ∀ᵐ z
        ∂((μ.liftFinitePermutationSkewProductSheet
          hskew i).measure : Measure (Z × Fin m)),
      HGAS.ForwardRecurrentAt
        (fun t : ℝ ↦ Φ t z) 0 := by
  letI : MetricSpace (Fin m) :=
    TopologicalSpace.metrizableSpaceMetric (Fin m)
  exact
    @InvariantProbabilityMeasure.ae_forwardRecurrentAt_zero
      (Z × Fin m) inferInstance inferInstance
      inferInstance inferInstance Φ
      (μ.liftFinitePermutationSkewProductSheet hskew i)

/-- Every single-sheet lift contains a forward recurrent point. -/
theorem exists_forwardRecurrentAt_zero_liftFiniteSheet
    (μ : InvariantProbabilityMeasure ψ)
    (hskew : IsFinitePermutationSkewProduct m Φ ψ σ)
    (i : Fin m) :
    ∃ z : Z × Fin m,
      HGAS.ForwardRecurrentAt
        (fun t : ℝ ↦ Φ t z) 0 :=
  Filter.Eventually.exists
    (μ.ae_forwardRecurrentAt_zero_liftFiniteSheet
      hskew i)

end InvariantProbabilityMeasure

end HGAS.Dynamics
