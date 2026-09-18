import HGAS.Dynamics.HomeomorphicFlow
import HGAS.Dynamics.InvariantFullMeasureRestriction
import HGAS.Dynamics.InvariantRestriction
import Mathlib.Tactic

/-!
# Observable averages on invariant components

This module records reusable measure-theoretic facts for an invariant
component of a compact flow:

* restriction of a bounded continuous observable to a subtype;
* preservation of its average under an equivariant pushforward;
* preservation of its average when an invariant probability is pulled
  back to a full-measure invariant subtype;
* an upper bound obtained by splitting an invariant probability between
  an invariant set and its complement.

The last result is especially useful when a phase space is, up to null
sets, the union of two invariant components with the same maximal
observable average.
-/

namespace HGAS.Dynamics

open Function MeasureTheory Set
open scoped BoundedContinuousFunction ENNReal

noncomputable section

variable {X Y : Type*}
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Restrict a bounded continuous observable to a subtype. -/
def subtypeObservable
    (a : X →ᵇ ℝ) (s : Set X) : s →ᵇ ℝ :=
  a.compContinuous ⟨Subtype.val, continuous_subtype_val⟩

omit [MeasurableSpace X] [BorelSpace X] in
@[simp]
theorem subtypeObservable_apply
    (a : X →ᵇ ℝ) (s : Set X) (x : s) :
    subtypeObservable a s x = a x :=
  rfl

/-- An equivariant pushforward preserves the average of a pulled-back
observable. -/
theorem observableAverage_mapEquivariant
    {ϕ : Flow ℝ X} {ψ : Flow ℝ Y}
    (μ : InvariantProbabilityMeasure ϕ)
    (q : X → Y) (hq : Continuous q)
    (hequiv : ∀ t : ℝ, Function.Semiconj q (ϕ t) (ψ t))
    (a : Y →ᵇ ℝ) :
    observableAverage a
        (μ.mapEquivariant q hq hequiv).measure =
      observableAverage
        (a.compContinuous ⟨q, hq⟩) μ.measure := by
  unfold observableAverage
  rw [InvariantProbabilityMeasure.mapEquivariant_measure]
  change
    (∫ y : Y, a y
        ∂Measure.map q (μ.measure : Measure X)) =
      ∫ x : X, (a.compContinuous ⟨q, hq⟩) x
        ∂(μ.measure : Measure X)
  rw [integral_map
    (f := fun y : Y ↦ a y)
    (φ := q)
    hq.measurable.aemeasurable
    a.continuous.aestronglyMeasurable]
  rfl

/-- Pulling an invariant probability to a full-measure invariant subtype
does not change the average of an ambient observable. -/
theorem observableAverage_restrictToFullMeasureInvariant
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    {s : Set X} (hs : MeasurableSet s)
    (hfull : (μ.measure : Measure X) s = 1)
    (hinv : IsInvariant ϕ s)
    (a : X →ᵇ ℝ) :
    observableAverage (subtypeObservable a s)
        (μ.restrictToFullMeasureInvariant hs hfull hinv).measure =
      observableAverage a μ.measure := by
  unfold observableAverage
  have hmap :=
    μ.map_restrictToFullMeasureInvariant_measure
      hs hfull hinv
  calc
    (∫ x : s, subtypeObservable a s x
        ∂((μ.restrictToFullMeasureInvariant hs hfull hinv).measure :
          Measure s)) =
        ∫ y : X, a y
          ∂Measure.map ((↑) : s → X)
            ((μ.restrictToFullMeasureInvariant
              hs hfull hinv).measure : Measure s) := by
          symm
          rw [integral_map
            (f := fun y : X ↦ a y)
            (φ := ((↑) : s → X))
            measurable_subtype_coe.aemeasurable
            a.continuous.aestronglyMeasurable]
          rfl
    _ = ∫ y : X, a y ∂(μ.measure : Measure X) := by
      rw [hmap]

/-- An invariant probability on a restricted flow pushes to the ambient
flow along the subtype inclusion. -/
def InvariantProbabilityMeasure.mapSubtype
    {ϕ : Flow ℝ X} {s : Set X}
    (hinv : IsInvariant ϕ s)
    (μ : InvariantProbabilityMeasure (ϕ.restrict hinv)) :
    InvariantProbabilityMeasure ϕ :=
  μ.mapEquivariant Subtype.val continuous_subtype_val
    (fun _ _ ↦ rfl)

@[simp]
theorem InvariantProbabilityMeasure.mapSubtype_measure
    {ϕ : Flow ℝ X} {s : Set X}
    (hinv : IsInvariant ϕ s)
    (μ : InvariantProbabilityMeasure (ϕ.restrict hinv)) :
    (μ.mapSubtype hinv).measure =
      μ.measure.map measurable_subtype_coe.aemeasurable :=
  rfl

/-- Pushing a component probability to the ambient flow preserves the
corresponding restricted-observable average. -/
theorem observableAverage_mapSubtype
    {ϕ : Flow ℝ X} {s : Set X}
    (hinv : IsInvariant ϕ s)
    (μ : InvariantProbabilityMeasure (ϕ.restrict hinv))
    (a : X →ᵇ ℝ) :
    observableAverage a (μ.mapSubtype hinv).measure =
      observableAverage (subtypeObservable a s) μ.measure :=
  observableAverage_mapEquivariant
    μ Subtype.val continuous_subtype_val
      (fun _ _ ↦ rfl) a

/-- Split an invariant probability between an invariant component and its
complement.  If almost every point belongs to one of two classes and every
invariant probability concentrated on either class has average at most
`β`, then the original average is also at most `β`.

Only the first class must itself be measurable and invariant: its
complement is automatically invariant for a two-sided flow, and the
almost-sure union hypothesis puts that complementary piece in the second
class. -/
theorem observableAverage_le_of_ae_mem_invariant_union
    [Nonempty X]
    {ϕ : Flow ℝ X}
    (a : X →ᵇ ℝ) (β : ℝ)
    {s t : Set X}
    (hs : MeasurableSet s)
    (hsinv : IsInvariant ϕ s)
    (hboundS :
      ∀ μ : InvariantProbabilityMeasure ϕ,
        (∀ᵐ x ∂(μ.measure : Measure X), x ∈ s) →
        observableAverage a μ.measure ≤ β)
    (hboundT :
      ∀ μ : InvariantProbabilityMeasure ϕ,
        (∀ᵐ x ∂(μ.measure : Measure X), x ∈ t) →
        observableAverage a μ.measure ≤ β)
    (μ : InvariantProbabilityMeasure ϕ)
    (hunion :
      ∀ᵐ x ∂(μ.measure : Measure X), x ∈ s ∨ x ∈ t) :
    observableAverage a μ.measure ≤ β := by
  let νs : FiniteMeasure X :=
    μ.measure.toFiniteMeasure.restrict s
  let νo : FiniteMeasure X :=
    μ.measure.toFiniteMeasure.restrict sᶜ
  have hsum :
      νs + νo = μ.measure.toFiniteMeasure := by
    apply FiniteMeasure.toMeasure_injective
    simpa only [νs, νo,
      FiniteMeasure.toMeasure_add,
      FiniteMeasure.restrict_measure_eq] using
      (Measure.restrict_add_restrict_compl hs :
        (μ.measure : Measure X).restrict s +
          (μ.measure : Measure X).restrict sᶜ =
        (μ.measure : Measure X))
  have hdecomp :
      (μ.measure : Measure X) =
        (νs : Measure X) + (νo : Measure X) := by
    have h := congrArg FiniteMeasure.toMeasure hsum
    exact h.symm
  have hνsMeasure :
      (νs : Measure X) =
        νs.mass • (νs.normalize : Measure X) := by
    have h :=
      congrArg FiniteMeasure.toMeasure
        νs.self_eq_mass_smul_normalize
    simpa only [FiniteMeasure.toMeasure_smul] using h
  have hνoMeasure :
      (νo : Measure X) =
        νo.mass • (νo.normalize : Measure X) := by
    have h :=
      congrArg FiniteMeasure.toMeasure
        νo.self_eq_mass_smul_normalize
    simpa only [FiniteMeasure.toMeasure_smul] using h
  have hνsInt : Integrable a (νs : Measure X) :=
    a.integrable _
  have hνoInt : Integrable a (νo : Measure X) :=
    a.integrable _
  have haverage :
      observableAverage a μ.measure =
        (νs.mass : ℝ) *
            observableAverage a νs.normalize +
          (νo.mass : ℝ) *
            observableAverage a νo.normalize := by
    unfold observableAverage
    calc
      (∫ x, a x ∂(μ.measure : Measure X)) =
          ∫ x, a x
            ∂((νs : Measure X) + (νo : Measure X)) := by
              rw [hdecomp]
      _ =
          (∫ x, a x ∂(νs : Measure X)) +
            ∫ x, a x ∂(νo : Measure X) :=
        integral_add_measure hνsInt hνoInt
      _ =
          (νs.mass : ℝ) *
              ∫ x, a x ∂(νs.normalize : Measure X) +
            (νo.mass : ℝ) *
              ∫ x, a x ∂(νo.normalize : Measure X) := by
        rw [hνsMeasure, hνoMeasure]
        simp only [integral_smul_nnreal_measure,
          NNReal.smul_def, smul_eq_mul]
  have hmass :
      (νs.mass : ℝ) + (νo.mass : ℝ) = 1 := by
    have hmassNN : νs.mass + νo.mass = 1 := by
      have htotal :
          (νs + νo).mass = 1 := by
        simpa using congrArg FiniteMeasure.mass hsum
      rw [← htotal]
      unfold FiniteMeasure.mass
      exact
        (congrFun (FiniteMeasure.coeFn_add νs νo)
          Set.univ).symm
    exact_mod_cast hmassNN
  have hweightedS :
      (νs.mass : ℝ) *
          observableAverage a νs.normalize ≤
        (νs.mass : ℝ) * β := by
    by_cases hzero : νs = 0
    · simp [hzero]
    · let μs :=
        normalizeInvariantRestriction
          ϕ μ s hs hsinv
          (by simpa only [νs] using hzero)
      have hmem :
          ∀ᵐ x ∂(μs.measure : Measure X), x ∈ s :=
        ae_mem_normalize_restrict
          μ.measure.toFiniteMeasure hs
          (by simpa only [νs] using hzero)
      have hbound :
          observableAverage a νs.normalize ≤ β := by
        change observableAverage a μs.measure ≤ β
        exact hboundS μs hmem
      exact
        mul_le_mul_of_nonneg_left hbound
          (NNReal.coe_nonneg _)
  have hweightedO :
      (νo.mass : ℝ) *
          observableAverage a νo.normalize ≤
        (νo.mass : ℝ) * β := by
    by_cases hzero : νo = 0
    · simp [hzero]
    · have hcomplInv : IsInvariant ϕ sᶜ :=
        isInvariant_compl_of_flow ϕ hsinv
      let μo :=
        normalizeInvariantRestriction
          ϕ μ sᶜ hs.compl hcomplInv
          (by simpa only [νo] using hzero)
      have hcompl :
          ∀ᵐ x ∂(μo.measure : Measure X), x ∈ sᶜ :=
        ae_mem_normalize_restrict
          μ.measure.toFiniteMeasure hs.compl
          (by simpa only [νo] using hzero)
      have hunionO :
          ∀ᵐ x ∂(μo.measure : Measure X),
            x ∈ s ∨ x ∈ t := by
        change
          ∀ᵐ x ∂
            (((μ.measure.toFiniteMeasure.restrict sᶜ).normalize :
              ProbabilityMeasure X) : Measure X),
            x ∈ s ∨ x ∈ t
        rw [(μ.measure.toFiniteMeasure.restrict sᶜ).toMeasure_normalize_eq_of_nonzero
          (by simpa only [νo] using hzero)]
        exact Measure.ae_smul_measure
          (ae_restrict_of_ae hunion) _
      have htmem :
          ∀ᵐ x ∂(μo.measure : Measure X), x ∈ t := by
        filter_upwards [hcompl, hunionO] with x hxcompl hx
        exact hx.resolve_left hxcompl
      have hbound :
          observableAverage a νo.normalize ≤ β := by
        change observableAverage a μo.measure ≤ β
        exact hboundT μo htmem
      exact
        mul_le_mul_of_nonneg_left hbound
          (NNReal.coe_nonneg _)
  rw [haverage]
  calc
    (νs.mass : ℝ) *
          observableAverage a νs.normalize +
        (νo.mass : ℝ) *
          observableAverage a νo.normalize ≤
        (νs.mass : ℝ) * β +
          (νo.mass : ℝ) * β :=
      add_le_add hweightedS hweightedO
    _ = β := by
      rw [← add_mul, hmass, one_mul]

end

end HGAS.Dynamics
