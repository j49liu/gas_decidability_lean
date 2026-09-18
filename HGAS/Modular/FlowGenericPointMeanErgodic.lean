import HGAS.Dynamics.ErgodicInvariantProbability
import HGAS.Dynamics.TimeAverages
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# Mean-ergodic infrastructure for generic points of real flows

This module develops the Hilbert-space part of the generic-point argument
for a continuous real flow.  The key device is to replace an observable
`f` by its one-unit block integral

```text
                   g(x) = ∫₀¹ f(ϕₜ x) dt.
```

The continuous-time average of `f` over an integer interval is then the
ordinary Birkhoff average of `g` for the time-one map.  This permits use of
Mathlib's von Neumann mean ergodic theorem without assuming that the
time-one map is itself ergodic.

The definitions and elementary identities are independent of the modular
quotient and are intended to be reusable.
-/

namespace HGAS.Dynamics

open Filter Function _root_.MeasureTheory Set Topology
open scoped BoundedContinuousFunction

noncomputable section

variable {X : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

/-- An invariant probability makes each time map measure-preserving as an
ordinary measure map. -/
def InvariantProbabilityMeasure.measurePreservingTime
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ) (t : ℝ) :
    MeasurePreserving (ϕ t)
      (μ.measure : Measure X) (μ.measure : Measure X) where
  measurable := (ϕ.continuous_toFun t).measurable
  map_eq := μ.map_time_toMeasure t

/-- The integral of an observable over one unit of flow time, bundled as
a bounded continuous observable. -/
def unitBlockObservable
    (ϕ : Flow ℝ X) (f : X →ᵇ ℝ) : X →ᵇ ℝ where
  toFun := orbitIntegral ϕ f 1
  continuous_toFun := continuous_orbitIntegral ϕ f 1
  map_bounded' := by
    refine ⟨2 * ‖f‖, fun x y ↦ ?_⟩
    rw [Real.dist_eq]
    calc
      |orbitIntegral ϕ f 1 x -
          orbitIntegral ϕ f 1 y| ≤
          |orbitIntegral ϕ f 1 x| +
            |orbitIntegral ϕ f 1 y| :=
        abs_sub _ _
      _ ≤ ‖f‖ + ‖f‖ := by
        gcongr
        · simpa only [Real.norm_eq_abs, abs_one, mul_one] using
            norm_orbitIntegral_le ϕ f 1 x
        · simpa only [Real.norm_eq_abs, abs_one, mul_one] using
            norm_orbitIntegral_le ϕ f 1 y
      _ = 2 * ‖f‖ := by ring

omit [MeasurableSpace X] [BorelSpace X] in
@[simp]
theorem unitBlockObservable_apply
    (ϕ : Flow ℝ X) (f : X →ᵇ ℝ) (x : X) :
    unitBlockObservable ϕ f x =
      orbitIntegral ϕ f 1 x :=
  rfl

omit [MeasurableSpace X] [BorelSpace X] in
/-- Iterating the time-one map is the same as flowing for the
corresponding natural-number time. -/
theorem iterate_flow_one
    (ϕ : Flow ℝ X) (n : ℕ) (x : X) :
    (ϕ 1)^[n] x = ϕ (n : ℝ) x := by
  induction n with
  | zero =>
      simp only [iterate_zero_apply, Nat.cast_zero,
        ϕ.map_zero_apply]
  | succ n ih =>
      rw [iterate_succ_apply', ih, ← ϕ.map_add]
      congr 1
      norm_num [add_comm]

omit [MeasurableSpace X] [BorelSpace X] in
/-- An integer-time orbit integral is the sum of the one-unit block
observable along the time-one orbit. -/
theorem orbitIntegral_nat_eq_birkhoffSum_unitBlock
    (ϕ : Flow ℝ X) (f : X →ᵇ ℝ)
    (n : ℕ) (x : X) :
    orbitIntegral ϕ f (n : ℝ) x =
      birkhoffSum (ϕ 1) (unitBlockObservable ϕ f) n x := by
  induction n with
  | zero =>
      simp [orbitIntegral, birkhoffSum]
  | succ n ih =>
      rw [show (n.succ : ℝ) = (n + 1 : ℕ) * (1 : ℝ) by
        norm_num]
      rw [orbitIntegral_natSucc_mul]
      simp only [mul_one]
      rw [ih]
      simp only [birkhoffSum_succ, unitBlockObservable_apply]
      rw [iterate_flow_one]

omit [MeasurableSpace X] [BorelSpace X] in
/-- The normalized continuous-time average over an integer interval is
the Birkhoff average of the unit-block observable. -/
theorem orbitIntegral_nat_average_eq_birkhoffAverage
    (ϕ : Flow ℝ X) (f : X →ᵇ ℝ)
    (n : ℕ) (x : X) :
    (n : ℝ)⁻¹ * orbitIntegral ϕ f (n : ℝ) x =
      birkhoffAverage ℝ (ϕ 1)
        (unitBlockObservable ϕ f) n x := by
  rw [orbitIntegral_nat_eq_birkhoffSum_unitBlock]
  rfl

omit [MeasurableSpace X] [BorelSpace X] in
/-- Shifting the initial point by time `s` changes an orbit integral over
time `T` only by the two boundary pieces of length `s`. -/
theorem orbitIntegral_flow_sub
    (ϕ : Flow ℝ X) (f : X →ᵇ ℝ)
    (T s : ℝ) (x : X) :
    orbitIntegral ϕ f T (ϕ s x) -
        orbitIntegral ϕ f T x =
      orbitIntegral ϕ f s (ϕ T x) -
        orbitIntegral ϕ f s x := by
  have hst := orbitIntegral_add ϕ f s T x
  have hts := orbitIntegral_add ϕ f T s x
  rw [add_comm s T] at hst
  linarith

/-- The Koopman isometry on real `L²` induced by a time map of an
invariant flow probability. -/
def InvariantProbabilityMeasure.koopmanL2
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ) (t : ℝ) :
    Lp ℝ 2 (μ.measure : Measure X) →ₗᵢ[ℝ]
      Lp ℝ 2 (μ.measure : Measure X) :=
  Lp.compMeasurePreservingₗᵢ ℝ (ϕ t)
    (μ.measurePreservingTime t)

/-- The `L²` vector represented by a bounded continuous observable. -/
def InvariantProbabilityMeasure.boundedContinuousToL2
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (f : X →ᵇ ℝ) :
    Lp ℝ 2 (μ.measure : Measure X) :=
  (BoundedContinuousFunction.toLp 2
    (μ.measure : Measure X) ℝ) f

theorem InvariantProbabilityMeasure.boundedContinuousToL2_coeFn
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (f : X →ᵇ ℝ) :
    (μ.boundedContinuousToL2 f : X → ℝ) =ᵐ[
        (μ.measure : Measure X)] f :=
  BoundedContinuousFunction.coeFn_toLp
    2 (μ.measure : Measure X) ℝ f

/-- For a probability measure, passage from the supremum norm to `L²`
has operator norm at most one. -/
theorem InvariantProbabilityMeasure.norm_boundedContinuousToL2_le
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (f : X →ᵇ ℝ) :
    ‖μ.boundedContinuousToL2 f‖ ≤ ‖f‖ := by
  have h :=
    BoundedContinuousFunction.Lp_norm_le
      (p := (2 : ENNReal))
      (μ := (μ.measure : Measure X)) f
  change
    ‖μ.boundedContinuousToL2 f‖ ≤
      measureUnivNNReal (μ.measure : Measure X) ^
        (2 : ENNReal).toReal⁻¹ * ‖f‖ at h
  simpa [measureUnivNNReal] using h

/-- Composition of a bounded continuous observable by a time map. -/
def timeComposedBoundedContinuous
    (ϕ : Flow ℝ X) (t : ℝ) (f : X →ᵇ ℝ) :
    X →ᵇ ℝ :=
  f.compContinuous ⟨ϕ t, ϕ.continuous_toFun t⟩

omit [MeasurableSpace X] [BorelSpace X] in
@[simp]
theorem timeComposedBoundedContinuous_apply
    (ϕ : Flow ℝ X) (t : ℝ) (f : X →ᵇ ℝ) (x : X) :
    timeComposedBoundedContinuous ϕ t f x =
      f (ϕ t x) :=
  rfl

omit [MeasurableSpace X] [BorelSpace X] in
/-- Iterating composition by the time-one map composes with the
corresponding integer-time map. -/
theorem iterate_timeComposed_one_apply
    (ϕ : Flow ℝ X) (f : X →ᵇ ℝ) (n : ℕ) (x : X) :
    (timeComposedBoundedContinuous ϕ 1)^[n] f x =
      f (ϕ (n : ℝ) x) := by
  induction n generalizing x with
  | zero =>
      simp only [iterate_zero_apply, Nat.cast_zero, ϕ.map_zero_apply]
  | succ n ih =>
      rw [iterate_succ_apply', timeComposedBoundedContinuous_apply, ih,
        ← ϕ.map_add]
      congr 1
      norm_num [add_comm]

/-- The integer-time continuous orbit average, bundled as a bounded
continuous function.  The construction uses one-unit blocks, so no
compactness hypothesis on the phase space is needed. -/
def integerOrbitAverageObservable
    (ϕ : Flow ℝ X) (f : X →ᵇ ℝ) (n : ℕ) :
    X →ᵇ ℝ :=
  birkhoffAverage ℝ
    (timeComposedBoundedContinuous ϕ 1) _root_.id n
    (unitBlockObservable ϕ f)

omit [MeasurableSpace X] [BorelSpace X] in
/-- Pointwise, the bundled integer-time average is the normalized orbit
integral. -/
theorem integerOrbitAverageObservable_apply
    (ϕ : Flow ℝ X) (f : X →ᵇ ℝ) (n : ℕ) (x : X) :
    integerOrbitAverageObservable ϕ f n x =
      (n : ℝ)⁻¹ * orbitIntegral ϕ f (n : ℝ) x := by
  rw [orbitIntegral_nat_average_eq_birkhoffAverage]
  simp [integerOrbitAverageObservable, birkhoffAverage,
    birkhoffSum, iterate_timeComposed_one_apply,
    iterate_flow_one]

omit [MeasurableSpace X] [BorelSpace X] in
/-- Uniform boundary-term estimate for translating an integer orbit
average by an arbitrary flow time. -/
theorem norm_timeComposed_integerOrbitAverage_sub_le
    (ϕ : Flow ℝ X) (f : X →ᵇ ℝ)
    {n : ℕ} (hn : 0 < n) (s : ℝ) :
    ‖timeComposedBoundedContinuous ϕ s
          (integerOrbitAverageObservable ϕ f n) -
        integerOrbitAverageObservable ϕ f n‖ ≤
      (n : ℝ)⁻¹ * (2 * ‖f‖ * |s|) := by
  rw [BoundedContinuousFunction.norm_le]
  · intro x
    change
      |integerOrbitAverageObservable ϕ f n (ϕ s x) -
          integerOrbitAverageObservable ϕ f n x| ≤
        (n : ℝ)⁻¹ * (2 * ‖f‖ * |s|)
    rw [integerOrbitAverageObservable_apply,
      integerOrbitAverageObservable_apply]
    rw [← mul_sub, orbitIntegral_flow_sub]
    calc
      |(n : ℝ)⁻¹ *
          (orbitIntegral ϕ f s (ϕ (n : ℝ) x) -
            orbitIntegral ϕ f s x)| =
          (n : ℝ)⁻¹ *
            |orbitIntegral ϕ f s (ϕ (n : ℝ) x) -
              orbitIntegral ϕ f s x| := by
                rw [abs_mul, abs_of_nonneg]
                positivity
      _ ≤ (n : ℝ)⁻¹ *
          (|orbitIntegral ϕ f s (ϕ (n : ℝ) x)| +
            |orbitIntegral ϕ f s x|) := by
              gcongr
              exact abs_sub _ _
      _ ≤ (n : ℝ)⁻¹ * (‖f‖ * |s| + ‖f‖ * |s|) := by
              gcongr
              · simpa only [Real.norm_eq_abs] using
                  norm_orbitIntegral_le ϕ f s
                    (ϕ (n : ℝ) x)
              · simpa only [Real.norm_eq_abs] using
                  norm_orbitIntegral_le ϕ f s x
      _ = (n : ℝ)⁻¹ * (2 * ‖f‖ * |s|) := by ring
  · positivity

/-- Koopman composition of a bounded continuous observable agrees in
`L²` with its bounded-continuous time composition. -/
theorem InvariantProbabilityMeasure.koopmanL2_boundedContinuous
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (t : ℝ) (f : X →ᵇ ℝ) :
    (μ.koopmanL2 t) (μ.boundedContinuousToL2 f) =
      μ.boundedContinuousToL2
        (timeComposedBoundedContinuous ϕ t f) := by
  apply Lp.ext
  have hleft :=
    Lp.coeFn_compMeasurePreserving
      (μ.boundedContinuousToL2 f)
      (μ.measurePreservingTime t)
  have hmiddle :=
    (μ.measurePreservingTime t).quasiMeasurePreserving.ae_eq_comp
      (μ.boundedContinuousToL2_coeFn f)
  have hright :=
    μ.boundedContinuousToL2_coeFn
      (timeComposedBoundedContinuous ϕ t f)
  exact hleft.trans <| by
    simpa only [Function.comp_apply,
      timeComposedBoundedContinuous_apply] using
        hmiddle.trans hright.symm

/-- The Hilbert-space Birkhoff average for the time-one Koopman operator
is represented by the bounded continuous integer orbit average. -/
theorem InvariantProbabilityMeasure.birkhoffAverage_koopmanL2_eq
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (f : X →ᵇ ℝ) (n : ℕ) :
    birkhoffAverage ℝ (μ.koopmanL2 1) _root_.id n
        (μ.boundedContinuousToL2 (unitBlockObservable ϕ f)) =
      μ.boundedContinuousToL2
        (integerOrbitAverageObservable ϕ f n) := by
  unfold integerOrbitAverageObservable birkhoffAverage birkhoffSum
  unfold InvariantProbabilityMeasure.boundedContinuousToL2
  rw [map_inv_natCast_smul
    (BoundedContinuousFunction.toLp 2
      (μ.measure : Measure X) ℝ) ℝ ℝ]
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [id_eq]
  induction k with
  | zero =>
      simp only [iterate_zero_apply]
  | succ k ih =>
      have hk' : k ∈ Finset.range n :=
        Finset.mem_range.mpr <|
          Nat.lt_of_succ_lt (Finset.mem_range.mp hk)
      rw [iterate_succ_apply', iterate_succ_apply', ih hk']
      exact
        μ.koopmanL2_boundedContinuous 1
          ((timeComposedBoundedContinuous ϕ 1)^[k]
            (unitBlockObservable ϕ f))

/-- The `L²` norm of the change in an integer orbit average under any
fixed flow time is controlled by the same elementary boundary term as
the supremum norm. -/
theorem InvariantProbabilityMeasure.norm_koopmanL2_integerAverage_sub_le
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (f : X →ᵇ ℝ) {n : ℕ} (hn : 0 < n) (s : ℝ) :
    ‖(μ.koopmanL2 s)
          (μ.boundedContinuousToL2
            (integerOrbitAverageObservable ϕ f n)) -
        μ.boundedContinuousToL2
          (integerOrbitAverageObservable ϕ f n)‖ ≤
      (n : ℝ)⁻¹ * (2 * ‖f‖ * |s|) := by
  rw [μ.koopmanL2_boundedContinuous]
  unfold InvariantProbabilityMeasure.boundedContinuousToL2
  rw [← map_sub]
  exact
    (μ.norm_boundedContinuousToL2_le _).trans
      (norm_timeComposed_integerOrbitAverage_sub_le
        ϕ f hn s)

/-- The Hilbert-space limit supplied by the mean ergodic theorem for
integer continuous-time averages. -/
def InvariantProbabilityMeasure.integerAverageL2Limit
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (f : X →ᵇ ℝ) :
    Lp ℝ 2 (μ.measure : Measure X) :=
  ((LinearMap.eqLocus
      (μ.koopmanL2 1).toContinuousLinearMap 1).orthogonalProjection
        (μ.boundedContinuousToL2
          (unitBlockObservable ϕ f)) :
      LinearMap.eqLocus
        (μ.koopmanL2 1).toContinuousLinearMap 1)

/-- Von Neumann's theorem gives `L²` convergence of the positive integer
continuous-time averages to `integerAverageL2Limit`. -/
theorem InvariantProbabilityMeasure.tendsto_integerAverage_L2
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (f : X →ᵇ ℝ) :
    Tendsto
      (fun n : ℕ ↦
        μ.boundedContinuousToL2
          (integerOrbitAverageObservable ϕ f (n + 1)))
      atTop (𝓝 (μ.integerAverageL2Limit f)) := by
  have h :=
    ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection
      (μ.koopmanL2 1).toContinuousLinearMap
      (LinearIsometry.norm_toContinuousLinearMap_le
        (μ.koopmanL2 1))
      (μ.boundedContinuousToL2
        (unitBlockObservable ϕ f))
  have h' := h.comp (tendsto_add_atTop_nat 1)
  change
    Tendsto
      ((fun n : ℕ ↦
          birkhoffAverage ℝ (μ.koopmanL2 1) _root_.id n
            (μ.boundedContinuousToL2
              (unitBlockObservable ϕ f))) ∘
        fun n : ℕ ↦ n + 1)
      atTop (𝓝 (μ.integerAverageL2Limit f)) at h'
  exact h'.congr fun n ↦
    μ.birkhoffAverage_koopmanL2_eq f (n + 1)

/-- Although the mean-ergodic theorem was applied to the time-one map,
its limit is invariant under every time map of the original flow.  This
is where the boundary-term estimate recovers the full real action. -/
theorem InvariantProbabilityMeasure.koopmanL2_integerAverageL2Limit
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (f : X →ᵇ ℝ) (s : ℝ) :
    (μ.koopmanL2 s) (μ.integerAverageL2Limit f) =
      μ.integerAverageL2Limit f := by
  let A : ℕ → Lp ℝ 2 (μ.measure : Measure X) :=
    fun n ↦ μ.boundedContinuousToL2
      (integerOrbitAverageObservable ϕ f (n + 1))
  have hA :
      Tendsto A atTop (𝓝 (μ.integerAverageL2Limit f)) := by
    simpa only [A] using μ.tendsto_integerAverage_L2 f
  have hmap :
      Tendsto (fun n ↦ (μ.koopmanL2 s) (A n))
        atTop
        (𝓝 ((μ.koopmanL2 s)
          (μ.integerAverageL2Limit f))) :=
    ((μ.koopmanL2 s).continuous.tendsto
      (μ.integerAverageL2Limit f)).comp hA
  have hsub :
      Tendsto
        (fun n ↦ (μ.koopmanL2 s) (A n) - A n)
        atTop
        (𝓝 ((μ.koopmanL2 s)
          (μ.integerAverageL2Limit f) -
            μ.integerAverageL2Limit f)) :=
    hmap.sub hA
  have hnorm :
      Tendsto
        (fun n ↦ ‖(μ.koopmanL2 s) (A n) - A n‖)
        atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦ norm_nonneg _
    · exact Eventually.of_forall fun n ↦ by
        simpa only [A] using
          μ.norm_koopmanL2_integerAverage_sub_le
            f (Nat.succ_pos n) s
    · have hinv :
          Tendsto
            (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹)
            atTop (𝓝 0) := by
            simpa only [Function.comp_apply] using
              ((tendsto_inv_atTop_nhds_zero_nat
                (𝕜 := ℝ)).comp
                  (tendsto_add_atTop_nat 1))
      simpa only [zero_mul] using
        hinv.mul_const (2 * ‖f‖ * |s|)
  have hzero :
      Tendsto
        (fun n ↦ (μ.koopmanL2 s) (A n) - A n)
        atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  exact sub_eq_zero.mp <| tendsto_nhds_unique hsub hzero

/-- An `L²` function invariant under every Koopman time of an ergodic
real flow is almost everywhere constant.

This is the unbundled-flow counterpart of Mathlib's corresponding lemma
for a single ergodic transformation.  The proof applies the flow
zero--one law to the inverse image of each measurable set in a countable
separating family for `ℝ`. -/
theorem IsErgodicInvariantProbability.ae_eq_const_of_koopmanL2_invariant
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (hμ : IsErgodicInvariantProbability ϕ μ.measure)
    (g : Lp ℝ 2 (μ.measure : Measure X))
    (hinv :
      ∀ s : ℝ,
        (μ.koopmanL2 s) g = g) :
    ∃ c : ℝ,
      (g : X → ℝ) =ᵐ[(μ.measure : Measure X)]
        Function.const X c := by
  refine
    exists_eventuallyEq_const_of_forall_separating
      MeasurableSet ?_
  intro U hU
  have hgmeas : Measurable (g : X → ℝ) :=
    (Lp.stronglyMeasurable g).measurable
  have hpremeas :
      MeasurableSet ((g : X → ℝ) ⁻¹' U) :=
    hU.preimage hgmeas
  have hginv :
      ∀ s : ℝ,
        (g : X → ℝ) ∘ ϕ s =ᵐ[(μ.measure : Measure X)]
          (g : X → ℝ) := by
    intro s
    have hcomp :=
      Lp.coeFn_compMeasurePreserving g
        (μ.measurePreservingTime s)
    have hop := hinv s
    change
      (Lp.compMeasurePreserving (ϕ s)
        (μ.measurePreservingTime s)) g = g at hop
    exact hcomp.symm.trans <| by rw [hop]
  have hpreinv :
      ∀ s : ℝ,
        (ϕ s) ⁻¹' ((g : X → ℝ) ⁻¹' U) =ᵐ[
            (μ.measure : Measure X)]
          ((g : X → ℝ) ⁻¹' U) := by
    intro s
    have hmem := (hginv s).mono (fun x hx ↦ by
      simp only [Function.comp_apply] at hx
      change (g (ϕ s x) ∈ U ↔ g x ∈ U)
      rw [hx])
    exact hmem.set_eq
  rcases hμ.zero_or_one hpremeas hpreinv with hzero | hone
  · right
    rw [ae_iff]
    simpa only [mem_preimage, mem_setOf_eq, not_not] using hzero
  · left
    rw [ae_iff]
    have hcompl :
        (μ.measure : Measure X)
          (((g : X → ℝ) ⁻¹' U)ᶜ) = 0 := by
      rw [measure_compl hpremeas (measure_ne_top _ _), hone]
      norm_num
    simpa only [compl_setOf, mem_preimage, mem_setOf_eq] using hcompl

/-- Pairing a bounded continuous `L²` vector with the constant-one vector
recovers its ordinary integral. -/
theorem InvariantProbabilityMeasure.inner_boundedContinuousToL2_const_one
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (f : X →ᵇ ℝ) :
    inner ℝ
        (μ.boundedContinuousToL2 f)
        (Lp.const (2 : ENNReal)
          (μ.measure : Measure X) (1 : ℝ)) =
      ∫ x, f x ∂(μ.measure : Measure X) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [μ.boundedContinuousToL2_coeFn f,
      Lp.coeFn_const (2 : ENNReal)
        (μ.measure : Measure X) (1 : ℝ)]
      with x hfx hone
  calc
    inner ℝ
        ((μ.boundedContinuousToL2 f : X → ℝ) x)
        (((Lp.const (2 : ENNReal)
          (μ.measure : Measure X) (1 : ℝ)) :
            X → ℝ) x) =
      inner ℝ (f x) 1 := by
        rw [hfx, hone]
        rfl
    _ = f x := by rw [RCLike.inner_apply]; simp

/-- The space integral of every positive integer orbit average equals the
space integral of the original observable. -/
theorem InvariantProbabilityMeasure.integral_integerOrbitAverageObservable
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (f : X →ᵇ ℝ) {n : ℕ} (hn : 0 < n) :
    (∫ x, integerOrbitAverageObservable ϕ f n x
        ∂(μ.measure : Measure X)) =
      ∫ x, f x ∂(μ.measure : Measure X) := by
  simp_rw [integerOrbitAverageObservable_apply]
  rw [integral_const_mul,
    integral_orbitIntegral_eq ϕ f μ (n : ℝ)]
  field_simp

/-- On a probability space, the `L²` pairing of constants `c` and `1`
is `c`. -/
theorem InvariantProbabilityMeasure.inner_const_const_one
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ) (c : ℝ) :
    inner ℝ
        (Lp.const (2 : ENNReal)
          (μ.measure : Measure X) c)
        (Lp.const (2 : ENNReal)
          (μ.measure : Measure X) (1 : ℝ)) =
      c := by
  rw [L2.inner_def]
  calc
    (∫ x,
        inner ℝ
          (((Lp.const (2 : ENNReal)
            (μ.measure : Measure X) c) : X → ℝ) x)
          (((Lp.const (2 : ENNReal)
            (μ.measure : Measure X) (1 : ℝ)) :
              X → ℝ) x)
        ∂(μ.measure : Measure X)) =
      ∫ _ : X, c ∂(μ.measure : Measure X) := by
        apply integral_congr_ae
        filter_upwards
          [Lp.coeFn_const (2 : ENNReal)
              (μ.measure : Measure X) c,
            Lp.coeFn_const (2 : ENNReal)
              (μ.measure : Measure X) (1 : ℝ)]
            with x hc hone
        rw [hc, hone, RCLike.inner_apply]
        simp
    _ = c := by simp

/-- **Continuous-time mean ergodic theorem for an ergodic probability.**

For every bounded continuous observable, its positive integer orbit
averages converge in `L²` to the constant equal to its space average.
No ergodicity of the time-one map is assumed or needed. -/
theorem IsErgodicInvariantProbability.tendsto_integerAverage_L2
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (hμ : IsErgodicInvariantProbability ϕ μ.measure)
    (f : X →ᵇ ℝ) :
    Tendsto
      (fun n : ℕ ↦
        μ.boundedContinuousToL2
          (integerOrbitAverageObservable ϕ f (n + 1)))
      atTop
      (𝓝 (Lp.const (2 : ENNReal)
        (μ.measure : Measure X)
        (∫ x, f x ∂(μ.measure : Measure X)))) := by
  obtain ⟨c, hc⟩ :=
    hμ.ae_eq_const_of_koopmanL2_invariant
      μ (μ.integerAverageL2Limit f)
        (μ.koopmanL2_integerAverageL2Limit f)
  have hconst :
      μ.integerAverageL2Limit f =
        Lp.const (2 : ENNReal)
          (μ.measure : Measure X) c := by
    apply Lp.ext
    exact hc.trans <|
      (Lp.coeFn_const (2 : ENNReal)
        (μ.measure : Measure X) c).symm
  have hA := μ.tendsto_integerAverage_L2 f
  rw [hconst] at hA
  have hinner :
      Tendsto
        (fun n : ℕ ↦
          inner ℝ
            (μ.boundedContinuousToL2
              (integerOrbitAverageObservable ϕ f (n + 1)))
            (Lp.const (2 : ENNReal)
              (μ.measure : Measure X) (1 : ℝ)))
        atTop
        (𝓝 (inner ℝ
          (Lp.const (2 : ENNReal)
            (μ.measure : Measure X) c)
          (Lp.const (2 : ENNReal)
            (μ.measure : Measure X) (1 : ℝ)))) :=
    hA.inner
      (tendsto_const_nhds :
        Tendsto
          (fun _ : ℕ ↦
            Lp.const (2 : ENNReal)
              (μ.measure : Measure X) (1 : ℝ))
          atTop
          (𝓝 (Lp.const (2 : ENNReal)
            (μ.measure : Measure X) (1 : ℝ))))
  have hscalar :
      Tendsto
        (fun _ : ℕ ↦
          ∫ x, f x ∂(μ.measure : Measure X))
        atTop (𝓝 c) := by
    simpa only
      [μ.inner_boundedContinuousToL2_const_one,
        μ.integral_integerOrbitAverageObservable f
          (Nat.succ_pos _),
        μ.inner_const_const_one] using hinner
  have hc_eq :
      (∫ x, f x ∂(μ.measure : Measure X)) = c :=
    tendsto_nhds_unique tendsto_const_nhds hscalar
  simpa only [hc_eq] using hA

/-- Every bounded continuous observable admits a subsequence of positive
integer orbit averages which converges almost everywhere to its space
average under an ergodic invariant probability. -/
theorem IsErgodicInvariantProbability.exists_subsequence_ae_tendsto_integerAverage
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (hμ : IsErgodicInvariantProbability ϕ μ.measure)
    (f : X →ᵇ ℝ) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂(μ.measure : Measure X),
        Tendsto
          (fun i : ℕ ↦
            integerOrbitAverageObservable ϕ f (ns i + 1) x)
          atTop
          (𝓝 (∫ y, f y ∂(μ.measure : Measure X))) := by
  let c : ℝ := ∫ y, f y ∂(μ.measure : Measure X)
  let F : ℕ → Lp ℝ 2 (μ.measure : Measure X) :=
    fun n ↦ μ.boundedContinuousToL2
      (integerOrbitAverageObservable ϕ f (n + 1))
  let C : Lp ℝ 2 (μ.measure : Measure X) :=
    Lp.const (2 : ENNReal) (μ.measure : Measure X) c
  have hL2 : Tendsto F atTop (𝓝 C) := by
    simpa only [F, C, c] using hμ.tendsto_integerAverage_L2 μ f
  obtain ⟨ns, hns, hpoint⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hL2).exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  have hrepresentatives :
      ∀ᵐ x ∂(μ.measure : Measure X), ∀ i : ℕ,
        (F (ns i) : X → ℝ) x =
          integerOrbitAverageObservable ϕ f (ns i + 1) x :=
    ae_all_iff.mpr fun i ↦
      μ.boundedContinuousToL2_coeFn
        (integerOrbitAverageObservable ϕ f (ns i + 1))
  have hconstant :
      ∀ᵐ x ∂(μ.measure : Measure X),
        (C : X → ℝ) x = c := by
    simpa only [C, c, Function.const_apply] using
      Lp.coeFn_const (2 : ENNReal)
        (μ.measure : Measure X) c
  filter_upwards [hpoint, hrepresentatives, hconstant]
    with x hxpoint hxrepresentatives hxconstant
  have h :=
    hxpoint.congr'
      (Eventually.of_forall fun i ↦ hxrepresentatives i)
  simpa only [hxconstant, c] using h

end

end HGAS.Dynamics
