import HGAS.Dynamics.FlowPointwiseErgodic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

/-!
# Pointwise ergodic theorem for a general invariant flow probability

`FlowPointwiseErgodic` proves the almost-everywhere theorem in the
ergodic case, where the limit is the constant space mean.  The
classification argument for invariant measures also needs the
nonergodic form.  This file proves it for bounded continuous
observables without invoking ergodic decomposition.

Let `F(x) = ∫₀¹ f(ϕₜx) dt` be the unit-block observable.  The mean
ergodic theorem gives an `L²` limit `G` of the Birkhoff averages of
`F`.  There are two elementary ingredients:

* `G` is invariant under every time map, so its Birkhoff averages equal
  `G` almost everywhere;
* `F - G` is in the `L¹` closure of bounded coboundaries.  Indeed,
  `F - AₙF` is an exact coboundary with an explicitly bounded transfer
  function, while `AₙF → G` in `L²`, hence in `L¹`.

The maximal-ergodic Banach principle from `PointwiseErgodic` then shows
that the averages of `F - G` converge almost everywhere to zero.  Adding
the invariant part proves convergence of the full sequence to `G`.

This is a reusable, continuous-flow version of the nonergodic Birkhoff
theorem for bounded continuous real observables.
-/

open Filter Function MeasureTheory Set Topology
open scoped BoundedContinuousFunction

noncomputable section

namespace HGAS.Dynamics

variable {X : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

omit [TopologicalSpace X] [BorelSpace X] in
/-- On a probability space, the `L¹` distance between representatives
of two `L²` vectors is at most their `L²` distance. -/
theorem integral_abs_coe_sub_le_norm_L2
    {μ : Measure X} [IsProbabilityMeasure μ]
    (u v : Lp ℝ 2 μ) :
    (∫ x, |u x - v x| ∂μ) ≤ ‖u - v‖ := by
  have huv_meas :
      AEStronglyMeasurable
        (fun x ↦ u x - v x) μ :=
    (Lp.stronglyMeasurable u).aestronglyMeasurable.sub
      (Lp.stronglyMeasurable v).aestronglyMeasurable
  have huv_mem2 :
      MemLp (fun x ↦ u x - v x) 2 μ :=
    (Lp.memLp u).sub (Lp.memLp v)
  have hcompare :
      eLpNorm (fun x ↦ u x - v x) 1 μ ≤
        eLpNorm (fun x ↦ u x - v x) 2 μ :=
    eLpNorm_le_eLpNorm_of_exponent_le
      (by norm_num) huv_meas
  calc
    (∫ x, |u x - v x| ∂μ) =
        ENNReal.toReal
          (eLpNorm (fun x ↦ u x - v x) 1 μ) := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      simpa only [Real.norm_eq_abs] using
        integral_norm_eq_lintegral_enorm huv_meas
    _ ≤
        ENNReal.toReal
          (eLpNorm (fun x ↦ u x - v x) 2 μ) :=
      ENNReal.toReal_mono huv_mem2.eLpNorm_ne_top hcompare
    _ = ‖u - v‖ := by
      rw [Lp.norm_def]
      congr 1
      exact eLpNorm_congr_ae (Lp.coeFn_sub u v).symm

/-- The bounded continuous integer averages converge in `L¹`, at the
level of chosen representatives, to the mean-ergodic `L²` limit. -/
theorem
    InvariantProbabilityMeasure.tendsto_integral_abs_integerAverage_sub_L2Limit
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (f : X →ᵇ ℝ) :
    Tendsto
      (fun n : ℕ ↦
        ∫ x,
          |integerOrbitAverageObservable ϕ f (n + 1) x -
            μ.integerAverageL2Limit f x|
          ∂(μ.measure : Measure X))
      atTop (𝓝 0) := by
  let U : ℕ → Lp ℝ 2 (μ.measure : Measure X) :=
    fun n ↦
      μ.boundedContinuousToL2
        (integerOrbitAverageObservable ϕ f (n + 1))
  let G : Lp ℝ 2 (μ.measure : Measure X) :=
    μ.integerAverageL2Limit f
  have hL2 : Tendsto U atTop (𝓝 G) := by
    simpa only [U, G] using μ.tendsto_integerAverage_L2 f
  have hnorm :
      Tendsto (fun n ↦ ‖U n - G‖) atTop (𝓝 0) := by
    have hG :
        Tendsto (fun _ : ℕ ↦ G) atTop (𝓝 G) :=
      tendsto_const_nhds
    simpa only [sub_self, norm_zero] using
      (hL2.sub hG).norm
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦
      integral_nonneg fun _ ↦ abs_nonneg _
  · exact Eventually.of_forall fun n ↦ by
      calc
        (∫ x,
            |integerOrbitAverageObservable ϕ f (n + 1) x -
              μ.integerAverageL2Limit f x|
            ∂(μ.measure : Measure X)) =
            ∫ x, |U n x - G x|
              ∂(μ.measure : Measure X) := by
          apply integral_congr_ae
          filter_upwards [
            μ.boundedContinuousToL2_coeFn
              (integerOrbitAverageObservable ϕ f (n + 1))]
            with x hx
          simp only [U, G, hx]
        _ ≤ ‖U n - G‖ :=
          integral_abs_coe_sub_le_norm_L2 (U n) G
  · exact hnorm

/-- The residual between the unit-block observable and the mean-ergodic
limit is an `L¹` limit of coboundaries with bounded transfer functions. -/
theorem
    InvariantProbabilityMeasure.isL1LimitOfBoundedCoboundaries_unitBlock_sub_L2Limit
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (f : X →ᵇ ℝ) :
    IsL1LimitOfBoundedCoboundaries
      (ϕ 1)
      (fun x ↦
        unitBlockObservable ϕ f x -
          μ.integerAverageL2Limit f x)
      (μ.measure : Measure X) := by
  intro ε hε
  have hL1 :=
    μ.tendsto_integral_abs_integerAverage_sub_L2Limit f
  have hevent :
      ∀ᶠ m : ℕ in atTop,
        (∫ x,
          |integerOrbitAverageObservable ϕ f (m + 1) x -
            μ.integerAverageL2Limit f x|
          ∂(μ.measure : Measure X)) < ε :=
    (tendsto_order.mp hL1).2 ε hε
  obtain ⟨m, hm⟩ := eventually_atTop.mp hevent
  let n : ℕ := m + 1
  let F : X → ℝ := unitBlockObservable ϕ f
  let g : X → ℝ :=
    birkhoffCoboundaryTransfer (ϕ 1) F n
  have hFmeas : Measurable F := by
    exact (unitBlockObservable ϕ f).continuous.measurable
  have hFint :
      Integrable F (μ.measure : Measure X) :=
    Integrable.of_bound hFmeas.aestronglyMeasurable
      ‖unitBlockObservable ϕ f‖
      (Eventually.of_forall fun x ↦ by
        simpa only [F, Real.norm_eq_abs] using
          (unitBlockObservable ϕ f).norm_coe_le_norm x)
  have hn : 0 < n := Nat.succ_pos m
  refine
    ⟨g,
      measurable_birkhoffCoboundaryTransfer
        (μ.measurePreservingTime 1).measurable hFmeas n,
      integrable_birkhoffCoboundaryTransfer
        (μ.measurePreservingTime 1) hFint n,
      isBounded_range_birkhoffCoboundaryTransfer
        (ϕ 1) (norm_nonneg (unitBlockObservable ϕ f))
        (fun x ↦ by
          simpa only [F, Real.norm_eq_abs] using
            (unitBlockObservable ϕ f).norm_coe_le_norm x)
        n, ?_⟩
  have hpoint (x : X) :
      (unitBlockObservable ϕ f x -
          μ.integerAverageL2Limit f x) -
        (g (ϕ 1 x) - g x) =
      integerOrbitAverageObservable ϕ f n x -
        μ.integerAverageL2Limit f x := by
    have hcob :=
      birkhoffCoboundaryTransfer_comp_sub
        (ϕ 1) F hn x
    have havg :=
      birkhoffAverage_unitBlockObservable_eq_integerOrbitAverage
        ϕ f n x
    change
      (F x - μ.integerAverageL2Limit f x) -
        (birkhoffCoboundaryTransfer (ϕ 1) F n (ϕ 1 x) -
          birkhoffCoboundaryTransfer (ϕ 1) F n x) =
        integerOrbitAverageObservable ϕ f n x -
          μ.integerAverageL2Limit f x
    rw [hcob, havg]
    ring
  have havg := hm m (le_refl m)
  simpa only [hpoint, n] using havg

omit [TopologicalSpace X] [BorelSpace X] in
/-- Pairing an arbitrary real `L²` vector with the constant-one vector
is integration of its chosen representative. -/
theorem inner_L2_const_one_eq_integral
    {μ : Measure X} [IsProbabilityMeasure μ]
    (g : Lp ℝ 2 μ) :
    inner ℝ g (Lp.const (2 : ENNReal) μ (1 : ℝ)) =
      ∫ x, g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    Lp.coeFn_const (2 : ENNReal) μ (1 : ℝ)]
    with x hx
  rw [hx, RCLike.inner_apply]
  simp

/-- The integral of the mean-ergodic limit is the integral of the
original bounded continuous observable. -/
theorem
    InvariantProbabilityMeasure.integral_integerAverageL2Limit
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (f : X →ᵇ ℝ) :
    (∫ x, μ.integerAverageL2Limit f x
        ∂(μ.measure : Measure X)) =
      ∫ x, f x ∂(μ.measure : Measure X) := by
  have hL2 := μ.tendsto_integerAverage_L2 f
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
          (μ.integerAverageL2Limit f)
          (Lp.const (2 : ENNReal)
            (μ.measure : Measure X) (1 : ℝ)))) :=
    hL2.inner
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
        atTop
        (𝓝 (∫ x, μ.integerAverageL2Limit f x
          ∂(μ.measure : Measure X))) := by
    simpa only [
      μ.inner_boundedContinuousToL2_const_one,
      μ.integral_integerOrbitAverageObservable f
        (Nat.succ_pos _),
      inner_L2_const_one_eq_integral] using hinner
  exact
    (tendsto_nhds_unique tendsto_const_nhds hscalar).symm

/-- **Nonergodic pointwise ergodic theorem for continuous flows.**

For every invariant probability and every bounded continuous real
observable, the full sequence of positive integer orbit averages
converges almost everywhere to the representative of the mean-ergodic
`L²` projection. -/
theorem
    InvariantProbabilityMeasure.ae_tendsto_integerOrbitAverage_L2Limit
    {ϕ : Flow ℝ X}
    (μ : InvariantProbabilityMeasure ϕ)
    (f : X →ᵇ ℝ) :
    ∀ᵐ x ∂(μ.measure : Measure X),
      Tendsto
        (fun n : ℕ ↦
          integerOrbitAverageObservable ϕ f (n + 1) x)
        atTop
        (𝓝 (μ.integerAverageL2Limit f x)) := by
  let G : Lp ℝ 2 (μ.measure : Measure X) :=
    μ.integerAverageL2Limit f
  let F : X → ℝ := unitBlockObservable ϕ f
  let r : X → ℝ := fun x ↦ F x - G x
  have hGmeas : Measurable (G : X → ℝ) :=
    (Lp.stronglyMeasurable G).measurable
  have hGint : Integrable (G : X → ℝ)
      (μ.measure : Measure X) :=
    (Lp.memLp G).integrable (by norm_num)
  have hFmeas : Measurable F :=
    (unitBlockObservable ϕ f).continuous.measurable
  have hFint : Integrable F (μ.measure : Measure X) :=
    Integrable.of_bound hFmeas.aestronglyMeasurable
      ‖unitBlockObservable ϕ f‖
      (Eventually.of_forall fun x ↦ by
        simpa only [F, Real.norm_eq_abs] using
          (unitBlockObservable ϕ f).norm_coe_le_norm x)
  have hrmeas : Measurable r :=
    hFmeas.sub hGmeas
  have hrint : Integrable r (μ.measure : Measure X) :=
    hFint.sub hGint
  have hrzero :
      ∀ᵐ x ∂(μ.measure : Measure X),
        Tendsto
          (fun n ↦ birkhoffAverage ℝ (ϕ 1) r n x)
          atTop (𝓝 0) := by
    apply
      ae_tendsto_birkhoffAverage_zero_of_L1Limit_boundedCoboundaries
        (μ.measurePreservingTime 1)
        hrmeas hrint
    simpa only [r, F, G] using
      μ.isL1LimitOfBoundedCoboundaries_unitBlock_sub_L2Limit f
  have hGiterate (k : ℕ) :
      (fun x ↦ G ((ϕ 1)^[k] x)) =ᵐ[
          (μ.measure : Measure X)] (G : X → ℝ) := by
    have hcomp :=
      Lp.coeFn_compMeasurePreserving G
        (μ.measurePreservingTime (k : ℝ))
    have hinv :=
      μ.koopmanL2_integerAverageL2Limit f (k : ℝ)
    change
      Lp.compMeasurePreserving (ϕ (k : ℝ))
          (μ.measurePreservingTime (k : ℝ)) G =
        G at hinv
    have hflow :
        (fun x ↦ (ϕ 1)^[k] x) =
          (fun x ↦ ϕ (k : ℝ) x) := by
      funext x
      exact iterate_flow_one ϕ k x
    simpa only [iterate_flow_one] using
      hcomp.symm.trans (by rw [hinv])
  have hGiterateAll :
      ∀ᵐ x ∂(μ.measure : Measure X), ∀ k : ℕ,
        G ((ϕ 1)^[k] x) = G x :=
    ae_all_iff.mpr hGiterate
  filter_upwards [hrzero, hGiterateAll] with x hxzero hxG
  have hGaverage (n : ℕ) (hn : 0 < n) :
      birkhoffAverage ℝ (ϕ 1) (G : X → ℝ) n x =
        G x := by
    unfold birkhoffAverage birkhoffSum
    simp_rw [hxG]
    simp [Nat.ne_of_gt hn]
  have hdecomp (n : ℕ) (hn : 0 < n) :
      integerOrbitAverageObservable ϕ f n x =
        birkhoffAverage ℝ (ϕ 1) r n x + G x := by
    rw [← birkhoffAverage_unitBlockObservable_eq_integerOrbitAverage
      ϕ f n x]
    have hF : F = r + (G : X → ℝ) := by
      funext y
      change F y = (F y - G y) + G y
      ring
    change
      birkhoffAverage ℝ (ϕ 1) F n x =
        birkhoffAverage ℝ (ϕ 1) r n x + G x
    rw [hF]
    have hadd :
        birkhoffAverage ℝ (ϕ 1)
            (r + (G : X → ℝ)) n x =
          birkhoffAverage ℝ (ϕ 1) r n x +
            birkhoffAverage ℝ (ϕ 1) (G : X → ℝ) n x :=
      congrFun (congrFun (birkhoffAverage_add (R := ℝ)) n) x
    rw [hadd, hGaverage n hn]
  have hxzero' :=
    hxzero.comp (tendsto_add_atTop_nat 1)
  have hxadd := hxzero'.add_const (G x)
  have hxadd' :
      Tendsto
        (fun n ↦
          birkhoffAverage ℝ (ϕ 1) r (n + 1) x + G x)
        atTop (𝓝 (G x)) := by
    simpa only [Function.comp_apply, zero_add] using hxadd
  exact hxadd'.congr fun n ↦
    (hdecomp (n + 1) (Nat.succ_pos n)).symm

end HGAS.Dynamics
