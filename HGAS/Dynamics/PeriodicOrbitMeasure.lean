import HGAS.Dynamics.TimeAverages
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic

/-!
# Canonical invariant probability on a periodic orbit

Let `ϕ` be a continuous real flow and suppose `ϕ T x = x` for some
positive period `T`.  The map

```
  ℝ/ℤ → X,   [r] ↦ ϕ (T r) x
```

is well defined and continuous.  Pushing normalized Haar probability on
the unit additive circle through this map gives the canonical invariant
probability on the periodic orbit.

The construction is completely general and is used by the closed
horocycle branch of the modular invariant-measure classification.
-/

namespace HGAS.Dynamics

open Function MeasureTheory Set
open scoped BoundedContinuousFunction

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-! We use the same normalized unit-circle Haar measure as the clock
modules. -/

local instance unitAddCircleMeasureSpace :
    MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance unitAddCircleIsAddHaar :
    Measure.IsAddHaarMeasure
      (volume : Measure UnitAddCircle) :=
  inferInstanceAs
    (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance unitAddCircleIsProbability :
    IsProbabilityMeasure
      (volume : Measure UnitAddCircle) :=
  inferInstanceAs
    (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Normalized Haar probability on `ℝ/ℤ`. -/
def unitAddCircleHaarProbability :
    ProbabilityMeasure UnitAddCircle :=
  ⟨volume, inferInstance⟩

@[simp]
theorem unitAddCircleHaarProbability_toMeasure :
    (unitAddCircleHaarProbability :
      Measure UnitAddCircle) = volume :=
  rfl

/-- The circle flow whose phase speed is `T⁻¹`. -/
def periodicPhaseFlow (T : ℝ) :
    Flow ℝ UnitAddCircle where
  toFun t θ := θ + (t / T : UnitAddCircle)
  cont' := by
    apply Continuous.add
    · exact continuous_snd
    · exact QuotientAddGroup.continuous_mk.comp
        (continuous_fst.div_const T)
  map_add' := by
    intro t u θ
    rw [show (t + u) / T = u / T + t / T by ring]
    simp only [QuotientAddGroup.mk_add]
    abel
  map_zero' := by
    intro θ
    simp only [zero_div, QuotientAddGroup.mk_zero,
      add_zero]

@[simp]
theorem periodicPhaseFlow_apply
    (T t : ℝ) (θ : UnitAddCircle) :
    periodicPhaseFlow T t θ =
      θ + (t / T : UnitAddCircle) :=
  rfl

/-- Normalized circle Haar probability is invariant under the periodic
phase flow. -/
theorem unitAddCircleHaarProbability_invariant
    (T : ℝ) :
    IsInvariantProbability
      (periodicPhaseFlow T)
      unitAddCircleHaarProbability := by
  intro t
  apply ProbabilityMeasure.toMeasure_injective
  change
    Measure.map
        (fun θ : UnitAddCircle ↦
          θ + (t / T : UnitAddCircle))
        volume = volume
  exact map_add_right_eq_self volume (t / T : UnitAddCircle)

/-- Every integral multiple of a period is again a period. -/
private theorem zsmul_period
    (ϕ : Flow ℝ X) (x : X)
    {T : ℝ} (hperiod : ϕ T x = x)
    (n : ℤ) :
    ϕ ((n : ℝ) * T) x = x := by
  letI : AddAction ℝ X := ϕ.toAddAction
  have hTmem :
      T ∈ AddAction.stabilizer ℝ x :=
    AddAction.mem_stabilizer_iff.mpr hperiod
  have hnmem :=
    (AddAction.stabilizer ℝ x).zsmul_mem hTmem n
  have hnfix :
      (n • T) +ᵥ x = x :=
    AddAction.mem_stabilizer_iff.mp hnmem
  simpa only [zsmul_eq_mul] using hnfix

/-- The orbit map from the unit additive circle associated to a chosen
period. -/
def periodicOrbitMap
    (ϕ : Flow ℝ X) (x : X)
    (T : ℝ) (hperiod : ϕ T x = x) :
    UnitAddCircle → X :=
  Quotient.lift
    (fun r : ℝ ↦ ϕ (T * r) x)
    (by
      intro a b hab
      have habCircle :
          (a : UnitAddCircle) =
            (b : UnitAddCircle) :=
        Quotient.sound hab
      have habMem :
          a - b ∈ AddSubgroup.zmultiples (1 : ℝ) :=
        QuotientAddGroup.eq_iff_sub_mem.mp habCircle
      obtain ⟨n, hn⟩ :=
        AddSubgroup.mem_zmultiples_iff.mp habMem
      have hnReal : (n : ℝ) = a - b := by
        simpa only [zsmul_eq_mul, mul_one] using hn
      have htime :
          T * a = (n : ℝ) * T + T * b := by
        rw [hnReal]
        ring
      change ϕ (T * a) x = ϕ (T * b) x
      rw [htime, ϕ.map_add]
      calc
        ϕ ((n : ℝ) * T) (ϕ (T * b) x) =
            ϕ (T * b) (ϕ ((n : ℝ) * T) x) := by
          rw [← ϕ.map_add, ← ϕ.map_add, add_comm]
        _ = ϕ (T * b) x := by
          rw [zsmul_period ϕ x hperiod n])

@[simp]
theorem periodicOrbitMap_coe
    (ϕ : Flow ℝ X) (x : X)
    (T : ℝ) (hperiod : ϕ T x = x)
    (r : ℝ) :
    periodicOrbitMap ϕ x T hperiod
        (r : UnitAddCircle) =
      ϕ (T * r) x :=
  rfl

/-- The periodic orbit map is continuous. -/
theorem periodicOrbitMap_continuous
    (ϕ : Flow ℝ X) (x : X)
    (T : ℝ) (hperiod : ϕ T x = x) :
    Continuous (periodicOrbitMap ϕ x T hperiod) := by
  apply Continuous.quotient_lift
  exact ϕ.continuous
    (continuous_const.mul continuous_id)
    continuous_const

/-- For nonzero `T`, the periodic orbit map semiconjugates phase
translation to the original flow. -/
theorem periodicOrbitMap_semiconj
    (ϕ : Flow ℝ X) (x : X)
    {T : ℝ} (hT : T ≠ 0)
    (hperiod : ϕ T x = x)
    (t : ℝ) :
    Function.Semiconj
      (periodicOrbitMap ϕ x T hperiod)
      (periodicPhaseFlow T t)
      (ϕ t) := by
  intro θ
  induction θ using QuotientAddGroup.induction_on with
  | _ r =>
      change
        ϕ (T * (r + t / T)) x =
          ϕ t (ϕ (T * r) x)
      rw [← ϕ.map_add]
      congr 1
      field_simp
      ring

variable [MeasurableSpace X] [BorelSpace X]

/-- The canonical invariant probability carried by a chosen positive
periodic orbit. -/
def periodicOrbitInvariantProbability
    (ϕ : Flow ℝ X) (x : X)
    {T : ℝ} (hT : 0 < T)
    (hperiod : ϕ T x = x) :
    InvariantProbabilityMeasure ϕ :=
  let source :
      InvariantProbabilityMeasure
        (periodicPhaseFlow T) :=
    ⟨unitAddCircleHaarProbability,
      unitAddCircleHaarProbability_invariant T⟩
  source.mapEquivariant
    (periodicOrbitMap ϕ x T hperiod)
    (periodicOrbitMap_continuous ϕ x T hperiod)
    (periodicOrbitMap_semiconj
      ϕ x hT.ne' hperiod)

@[simp]
theorem periodicOrbitInvariantProbability_measure
    (ϕ : Flow ℝ X) (x : X)
    {T : ℝ} (hT : 0 < T)
    (hperiod : ϕ T x = x) :
    (periodicOrbitInvariantProbability
        ϕ x hT hperiod).measure =
      unitAddCircleHaarProbability.map
        (periodicOrbitMap_continuous
      ϕ x T hperiod).measurable.aemeasurable :=
  rfl

/-- Integration against the canonical periodic-orbit probability is
integration of the pulled-back observable against normalized circle Haar
measure. -/
theorem integral_periodicOrbitInvariantProbability
    (ϕ : Flow ℝ X) (x : X)
    {T : ℝ} (hT : 0 < T)
    (hperiod : ϕ T x = x)
    (f : X →ᵇ ℝ) :
    (∫ y, f y
        ∂((periodicOrbitInvariantProbability
          ϕ x hT hperiod).measure : Measure X)) =
      ∫ θ : UnitAddCircle,
        f (periodicOrbitMap ϕ x T hperiod θ) := by
  rw [periodicOrbitInvariantProbability_measure]
  exact integral_map
    (periodicOrbitMap_continuous
      ϕ x T hperiod).measurable.aemeasurable
    f.continuous.aestronglyMeasurable

omit [MeasurableSpace X] [BorelSpace X] in
/-- The integral over one full period has the same value from every point
of the periodic orbit. -/
theorem orbitIntegral_eq_of_mem_periodic_orbit
    (ϕ : Flow ℝ X) (f : X →ᵇ ℝ)
    (x : X) {T : ℝ} (hperiod : ϕ T x = x)
    {y : X} (hy : y ∈ Flow.orbit ϕ x) :
    orbitIntegral ϕ f T y =
      orbitIntegral ϕ f T x := by
  obtain ⟨u, rfl⟩ := hy
  let g : ℝ → ℝ := fun t ↦ f (ϕ t x)
  have hg : Function.Periodic g T := by
    intro t
    dsimp only [g]
    rw [ϕ.map_add, hperiod]
  calc
    orbitIntegral ϕ f T (ϕ u x) =
        ∫ t in (0 : ℝ)..T, g (t + u) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only [g]
      congr 1
      rw [← ϕ.map_add]
    _ = ∫ t in (0 : ℝ) + u..T + u, g t :=
      intervalIntegral.integral_comp_add_right g u
    _ = ∫ t in u..u + T, g t := by
      rw [zero_add, add_comm T u]
    _ = ∫ t in (0 : ℝ)..0 + T, g t :=
      hg.intervalIntegral_add_eq u 0
    _ = orbitIntegral ϕ f T x := by
      simp only [zero_add, orbitIntegral, g]

omit [MeasurableSpace X] [BorelSpace X] in
/-- For nonzero period, the range of the circle map is exactly the full
flow orbit. -/
theorem range_periodicOrbitMap
    (ϕ : Flow ℝ X) (x : X)
    {T : ℝ} (hT : T ≠ 0)
    (hperiod : ϕ T x = x) :
    Set.range (periodicOrbitMap ϕ x T hperiod) =
      Flow.orbit ϕ x := by
  ext y
  constructor
  · rintro ⟨θ, rfl⟩
    induction θ using QuotientAddGroup.induction_on with
    | _ r =>
        exact ⟨T * r, rfl⟩
  · rintro ⟨t, rfl⟩
    refine ⟨(t / T : UnitAddCircle), ?_⟩
    rw [periodicOrbitMap_coe]
    congr 1
    exact mul_div_cancel₀ t hT

omit [MeasurableSpace X] [BorelSpace X] in
/-- A periodic orbit is compact. -/
theorem isCompact_flow_orbit_of_periodic
    (ϕ : Flow ℝ X) (x : X)
    {T : ℝ} (hT : T ≠ 0)
    (hperiod : ϕ T x = x) :
    IsCompact (Flow.orbit ϕ x) := by
  rw [← range_periodicOrbitMap ϕ x hT hperiod]
  exact isCompact_range
    (periodicOrbitMap_continuous ϕ x T hperiod)

/-- The canonical periodic-orbit probability gives full mass to the
periodic orbit. -/
theorem periodicOrbitInvariantProbability_orbit_mass
    [T2Space X]
    (ϕ : Flow ℝ X) (x : X)
    {T : ℝ} (hT : 0 < T)
    (hperiod : ϕ T x = x) :
    ((periodicOrbitInvariantProbability
        ϕ x hT hperiod).measure :
          Measure X) (Flow.orbit ϕ x) = 1 := by
  rw [periodicOrbitInvariantProbability_measure]
  change
    Measure.map
        (periodicOrbitMap ϕ x T hperiod)
        volume (Flow.orbit ϕ x) = 1
  rw [Measure.map_apply
    (periodicOrbitMap_continuous
      ϕ x T hperiod).measurable]
  · rw [← range_periodicOrbitMap
      ϕ x hT.ne' hperiod]
    simp only [preimage_range, measure_univ]
  · exact (isCompact_flow_orbit_of_periodic
      ϕ x hT.ne' hperiod).isClosed.measurableSet

/-- An invariant probability carried by a periodic orbit is uniquely the
canonical normalized arclength probability constructed above. -/
theorem invariantProbability_eq_periodicOrbitInvariantProbability
    [T2Space X] [HasOuterApproxClosed X]
    (ϕ : Flow ℝ X) (x : X)
    {T : ℝ} (hT : 0 < T)
    (hperiod : ϕ T x = x)
    (μ : InvariantProbabilityMeasure ϕ)
    (hmass :
      (μ.measure : Measure X)
        (Flow.orbit ϕ x) = 1) :
    μ.measure =
      (periodicOrbitInvariantProbability
        ϕ x hT hperiod).measure := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let A : ℝ := orbitIntegral ϕ f T x
  have horbitCompact :=
    isCompact_flow_orbit_of_periodic
      ϕ x hT.ne' hperiod
  have horbitMeasurable :
      MeasurableSet (Flow.orbit ϕ x) :=
    horbitCompact.isClosed.measurableSet
  have hμcompl :
      (μ.measure : Measure X)
          (Flow.orbit ϕ x)ᶜ = 0 := by
    rw [measure_compl horbitMeasurable
          (measure_ne_top (μ.measure : Measure X)
            (Flow.orbit ϕ x)),
      hmass, measure_univ, tsub_self]
  have hμmem :
      ∀ᵐ y ∂(μ.measure : Measure X),
        y ∈ Flow.orbit ϕ x :=
    mem_ae_iff.mpr hμcompl
  have hμorbit :
      (fun y ↦ orbitIntegral ϕ f T y) =ᵐ[
          (μ.measure : Measure X)] fun _ ↦ A :=
    hμmem.mono fun y hy ↦
      orbitIntegral_eq_of_mem_periodic_orbit
        ϕ f x hperiod hy
  let ν :=
    periodicOrbitInvariantProbability
      ϕ x hT hperiod
  have hνmass :
      (ν.measure : Measure X)
          (Flow.orbit ϕ x) = 1 :=
    periodicOrbitInvariantProbability_orbit_mass
      ϕ x hT hperiod
  have hνcompl :
      (ν.measure : Measure X)
          (Flow.orbit ϕ x)ᶜ = 0 := by
    rw [measure_compl horbitMeasurable
          (measure_ne_top (ν.measure : Measure X)
            (Flow.orbit ϕ x)),
      hνmass, measure_univ, tsub_self]
  have hνmem :
      ∀ᵐ y ∂(ν.measure : Measure X),
        y ∈ Flow.orbit ϕ x :=
    mem_ae_iff.mpr hνcompl
  have hνorbit :
      (fun y ↦ orbitIntegral ϕ f T y) =ᵐ[
          (ν.measure : Measure X)] fun _ ↦ A :=
    hνmem.mono fun y hy ↦
      orbitIntegral_eq_of_mem_periodic_orbit
        ϕ f x hperiod hy
  have hμaverage :
      T * ∫ y, f y ∂(μ.measure : Measure X) = A := by
    rw [← integral_orbitIntegral_eq ϕ f μ T]
    rw [integral_congr_ae hμorbit]
    simp only [integral_const, A, probReal_univ,
      one_smul]
  have hνaverage :
      T * ∫ y, f y ∂(ν.measure : Measure X) = A := by
    rw [← integral_orbitIntegral_eq ϕ f ν T]
    rw [integral_congr_ae hνorbit]
    simp only [integral_const, A, probReal_univ,
      one_smul]
  exact (mul_left_cancel₀ hT.ne'
    (hμaverage.trans hνaverage.symm))

end

end HGAS.Dynamics
