import HGAS.Clocks.ControllerPhaseFlow
import HGAS.Clocks.ErgodicControllerSelection
import HGAS.Clocks.PhaseTorusFlow
import Mathlib.Tactic

/-!
# Ergodic classification of the coupled controller--phase clocks

This file closes a small but conceptually important gap between the
polynomial controller equations and the radical phase-clock argument.
The literal coupled flow is not globally a constant torus translation:
before a controller reaches an equilibrium, its phase velocity
`pᵢ Re(rᵢ + sᵢ I)` varies with time.

For an *ergodic invariant probability*, however, every controller marginal
is a Dirac probability at one of the four controller equilibria.  Since
there are only finitely many coordinates, the whole measure is concentrated
on one controller fibre.  On this full-measure fibre the orbit integral in
the skew-product definition is exactly

```text
                         t · pᵢ Re(xᵢ).
```

Thus the physical phase marginal is invariant under a genuine constant
product rotation.  The locking equation identifies each angular velocity
as a signed square root of `pᵢ`; for distinct primes, the existing radical
independence theorem then identifies the phase marginal (in turns) with
Haar probability.

The proof deliberately works with almost-everywhere semiconjugacy rather
than pretending that the phase projection is globally equivariant.
-/

noncomputable section

open Complex Filter Function MeasureTheory Set

namespace HGAS.Clocks.ErgodicControllerPhaseHaar

local instance : MeasurableSpace Circle :=
  borel Circle

local instance : BorelSpace Circle :=
  ⟨rfl⟩

variable {d : Type*} [Finite d]

abbrev State (d : Type*) :=
  HGAS.Clocks.ControllerPhaseFlow.State d

/-- The controller and phase projections from the coupled state space. -/
def controllerProjection (z : State d) : d → Circle :=
  z.1

def phaseProjection (z : State d) : d → Circle :=
  z.2

omit [Finite d] in
theorem continuous_controllerProjection :
    Continuous (controllerProjection : State d → (d → Circle)) :=
  continuous_fst

omit [Finite d] in
theorem continuous_phaseProjection :
    Continuous (phaseProjection : State d → (d → Circle)) :=
  continuous_snd

/-- A map whose pushforward is a Dirac probability is almost surely equal
to the atom.  This elementary helper keeps the controller-selection proof
independent of any choice of coordinates. -/
theorem ae_eq_of_map_eq_diracProba
    {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass Y]
    (μ : ProbabilityMeasure X)
    (f : X → Y) (hf : AEMeasurable f (μ : Measure X))
    (y : Y)
    (hmap : μ.map hf = MeasureTheory.diracProba y) :
    ∀ᵐ x ∂(μ : Measure X), f x = y := by
  have htarget :
      ∀ᵐ z ∂((μ.map hf : ProbabilityMeasure Y) : Measure Y), z = y := by
    rw [hmap]
    simpa only [id_eq] using
      (MeasureTheory.ae_eq_dirac (fun z : Y ↦ z) :
        (fun z : Y ↦ z) =ᵐ[Measure.dirac y] fun _ ↦ y)
  exact ae_of_ae_map hf htarget

/-- For every controller coordinate, ergodicity selects one equilibrium.
All selected equalities hold simultaneously because the index type is
finite.  The theorem exposes both the coordinatewise Dirac marginals and
the stronger almost-everywhere statement for the whole controller tuple. -/
theorem exists_lockedControllerTuple
    (p : d → ℝ) (hp : ∀ i, 1 < p i)
    (μ : ProbabilityMeasure (State d))
    (hμ :
      HGAS.Dynamics.IsErgodicInvariantProbability
        (HGAS.Clocks.ControllerPhaseFlow.controllerPhaseFlow p hp) μ) :
    ∃ x : d → Circle,
      (∀ i,
        x i ∈ HGAS.Clocks.ControllerFlow.controllerEquilibria (p i)) ∧
      (∀ i,
        μ.map
            ((HGAS.Clocks.ControllerPhaseFlow.continuous_controllerProjection
                i).measurable.aemeasurable) =
          MeasureTheory.diracProba (x i)) ∧
      (∀ᵐ z ∂(μ : Measure (State d)), z.1 = x) := by
  have hselect :
      ∀ i : d, ∃ x : Circle,
        x ∈ HGAS.Clocks.ControllerFlow.controllerEquilibria (p i) ∧
          μ.map
              ((HGAS.Clocks.ControllerPhaseFlow.continuous_controllerProjection
                  i).measurable.aemeasurable) =
            MeasureTheory.diracProba x := by
    intro i
    exact
      HGAS.Clocks.ControllerFlow.exists_controllerFactorMap_eq_diracProba_at_equilibrium
          (p i) (hp i) μ hμ
          (fun z : State d ↦ z.1 i)
          (HGAS.Clocks.ControllerPhaseFlow.continuous_controllerProjection i)
          (HGAS.Clocks.ControllerPhaseFlow.controllerProjection_semiconj
            p hp i)
  choose x hx hdirac using hselect
  have hcoordinate :
      ∀ i : d, ∀ᵐ z ∂(μ : Measure (State d)), z.1 i = x i := by
    intro i
    exact ae_eq_of_map_eq_diracProba μ
      (fun z : State d ↦ z.1 i)
      ((HGAS.Clocks.ControllerPhaseFlow.continuous_controllerProjection
        i).measurable.aemeasurable)
      (x i) (hdirac i)
  have hall :
      ∀ᵐ z ∂(μ : Measure (State d)), ∀ i, z.1 i = x i :=
    ae_all_iff.mpr hcoordinate
  refine ⟨x, hx, hdirac, ?_⟩
  filter_upwards [hall] with z hz
  exact funext hz

/-- Joint-marginal form of controller selection: the pushforward by the
entire controller projection is one Dirac probability. -/
theorem exists_controllerMarginal_eq_diracProba
    (p : d → ℝ) (hp : ∀ i, 1 < p i)
    (μ : ProbabilityMeasure (State d))
    (hμ :
      HGAS.Dynamics.IsErgodicInvariantProbability
        (HGAS.Clocks.ControllerPhaseFlow.controllerPhaseFlow p hp) μ) :
    ∃ x : d → Circle,
      (∀ i,
        x i ∈ HGAS.Clocks.ControllerFlow.controllerEquilibria (p i)) ∧
      μ.map continuous_controllerProjection.measurable.aemeasurable =
        MeasureTheory.diracProba x ∧
      (∀ᵐ z ∂(μ : Measure (State d)), z.1 = x) := by
  obtain ⟨x, hx, _, hae⟩ :=
    exists_lockedControllerTuple p hp μ hμ
  refine ⟨x, hx, ?_, hae⟩
  apply ProbabilityMeasure.toMeasure_injective
  change
    Measure.map controllerProjection (μ : Measure (State d)) =
      Measure.dirac x
  calc
    Measure.map controllerProjection (μ : Measure (State d)) =
        Measure.map (fun _ : State d ↦ x) (μ : Measure (State d)) := by
      apply Measure.map_congr
      simpa only [controllerProjection] using hae
    _ = Measure.dirac x := by
      rw [Measure.map_const]
      simp

omit [Finite d] in
/-- The chosen controller tuple is fixed by the product controller flow. -/
theorem controllerTuple_isFixed
    (p : d → ℝ) (hp : ∀ i, 1 < p i)
    {x : d → Circle}
    (hx : ∀ i,
      x i ∈ HGAS.Clocks.ControllerFlow.controllerEquilibria (p i)) :
    HGAS.Dynamics.InvariantProbabilityMeasure.IsFlowFixedPoint
      (HGAS.Clocks.ControllerPhaseFlow.controllerTorusFlow p hp) x := by
  intro t
  funext i
  exact
    HGAS.Clocks.ControllerFlow.isFlowFixedPoint_of_mem_controllerEquilibria
        (p i) (hp i) (hx i) t

omit [Finite d] in
/-- On the selected controller fibre, the literal coupled phase flow is the
constant physical product rotation with angular velocity `pᵢ Re(xᵢ)`. -/
theorem phase_of_lockedController
    (p : d → ℝ) (hp : ∀ i, 1 < p i)
    {x : d → Circle}
    (hx : ∀ i,
      x i ∈ HGAS.Clocks.ControllerFlow.controllerEquilibria (p i))
    (t : ℝ) (z : d → Circle) :
    (HGAS.Clocks.ControllerPhaseFlow.controllerPhaseFlow
        p hp t (x, z)).2 =
      HGAS.Clocks.PhaseTorusFlow.phaseTorusFlow
        (fun i ↦ p i * (x i : ℂ).re) t z := by
  funext i
  change
    ((HGAS.Dynamics.ContinuousPhaseSkewFlow.phaseSkewFlow
      (HGAS.Clocks.ControllerPhaseFlow.controllerTorusFlow p hp)
      (HGAS.Clocks.ControllerPhaseFlow.angularVelocity p)
      t (x, z)).2 i) =
      _
  rw [HGAS.Dynamics.ContinuousPhaseSkewFlow.phaseSkewFlow_phase_of_fixed
      (HGAS.Clocks.ControllerPhaseFlow.controllerTorusFlow p hp)
      (HGAS.Clocks.ControllerPhaseFlow.angularVelocity p)
      (controllerTuple_isFixed p hp hx)]
  simp only [HGAS.Clocks.ControllerPhaseFlow.angularVelocity_apply,
    HGAS.Clocks.PhaseTorusFlow.phaseTorusFlow_apply,
    HGAS.Clocks.PhaseClockFlow.phaseRotationFlow_apply]
  congr 2
  ring

omit [Finite d] in
/-- Although phase projection is not globally equivariant, it is
equivariant almost everywhere under any measure concentrated on a selected
controller fibre. -/
theorem phaseProjection_ae_semiconj
    (p : d → ℝ) (hp : ∀ i, 1 < p i)
    (μ : ProbabilityMeasure (State d))
    {x : d → Circle}
    (hx : ∀ i,
      x i ∈ HGAS.Clocks.ControllerFlow.controllerEquilibria (p i))
    (hae : ∀ᵐ z ∂(μ : Measure (State d)), z.1 = x)
    (t : ℝ) :
    (fun z : State d ↦
        HGAS.Clocks.PhaseTorusFlow.phaseTorusFlow
          (fun i ↦ p i * (x i : ℂ).re) t z.2) =ᵐ[
      (μ : Measure (State d))]
      fun z ↦
        (HGAS.Clocks.ControllerPhaseFlow.controllerPhaseFlow
          p hp t z).2 := by
  filter_upwards [hae] with z hz
  subst hz
  exact (phase_of_lockedController p hp hx t z.2).symm

/-- The physical phase pushforward of an invariant coupled measure is an
invariant probability for the locked constant product rotation. -/
def lockedPhaseInvariantProbability
    (p : d → ℝ) (hp : ∀ i, 1 < p i)
    (μ : ProbabilityMeasure (State d))
    (hμ :
      HGAS.Dynamics.IsInvariantProbability
        (HGAS.Clocks.ControllerPhaseFlow.controllerPhaseFlow p hp) μ)
    (x : d → Circle)
    (hx : ∀ i,
      x i ∈ HGAS.Clocks.ControllerFlow.controllerEquilibria (p i))
    (hae : ∀ᵐ z ∂(μ : Measure (State d)), z.1 = x) :
    HGAS.Dynamics.InvariantProbabilityMeasure
      (HGAS.Clocks.PhaseTorusFlow.phaseTorusFlow
        (fun i ↦ p i * (x i : ℂ).re)) where
  measure :=
    μ.map continuous_phaseProjection.measurable.aemeasurable
  invariant := by
    intro t
    apply ProbabilityMeasure.toMeasure_injective
    simp only [HGAS.Dynamics.timePushforward,
      ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map
      (HGAS.Clocks.PhaseTorusFlow.phaseTorusFlow _
        |>.continuous_toFun t).measurable
      continuous_phaseProjection.measurable]
    rw [Measure.map_congr (by
      simpa only [Function.comp_apply, phaseProjection] using
        phaseProjection_ae_semiconj p hp μ hx hae t)]
    change
      Measure.map
          (phaseProjection ∘
            HGAS.Clocks.ControllerPhaseFlow.controllerPhaseFlow p hp t)
          (μ : Measure (State d)) =
        Measure.map phaseProjection (μ : Measure (State d))
    rw [← Measure.map_map
      continuous_phaseProjection.measurable
      (HGAS.Clocks.ControllerPhaseFlow.controllerPhaseFlow p hp
        |>.continuous_toFun t).measurable]
    have htime :
        Measure.map
            (HGAS.Clocks.ControllerPhaseFlow.controllerPhaseFlow p hp t)
            (μ : Measure (State d)) =
          (μ : Measure (State d)) := by
      have h := congrArg ProbabilityMeasure.toMeasure (hμ t)
      simpa only [HGAS.Dynamics.timePushforward,
        ProbabilityMeasure.toMeasure_map] using h
    rw [htime]

omit [Finite d] in
/-- A locked prime controller supplies exactly one of the two signed radical
angular velocities. -/
theorem exists_sign_lockedFrequency
    (p : d → ℕ)
    (hp : ∀ i : d, (p i).Prime)
    {x : d → Circle}
    (hx : ∀ i,
      x i ∈ HGAS.Clocks.ControllerFlow.controllerEquilibria
        (p i : ℝ)) :
    ∃ sign : d → ℤ,
      (∀ i, sign i = 1 ∨ sign i = -1) ∧
      (fun i ↦ (p i : ℝ) * (x i : ℂ).re) =
        HGAS.Clocks.RadicalIndependence.signedPrimeSqrtFrequency
          p sign := by
  let sign : d → ℤ :=
    fun i ↦ if 0 ≤ (p i : ℝ) * (x i : ℂ).re then 1 else -1
  have hsign : ∀ i, sign i = 1 ∨ sign i = -1 := by
    intro i
    by_cases hi : 0 ≤ (p i : ℝ) * (x i : ℂ).re
    · left
      simp [sign, hi]
    · right
      simp [sign, hi]
  refine ⟨sign, hsign, funext fun i ↦ ?_⟩
  have hpgt : (1 : ℝ) < (p i : ℝ) := by
    exact_mod_cast (hp i).one_lt
  have hlock :
      (p i : ℝ) * (x i : ℂ).re ^ 2 = 1 :=
    by
      have hre :=
        (HGAS.Clocks.ControllerFlow.mem_controllerEquilibria_iff_coordinate_squares
          (p i : ℝ) hpgt (x i)).mp (hx i) |>.1
      rw [hre]
      have hpne : (p i : ℝ) ≠ 0 := ne_of_gt (zero_lt_one.trans hpgt)
      field_simp
  have hsq :
      ((p i : ℝ) * (x i : ℂ).re) ^ 2 = (p i : ℝ) := by
    calc
      ((p i : ℝ) * (x i : ℂ).re) ^ 2 =
          (p i : ℝ) *
            ((p i : ℝ) * (x i : ℂ).re ^ 2) := by ring
      _ = (p i : ℝ) := by rw [hlock, mul_one]
  have habs :
      |(p i : ℝ) * (x i : ℂ).re| =
        Real.sqrt (p i : ℝ) := by
    rw [← Real.sqrt_sq_eq_abs, hsq]
  by_cases hi : 0 ≤ (p i : ℝ) * (x i : ℂ).re
  · simp only [HGAS.Clocks.RadicalIndependence.signedPrimeSqrtFrequency]
    rw [show sign i = 1 by simp [sign, hi]]
    norm_num
    simpa [abs_of_nonneg hi] using habs
  · have hineg : (p i : ℝ) * (x i : ℂ).re < 0 :=
      lt_of_not_ge hi
    simp only [HGAS.Clocks.RadicalIndependence.signedPrimeSqrtFrequency]
    rw [show sign i = -1 by simp [sign, hi]]
    norm_num
    have := habs
    rw [abs_of_neg hineg] at this
    linarith

omit [Finite d] in
/-- A prime natural controller parameter is strictly greater than one after
casting to the real numbers.  Naming this proof keeps all occurrences of
the literal coupled flow definitionally synchronized. -/
theorem primeControllerParameters_gt_one
    (p : d → ℕ) (hp : ∀ i : d, (p i).Prime) :
    ∀ i : d, (1 : ℝ) < (p i : ℝ) := by
  intro i
  exact_mod_cast (hp i).one_lt

/-- Full ergodic classification for distinct prime controller clocks.
It simultaneously exposes:

* the selected controller tuple and its joint Dirac marginal;
* concentration of the original measure on that controller fibre;
* the signs and exact signed-radical locked angular velocities;
* Haar probability for the physical phase marginal after converting
  radians to turns.
-/
theorem exists_lockedController_sign_and_phaseHaar
    [Fintype d]
    (p : d → ℕ)
    (hp : ∀ i : d, (p i).Prime)
    (hinjective : Function.Injective p)
    (μ : ProbabilityMeasure (State d))
    (hμ :
      HGAS.Dynamics.IsErgodicInvariantProbability
        (HGAS.Clocks.ControllerPhaseFlow.controllerPhaseFlow
          (fun i ↦ (p i : ℝ))
          (primeControllerParameters_gt_one p hp)) μ) :
    ∃ (x : d → Circle) (sign : d → ℤ),
      (∀ i,
        x i ∈ HGAS.Clocks.ControllerFlow.controllerEquilibria
          (p i : ℝ)) ∧
      μ.map continuous_controllerProjection.measurable.aemeasurable =
        MeasureTheory.diracProba x ∧
      (∀ᵐ z ∂(μ : Measure (State d)), z.1 = x) ∧
      (∀ i, sign i = 1 ∨ sign i = -1) ∧
      (fun i ↦ (p i : ℝ) * (x i : ℂ).re) =
        HGAS.Clocks.RadicalIndependence.signedPrimeSqrtFrequency
          p sign ∧
      (μ.map continuous_phaseProjection.measurable.aemeasurable).map
          (HGAS.Clocks.PhaseTorusFlow.continuous_phaseTorusToTurns
            |>.measurable.aemeasurable) =
        HGAS.Clocks.RadicalClock.torusHaarProbability := by
  let hpReal : ∀ i : d, (1 : ℝ) < (p i : ℝ) :=
    primeControllerParameters_gt_one p hp
  obtain ⟨x, hx, hcontroller, hae⟩ :=
    exists_controllerMarginal_eq_diracProba
      (fun i ↦ (p i : ℝ)) hpReal μ hμ
  obtain ⟨sign, hsign, hfrequency⟩ :=
    exists_sign_lockedFrequency p hp hx
  let ν :
      HGAS.Dynamics.InvariantProbabilityMeasure
        (HGAS.Clocks.PhaseTorusFlow.phaseTorusFlow
          (fun i ↦ (p i : ℝ) * (x i : ℂ).re)) :=
    lockedPhaseInvariantProbability
      (fun i ↦ (p i : ℝ)) hpReal μ hμ.invariant x hx hae
  have hhaar :
      (ν.mapEquivariant
        HGAS.Clocks.PhaseTorusFlow.phaseTorusToTurns
        HGAS.Clocks.PhaseTorusFlow.continuous_phaseTorusToTurns
        (HGAS.Clocks.PhaseTorusFlow.phaseTorusToTurns_semiconj
          (fun i ↦ (p i : ℝ) * (x i : ℂ).re))).measure =
        HGAS.Clocks.RadicalClock.torusHaarProbability := by
    apply
      HGAS.Clocks.RadicalClock.invariantProbability_eq_torusHaar_of_noCharacter
    rw [HGAS.Clocks.PhaseTorusFlow.turnsFrequency_eq_commonScale]
    have hfrequency_apply :
        ∀ i,
          (p i : ℝ) * (x i : ℂ).re =
            HGAS.Clocks.RadicalIndependence.signedPrimeSqrtFrequency
              p sign i :=
      congrFun hfrequency
    simp_rw [hfrequency_apply]
    exact
      HGAS.Clocks.ScaledRadicalClock.scaledSignedPrimeSqrtFrequency_hasNoCharacter
          (1 / (2 * Real.pi))
          HGAS.Clocks.ScaledRadicalClock.one_div_two_pi_ne_zero
          p hp hinjective sign hsign
  refine ⟨x, sign, hx, hcontroller, hae, hsign, hfrequency, ?_⟩
  simpa only [ν, lockedPhaseInvariantProbability,
    HGAS.Dynamics.InvariantProbabilityMeasure.mapEquivariant_measure]
    using hhaar

end HGAS.Clocks.ErgodicControllerPhaseHaar
