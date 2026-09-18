import HGAS.Clocks.ErgodicControllerPhaseHaar
import HGAS.Clocks.PhaseTorusFlow
import HGAS.Dynamics.InvariantRestriction
import Mathlib.Tactic

/-!
# Haar phase marginal without an ergodicity hypothesis

An invariant probability of the coupled controller--phase flow need not
choose one controller equilibrium.  It may mix all of the finitely many
equilibria.  Nevertheless its *phase* marginal is still Haar.

The point is elementary but slightly more delicate than the ergodic
argument.  Every controller marginal is supported on the four
eigen-directions.  We partition this finite support according to the sign
of each locked frequency.  Every sign branch is measurable and invariant.
After normalizing the restriction to a positive-mass branch, the phase
projection is an exact factor of one fixed signed-radical translation.
Unique ergodicity of that translation makes the conditional phase
marginal Haar.  Finally, a finite mixture of copies of the same Haar
probability is Haar.

This proof uses only normalized restrictions to explicit invariant sets.
In particular, it does not invoke ergodic decomposition or conditional
measures.
-/

noncomputable section

open Complex Filter Function MeasureTheory Set
open scoped BigOperators ENNReal

namespace HGAS.Clocks.NonergodicControllerPhaseHaar

local instance : MeasurableSpace Circle :=
  borel Circle

local instance : BorelSpace Circle :=
  ⟨rfl⟩

variable {d : Type*} [Finite d] [Fintype d]

abbrev State (d : Type*) :=
  HGAS.Clocks.ControllerPhaseFlow.State d

abbrev SignTuple (d : Type*) :=
  d → Bool

/-- Encode a binary sign as the integer `+1` or `-1`. -/
def signInt (b : Bool) : ℤ :=
  if b then -1 else 1

@[simp]
theorem signInt_false : signInt false = 1 := by
  rfl

@[simp]
theorem signInt_true : signInt true = -1 := by
  rfl

theorem signInt_eq_one_or_neg_one (b : Bool) :
    signInt b = 1 ∨ signInt b = -1 := by
  cases b <;> simp

theorem signInt_injective : Function.Injective signInt := by
  intro a b h
  cases a <;> cases b <;> simp_all

/-- The controller equilibrium set is closed (hence Borel measurable).
This small topological fact is useful independently of the finite-branch
argument below. -/
theorem isClosed_controllerEquilibria (q : ℝ) :
    IsClosed (HGAS.Clocks.ControllerFlow.controllerEquilibria q) := by
  let a := HGAS.Clocks.ControllerFlow.controllerExponent q
  have hplus : Continuous (fun z : Circle ↦
      HGAS.Clocks.ControllerFlow.expandingCoordinate a (z : ℂ)) := by
    exact
      (Complex.continuous_im.comp continuous_subtype_val).add
        (continuous_const.mul
          (Complex.continuous_re.comp continuous_subtype_val))
  have hminus : Continuous (fun z : Circle ↦
      HGAS.Clocks.ControllerFlow.contractingCoordinate a (z : ℂ)) := by
    exact
      (Complex.continuous_im.comp continuous_subtype_val).sub
        (continuous_const.mul
          (Complex.continuous_re.comp continuous_subtype_val))
  change IsClosed
    ({z : Circle |
        HGAS.Clocks.ControllerFlow.expandingCoordinate a (z : ℂ) = 0} ∪
      {z : Circle |
        HGAS.Clocks.ControllerFlow.contractingCoordinate a (z : ℂ) = 0})
  exact
    (isClosed_eq hplus continuous_const).union
      (isClosed_eq hminus continuous_const)

theorem measurableSet_controllerEquilibria (q : ℝ) :
    MeasurableSet (HGAS.Clocks.ControllerFlow.controllerEquilibria q) :=
  (isClosed_controllerEquilibria q).measurableSet

/-- A sign branch consists of controller equilibria whose physical angular
velocities have one prescribed sign tuple.  The phase coordinates are
unrestricted. -/
def controllerSignBranch
    (p : d → ℕ) (ε : SignTuple d) : Set (State d) :=
  {z | ∀ i,
    z.1 i ∈
        HGAS.Clocks.ControllerFlow.controllerEquilibria (p i : ℝ) ∧
      (p i : ℝ) * (z.1 i : ℂ).re =
        HGAS.Clocks.RadicalIndependence.signedPrimeSqrtFrequency
          p (fun j ↦ signInt (ε j)) i}

omit [Fintype d] in
theorem measurableSet_controllerSignBranch
    (p : d → ℕ) (ε : SignTuple d) :
    MeasurableSet (controllerSignBranch p ε) := by
  rw [controllerSignBranch, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  have hcontroller : Continuous (fun z : State d ↦ z.1 i) :=
    (continuous_apply i).comp continuous_fst
  have hfrequency : Continuous (fun z : State d ↦
      (p i : ℝ) * (z.1 i : ℂ).re) :=
    continuous_const.mul
      (Complex.continuous_re.comp
        (continuous_subtype_val.comp hcontroller))
  exact
    (measurableSet_controllerEquilibria (p i : ℝ)).preimage
        hcontroller.measurable |>.inter
      (isClosed_eq hfrequency continuous_const).measurableSet

omit [Finite d] [Fintype d] in
/-- Every prescribed sign branch is invariant under the literal coupled
flow: all its controller coordinates are fixed eigen-directions. -/
theorem isInvariant_controllerSignBranch
    (p : d → ℕ) (hp : ∀ i : d, (p i).Prime)
    (ε : SignTuple d) :
    IsInvariant
      (HGAS.Clocks.ControllerPhaseFlow.controllerPhaseFlow
        (fun i ↦ (p i : ℝ))
        (HGAS.Clocks.ErgodicControllerPhaseHaar.primeControllerParameters_gt_one
          p hp))
      (controllerSignBranch p ε) := by
  intro t z hz i
  have hfixed :=
    HGAS.Clocks.ControllerFlow.isFlowFixedPoint_of_mem_controllerEquilibria
      (p i : ℝ)
      (HGAS.Clocks.ErgodicControllerPhaseHaar.primeControllerParameters_gt_one
        p hp i)
      (hz i).1 t
  rw [HGAS.Clocks.ControllerPhaseFlow.controllerPhaseFlow_controller,
    hfixed]
  exact hz i

/-- Equality of two signed prime-root frequencies in one coordinate
recovers the underlying binary sign. -/
theorem sign_eq_of_frequency_eq
    {q : ℕ} (hq : q.Prime) {a b : Bool}
    (h :
      ((signInt a : ℤ) : ℝ) * Real.sqrt (q : ℝ) =
        ((signInt b : ℤ) : ℝ) * Real.sqrt (q : ℝ)) :
    a = b := by
  have hsqrt : 0 < Real.sqrt (q : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hq.pos)
  apply signInt_injective
  have hcast :
      ((signInt a : ℤ) : ℝ) = ((signInt b : ℤ) : ℝ) := by
    exact mul_right_cancel₀ (ne_of_gt hsqrt) h
  exact_mod_cast hcast

omit [Finite d] [Fintype d] in
/-- Different sign branches are disjoint. -/
theorem pairwiseDisjoint_controllerSignBranch
    (p : d → ℕ) (hp : ∀ i : d, (p i).Prime) :
    Pairwise (Disjoint on controllerSignBranch p) := by
  intro ε η hne
  change Disjoint (controllerSignBranch p ε)
    (controllerSignBranch p η)
  rw [Set.disjoint_left]
  intro z hzε hzη
  apply hne
  funext i
  apply sign_eq_of_frequency_eq (hp i)
  simpa only [
    HGAS.Clocks.RadicalIndependence.signedPrimeSqrtFrequency] using
      (hzε i).2.symm.trans (hzη i).2

omit [Finite d] [Fintype d] in
/-- Every tuple of prime-controller equilibria belongs to one of the
binary sign branches. -/
theorem mem_iUnion_controllerSignBranch_of_equilibria
    (p : d → ℕ) (hp : ∀ i : d, (p i).Prime)
    {z : State d}
    (hz : ∀ i,
      z.1 i ∈
        HGAS.Clocks.ControllerFlow.controllerEquilibria (p i : ℝ)) :
    z ∈ ⋃ ε : SignTuple d, controllerSignBranch p ε := by
  obtain ⟨sign, hsign, hfrequency⟩ :=
    HGAS.Clocks.ErgodicControllerPhaseHaar.exists_sign_lockedFrequency
      p hp hz
  let ε : SignTuple d :=
    fun i ↦ if sign i = 1 then false else true
  have hsignInt : ∀ i, signInt (ε i) = sign i := by
    intro i
    rcases hsign i with hi | hi
    · simp [ε, hi]
    · have hne : (-1 : ℤ) ≠ 1 := by norm_num
      simp [ε, hi, hne]
  apply Set.mem_iUnion.mpr
  refine ⟨ε, fun i ↦ ⟨hz i, ?_⟩⟩
  have hi := congrFun hfrequency i
  simpa only [hsignInt] using hi

omit [Fintype d] in
/-- An arbitrary invariant probability of the coupled flow is supported
on the finite union of its sign branches. -/
theorem ae_mem_iUnion_controllerSignBranch
    (p : d → ℕ) (hp : ∀ i : d, (p i).Prime)
    (μ : HGAS.Dynamics.InvariantProbabilityMeasure
      (HGAS.Clocks.ControllerPhaseFlow.controllerPhaseFlow
        (fun i ↦ (p i : ℝ))
        (HGAS.Clocks.ErgodicControllerPhaseHaar.primeControllerParameters_gt_one
          p hp))) :
    ∀ᵐ z ∂(μ.measure : Measure (State d)),
      z ∈ ⋃ ε : SignTuple d, controllerSignBranch p ε := by
  have hcoordinate :
      ∀ i : d, ∀ᵐ z ∂(μ.measure : Measure (State d)),
        z.1 i ∈
          HGAS.Clocks.ControllerFlow.controllerEquilibria (p i : ℝ) := by
    intro i
    let ν :=
      μ.mapEquivariant
        (fun z : State d ↦ z.1 i)
        (HGAS.Clocks.ControllerPhaseFlow.continuous_controllerProjection i)
        (HGAS.Clocks.ControllerPhaseFlow.controllerProjection_semiconj
          (fun i ↦ (p i : ℝ))
          (HGAS.Clocks.ErgodicControllerPhaseHaar.primeControllerParameters_gt_one
            p hp) i)
    have hzero :
        (ν.measure : Measure Circle)
          ((HGAS.Clocks.ControllerFlow.controllerEquilibria
            (p i : ℝ))ᶜ) = 0 :=
      HGAS.Clocks.ControllerFlow.invariantProbability_controllerEquilibria_compl_eq_zero
        (p i : ℝ)
        (HGAS.Clocks.ErgodicControllerPhaseHaar.primeControllerParameters_gt_one
          p hp i) ν
    have htarget :
        ∀ᵐ x ∂(ν.measure : Measure Circle),
          x ∈ HGAS.Clocks.ControllerFlow.controllerEquilibria (p i : ℝ) := by
      rw [ae_iff]
      simpa only [Set.mem_compl_iff] using hzero
    exact ae_of_ae_map
      (HGAS.Clocks.ControllerPhaseFlow.continuous_controllerProjection
        i).measurable.aemeasurable htarget
  have hall :
      ∀ᵐ z ∂(μ.measure : Measure (State d)), ∀ i,
        z.1 i ∈
          HGAS.Clocks.ControllerFlow.controllerEquilibria (p i : ℝ) :=
    ae_all_iff.mpr hcoordinate
  filter_upwards [hall] with z hz
  exact mem_iUnion_controllerSignBranch_of_equilibria p hp hz

omit [Finite d] [Fintype d] in
/-- On an almost-sure fixed-frequency controller locus, phase projection
is almost everywhere equivariant with the corresponding constant product
rotation.  Unlike the earlier locked-fibre lemma, the imaginary controller
signs may vary from point to point. -/
theorem phaseProjection_ae_semiconj_of_lockedFrequency
    (q : d → ℝ) (hq : ∀ i, 1 < q i)
    (ω : d → ℝ)
    (μ : ProbabilityMeasure (State d))
    (hae :
      ∀ᵐ z ∂(μ : Measure (State d)), ∀ i,
        z.1 i ∈
            HGAS.Clocks.ControllerFlow.controllerEquilibria (q i) ∧
          q i * (z.1 i : ℂ).re = ω i)
    (t : ℝ) :
    (fun z : State d ↦
        HGAS.Clocks.PhaseTorusFlow.phaseTorusFlow ω t z.2) =ᵐ[
      (μ : Measure (State d))]
      fun z ↦
        (HGAS.Clocks.ControllerPhaseFlow.controllerPhaseFlow
          q hq t z).2 := by
  filter_upwards [hae] with z hz
  have hphase :=
    HGAS.Clocks.ErgodicControllerPhaseHaar.phase_of_lockedController
      q hq (x := z.1) (fun i ↦ (hz i).1) t z.2
  simpa only [funext fun i ↦ (hz i).2] using hphase.symm

/-- Package the preceding almost-everywhere semiconjugacy as an invariant
probability for the constant physical phase flow. -/
def lockedFrequencyPhaseInvariantProbability
    (q : d → ℝ) (hq : ∀ i, 1 < q i)
    (ω : d → ℝ)
    (μ : HGAS.Dynamics.InvariantProbabilityMeasure
      (HGAS.Clocks.ControllerPhaseFlow.controllerPhaseFlow q hq))
    (hae :
      ∀ᵐ z ∂(μ.measure : Measure (State d)), ∀ i,
        z.1 i ∈
            HGAS.Clocks.ControllerFlow.controllerEquilibria (q i) ∧
          q i * (z.1 i : ℂ).re = ω i) :
    HGAS.Dynamics.InvariantProbabilityMeasure
      (HGAS.Clocks.PhaseTorusFlow.phaseTorusFlow ω) where
  measure :=
    μ.measure.map
      (HGAS.Clocks.ErgodicControllerPhaseHaar.continuous_phaseProjection
        (d := d)).measurable.aemeasurable
  invariant := by
    intro t
    apply ProbabilityMeasure.toMeasure_injective
    simp only [HGAS.Dynamics.timePushforward,
      ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map
      (HGAS.Clocks.PhaseTorusFlow.phaseTorusFlow ω
        |>.continuous_toFun t).measurable
      (HGAS.Clocks.ErgodicControllerPhaseHaar.continuous_phaseProjection
        (d := d)).measurable]
    apply Eq.trans
      (Measure.map_congr (by
        simpa only [Function.comp_apply,
          HGAS.Clocks.ErgodicControllerPhaseHaar.phaseProjection] using
          phaseProjection_ae_semiconj_of_lockedFrequency
            q hq ω μ.measure hae t))
    change
      Measure.map
          (HGAS.Clocks.ErgodicControllerPhaseHaar.phaseProjection ∘
            HGAS.Clocks.ControllerPhaseFlow.controllerPhaseFlow q hq t)
          (μ.measure : Measure (State d)) =
        Measure.map
          HGAS.Clocks.ErgodicControllerPhaseHaar.phaseProjection
          (μ.measure : Measure (State d))
    rw [← Measure.map_map
      (HGAS.Clocks.ErgodicControllerPhaseHaar.continuous_phaseProjection
        (d := d)).measurable
      (HGAS.Clocks.ControllerPhaseFlow.controllerPhaseFlow q hq
        |>.continuous_toFun t).measurable]
    rw [μ.map_time_toMeasure t]

/-- If an invariant probability is concentrated on one sign branch, its
phase marginal in turns is Haar.  No controller tuple is selected. -/
theorem phaseHaar_of_ae_mem_controllerSignBranch
    (p : d → ℕ)
    (hp : ∀ i : d, (p i).Prime)
    (hinjective : Function.Injective p)
    (ε : SignTuple d)
    (μ : HGAS.Dynamics.InvariantProbabilityMeasure
      (HGAS.Clocks.ControllerPhaseFlow.controllerPhaseFlow
        (fun i ↦ (p i : ℝ))
        (HGAS.Clocks.ErgodicControllerPhaseHaar.primeControllerParameters_gt_one
          p hp)))
    (hae :
      ∀ᵐ z ∂(μ.measure : Measure (State d)),
        z ∈ controllerSignBranch p ε) :
    (μ.measure.map
        (HGAS.Clocks.ErgodicControllerPhaseHaar.continuous_phaseProjection
          (d := d)).measurable.aemeasurable).map
      (HGAS.Clocks.PhaseTorusFlow.continuous_phaseTorusToTurns
        |>.measurable.aemeasurable) =
      HGAS.Clocks.RadicalClock.torusHaarProbability := by
  let ν :=
    lockedFrequencyPhaseInvariantProbability
      (fun i ↦ (p i : ℝ))
      (HGAS.Clocks.ErgodicControllerPhaseHaar.primeControllerParameters_gt_one
        p hp)
      (HGAS.Clocks.RadicalIndependence.signedPrimeSqrtFrequency
        p (fun i ↦ signInt (ε i)))
      μ hae
  simpa only [ν, lockedFrequencyPhaseInvariantProbability] using
    HGAS.Clocks.PhaseTorusFlow.physicalSignedRadicalPhase_marginal_eq_haar
      p hp hinjective (fun i ↦ signInt (ε i))
      (fun i ↦ signInt_eq_one_or_neg_one (ε i)) ν

/-- **Non-ergodic coupled-clock Haar theorem.**  For distinct prime
controllers, every invariant probability of the literal coupled
controller--phase flow has Haar physical phase marginal in turns.

The controller marginal may be an arbitrary mixture of the finitely many
equilibria and sign branches. -/
theorem phaseHaar_of_invariantProbability
    (p : d → ℕ)
    (hp : ∀ i : d, (p i).Prime)
    (hinjective : Function.Injective p)
    (μ : ProbabilityMeasure (State d))
    (hμ :
      HGAS.Dynamics.IsInvariantProbability
        (HGAS.Clocks.ControllerPhaseFlow.controllerPhaseFlow
          (fun i ↦ (p i : ℝ))
          (HGAS.Clocks.ErgodicControllerPhaseHaar.primeControllerParameters_gt_one
            p hp)) μ) :
    (μ.map
        (HGAS.Clocks.ErgodicControllerPhaseHaar.continuous_phaseProjection
          (d := d)).measurable.aemeasurable).map
      (HGAS.Clocks.PhaseTorusFlow.continuous_phaseTorusToTurns
        |>.measurable.aemeasurable) =
      HGAS.Clocks.RadicalClock.torusHaarProbability := by
  let Φ :=
    HGAS.Clocks.ControllerPhaseFlow.controllerPhaseFlow
      (fun i ↦ (p i : ℝ))
      (HGAS.Clocks.ErgodicControllerPhaseHaar.primeControllerParameters_gt_one
        p hp)
  let μInv : HGAS.Dynamics.InvariantProbabilityMeasure Φ :=
    ⟨μ, hμ⟩
  let branch : SignTuple d → Set (State d) :=
    controllerSignBranch p
  let phaseInTurns : State d → UnitAddTorus d :=
    HGAS.Clocks.PhaseTorusFlow.phaseTorusToTurns ∘
      HGAS.Clocks.ErgodicControllerPhaseHaar.phaseProjection
  have hphaseInTurns : Continuous phaseInTurns :=
    HGAS.Clocks.PhaseTorusFlow.continuous_phaseTorusToTurns.comp
      HGAS.Clocks.ErgodicControllerPhaseHaar.continuous_phaseProjection
  have hbranchMeas : ∀ ε, MeasurableSet (branch ε) :=
    measurableSet_controllerSignBranch p
  have hbranchDisjoint : Pairwise (Disjoint on branch) :=
    pairwiseDisjoint_controllerSignBranch p hp
  have hfull :
      ∀ᵐ z ∂(μ : Measure (State d)), z ∈ ⋃ ε, branch ε := by
    simpa only [μInv, branch] using
      ae_mem_iUnion_controllerSignBranch p hp μInv
  have hconditional :
      ∀ ε : SignTuple d,
        Measure.map phaseInTurns
            ((μ : Measure (State d)).restrict (branch ε)) =
          (μ.toFiniteMeasure.restrict (branch ε)).mass •
            ((HGAS.Clocks.RadicalClock.torusHaarProbability (d := d) :
                ProbabilityMeasure (UnitAddTorus d)) :
              Measure (UnitAddTorus d)) := by
    intro ε
    let m : FiniteMeasure (State d) :=
      μ.toFiniteMeasure.restrict (branch ε)
    by_cases hm : m = 0
    · have hmass : m.mass = 0 := by simp [hm]
      have hmeasure : (m : Measure (State d)) = 0 := by simp [hm]
      change
        Measure.map phaseInTurns (m : Measure (State d)) =
          m.mass •
            ((HGAS.Clocks.RadicalClock.torusHaarProbability (d := d) :
                ProbabilityMeasure (UnitAddTorus d)) :
              Measure (UnitAddTorus d))
      rw [hmeasure, Measure.map_zero, hmass, zero_smul]
    · let ν : HGAS.Dynamics.InvariantProbabilityMeasure Φ :=
        HGAS.Dynamics.normalizeInvariantRestriction
          Φ μInv (branch ε) (hbranchMeas ε)
          (by
            simpa only [Φ, branch] using
              isInvariant_controllerSignBranch p hp ε)
          (by simpa only [μInv, m] using hm)
      have hνmem :
          ∀ᵐ z ∂(ν.measure : Measure (State d)), z ∈ branch ε := by
        exact HGAS.Dynamics.ae_mem_normalize_restrict
          μ.toFiniteMeasure (hbranchMeas ε)
          (by simpa only [m] using hm)
      have hhaarProbability :
          (ν.measure.map
              (HGAS.Clocks.ErgodicControllerPhaseHaar.continuous_phaseProjection
                (d := d)).measurable.aemeasurable).map
            (HGAS.Clocks.PhaseTorusFlow.continuous_phaseTorusToTurns
              |>.measurable.aemeasurable) =
            HGAS.Clocks.RadicalClock.torusHaarProbability := by
        apply phaseHaar_of_ae_mem_controllerSignBranch
          p hp hinjective ε ν
        simpa only [branch] using hνmem
      have hhaar :
          Measure.map phaseInTurns (ν.measure : Measure (State d)) =
            ((HGAS.Clocks.RadicalClock.torusHaarProbability (d := d) :
                ProbabilityMeasure (UnitAddTorus d)) :
              Measure (UnitAddTorus d)) := by
        have h := congrArg ProbabilityMeasure.toMeasure hhaarProbability
        simpa only [ProbabilityMeasure.toMeasure_map, phaseInTurns,
          Function.comp_apply, Measure.map_map
            (HGAS.Clocks.PhaseTorusFlow.continuous_phaseTorusToTurns
              |>.measurable)
            (HGAS.Clocks.ErgodicControllerPhaseHaar.continuous_phaseProjection
              (d := d)).measurable] using h
      have hmDecompose :
          (m : Measure (State d)) =
            m.mass • (ν.measure : Measure (State d)) := by
        have h :=
          congrArg FiniteMeasure.toMeasure
            m.self_eq_mass_smul_normalize
        simpa only [ν, HGAS.Dynamics.normalizeInvariantRestriction,
          μInv, m, FiniteMeasure.toMeasure_smul] using h
      change
        Measure.map phaseInTurns (m : Measure (State d)) =
          m.mass •
            ((HGAS.Clocks.RadicalClock.torusHaarProbability (d := d) :
                ProbabilityMeasure (UnitAddTorus d)) :
              Measure (UnitAddTorus d))
      rw [hmDecompose, Measure.map_smul, hhaar]
  apply ProbabilityMeasure.toMeasure_injective
  have hmap :
      Measure.map phaseInTurns (μ : Measure (State d)) =
        ((HGAS.Clocks.RadicalClock.torusHaarProbability (d := d) :
            ProbabilityMeasure (UnitAddTorus d)) :
          Measure (UnitAddTorus d)) := by
    rw [← Measure.restrict_eq_self_of_ae_mem hfull]
    rw [Measure.restrict_iUnion hbranchDisjoint hbranchMeas]
    rw [Measure.map_sum hphaseInTurns.measurable.aemeasurable]
    ext A hA
    rw [Measure.sum_apply _ hA]
    simp_rw [hconditional]
    simp only [Measure.smul_apply, FiniteMeasure.restrict_mass]
    simp_rw [ENNReal.smul_def, smul_eq_mul]
    rw [ENNReal.tsum_mul_right]
    have hunion :
        (μ : Measure (State d)) (⋃ ε, branch ε) = 1 := by
      have h :=
        (ae_mem_iff_measure_eq
          (MeasurableSet.iUnion hbranchMeas).nullMeasurableSet).mp hfull
      simpa only [measure_univ] using h
    have hmassMeasure :
        ∑' ε : SignTuple d, (μ : Measure (State d)) (branch ε) = 1 := by
      rw [← measure_iUnion hbranchDisjoint hbranchMeas]
      exact hunion
    have hmass :
        ∑' ε : SignTuple d,
          (μ.toFiniteMeasure (branch ε) : ENNReal) = 1 := by
      simpa only [ProbabilityMeasure.toFiniteMeasure_apply,
        ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
          hmassMeasure
    rw [hmass, one_mul]
  simpa only [ProbabilityMeasure.toMeasure_map, phaseInTurns,
    Measure.map_map
      (HGAS.Clocks.PhaseTorusFlow.continuous_phaseTorusToTurns
        |>.measurable)
      (HGAS.Clocks.ErgodicControllerPhaseHaar.continuous_phaseProjection
        (d := d)).measurable] using hmap

end HGAS.Clocks.NonergodicControllerPhaseHaar
