import HGAS.Modular.GammaTwoFrameQuotient
import HGAS.Dynamics.ErgodicInvariantProbability
import HGAS.Dynamics.PeriodicOrbitMeasure
import Mathlib.Dynamics.Ergodic.Action.Basic
import Mathlib.Tactic

/-!
# The exact invariant-measure interface for the level-two horocycle flow

This file separates the elementary measure-theoretic reductions from the
Dani invariant-measure and Dani--Smillie orbit-classification results.

The formal boundary is deliberately sharp:

* `IsRightInvariantFrameProbability` is the intrinsic definition of the
  normalized Haar probability on `Γ(2) \ SL(2, ℝ)`;
* `IsClosedHorocycleProbability` says that an invariant probability is
  carried by one periodic horocycle;
* `DaniSmillieClassification` is the precise periodic-or-Haar assertion;
* all changes of nonzero time scale and all implications from frame-Haar
  invariance to horocycle invariance are proved below.

This foundational interface file itself does not prove
`DaniSmillieClassification`; it keeps the proposition named rather than
introducing it as an axiom or an opaque compiler hypothesis.  The completed
project proves the required level-two instance downstream in
`HGAS.Modular.GammaTwoOffPeriodicUnique`, culminating in
`gammaTwoDaniSmillieTheorem_unconditional`.
-/

namespace HGAS.Modular

open Function MeasureTheory Set

noncomputable section

variable {X : Type*} [TopologicalSpace X]
  [MeasurableSpace X] [BorelSpace X]

namespace Dynamics

/-- Invariance is unchanged by a nonzero linear reparameterization of
time. -/
theorem isInvariantProbability_scaled_iff
    (ϕ : Flow ℝ X) {s : ℝ} (hs : s ≠ 0)
    (μ : ProbabilityMeasure X) :
    HGAS.Dynamics.IsInvariantProbability
        { toFun := fun t x ↦ ϕ (s * t) x
          cont' :=
            ϕ.continuous
              (continuous_const.mul continuous_fst)
              continuous_snd
          map_add' := by
            intro t u x
            rw [mul_add, ϕ.map_add]
          map_zero' := by
            intro x
            simp only [mul_zero, ϕ.map_zero_apply] }
        μ ↔
      HGAS.Dynamics.IsInvariantProbability ϕ μ := by
  constructor
  · intro h t
    have hscaled := h (t / s)
    simpa only [HGAS.Dynamics.timePushforward,
      mul_div_cancel₀ t hs] using hscaled
  · intro h t
    exact h (s * t)

/-- Ergodicity is unchanged by a nonzero linear reparameterization of
time. -/
theorem isErgodicInvariantProbability_scaled_iff
    (ϕ : Flow ℝ X) {s : ℝ} (hs : s ≠ 0)
    (μ : ProbabilityMeasure X) :
    HGAS.Dynamics.IsErgodicInvariantProbability
        { toFun := fun t x ↦ ϕ (s * t) x
          cont' :=
            ϕ.continuous
              (continuous_const.mul continuous_fst)
              continuous_snd
          map_add' := by
            intro t u x
            rw [mul_add, ϕ.map_add]
          map_zero' := by
            intro x
            simp only [mul_zero, ϕ.map_zero_apply] }
        μ ↔
      HGAS.Dynamics.IsErgodicInvariantProbability ϕ μ := by
  let ψ : Flow ℝ X :=
    { toFun := fun t x ↦ ϕ (s * t) x
      cont' :=
        ϕ.continuous
          (continuous_const.mul continuous_fst)
          continuous_snd
      map_add' := by
        intro t u x
        rw [mul_add, ϕ.map_add]
      map_zero' := by
        intro x
        simp only [mul_zero, ϕ.map_zero_apply] }
  have hinvariant :
      HGAS.Dynamics.IsInvariantProbability ψ μ ↔
        HGAS.Dynamics.IsInvariantProbability ϕ μ :=
    isInvariantProbability_scaled_iff ϕ hs μ
  constructor
  · intro h
    refine ⟨hinvariant.mp h.1, ?_⟩
    intro A hA hAinv
    apply h.2 A hA
    intro t
    exact hAinv (s * t)
  · intro h
    refine ⟨hinvariant.mpr h.1, ?_⟩
    intro A hA hAinv
    apply h.2 A hA
    intro t
    have hpre := hAinv (t / s)
    convert hpre using 1
    field_simp

end Dynamics

/-! ## Closed and Haar alternatives -/

/-- A point lies on a periodic orbit of the scale-`s` horocycle flow. -/
def IsPeriodicHorocyclePoint
    (s : ℝ) (q : GammaTwoFrameQuotient) : Prop :=
  ∃ T : ℝ, 0 < T ∧
    scaledGammaTwoHorocycleFlow s T q = q

/-- A probability is carried by one periodic horocycle.

When combined with `HGAS.Dynamics.IsErgodicInvariantProbability`, invariance
forces this measure to be normalized arclength on that orbit.  The support
formulation is the one needed for the classification statement and does
not presuppose a choice of a least positive period. -/
def IsClosedHorocycleProbability
    (s : ℝ)
    (μ : ProbabilityMeasure GammaTwoFrameQuotient) : Prop :=
  ∃ q : GammaTwoFrameQuotient,
    IsPeriodicHorocyclePoint s q ∧
      (μ : Measure GammaTwoFrameQuotient)
          (Flow.orbit
            (scaledGammaTwoHorocycleFlow s) q) = 1

/-- The normalized arclength probability attached to an explicitly
periodic scale-`s` horocycle. -/
def closedHorocycleInvariantProbability
    (s : ℝ) (q : GammaTwoFrameQuotient)
    {T : ℝ} (hT : 0 < T)
    (hperiod :
      scaledGammaTwoHorocycleFlow s T q = q) :
    Dynamics.InvariantProbabilityMeasure
      (scaledGammaTwoHorocycleFlow s) :=
  Dynamics.periodicOrbitInvariantProbability
    (scaledGammaTwoHorocycleFlow s) q hT hperiod

/-- The canonical arclength construction really belongs to the closed
horocycle alternative. -/
theorem closedHorocycleInvariantProbability_isClosed
    (s : ℝ) (q : GammaTwoFrameQuotient)
    {T : ℝ} (hT : 0 < T)
    (hperiod :
      scaledGammaTwoHorocycleFlow s T q = q) :
    IsClosedHorocycleProbability s
      (closedHorocycleInvariantProbability
        s q hT hperiod).measure := by
  refine ⟨q, ⟨T, hT, hperiod⟩, ?_⟩
  exact Dynamics.periodicOrbitInvariantProbability_orbit_mass
    (scaledGammaTwoHorocycleFlow s) q hT hperiod

/-- Exact normalized-arclength form of the closed horocycle alternative. -/
def IsNormalizedClosedHorocycleProbability
    (s : ℝ)
    (μ : ProbabilityMeasure GammaTwoFrameQuotient) : Prop :=
  ∃ q : GammaTwoFrameQuotient,
    ∃ T : ℝ, ∃ hT : 0 < T,
      ∃ hperiod :
        scaledGammaTwoHorocycleFlow s T q = q,
        μ =
          (closedHorocycleInvariantProbability
            s q hT hperiod).measure

/-- Exact normalized arclength implies the support-form closed-orbit
alternative. -/
theorem IsNormalizedClosedHorocycleProbability.isClosed
    {s : ℝ}
    {μ : ProbabilityMeasure GammaTwoFrameQuotient}
    (hμ : IsNormalizedClosedHorocycleProbability s μ) :
    IsClosedHorocycleProbability s μ := by
  obtain ⟨q, T, hT, hperiod, rfl⟩ := hμ
  exact closedHorocycleInvariantProbability_isClosed
    s q hT hperiod

/-- Conversely, invariance plus full mass on a periodic horocycle forces
the unique normalized arclength probability. -/
theorem normalizedClosedHorocycleProbability_of_isClosed
    {s : ℝ}
    (μ :
      Dynamics.InvariantProbabilityMeasure
        (scaledGammaTwoHorocycleFlow s))
    (hμ : IsClosedHorocycleProbability s μ.measure) :
    IsNormalizedClosedHorocycleProbability s μ.measure := by
  obtain ⟨q, ⟨T, hT, hperiod⟩, hmass⟩ := hμ
  refine ⟨q, T, hT, hperiod, ?_⟩
  exact Dynamics.invariantProbability_eq_periodicOrbitInvariantProbability
    (scaledGammaTwoHorocycleFlow s) q hT hperiod μ hmass

/-- A probability on the frame quotient is normalized frame Haar measure
if it is invariant under every descended right translation.

This is an intrinsic definition: it does not depend on a fundamental
domain or Iwasawa coordinates. -/
def IsRightInvariantFrameProbability
    (ν : ProbabilityMeasure GammaTwoFrameQuotient) : Prop :=
  ∀ a : RealModularFrame,
    ν.map
        (gammaTwoFrameRightMul_continuous a).measurable.aemeasurable =
      ν

/-- A right-invariant frame probability is invariant under the unscaled
horocycle flow. -/
theorem IsRightInvariantFrameProbability.horocycleInvariant
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν) :
    Dynamics.IsInvariantProbability gammaTwoHorocycleFlow ν := by
  intro t
  simpa only [Dynamics.timePushforward,
    gammaTwoHorocycleFlow_eq_rightMul] using
      hν (upperUnipotent t)

/-- A right-invariant frame probability is invariant under every scaled
horocycle flow, including the zero scale. -/
theorem IsRightInvariantFrameProbability.scaledHorocycleInvariant
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν)
    (s : ℝ) :
    Dynamics.IsInvariantProbability
      (scaledGammaTwoHorocycleFlow s) ν := by
  intro t
  change
    Dynamics.timePushforward gammaTwoHorocycleFlow ν
        (s * t) = ν
  exact hν.horocycleInvariant (s * t)

/-- The exact Dani--Smillie periodic-or-Haar assertion on the level-two
frame quotient.

The proposition is parameterized by a chosen normalized frame-Haar
probability `ν`.  This cleanly separates finite covolume/existence of Haar
probability from the deep classification of the ergodic invariant
probabilities. -/
def DaniSmillieClassification
    (ν : ProbabilityMeasure GammaTwoFrameQuotient) : Prop :=
  IsRightInvariantFrameProbability ν ∧
    ∀ μ : ProbabilityMeasure GammaTwoFrameQuotient,
      HGAS.Dynamics.IsErgodicInvariantProbability
          gammaTwoHorocycleFlow μ →
        IsClosedHorocycleProbability 1 μ ∨ μ = ν

/-- Finite covolume, formulated only at the measure-theoretic level needed
by the reduction. -/
def GammaTwoHasFiniteFrameVolume : Prop :=
  ∃ ν : ProbabilityMeasure GammaTwoFrameQuotient,
    IsRightInvariantFrameProbability ν

/-- The complete classification package is the existence of normalized
frame Haar probability together with the periodic-or-Haar classification. -/
def GammaTwoDaniSmillieTheorem : Prop :=
  ∃ ν : ProbabilityMeasure GammaTwoFrameQuotient,
    DaniSmillieClassification ν

/-! ## Scale reduction -/

private theorem gammaTwoHorocycle_period_neg
    {q : GammaTwoFrameQuotient} {T : ℝ}
    (hT : gammaTwoHorocycleFlow T q = q) :
    gammaTwoHorocycleFlow (-T) q = q := by
  have h :=
    congrArg (gammaTwoHorocycleFlow (-T)) hT
  have hzero :
      gammaTwoHorocycleFlow (-T)
          (gammaTwoHorocycleFlow T q) = q := by
    rw [← gammaTwoHorocycleFlow.map_add]
    simp only [neg_add_cancel,
      gammaTwoHorocycleFlow.map_zero_apply]
  exact h.symm.trans hzero

/-- Periodicity at a nonzero scale is equivalent to periodicity for the
unit-speed horocycle flow. -/
theorem isPeriodicHorocyclePoint_iff_of_ne_zero
    {s : ℝ} (hs : s ≠ 0)
    (q : GammaTwoFrameQuotient) :
    IsPeriodicHorocyclePoint s q ↔
      IsPeriodicHorocyclePoint 1 q := by
  constructor
  · rintro ⟨T, hT, hperiod⟩
    change gammaTwoHorocycleFlow (s * T) q = q at hperiod
    by_cases hspos : 0 < s
    · refine ⟨s * T, mul_pos hspos hT, ?_⟩
      rw [scaledGammaTwoHorocycleFlow_one]
      change gammaTwoHorocycleFlow (s * T) q = q
      exact hperiod
    · have hsneg : s < 0 := lt_of_le_of_ne
          (le_of_not_gt hspos) hs
      refine ⟨(-s) * T, mul_pos (neg_pos.mpr hsneg) hT, ?_⟩
      rw [scaledGammaTwoHorocycleFlow_one]
      change
        gammaTwoHorocycleFlow ((-s) * T) q = q
      have hbackward :=
        gammaTwoHorocycle_period_neg hperiod
      have heq : (-s) * T = -(s * T) := by ring
      rw [heq]
      exact hbackward
  · rintro ⟨T, hT, hperiod⟩
    rw [scaledGammaTwoHorocycleFlow_one] at hperiod
    change gammaTwoHorocycleFlow T q = q at hperiod
    by_cases hspos : 0 < s
    · refine ⟨T / s, div_pos hT hspos, ?_⟩
      change
        gammaTwoHorocycleFlow (s * (T / s)) q = q
      rw [mul_div_cancel₀ T hs]
      exact hperiod
    · have hsneg : s < 0 := lt_of_le_of_ne
          (le_of_not_gt hspos) hs
      refine ⟨T / (-s), div_pos hT (neg_pos.mpr hsneg), ?_⟩
      have hbackward :=
        gammaTwoHorocycle_period_neg hperiod
      have hscale : s * (T / -s) = -T := by
        field_simp
      change
        gammaTwoHorocycleFlow (s * (T / -s)) q = q
      rw [hscale]
      exact hbackward

/-- The set-theoretic orbit is unchanged by a nonzero scale. -/
theorem scaledGammaTwoHorocycleFlow_orbit_eq
    {s : ℝ} (hs : s ≠ 0)
    (q : GammaTwoFrameQuotient) :
    Flow.orbit (scaledGammaTwoHorocycleFlow s) q =
      Flow.orbit gammaTwoHorocycleFlow q := by
  ext y
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨s * t, ?_⟩
    change
      gammaTwoHorocycleFlow (s * t) q = y
    change
      gammaTwoHorocycleFlow (s * t) q = y at ht
    exact ht
  · rintro ⟨t, ht⟩
    refine ⟨t / s, ?_⟩
    change
      gammaTwoHorocycleFlow (s * (t / s)) q = y
    rw [mul_div_cancel₀ t hs]
    exact ht

/-- The closed-orbit alternative is independent of a nonzero time scale. -/
theorem isClosedHorocycleProbability_iff_of_ne_zero
    {s : ℝ} (hs : s ≠ 0)
    (μ : ProbabilityMeasure GammaTwoFrameQuotient) :
    IsClosedHorocycleProbability s μ ↔
      IsClosedHorocycleProbability 1 μ := by
  constructor <;>
    rintro ⟨q, hperiod, hsupport⟩ <;>
    refine ⟨q, ?_, ?_⟩
  · exact (isPeriodicHorocyclePoint_iff_of_ne_zero hs q).mp
      hperiod
  · rw [scaledGammaTwoHorocycleFlow_one,
      ← scaledGammaTwoHorocycleFlow_orbit_eq hs]
    exact hsupport
  · exact (isPeriodicHorocyclePoint_iff_of_ne_zero hs q).mpr
      hperiod
  · rw [scaledGammaTwoHorocycleFlow_one] at hsupport
    rw [scaledGammaTwoHorocycleFlow_orbit_eq hs]
    exact hsupport

/-- Dani--Smillie at unit speed implies the same classification at every
fixed nonzero scale. -/
theorem DaniSmillieClassification.classify_at_nonzero_scale
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hDS : DaniSmillieClassification ν)
    {s : ℝ} (hs : s ≠ 0)
    (μ : ProbabilityMeasure GammaTwoFrameQuotient)
    (hμ :
      HGAS.Dynamics.IsErgodicInvariantProbability
        (scaledGammaTwoHorocycleFlow s) μ) :
    IsClosedHorocycleProbability s μ ∨ μ = ν := by
  have hunit :
      HGAS.Dynamics.IsErgodicInvariantProbability
        gammaTwoHorocycleFlow μ := by
    have hiff :=
      Dynamics.isErgodicInvariantProbability_scaled_iff
        gammaTwoHorocycleFlow hs μ
    exact hiff.mp hμ
  rcases hDS.2 μ hunit with hclosed | hhaar
  · exact Or.inl
      ((isClosedHorocycleProbability_iff_of_ne_zero
        hs μ).mpr hclosed)
  · exact Or.inr hhaar

/-- Exact version of the preceding theorem: on the periodic branch the
measure is the canonical normalized arclength probability, not merely a
probability with full orbit mass. -/
theorem DaniSmillieClassification.classify_exact_at_nonzero_scale
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hDS : DaniSmillieClassification ν)
    {s : ℝ} (hs : s ≠ 0)
    (μ : ProbabilityMeasure GammaTwoFrameQuotient)
    (hμ :
      HGAS.Dynamics.IsErgodicInvariantProbability
        (scaledGammaTwoHorocycleFlow s) μ) :
    IsNormalizedClosedHorocycleProbability s μ ∨ μ = ν := by
  rcases hDS.classify_at_nonzero_scale hs μ hμ with
      hclosed | hhaar
  · left
    let μInvariant :
        Dynamics.InvariantProbabilityMeasure
          (scaledGammaTwoHorocycleFlow s) :=
      ⟨μ, hμ.invariant⟩
    exact normalizedClosedHorocycleProbability_of_isClosed
      μInvariant hclosed
  · exact Or.inr hhaar

end

end HGAS.Modular
