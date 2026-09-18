import HGAS.Dynamics.UniformNegativeBlocks
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Metrizable.Basic

/-!
# Excluding periodic mass by a contracting renormalization

This file isolates the measure-theoretic core of the periodic-mass
exclusion argument used for horocycle flows.

Let `ϕ` be a continuous real flow.  Suppose that continuous maps `A n`
renormalize periods by positive factors `c n` tending arbitrarily close
to zero.  A compact set cannot contain points with arbitrarily short
positive periods.  Consequently, if the family of pushforwards
`(A n)₊ μ` is tight, then `μ` gives zero mass to the periodic points.

There is a small but important point in the proof.  The periodic set need
not be closed.  We write it as a countable union of **closed bounded-period
strata**

```text
  {x | some period T lies in [1/(k+1), m]}.
```

If the periodic set has positive measure, one such stratum has positive
measure.  Inner regularity then supplies a positive-measure compact subset
of that fixed stratum.  This bounded-period choice is what makes one
renormalization time work uniformly on the compact subset.

The result is abstract and reusable.  For the horocycle flow, `A n` is
positive geodesic time and `c n = exp(-n)`.
-/

namespace HGAS.Dynamics

open Filter Function MeasureTheory Set Topology

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- The set of points possessing a positive period for a real flow. -/
def periodicPointSet (ϕ : Flow ℝ X) : Set X :=
  {x | ∃ T : ℝ, 0 < T ∧ ϕ T x = x}

/-- Points admitting a period in the closed interval `[a,b]`. -/
def periodStratum (ϕ : Flow ℝ X) (a b : ℝ) : Set X :=
  {x | ∃ T ∈ Icc a b, ϕ T x = x}

/-- A period stratum over a compact time interval is closed. -/
theorem isClosed_periodStratum
    [T2Space X] (ϕ : Flow ℝ X) (a b : ℝ) :
    IsClosed (periodStratum ϕ a b) := by
  let Z : Set (Icc a b × X) :=
    {p | ϕ p.1.1 p.2 = p.2}
  have hZ : IsClosed Z := by
    exact isClosed_eq
      (ϕ.continuous
        (continuous_subtype_val.comp continuous_fst)
        continuous_snd)
      continuous_snd
  have hproj : IsClosed (Prod.snd '' Z) :=
    isClosedMap_snd_of_compactSpace Z hZ
  convert hproj using 1
  ext x
  simp only [periodStratum, mem_setOf_eq, mem_image, Z]
  constructor
  · rintro ⟨T, hT, hperiod⟩
    exact ⟨(⟨T, hT⟩, x), hperiod, rfl⟩
  · rintro ⟨p, hperiod, rfl⟩
    exact ⟨p.1.1, p.1.2, hperiod⟩

/-- The positive-period set is a countable union of closed strata whose
periods have both a positive lower bound and a finite upper bound. -/
theorem periodicPointSet_eq_iUnion_periodStratum
    (ϕ : Flow ℝ X) :
    periodicPointSet ϕ =
      ⋃ k : ℕ, ⋃ m : ℕ,
        periodStratum ϕ (1 / (k + 1 : ℝ)) (m : ℝ) := by
  ext x
  constructor
  · rintro ⟨T, hT, hperiod⟩
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hT
    obtain ⟨m, hm⟩ := exists_nat_gt T
    apply mem_iUnion.2
    refine ⟨k, mem_iUnion.2 ⟨m, ?_⟩⟩
    exact ⟨T, ⟨hk.le, hm.le⟩, hperiod⟩
  · intro hx
    obtain ⟨k, m, T, hT, hperiod⟩ := by
      simpa only [mem_iUnion, periodStratum, mem_setOf_eq] using hx
    refine ⟨T, ?_, hperiod⟩
    exact lt_of_lt_of_le
      (one_div_pos.mpr (by positivity))
      hT.1

/-- Compact sets have a positive period systole for `ϕ`: sufficiently
short positive periods do not occur on the compact set.

This property is automatic for the horocycle action on a quotient by a
discrete group, but it is stated abstractly here so the mass-exclusion
argument can be reused for other locally free flows. -/
def HasCompactPeriodSystole (ϕ : Flow ℝ X) : Prop :=
  ∀ K : Set X, IsCompact K →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ K, ∀ T : ℝ,
        0 < T → T ≤ δ → ϕ T x ≠ x

section Measure

variable [MeasurableSpace X] [BorelSpace X] [T2Space X]
variable [TopologicalSpace.PseudoMetrizableSpace X]
variable [SigmaCompactSpace X]

/-- The measure obtained by continuously pushing `μ` through `A`. -/
def continuousPushforwardMeasure
    (μ : ProbabilityMeasure X) (A : C(X, X)) :
    Measure X :=
  Measure.map A (μ : Measure X)

/-- A probability has a tight renormalization family when all of its
pushforwards under the specified continuous renormalizers are uniformly
tight. -/
def HasTightRenormalizationFamily
    (μ : ProbabilityMeasure X) (A : ℕ → C(X, X)) : Prop :=
  IsTightMeasureSet
    (Set.range (fun n ↦ continuousPushforwardMeasure μ (A n)))

/-- **Renormalized periodic-mass exclusion.**

Assume:

* compact sets have a positive lower bound on positive periods;
* `A n` sends a period `T` to the period `c n * T`;
* the factors `c n` are positive and become arbitrarily small;
* the family `(A n)₊ μ` is tight.

Then `μ` gives zero mass to every positive-period point.
-/
theorem measure_periodicPointSet_eq_zero_of_tight_renormalization
    (ϕ : Flow ℝ X)
    (μ : ProbabilityMeasure X)
    (A : ℕ → C(X, X))
    (c : ℕ → ℝ)
    (hsystole : HasCompactPeriodSystole ϕ)
    (hperiod :
      ∀ n x T, ϕ T x = x →
        ϕ (c n * T) (A n x) = A n x)
    (hcpos : ∀ n, 0 < c n)
    (hcsmall :
      ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, c n < ε)
    (htight : HasTightRenormalizationFamily μ A) :
    (μ : Measure X) (periodicPointSet ϕ) = 0 := by
  rw [periodicPointSet_eq_iUnion_periodStratum]
  apply measure_iUnion_null
  intro k
  apply measure_iUnion_null
  intro m
  let S : Set X :=
    periodStratum ϕ (1 / (k + 1 : ℝ)) (m : ℝ)
  have hSclosed : IsClosed S :=
    isClosed_periodStratum ϕ _ _
  by_contra hSμ
  have hSpos : 0 < (μ : Measure X) S :=
    pos_iff_ne_zero.mpr hSμ
  obtain ⟨K, hKS, hKcompact, hKpos⟩ :=
    hSclosed.measurableSet.exists_lt_isCompact hSpos
  obtain ⟨ε, hεpos, hεlt⟩ :
      ∃ ε : ENNReal, 0 < ε ∧ ε < (μ : Measure X) K :=
    exists_between hKpos
  obtain ⟨C, hCcompact, hCbound⟩ :=
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      htight) ε hεpos
  obtain ⟨δ, hδpos, hδ⟩ := hsystole C hCcompact
  have hmpos : 0 < (m + 1 : ℝ) := by positivity
  obtain ⟨n, hnsmall⟩ :=
    hcsmall (δ / (m + 1 : ℝ)) (div_pos hδpos hmpos)
  have hnscale :
      c n * (m : ℝ) < δ := by
    calc
      c n * (m : ℝ) ≤ c n * (m + 1 : ℝ) := by
        gcongr
        · exact (hcpos n).le
        · norm_num
      _ < (δ / (m + 1 : ℝ)) * (m + 1 : ℝ) := by
        gcongr
      _ = δ := by field_simp
  have hKpreimage :
      K ⊆ (A n) ⁻¹' Cᶜ := by
    intro x hxK
    have hxS := hKS hxK
    obtain ⟨T, hT, hTperiod⟩ := hxS
    have hcTpos : 0 < c n * T :=
      mul_pos (hcpos n) (lt_of_lt_of_le (by positivity) hT.1)
    have hcTle : c n * T ≤ δ := by
      exact (mul_le_mul_of_nonneg_left hT.2 (hcpos n).le).trans
        hnscale.le
    by_contra hxpre
    have hxC : A n x ∈ C := by
      simpa only [mem_preimage, mem_compl_iff, not_not] using hxpre
    exact
      (hδ (A n x) hxC (c n * T) hcTpos hcTle)
        (hperiod n x T hTperiod)
  have hmapBound :
      continuousPushforwardMeasure μ (A n) (Cᶜ) ≤ ε := by
    apply hCbound
    exact ⟨n, rfl⟩
  have hKle :
      (μ : Measure X) K ≤
        continuousPushforwardMeasure μ (A n) (Cᶜ) := by
    rw [continuousPushforwardMeasure,
      Measure.map_apply (A n).continuous.measurable
        hCcompact.isClosed.measurableSet.compl]
    exact measure_mono hKpreimage
  have hKleε : (μ : Measure X) K ≤ ε :=
    hKle.trans hmapBound
  exact (not_le_of_gt hεlt) hKleε

end Measure

end

end HGAS.Dynamics
