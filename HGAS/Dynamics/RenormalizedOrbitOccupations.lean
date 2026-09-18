import HGAS.Dynamics.RenormalizedPeriodicMassExclusion
import HGAS.Dynamics.TightOrbitOccupations

/-!
# Renormalized orbit occupations

This file records the elementary change-of-variables calculation behind
geodesic renormalization of horocycle occupation measures.

Suppose that a continuous map `A` intertwines a real flow `ϕ` with a
positive rescaling of time:

```text
  A (ϕ t x) = ϕ (c t) (A x),       c > 0.
```

Pushing the normalized occupation measure of the segment `(0,T]` through
`A` then gives exactly the normalized occupation measure of `(0,cT]`
starting at `A x`.  The normalization is important: it is precisely
preserved by the linear change of variables `u = c t`.

The result is abstract and is intended to be reused whenever a flow is
renormalized by another action.
-/

namespace HGAS.Dynamics

open Filter Function MeasureTheory Set Topology

noncomputable section

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [BorelSpace X]

/-- Positive linear dilation sends normalized Lebesgue measure on `(0,T]`
to normalized Lebesgue measure on `(0,cT]`. -/
theorem positiveIntervalProbability_map_mul_left
    (T c : ℝ) (hT : 0 < T) (hc : 0 < c) :
    (positiveIntervalProbability T hT).map
        (measurable_const_mul c).aemeasurable =
      positiveIntervalProbability (c * T) (mul_pos hc hT) := by
  apply ProbabilityMeasure.toMeasure_injective
  ext A hA
  rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (measurable_const_mul c) hA]
  simp only [positiveIntervalProbability, ProbabilityMeasure.coe_mk,
    Measure.smul_apply]
  rw [Measure.restrict_apply
    (hA.preimage (measurable_const_mul c))]
  rw [Measure.restrict_apply hA]
  have hcne : c ≠ 0 := ne_of_gt hc
  have hpreimage :
      (fun t : ℝ ↦ c * t) ⁻¹' A ∩ Ioc 0 T =
        (fun t : ℝ ↦ c * t) ⁻¹' (A ∩ Ioc 0 (c * T)) := by
    ext t
    simp only [mem_inter_iff, mem_preimage, mem_Ioc]
    constructor
    · rintro ⟨htA, ht0, htT⟩
      exact ⟨htA, mul_pos hc ht0, mul_le_mul_of_nonneg_left htT hc.le⟩
    · rintro ⟨htA, hct0, hctT⟩
      refine ⟨htA, ?_, ?_⟩
      · nlinarith
      · nlinarith
  rw [hpreimage, Real.volume_preimage_mul_left hcne]
  have hcabs : |c⁻¹| = c⁻¹ := abs_of_pos (inv_pos.mpr hc)
  rw [hcabs]
  change
    (ENNReal.ofReal T)⁻¹ *
        (ENNReal.ofReal c⁻¹ *
          volume (A ∩ Ioc 0 (c * T))) =
      (ENNReal.ofReal (c * T))⁻¹ *
        volume (A ∩ Ioc 0 (c * T))
  rw [ENNReal.ofReal_inv_of_pos hc,
    ENNReal.ofReal_mul hc.le]
  rw [ENNReal.mul_inv
    (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr hc))
    (Or.inl ENNReal.ofReal_ne_top)]
  ac_rfl

/-- Exact covariance of normalized occupation probabilities under a
positive time-renormalizing continuous map. -/
theorem map_orbitOccupationProbability_of_time_rescaling
    (ϕ : Flow ℝ X) (A : C(X, X)) (c : ℝ) (hc : 0 < c)
    (hcovariance :
      ∀ t x, A (ϕ t x) = ϕ (c * t) (A x))
    (x : X) (T : ℝ) (hT : 0 < T) :
    (orbitOccupationProbability ϕ x T hT).map
        A.continuous.measurable.aemeasurable =
      orbitOccupationProbability ϕ (A x) (c * T) (mul_pos hc hT) := by
  apply ProbabilityMeasure.toMeasure_injective
  let F : ℝ → X := fun t ↦ ϕ t x
  let G : ℝ → X := fun t ↦ ϕ t (A x)
  let D : ℝ → ℝ := fun t ↦ c * t
  have hF : Measurable F :=
    (ϕ.continuous continuous_id continuous_const).measurable
  have hG : Measurable G :=
    (ϕ.continuous continuous_id continuous_const).measurable
  have hD : Measurable D :=
    measurable_const_mul c
  change
    Measure.map A (Measure.map F
      (positiveIntervalProbability T hT : Measure ℝ)) =
      Measure.map G
        (positiveIntervalProbability (c * T) (mul_pos hc hT) :
          Measure ℝ)
  rw [Measure.map_map A.continuous.measurable hF]
  have hfunctions : A ∘ F = G ∘ D := by
    funext t
    exact hcovariance t x
  rw [hfunctions, ← Measure.map_map hG hD]
  congr 1
  exact congrArg
    (fun m : ProbabilityMeasure ℝ ↦ (m : Measure ℝ))
    (positiveIntervalProbability_map_mul_left T c hT hc)

section Nonescape

/-- Uniform finite-time nonescape for long real-time occupations.

The compact core is uniform in all starting points satisfying `Good`.
The time after which the estimate holds is allowed to depend on the
starting point and on the chosen sequence of durations.  This is the
quantifier pattern of the classical cusp estimate: the depth cutoff is
uniform, whereas the entrance time is not. -/
def UniformRealOccupationNonescape
    (ϕ : Flow ℝ X) (Good : X → Prop) : Prop :=
  ∀ ε : ENNReal, 0 < ε →
    ∃ K : Set X, IsCompact K ∧
      ∀ x : X, Good x →
        ∀ (T : ℕ → ℝ) (hTpos : ∀ j, 0 < T j),
          Tendsto T atTop atTop →
          ∀ᶠ j in atTop,
            (orbitOccupationProbability
                ϕ x (T j) (hTpos j) : Measure X) (Kᶜ) ≤ ε

/-- Uniform nonescape for weak limits of long real-time orbit
occupations.

The compact core may depend on the requested error, but is uniform in the
starting point satisfying `Good`.  The threshold at which a particular
orbit spends most of its time in that core is deliberately absent from
the definition: after passing to a weak limit, only the uniform core
matters.

This is the limit-measure formulation of the cusp estimate in
Hubbard--Miller Proposition 12. -/
def UniformRealOccupationLimitNonescape
    (ϕ : Flow ℝ X) (Good : X → Prop) : Prop :=
  ∀ ε : ENNReal, 0 < ε →
    ∃ K : Set X, IsCompact K ∧
      ∀ x : X, Good x →
        ∀ (T : ℕ → ℝ) (hTpos : ∀ j, 0 < T j)
          (μ : ProbabilityMeasure X),
          Tendsto T atTop atTop →
          Tendsto
            (fun j ↦
              orbitOccupationProbability
                ϕ x (T j) (hTpos j))
            atTop (𝓝 μ) →
          (μ : Measure X) (Kᶜ) ≤ ε

/-- The finite-time cusp estimate passes to every weak occupation limit.

The complement of a compact set is open.  The required inequality is
therefore exactly the open-set half of the Portmanteau theorem. -/
theorem uniformRealOccupationLimitNonescape_of_finiteTime
    (ϕ : Flow ℝ X) (Good : X → Prop)
    (hnonescape : UniformRealOccupationNonescape ϕ Good) :
    UniformRealOccupationLimitNonescape ϕ Good := by
  intro ε hε
  obtain ⟨K, hKcompact, hKbound⟩ :=
    hnonescape ε hε
  refine ⟨K, hKcompact, ?_⟩
  intro x hx T hTpos μ hTtop hμ
  have hopen : IsOpen (Kᶜ) :=
    hKcompact.isClosed.isOpen_compl
  have hportmanteau :
      (μ : Measure X) (Kᶜ) ≤
        atTop.liminf
          (fun j ↦
            (orbitOccupationProbability
              ϕ x (T j) (hTpos j) : Measure X) (Kᶜ)) :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      hμ hopen
  have hevent :
      ∀ᶠ j in atTop,
        (orbitOccupationProbability
            ϕ x (T j) (hTpos j) : Measure X) (Kᶜ) ≤ ε :=
    hKbound x hx T hTpos hTtop
  exact hportmanteau.trans
    (Filter.liminf_le_of_frequently_le' hevent.frequently)

/-- Uniform nonescape of long occupations implies tightness of all
renormalized pushforwards of every integer-occupation limit.

The proof has no geometry in it.  Its only ingredients are:

* exact covariance of occupation probabilities under time rescaling;
* continuity of pushforward in the weak topology;
* positivity of each time-rescaling factor.

This theorem isolates the precise bridge needed in the
Dani--Smillie/Hubbard--Miller periodic-mass argument. -/
theorem hasTightRenormalizationFamily_of_uniform_occupation_limit_nonescape
    (ϕ : Flow ℝ X)
    (Good : X → Prop)
    (A : ℕ → C(X, X))
    (c : ℕ → ℝ)
    (hc : ∀ n, 0 < c n)
    (hcovariance :
      ∀ n t x,
        A n (ϕ t x) = ϕ (c n * t) (A n x))
    (hGood : ∀ n x, Good x → Good (A n x))
    (hnonescape :
      UniformRealOccupationLimitNonescape ϕ Good)
    (x : X) (hx : Good x)
    (r : ℕ → ℕ) (μ : ProbabilityMeasure X)
    (hr : Tendsto r atTop atTop)
    (hμ :
      Tendsto
        (integerOrbitOccupationProbability ϕ x ∘ r)
        atTop (𝓝 μ)) :
    HasTightRenormalizationFamily μ A := by
  rw [HasTightRenormalizationFamily,
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨K, hKcompact, hKbound⟩ :=
    hnonescape ε hε
  refine ⟨K, hKcompact, ?_⟩
  intro ν hν
  obtain ⟨n, rfl⟩ := hν
  let L : ℕ → ℝ :=
    fun j ↦ c n * ((r j : ℝ) + 1)
  have hLpos : ∀ j, 0 < L j := by
    intro j
    exact mul_pos (hc n) (by positivity)
  have hrReal :
      Tendsto (fun j ↦ (r j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hr
  have hLtop : Tendsto L atTop atTop := by
    exact
      (tendsto_atTop_add_const_right atTop 1 hrReal).const_mul_atTop
        (hc n)
  let μn : ProbabilityMeasure X :=
    μ.map (A n).continuous.measurable.aemeasurable
  have hmap :
      Tendsto
        (fun j ↦
          ((integerOrbitOccupationProbability ϕ x (r j)).map
            (A n).continuous.measurable.aemeasurable))
        atTop (𝓝 μn) := by
    exact
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        (integerOrbitOccupationProbability ϕ x ∘ r)
        μ hμ (A n).continuous
  have hrenormalized :
      Tendsto
        (fun j ↦
          orbitOccupationProbability
            ϕ (A n x) (L j) (hLpos j))
        atTop (𝓝 μn) := by
    apply hmap.congr'
    filter_upwards with j
    apply
      map_orbitOccupationProbability_of_time_rescaling
        ϕ (A n) (c n) (hc n)
        (hcovariance n) x ((r j : ℝ) + 1) (by positivity)
  have hbound :
      (μn : Measure X) (Kᶜ) ≤ ε :=
    hKbound (A n x) (hGood n x hx)
      L hLpos μn hLtop hrenormalized
  exact hbound

end Nonescape

end

end HGAS.Dynamics
