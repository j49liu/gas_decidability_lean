import HGAS.Dynamics.RenormalizedOrbitOccupations
import HGAS.MeasureTheory.TightFiniteFamily
import HGAS.MeasureTheory.TightSingletonSigmaCompact

/-!
# From eventual nonescape to tight integer occupations

A long-time nonescape estimate controls occupation probabilities only
after a starting time which may depend on the orbit.  Prokhorov's theorem,
however, asks for tightness of the entire sequence

```text
  mₙ = (1 / (n + 1)) ∫₀ⁿ⁺¹ δ_{ϕₜx} dt.
```

The missing bridge is elementary but worth recording explicitly.  Given
an error tolerance, nonescape supplies one compact set for the tail.
There are only finitely many occupations before the tail begins.  Each
of these is a finite Borel measure, hence is tight on a sigma-compact
Hausdorff space; finite union then supplies one compact set for the
initial segment.  The union of the tail compact and initial compact
controls every `mₙ`.

This argument is independent of horocycle geometry.
-/

namespace HGAS.Dynamics

open Filter Function _root_.MeasureTheory Set Topology

noncomputable section

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  [BorelSpace X] [T2Space X] [SigmaCompactSpace X]

/-- Eventual uniform nonescape of real-time occupations implies
tightness of the complete integer-time occupation family of every good
starting point. -/
theorem isTight_integerOrbitOccupation_range_of_uniformRealOccupationNonescape
    (ϕ : Flow ℝ X) (Good : X → Prop)
    (hnonescape : UniformRealOccupationNonescape ϕ Good)
    (x : X) (hx : Good x) :
    IsTightMeasureSet
      (Set.range
        (fun n : ℕ ↦
          (integerOrbitOccupationProbability ϕ x n :
            Measure X))) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨Ktail, hKtailCompact, htail⟩ :=
    hnonescape ε hε
  let T : ℕ → ℝ := fun n ↦ (n : ℝ) + 1
  have hTpos : ∀ n, 0 < T n := by
    intro n
    dsimp only [T]
    positivity
  have hTtop : Tendsto T atTop atTop := by
    exact
      tendsto_atTop_add_const_right atTop 1
        tendsto_natCast_atTop_atTop
  have hevent :=
    htail x hx T hTpos hTtop
  rw [eventually_atTop] at hevent
  obtain ⟨N, hN⟩ := hevent
  let occupationMeasure : ℕ → Measure X :=
    fun n ↦
      (integerOrbitOccupationProbability ϕ x n :
        Measure X)
  let initialMeasures : Set (Measure X) :=
    occupationMeasure '' {n : ℕ | n < N}
  have hprefixFinite : initialMeasures.Finite := by
    exact (Set.finite_Iio N).image occupationMeasure
  have hprefixSingleton :
      ∀ μ ∈ initialMeasures,
        IsTightMeasureSet ({μ} : Set (Measure X)) := by
    intro μ hμ
    obtain ⟨n, hn, rfl⟩ := hμ
    dsimp only [occupationMeasure]
    exact
      HGAS.MeasureTheory.isTightMeasureSet_singleton_of_sigmaCompact
        (integerOrbitOccupationProbability ϕ x n :
          Measure X)
  have hprefixTight : IsTightMeasureSet initialMeasures :=
    HGAS.MeasureTheory.isTightMeasureSet_of_finite_of_singletons
      hprefixFinite hprefixSingleton
  obtain ⟨Kprefix, hKprefixCompact, hprefixBound⟩ :=
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      hprefixTight) ε hε
  refine
    ⟨Ktail ∪ Kprefix,
      hKtailCompact.union hKprefixCompact, ?_⟩
  intro μ hμ
  obtain ⟨n, rfl⟩ := hμ
  by_cases hn : n < N
  · have hnPrefix : occupationMeasure n ∈ initialMeasures :=
      ⟨n, hn, rfl⟩
    exact
      (measure_mono
        (compl_subset_compl.mpr
          (subset_union_right :
            Kprefix ⊆ Ktail ∪ Kprefix))).trans
        (hprefixBound (occupationMeasure n) hnPrefix)
  · have hNn : N ≤ n := Nat.le_of_not_gt hn
    have hnTail := hN n hNn
    exact
      (measure_mono
        (compl_subset_compl.mpr
          (subset_union_left :
            Ktail ⊆ Ktail ∪ Kprefix))).trans
        (by
          simpa only [T, integerOrbitOccupationProbability,
            occupationMeasure] using hnTail)

end

end HGAS.Dynamics
