import Stability.Selection.OrdinaryTimeBaseChart
import Stability.Selection.OrdinaryTimeAverageHorizon

/-!
# A generic finite-chart orbit from a compact-base measure

An ergodic invariant probability giving full mass to the finite central
chart and zero mean to every compact drift coordinate supplies one
forward-recurrent orbit with a global physical clock and full real-horizon
drift averages. A nonnegative zero-mean coordinate vanishes along its
entire orbit. No recurrent or generic orbit is assumed as input.

See Section 9, Lemma `lem:selectedorbit`.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Dynamics HGAS.CompactAccumulatorPipelineCode
open HGAS.CompactAccumulatorPipelineCode.AllAffineCompactSourceChart (layout affineSpeed)
open HGAS.CompactAccumulatorPipelineCode.AllAffineCompactBaseChartTrajectory
open Filter Topology MeasureTheory Set
open scoped BoundedContinuousFunction

variable {n m : ℕ}

/-- A single actual compact drift coordinate as a bounded observable. -/
def ordinaryBaseDriftCoordinate (K : ℕ) (κ : RationalCode)
    (h : Fin m → PolynomialCode n) (q : Fin m) : BaseSpace (layout n) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun b ↦ baseDriftBCF (layout n) (2 * K) κ h b q,
      (continuous_apply q).comp (baseDriftBCF (layout n) (2 * K) κ h).continuous⟩

/-- The actual base flow restricted to its invariant finite chart. -/
def ordinaryBaseFiniteFlow (E K : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j)) : Flow ℝ (FiniteBaseSpace n) :=
  (baseFlow (layout n) E (2 * K) P).restrict
    (ordinaryBase_finiteInterior_invariant E K P hP)

/-- The orbit data constructed from the compact-base measure. The clock
is the unmodified even central power, with full ordinary compact-time
means and only forward recurrence. -/
structure OrdinaryTimeBaseOrbit (E K : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
    (κ : RationalCode) (h : Fin m → PolynomialCode n) (q₀ : Fin m) where
  point : FiniteBaseSpace n
  speedMean : ℝ
  speedMean_pos : 0 < speedMean
  clock : PositiveIntegralClock (fun t ↦ ordinaryBaseSpeed K
    (ordinaryBaseFiniteFlow E K P hP t point).1)
  recurrent : ForwardRecurrentAt (fun t ↦ ordinaryBaseFiniteFlow E K P hP t point) 0
  zeroCoordinate : ∀ t, ordinaryBaseDriftCoordinate K κ h q₀
    (ordinaryBaseFiniteFlow E K P hP t point).1 = 0
  speed_generic : Tendsto (fun T : ℝ ↦ T⁻¹ * integralClock (fun t ↦ ordinaryBaseSpeed K
    (ordinaryBaseFiniteFlow E K P hP t point).1) T) atTop (𝓝 speedMean)
  drift_generic : ∀ q, Tendsto (fun T : ℝ ↦ T⁻¹ * ∫ t in (0 : ℝ)..T,
    ordinaryBaseDriftCoordinate K κ h q (ordinaryBaseFiniteFlow E K P hP t point).1)
    atTop (𝓝 0)

/-- The measure assumptions of the selected-orbit lemma construct all
the recurrent, generic, and clock data on a single actual base orbit. -/
theorem exists_ordinaryTimeBaseOrbit
    (E K : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
    (κ : RationalCode) (hκ : 0 ≤ (κ.decode : ℝ)) (h : Fin m → PolynomialCode n)
    (hh : ∀ q, MixedCentralPolynomialCode.TermsAffineBlockDegreeLE (layout n) (2 * K) (h q))
    (q₀ : Fin m)
    (hq₀ : ∀ x : Fin n → ℝ,
      0 ≤ MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x (PolynomialCode.decode (h q₀)))
    (μ : InvariantProbabilityMeasure (baseFlow (layout n) E (2 * K) P))
    (hμ : IsErgodicInvariantProbability (baseFlow (layout n) E (2 * K) P) μ.measure)
    (hfull : (μ.measure : Measure (BaseSpace (layout n))) (finiteInterior (n := n)) = 1)
    (hzero : ∀ q, (∫ b, baseDriftBCF (layout n) (2 * K) κ h b q
      ∂(μ.measure : Measure (BaseSpace (layout n)))) = 0) :
    Nonempty (OrdinaryTimeBaseOrbit E K P hP κ h q₀) := by
  let hs := ordinaryBase_finiteInterior_measurable (n := n)
  let hinv := ordinaryBase_finiteInterior_invariant E K P hP
  let ν := μ.restrictToFullMeasureInvariant hs hfull hinv
  have hν : IsErgodicInvariantProbability (ordinaryBaseFiniteFlow E K P hP) ν.measure :=
    hμ.restrictToFullMeasureInvariant μ hs hfull hinv
  let s := subtypeObservable (ordinaryBaseSpeed (n := n) K) finiteInterior
  let g := fun q ↦ subtypeObservable (ordinaryBaseDriftCoordinate K κ h q) finiteInterior
  have hz (q : Fin m) : (∫ b, g q b ∂(ν.measure : Measure (FiniteBaseSpace n))) = 0 := by
    change observableAverage (subtypeObservable (ordinaryBaseDriftCoordinate K κ h q)
      finiteInterior) ν.measure = 0
    rw [observableAverage_restrictToFullMeasureInvariant μ hs hfull hinv]
    exact hzero q
  have hg : ∀ b : FiniteBaseSpace n, 0 ≤ g q₀ b := by
    intro b
    change 0 ≤ baseDriftBCF (layout n) (2 * K) κ h b.1 q₀
    rw [baseDriftBCF_eq K κ h hh]
    exact mul_nonneg (mul_nonneg hκ (AllAffineCompactSourceChart.affineSpeed_nonneg K _))
      (hq₀ _)
  let c := ∫ b, s b ∂(ν.measure : Measure (FiniteBaseSpace n))
  have hc : 0 < c := by
    apply integral_pos_iff_support_of_nonneg
      (fun b ↦ (ordinaryBaseSpeed_pos K b).le) (ν.integrable_boundedContinuous s) |>.mpr
    have hsupp : Function.support (s : FiniteBaseSpace n → ℝ) = univ := by
      ext b
      simp only [Function.mem_support, mem_univ, iff_true]
      exact (ordinaryBaseSpeed_pos K b).ne'
    change 0 < (ν.measure : Measure (FiniteBaseSpace n)) (Function.support s)
    rw [hsupp]
    simp
  let f : Fin (1 + m) → FiniteBaseSpace n →ᵇ ℝ := fun q ↦
    match finSumFinEquiv.symm q with
    | Sum.inl _ => s
    | Sum.inr i => g i
  obtain ⟨b, hrec, hvalid, hgen, hrev⟩ :=
    hν.exists_recurrent_twoSidedGenericPoint_fin_zeroOrbit ν f (g q₀) hg (hz q₀)
  have hspeed : Tendsto (fun T : ℝ ↦ T⁻¹ * integralClock
      (fun t ↦ ordinaryBaseSpeed K (ordinaryBaseFiniteFlow E K P hP t b).1) T)
      atTop (𝓝 c) := by
    apply realMean_tendsto_of_integerMean (ordinaryBaseFiniteFlow E K P hP) s b
    simpa [f, c] using hgen (finSumFinEquiv (Sum.inl (0 : Fin 1)))
  have hreverse : Tendsto (fun T : ℝ ↦ T⁻¹ * integralClock
      (fun t ↦ ordinaryBaseSpeed K (ordinaryBaseFiniteFlow E K P hP (-t) b).1) T)
      atTop (𝓝 c) := by
    apply realMean_tendsto_of_integerMean (ordinaryBaseFiniteFlow E K P hP).reverse s b
    simpa [f, c] using hrev (finSumFinEquiv (Sum.inl (0 : Fin 1)))
  refine ⟨⟨b, c, hc, ?_, hrec, hvalid, hspeed, ?_⟩⟩
  · exact positiveIntegralClock_of_twoSidedMean
      (s.continuous.comp
        ((ordinaryBaseFiniteFlow E K P hP).continuous continuous_id continuous_const))
      (fun t ↦ ordinaryBaseSpeed_pos K _) hc hspeed hreverse
  · intro q
    apply realMean_tendsto_of_integerMean (ordinaryBaseFiniteFlow E K P hP) (g q) b
    simpa [f, hz] using hgen (finSumFinEquiv (Sum.inr q))

end Stability.Selection
