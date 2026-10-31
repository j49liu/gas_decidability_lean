import Stability.Selection.OrdinaryTimeCompactGraphTrajectory
import Stability.Dynamics.CompactInvariantGraph

/-!
# Positive central compactification of a parametrized primitive graph

A complete source orbit and its drift primitive share the reciprocal
central clock. Their positive-central/stereographic graph is therefore
preserved by the literal compiled source flow. Compactness then supplies
an invariant probability, without a same-time equivariance assumption.
-/

namespace Stability.Selection

noncomputable section

open HGAS HGAS.CompactAccumulatorPipelineCode Set
open AllAffineCompactSourceChart AllAffineCompactSourceTrajectory
open AllAffinePositiveCentralTrajectory
open scoped BoundedContinuousFunction

variable {n m : ℕ}

def positiveCompactGraphPoint (x : Fin n → ℝ) (z : Fin m → ℝ) : SourceSpace n m :=
  compactGraphPoint (layout n) (positiveBasePoint x) z

theorem continuous_positiveBasePoint :
    Continuous (positiveBasePoint : (Fin n → ℝ) → BaseSpace (layout n)) := by
  have hnorm : Continuous (normSq : (Fin n → ℝ) → ℝ) := by
    unfold normSq dot
    fun_prop
  have hs : Continuous (positiveCentralScale : (Fin n → ℝ) → ℝ) :=
    (continuous_const.add hnorm).sqrt.inv₀
      (fun z ↦ (Real.sqrt_pos.mpr (HGAS.one_add_normSq_pos z)).ne')
  apply Continuous.subtype_mk
  apply continuous_pi
  intro q
  obtain ⟨j | b, rfl⟩ := finSumFinEquiv.surjective q
  · change Continuous (fun a ↦ (positiveBasePoint a).val (finSumFinEquiv (Sum.inl j)))
    simpa only [positiveBasePoint_finSum_inl, positiveCentralChartPoint_x,
      Pi.smul_apply, smul_eq_mul] using hs.mul (continuous_apply j)
  · change Continuous (fun a ↦ (positiveBasePoint a).val (finSumFinEquiv (Sum.inr b)))
    simpa only [positiveBasePoint_finSum_inr, positiveCentralChartPoint_w] using hs

theorem continuous_positiveCompactGraphPoint :
    Continuous (fun p : (Fin n → ℝ) × (Fin m → ℝ) ↦ positiveCompactGraphPoint p.1 p.2) :=
  (continuous_compactGraphPoint (layout n)).comp
    ((continuous_positiveBasePoint.comp continuous_fst).prodMk continuous_snd)

theorem baseDrift_positiveBasePoint (K : ℕ) (κ : RationalCode)
    (h : Fin m → PolynomialCode n)
    (hh : ∀ i, MixedCentralPolynomialCode.TermsAffineBlockDegreeLE (layout n) (2 * K) (h i))
    (x : Fin n → ℝ) (i : Fin m) :
    baseDriftBCF (layout n) (2 * K) κ h (positiveBasePoint x) i =
      (κ.decode : ℝ) * affineSpeed K x *
        MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x (PolynomialCode.decode (h i)) := by
  change MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
    (MixedCentralPolynomialCode.scaledChartPoint (layout n) (fun _ ↦ positiveCentralScale x) x)
    (PolynomialCode.decode (slowedDriftCode (layout n) (2 * K) κ h i)) = _
  rw [eval₂Hom_slowedDriftCode_scaledChart (layout n) (2 * K) κ h hh,
    slowdown_eq_weight_pow, positiveCentralScale_evenPow_eq_affineSpeed]

/-- The actual reward polynomial on the positive graph has precisely the
two chart contributions used in the quantitative gain estimate. -/
theorem positiveCompactGraphPoint_reward (ε : RationalCode)
    (x : Fin n → ℝ) (z : Fin m → ℝ) :
    UnitSpherePolynomialWrapper.sourceRewardBCF (sourceBlock (m := m) (layout n))
        (rewardCode (n := n) (k := 1) (m := m) ε) (positiveCompactGraphPoint x z) =
      (1 - normSq z) / (1 + normSq z) + 2 / (1 + normSq x) - 1 - (ε.decode : ℝ) := by
  rw [UnitSpherePolynomialWrapper.sourceRewardBCF_apply]
  change MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
    (AccumulatorPolynomialCode.combinedPoint
      (MixedCentralPolynomialCode.scaledChartPoint (layout n) (fun _ ↦ positiveCentralScale x) x)
      (stereoU z) (stereoW z))
    (PolynomialCode.decode (rewardCode (n := n) (k := 1) (m := m) ε)) = _
  rw [eval₂Hom_rewardCode, Fin.prod_univ_one]
  have hs := positiveCentralChartPoint_w_sq x
  simp only [positiveCentralChartPoint_w] at hs
  rw [hs]
  simp only [stereoW, div_eq_mul_inv]

/-- The actual compact polynomial flow preserves the graph image. The
only dynamical inputs are the uncompactified source and primitive ODEs. -/
theorem positiveCompactGraph_range_invariant {A : Type*} [TopologicalSpace A]
    (φ : Flow ℝ A) (Γ : A → Fin n → ℝ) (B : A → Fin m → ℝ)
    (K E : ℕ) (κ ε : RationalCode) (P : PolynomialFieldCode n)
    (h : Fin m → PolynomialCode n)
    (hP : ∀ i, PolynomialCode.TermsDegreeLE E (P i))
    (hh : ∀ i, PolynomialCode.TermsDegreeLE E (h i))
    (hPK : ∀ i, MixedCentralPolynomialCode.TermsAffineBlockDegreeLE (layout n) (2 * K) (P i))
    (hhK : ∀ i, MixedCentralPolynomialCode.TermsAffineBlockDegreeLE (layout n) (2 * K) (h i))
    (hΓ : ∀ a, IsIntegralCurve (fun t ↦ Γ (φ t a))
      (fun _ y ↦ PolynomialFieldCode.realize P y))
    (hB : ∀ a i t, HasDerivAt (fun s ↦ B (φ s a) i)
      ((κ.decode : ℝ) *
        MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (Γ (φ t a)) (PolynomialCode.decode (h i))) t)
    (t : ℝ) (a : A) :
    sourceFlow (layout n) E (2 * K) κ P h ε t (positiveCompactGraphPoint (Γ a) (B a)) ∈
      range (fun x ↦ positiveCompactGraphPoint (Γ x) (B x)) := by
  let clock := reciprocalAffineClock K P (hΓ a)
  let path := fun s ↦ φ (clock.orderIso.symm s) a
  let γ := fun s ↦ positiveCompactGraphPoint (Γ (path s)) (B (path s))
  have hb : IsIntegralCurve (fun s ↦ (positiveBasePoint (Γ (path s))).val)
      (fun _ y ↦ PolynomialFieldCode.realize (baseFieldCode (layout n) (2 * K) P) y) :=
    positiveBaseCurve_isIntegralCurve K P hPK (hΓ a)
  have hz (i : Fin m) (s : ℝ) : HasDerivAt (fun r ↦ B (path r) i)
      (baseDriftBCF (layout n) (2 * K) κ h (positiveBasePoint (Γ (path s))) i) s := by
    have hd := (hB a i (clock.orderIso.symm s)).comp s (clock.symm_hasDerivAt s)
    apply hd.congr_deriv
    rw [baseDrift_positiveBasePoint K κ h hhK]
    dsimp only [clock, path, reciprocalAffineClockWeight]
    rw [inv_inv]
    ring
  have hγ := compactGraphPoint_isIntegralCurve (layout n) (2 * K) κ P h
    (fun s ↦ positiveBasePoint (Γ (path s))) (fun s ↦ B (path s)) hb hz
  have heq := compactSourceIntegralCurve_eq_flow (layout n) E (2 * K) κ P hP h hh ε
    (fun _ c ↦ Fin.elim0 c) γ hγ t
  have hzero : γ 0 = positiveCompactGraphPoint (Γ a) (B a) := by
    simp only [γ, path, PositiveIntegralClock.symm_zero, Flow.map_zero_apply]
  rw [hzero] at heq
  exact ⟨path t, heq⟩

/-- A continuous primitive graph over a compact parameter flow carries a
proved invariant probability with its pointwise reward lower bound. -/
theorem exists_invariantProbability_positiveCompactGraph
    {A : Type*} [TopologicalSpace A] [CompactSpace A] [Nonempty A]
    (φ : Flow ℝ A) (Γ : A → Fin n → ℝ) (B : A → Fin m → ℝ)
    (hΓcont : Continuous Γ) (hBcont : Continuous B)
    (K E : ℕ) (κ ε : RationalCode) (P : PolynomialFieldCode n)
    (h : Fin m → PolynomialCode n)
    (hP : ∀ i, PolynomialCode.TermsDegreeLE E (P i))
    (hh : ∀ i, PolynomialCode.TermsDegreeLE E (h i))
    (hPK : ∀ i, MixedCentralPolynomialCode.TermsAffineBlockDegreeLE (layout n) (2 * K) (P i))
    (hhK : ∀ i, MixedCentralPolynomialCode.TermsAffineBlockDegreeLE (layout n) (2 * K) (h i))
    (hΓ : ∀ a, IsIntegralCurve (fun t ↦ Γ (φ t a))
      (fun _ y ↦ PolynomialFieldCode.realize P y))
    (hB : ∀ a i t, HasDerivAt (fun s ↦ B (φ s a) i)
      ((κ.decode : ℝ) *
        MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (Γ (φ t a)) (PolynomialCode.decode (h i))) t)
    (reward : SourceSpace n m →ᵇ ℝ) (lower : ℝ)
    (hlower : ∀ a, lower ≤ reward (positiveCompactGraphPoint (Γ a) (B a))) :
    ∃ μ : HGAS.Dynamics.InvariantProbabilityMeasure
        (sourceFlow (layout n) E (2 * K) κ P h ε),
      (μ.measure : MeasureTheory.Measure (SourceSpace n m))
          (range (fun a ↦ positiveCompactGraphPoint (Γ a) (B a))) = 1 ∧
        lower ≤ HGAS.Dynamics.observableAverage reward μ.measure := by
  apply Stability.Dynamics.exists_invariantProbability_on_compact_range
    _ (fun a ↦ positiveCompactGraphPoint (Γ a) (B a))
    (continuous_positiveCompactGraphPoint.comp (hΓcont.prodMk hBcont))
    (positiveCompactGraph_range_invariant φ Γ B K E κ ε P h hP hh hPK hhK hΓ hB)
    reward lower hlower

end

end Stability.Selection
