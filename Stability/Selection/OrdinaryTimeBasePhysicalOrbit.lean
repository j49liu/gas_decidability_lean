import Stability.Selection.OrdinaryTimeBaseGenericOrbit
import HGAS.Dynamics.IntegralCurveStateTimeChange
import HGAS.Dynamics.GenericUnboundedClockContradiction

/-!
# Complete physical trajectories extracted from the compact base

The inverse positive clock gives the original polynomial ODE, pointwise
validity, forward recurrence, full real-horizon test means, and the
Euclidean growth bound with exponent equal to the clearing exponent.

See Section 9, Lemma `lem:selectedorbit`.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Dynamics HGAS.CompactAccumulatorPipelineCode
open HGAS.CompactAccumulatorPipelineCode.AllAffineCompactSourceChart (layout affineSpeed)
open HGAS.CompactAccumulatorPipelineCode.AllAffineCompactBaseChartTrajectory
open Filter Topology MeasureTheory

variable {n m E K : ℕ} {P : PolynomialFieldCode n}
variable {hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j)}
variable {κ : RationalCode} {h : Fin m → PolynomialCode n} {q₀ : Fin m}

namespace OrdinaryTimeBaseOrbit

variable (O : OrdinaryTimeBaseOrbit E K P hP κ h q₀)

/-- The recovered affine curve in compact time. -/
def affineCurve (t : ℝ) : Fin n → ℝ :=
  affinePoint (ordinaryBaseFiniteFlow E K P hP t O.point)

theorem continuous_affineCurve : Continuous O.affineCurve :=
  continuous_affinePoint.comp
    ((ordinaryBaseFiniteFlow E K P hP).continuous continuous_id continuous_const)

/-- The recovered source trajectory in ordinary time, defined for all real
times by the actual inverse integral clock. -/
def physicalCurve (t : ℝ) : Fin n → ℝ := O.affineCurve (O.clock.orderIso.symm t)

theorem continuous_physicalCurve : Continuous O.physicalCurve :=
  O.continuous_affineCurve.comp O.clock.orderIso.symm.continuous

theorem speed_eq (t : ℝ) :
    ordinaryBaseSpeed K (ordinaryBaseFiniteFlow E K P hP t O.point).1 =
      affineSpeed K (O.affineCurve t) := ordinaryBaseSpeed_eq K _

/-- The complete unscaled source ODE follows by the chain rule. -/
theorem physicalCurve_isIntegralCurve
    (hPdegree : ∀ j, MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
      (layout n) (2 * K) (P j)) :
    IsIntegralCurve O.physicalCurve (fun _ x ↦ PolynomialFieldCode.realize P x) := by
  have hscaled := affinePoint_isIntegralCurve K P hPdegree
    (fun t ↦ (ordinaryBaseFiniteFlow E K P hP t O.point).1)
    (baseFlow_integralCurve (layout n) E (2 * K) P hP
      (by intro _; dsimp; intro c; exact Fin.elim0 c) O.point.1)
    (fun t ↦ (ordinaryBaseFiniteFlow E K P hP t O.point).2)
  have hscaled' : IsIntegralCurve O.affineCurve
      (fun _ x ↦ timeScaledField (affineSpeed K) (PolynomialFieldCode.realize P) x) := hscaled
  intro t
  have hcomp := (hscaled' (O.clock.orderIso.symm t)).scomp t (O.clock.symm_hasDerivAt t)
  simpa only [physicalCurve, timeScaledField, smul_smul, ← O.speed_eq,
    inv_mul_cancel₀ (O.clock.positive _).ne', one_smul] using hcomp

theorem physicalCurve_forwardRecurrentAt : ForwardRecurrentAt O.physicalCurve 0 :=
  (O.recurrent.map continuous_affinePoint).inverseClock O.clock

/-- Pointwise zero compact validity becomes pointwise zero source validity;
the clock speed and rational scale are explicitly canceled. -/
theorem physicalCurve_zeroCoordinate
    (hκ : (κ.decode : ℝ) ≠ 0)
    (hh : ∀ q, MixedCentralPolynomialCode.TermsAffineBlockDegreeLE (layout n) (2 * K) (h q))
    (t : ℝ) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (O.physicalCurve t)
      (PolynomialCode.decode (h q₀)) = 0 := by
  have hz := O.zeroCoordinate (O.clock.orderIso.symm t)
  change baseDriftBCF (layout n) (2 * K) κ h _ q₀ = 0 at hz
  rw [baseDriftBCF_eq K κ h hh] at hz
  exact (mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero hκ (AllAffineCompactSourceChart.affineSpeed_pos K _).ne')

/-- Every actual scalar test has zero mean at full ordinary real horizons. -/
theorem physicalCurve_testMean_zero
    (hκ : (κ.decode : ℝ) ≠ 0)
    (hh : ∀ q, MixedCentralPolynomialCode.TermsAffineBlockDegreeLE (layout n) (2 * K) (h q))
    (q : Fin m) :
    Tendsto (fun H : ℝ ↦ H⁻¹ * ∫ t in (0 : ℝ)..H,
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (O.physicalCurve t)
        (PolynomialCode.decode (h q))) atTop (𝓝 0) := by
  let f : ℝ → ℝ := fun t ↦ MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (O.affineCurve t)
    (PolynomialCode.decode (h q))
  have hf : Continuous f := by
    have hp := (MvPolynomial.continuous_eval
      (MvPolynomial.map (algebraMap ℚ ℝ) (PolynomialCode.decode (h q)))).comp
      O.continuous_affineCurve
    simpa only [MvPolynomial.eval_map] using hp
  have hweighted : Tendsto (fun T : ℝ ↦ T⁻¹ * ∫ t in (0 : ℝ)..T,
      f t * ordinaryBaseSpeed K (ordinaryBaseFiniteFlow E K P hP t O.point).1)
      atTop (𝓝 0) := by
    have hmean := (O.drift_generic q).const_mul ((κ.decode : ℝ)⁻¹)
    simp only [mul_zero] at hmean
    apply hmean.congr'
    apply Eventually.of_forall
    intro T
    dsimp only
    rw [mul_left_comm, ← intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    change (κ.decode : ℝ)⁻¹ * baseDriftBCF (layout n) (2 * K) κ h _ q = _
    rw [baseDriftBCF_eq K κ h hh, O.speed_eq]
    dsimp [f, affineCurve]
    field_simp
  simpa only [zero_div] using inverseClock_fullMean_tendsto_ratio O.clock hf
    O.speedMean_pos.ne' O.speed_generic hweighted

/-- The reciprocal clock has finite full-horizon mean `1/speedMean`. -/
theorem reciprocalClockMean_tendsto :
    Tendsto (fun H : ℝ ↦ H⁻¹ * ∫ t in (0 : ℝ)..H, inverseClockReciprocal O.clock t)
      atTop (𝓝 (1 / O.speedMean)) := by
  have hf : Continuous (fun t ↦ (ordinaryBaseSpeed K
      (ordinaryBaseFiniteFlow E K P hP t O.point).1)⁻¹) :=
    O.clock.continuous.inv₀ (fun t ↦ (O.clock.positive t).ne')
  have hw : Tendsto (fun T : ℝ ↦ T⁻¹ * ∫ t in (0 : ℝ)..T,
      (ordinaryBaseSpeed K (ordinaryBaseFiniteFlow E K P hP t O.point).1)⁻¹ *
        ordinaryBaseSpeed K (ordinaryBaseFiniteFlow E K P hP t O.point).1)
      atTop (𝓝 1) := by
    have heq : ∀ᶠ T : ℝ in atTop, T⁻¹ * ∫ t in (0 : ℝ)..T,
        (ordinaryBaseSpeed K (ordinaryBaseFiniteFlow E K P hP t O.point).1)⁻¹ *
          ordinaryBaseSpeed K (ordinaryBaseFiniteFlow E K P hP t O.point).1 = 1 := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      simp only [inv_mul_cancel₀ (O.clock.positive _).ne', intervalIntegral.integral_const,
        sub_zero, smul_eq_mul, mul_one, inv_mul_cancel₀ hT.ne']
    apply tendsto_const_nhds.congr'
    filter_upwards [heq] with T hT
    exact hT.symm
  exact inverseClock_fullMean_tendsto_ratio O.clock hf O.speedMean_pos.ne' O.speed_generic hw

/-- Euclidean growth at the actual clearing exponent is bounded at every
sufficiently large real horizon. -/
theorem physicalCurve_growth :
    ∀ᶠ H : ℝ in atTop,
      H⁻¹ * (∫ t in (0 : ℝ)..H,
        (Real.sqrt (normSq (O.physicalCurve t))) ^ (2 * K : ℝ)) ≤ 1 / O.speedMean + 1 := by
  have hpoint (t : ℝ) : (Real.sqrt (normSq (O.physicalCurve t))) ^ (2 * K : ℝ) ≤
      inverseClockReciprocal O.clock t := by
    rw [inverseClockReciprocal_apply, O.speed_eq]
    change _ ≤ (affineSpeed K (O.physicalCurve t))⁻¹
    rw [affineSpeed, ← inv_pow, inv_inv]
    have hexp : (2 * K : ℝ) = ((2 * K : ℕ) : ℝ) := by norm_cast
    rw [hexp, Real.rpow_natCast, pow_mul, Real.sq_sqrt (normSq_nonneg _)]
    exact pow_le_pow_left₀ (normSq_nonneg _) (by linarith) K
  have hcont : Continuous (fun t ↦ (Real.sqrt (normSq (O.physicalCurve t))) ^ (2 * K : ℝ)) := by
    apply (Real.continuous_rpow_const (by positivity : (0 : ℝ) ≤ 2 * K)).comp
    apply Continuous.sqrt
    have hx := O.continuous_physicalCurve
    unfold normSq dot
    fun_prop
  filter_upwards [O.reciprocalClockMean_tendsto.eventually
    (Iio_mem_nhds (by linarith : 1 / O.speedMean < 1 / O.speedMean + 1)),
    eventually_gt_atTop (0 : ℝ)] with H hmean hH
  have hbound := intervalIntegral.integral_mono_on (μ := volume) hH.le
    (hcont.intervalIntegrable _ _)
    ((inverseClockReciprocal O.clock).continuous.intervalIntegrable _ _) (fun t _ ↦ hpoint t)
  exact (mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hH.le)).trans hmean.le

/-- The growth bound holds on the entire range of horizons stated in the
source selector, not only eventually. -/
theorem physicalCurve_growth_all_horizons :
    ∃ B : ℝ, ∀ H : ℝ, 1 ≤ H →
      H⁻¹ * (∫ t in (0 : ℝ)..H,
        (Real.sqrt (normSq (O.physicalCurve t))) ^ (2 * K : ℝ)) ≤ B := by
  apply forwardMean_bounded_on_ge_one _ _ O.physicalCurve_growth
  apply (Real.continuous_rpow_const (by positivity : (0 : ℝ) ≤ 2 * K)).comp
  apply Continuous.sqrt
  have hx := O.continuous_physicalCurve
  unfold normSq dot
  fun_prop

end OrdinaryTimeBaseOrbit

end Stability.Selection
