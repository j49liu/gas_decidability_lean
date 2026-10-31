import Stability.Simulation.ProjectiveAngularAlgebra
import Stability.Simulation.FiniteVariableTimeChange
import Stability.Dynamics.SourceAngularStability
import Stability.Dynamics.FiniteSolutionUniqueness
import Stability.Dynamics.FiniteOutputBound

/-!
# Actual angular trajectories in the projective quotient chart

Equator points are stationary. Backward finite-interval uniqueness prevents
an angular trajectory from reaching the equator if it starts off it.
For odd homogenizing degree, the actual quotient trajectory has a positive
time rate on either hemisphere. Finite time change transfers the source
output bound to its angular cocycle.
-/

namespace Stability.ProjectivePolynomialCode

open HGAS HGAS.Veronese MvPolynomial Set MeasureTheory

noncomputable section

variable {n : ℕ}

theorem angularFlow_eq_equator (ell : ℕ) (P : PolynomialFieldCode n) (b : PolynomialCode n)
    (hF : ContDiff ℝ 1 (PolynomialFieldCode.realize (fieldCode ell P b)))
    (hP : ∀ i t, t ∈ P i → ExponentCode.totalDegree t.1 < ell)
    (hb : ∀ t ∈ b, ExponentCode.totalDegree t.1 < ell - 1)
    (y : Fin (n + 1) → ℝ) (hy : sourceRadiusSq y = 1) (hz : y (Fin.last n) = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    sourceAngularAmbientFlow (PolynomialFieldCode.realize (fieldCode ell P b)) hF t y = y := by
  let γ := fun r ↦ sourceAngularAmbientFlow
    (PolynomialFieldCode.realize (fieldCode ell P b)) hF r y
  have hγ := sourceAngularAmbientFlow_isIntegralCurve
    (PolynomialFieldCode.realize (fieldCode ell P b)) hF y hy
  have hzero := angularField_fieldCode_equator ell P b hP hb y hz
  have heq := Stability.finiteSolution_unique (a := 0) (b := t) (contDiff_sourceAngularField hF)
    hγ.continuous.continuousOn (fun r _ ↦ hγ r) continuousOn_const
    (fun r _ ↦ by rw [hzero]; exact hasDerivAt_const r y)
    (show γ 0 = y by simp [γ])
  exact heq ⟨ht, le_rfl⟩

/-- A finite positive-time angular trajectory cannot reach the stationary
equator from a point outside it. -/
theorem angularFlow_last_ne_zero (ell : ℕ) (P : PolynomialFieldCode n) (b : PolynomialCode n)
    (hF : ContDiff ℝ 1 (PolynomialFieldCode.realize (fieldCode ell P b)))
    (hP : ∀ i t, t ∈ P i → ExponentCode.totalDegree t.1 < ell)
    (hb : ∀ t ∈ b, ExponentCode.totalDegree t.1 < ell - 1)
    (y : Fin (n + 1) → ℝ) (hy : sourceRadiusSq y = 1) (hz : y (Fin.last n) ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) :
    sourceAngularAmbientFlow (PolynomialFieldCode.realize (fieldCode ell P b)) hF t y
      (Fin.last n) ≠ 0 := by
  intro hzero
  let γ := fun r ↦ sourceAngularAmbientFlow
    (PolynomialFieldCode.realize (fieldCode ell P b)) hF r y
  have hγ := sourceAngularAmbientFlow_isIntegralCurve
    (PolynomialFieldCode.realize (fieldCode ell P b)) hF y hy
  have hstationary := angularField_fieldCode_equator ell P b hP hb (γ t) hzero
  have heq := HGAS.ode_solution_unique_Icc_left_of_contDiff
    (a := 0) (b := t) (contDiff_sourceAngularField hF) hγ.continuous.continuousOn
    (fun r _ ↦ (hγ r).hasDerivWithinAt) continuousOn_const
    (fun r _ ↦ by rw [hstationary]; exact (hasDerivAt_const r (γ t)).hasDerivWithinAt)
    (show γ t = γ t from rfl)
  have hstart := congrArg (fun v ↦ v (Fin.last n)) (heq ⟨le_rfl, ht⟩)
  apply hz
  simpa only [γ, Flow.map_zero_apply] using hstart.trans hzero

theorem chartRate_pos_of_odd {ell : ℕ} (hell : Odd ell) {z : ℝ} (hz : z ≠ 0) :
    0 < z ^ (ell - 1) := by
  obtain ⟨m, hm⟩ := hell
  have heven : Even (ell - 1) := ⟨m, by omega⟩
  exact heven.pow_pos hz

/-- A bound on all actual finite source output integrals bounds the
canonical angular cocycle of the compiled homogeneous field. -/
theorem boundedSourceAngularCocycle_of_boundedFiniteOutput
    (ell : ℕ) (hell : Odd ell) (P : PolynomialFieldCode n) (b : PolynomialCode n)
    (hF : ContDiff ℝ 1 (PolynomialFieldCode.realize (fieldCode ell P b)))
    (hP : ∀ i t, t ∈ P i → ExponentCode.totalDegree t.1 < ell)
    (hb : ∀ t ∈ b, ExponentCode.totalDegree t.1 < ell - 1)
    (hbounded : Stability.HasBoundedFiniteOutput (PolynomialFieldCode.realize P)
      (fun x ↦ eval₂Hom (algebraMap ℚ ℝ) x (PolynomialCode.decode b))) :
    Stability.HasBoundedSourceAngularCocycle
      (PolynomialFieldCode.realize (fieldCode ell P b)) hF := by
  obtain ⟨M, hM⟩ := hbounded
  refine ⟨max M 0, ?_⟩
  intro y hy T hT
  let γ := fun t ↦ sourceAngularAmbientFlow
    (PolynomialFieldCode.realize (fieldCode ell P b)) hF t y
  have hγ := sourceAngularAmbientFlow_isIntegralCurve
    (PolynomialFieldCode.realize (fieldCode ell P b)) hF y hy
  have hsphere (t : ℝ) : sourceRadiusSq (γ t) = 1 :=
    sourceAngularAmbientFlow_preserves_radiusSq _ hF y hy t
  by_cases hz : y (Fin.last n) = 0
  · have hzero : (∫ t in 0..T,
        HGAS.radialReward (PolynomialFieldCode.realize (fieldCode ell P b)) (γ t)) = 0 := by
      calc
        _ = ∫ _ in 0..T, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hT] at ht
          have hpoint := angularFlow_eq_equator ell P b hF hP hb y hy hz ht.1
          change HGAS.radialReward (PolynomialFieldCode.realize (fieldCode ell P b))
            (sourceAngularAmbientFlow _ hF t y) = 0
          rw [hpoint, HGAS.radialReward, realize_fieldCode_equator ell P b hP hb y hz,
            HGAS.dot_zero]
        _ = 0 := intervalIntegral.integral_zero
    exact hzero.le.trans (le_max_right _ _)
  · have hnonzero (t : ℝ) (ht : t ∈ Icc 0 T) : γ t (Fin.last n) ≠ 0 :=
      angularFlow_last_ne_zero ell P b hF hP hb y hy hz ht.1
    let x : ℝ → Fin n → ℝ := fun t i ↦ γ t i.castSucc / γ t (Fin.last n)
    let q : ℝ → ℝ := fun t ↦ γ t (Fin.last n) ^ (ell - 1)
    have hQ : ContinuousOn q (Icc 0 T) :=
      (((continuous_apply (Fin.last n)).comp hγ.continuous).pow (ell - 1)).continuousOn
    have hx : ContinuousOn x (Icc 0 T) := by
      apply continuousOn_pi.mpr
      intro i
      exact ((continuous_apply i.castSucc).comp hγ.continuous).continuousOn.div
        ((continuous_apply (Fin.last n)).comp hγ.continuous).continuousOn hnonzero
    have hg : ContinuousOn
        (fun t ↦ eval₂Hom (algebraMap ℚ ℝ) (x t) (PolynomialCode.decode b)) (Icc 0 T) :=
      (HGAS.contDiff_eval₂Hom_rational_real_fintype _).continuous.comp_continuousOn hx
    have hellOne : 1 ≤ ell := by obtain ⟨m, hm⟩ := hell; omega
    have hPdegree : ∀ i, PolynomialCode.TermsDegreeLE ell (P i) :=
      fun i t ht ↦ (hP i t ht).le
    have hbdegree : PolynomialCode.TermsDegreeLE (ell - 1) b := fun t ht ↦ (hb t ht).le
    obtain ⟨S, hS, z, hzcont, _, _, _, hdz, hint⟩ :=
      TimeChange.exists_segment_of_positive_time_rate
        (F := PolynomialFieldCode.realize P)
        (g := fun v ↦ eval₂Hom (algebraMap ℚ ℝ) v (PolynomialCode.decode b)) hT hx hQ hg
        (fun t ht ↦ hasDerivAt_quotient_chart ell hellOne P b hPdegree (hγ t)
          (hsphere t) (hnonzero t (Ioo_subset_Icc_self ht)))
        (fun t ht ↦ chartRate_pos_of_odd hell (hnonzero t ht))
    have hbound := hM S hS z hzcont hdz
    have heq : (∫ t in 0..T,
        HGAS.radialReward (PolynomialFieldCode.realize (fieldCode ell P b)) (γ t)) =
        ∫ t in 0..T, q t * eval₂Hom (algebraMap ℚ ℝ) (x t) (PolynomialCode.decode b) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hT] at ht
      dsimp only
      rw [radialReward_fieldCode_on_sphere ell P b (γ t) (hsphere t),
        eval_radialRateCode_quotient ell b hbdegree (γ t) (hnonzero t ht)]
    exact (heq.trans hint.symm).le.trans (hbound.trans (le_max_left _ _))

end

end Stability.ProjectivePolynomialCode
