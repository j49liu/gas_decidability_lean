import Stability.Simulation.ProjectiveAngularChart
import Stability.Simulation.ProjectiveCentralDynamics

/-!
# Projective stability is equivalent to bounded source output

Central lifting turns every supplied finite source trajectory into a
positive time change of an angular trajectory. Finite uniqueness identifies
the reparametrized curve with the canonical angular flow. Together with
the quotient-chart direction, this gives the criterion for the literal
homogeneous sparse polynomial field, with existence-aware stability.
-/

namespace Stability.ProjectivePolynomialCode

open HGAS HGAS.Veronese MvPolynomial Set MeasureTheory

noncomputable section

variable {n : ℕ}

/-- A bound on the canonical angular cocycle bounds every actual finite
source trajectory, including those that have no global continuation. -/
theorem boundedFiniteOutput_of_boundedSourceAngularCocycle
    (ell : ℕ) (hell : 1 ≤ ell) (P : PolynomialFieldCode n) (b : PolynomialCode n)
    (hF : ContDiff ℝ 1 (PolynomialFieldCode.realize (fieldCode ell P b)))
    (hP : ∀ i, PolynomialCode.TermsDegreeLE ell (P i))
    (hb : PolynomialCode.TermsDegreeLE (ell - 1) b)
    (hbounded : Stability.HasBoundedSourceAngularCocycle
      (PolynomialFieldCode.realize (fieldCode ell P b)) hF) :
    Stability.HasBoundedFiniteOutput (PolynomialFieldCode.realize P)
      (fun x ↦ eval₂Hom (algebraMap ℚ ℝ) x (PolynomialCode.decode b)) := by
  obtain ⟨M, hM⟩ := hbounded
  refine ⟨M, ?_⟩
  intro T hT x hx hderiv
  let γ : ℝ → Fin (n + 1) → ℝ := fun t ↦ centralLift (x t)
  let q : ℝ → ℝ := fun t ↦ (centralScale (x t) ^ (ell - 1))⁻¹
  have hγ : ContinuousOn γ (Icc 0 T) := continuous_centralLift.comp_continuousOn hx
  have hq : ContinuousOn q (Icc 0 T) :=
    ((continuous_centralScale.comp_continuousOn hx).pow (ell - 1)).inv₀
      (fun t _ ↦ pow_ne_zero _ (centralScale_pos (x t)).ne')
  have hreward : ContinuousOn
      (fun t ↦ HGAS.radialReward (PolynomialFieldCode.realize (fieldCode ell P b)) (γ t))
      (Icc 0 T) := (contDiff_sourceRadialReward hF).continuous.comp_continuousOn hγ
  obtain ⟨S, hS, z, hz, hz0, _, _, hdz, hint⟩ :=
    TimeChange.exists_segment_of_positive_time_rate
      (F := HGAS.angularField (PolynomialFieldCode.realize (fieldCode ell P b)))
      (g := HGAS.radialReward (PolynomialFieldCode.realize (fieldCode ell P b)))
      hT hγ hq hreward
      (fun t ht ↦ centralLift_hasDerivAt_angular ell hell P b hP (hderiv t ht))
      (fun t _ ↦ inv_pos.mpr (pow_pos (centralScale_pos (x t)) _))
  have hφ := sourceAngularAmbientFlow_isIntegralCurve
    (PolynomialFieldCode.realize (fieldCode ell P b)) hF (centralLift (x 0))
    (sourceRadiusSq_centralLift (x 0))
  have heq := Stability.finiteSolution_unique (a := 0) (b := S)
    (contDiff_sourceAngularField hF) hz hdz hφ.continuous.continuousOn (fun t _ ↦ hφ t)
    (by simpa only [Flow.map_zero_apply] using hz0)
  have hflowIntegral : (∫ t in 0..S,
      HGAS.radialReward (PolynomialFieldCode.realize (fieldCode ell P b)) (z t)) =
      ∫ t in 0..S, HGAS.radialReward (PolynomialFieldCode.realize (fieldCode ell P b))
        (sourceAngularAmbientFlow (PolynomialFieldCode.realize (fieldCode ell P b)) hF t
          (centralLift (x 0))) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hS] at ht
    exact congrArg (HGAS.radialReward (PolynomialFieldCode.realize (fieldCode ell P b))) (heq ht)
  have hsourceIntegral : (∫ t in 0..T,
      q t * HGAS.radialReward (PolynomialFieldCode.realize (fieldCode ell P b)) (γ t)) =
      ∫ t in 0..T, eval₂Hom (algebraMap ℚ ℝ) (x t) (PolynomialCode.decode b) := by
    apply intervalIntegral.integral_congr
    intro t _
    exact centralLift_weighted_radialReward ell P b hb (x t)
  have hbound := hM (centralLift (x 0)) (sourceRadiusSq_centralLift (x 0)) S hS
  exact (hint.trans hsourceIntegral).symm.le.trans (hflowIntegral.le.trans hbound)

/-- The full angular/source criterion for the actual odd-degree
projective compiler. Both directions quantify over genuine trajectories. -/
theorem boundedSourceAngularCocycle_iff_boundedFiniteOutput
    (ell : ℕ) (hell : Odd ell) (P : PolynomialFieldCode n) (b : PolynomialCode n)
    (hF : ContDiff ℝ 1 (PolynomialFieldCode.realize (fieldCode ell P b)))
    (hP : ∀ i t, t ∈ P i → ExponentCode.totalDegree t.1 < ell)
    (hb : ∀ t ∈ b, ExponentCode.totalDegree t.1 < ell - 1) :
    Stability.HasBoundedSourceAngularCocycle
      (PolynomialFieldCode.realize (fieldCode ell P b)) hF ↔
    Stability.HasBoundedFiniteOutput (PolynomialFieldCode.realize P)
      (fun x ↦ eval₂Hom (algebraMap ℚ ℝ) x (PolynomialCode.decode b)) := by
  have hellOne : 1 ≤ ell := by obtain ⟨m, hm⟩ := hell; omega
  constructor
  · exact boundedFiniteOutput_of_boundedSourceAngularCocycle ell hellOne P b hF
      (fun i t ht ↦ (hP i t ht).le) (fun t ht ↦ (hb t ht).le)
  · exact boundedSourceAngularCocycle_of_boundedFiniteOutput ell hell P b hF hP hb

/-- The compiled homogeneous field is Lyapunov stable, with local
forward existence included, exactly when source output integrals admit
one bound independent of all finite initial states and horizons. -/
theorem lyapunovStable_fieldCode_iff_boundedFiniteOutput
    (ell : ℕ) (hell : Odd ell) (P : PolynomialFieldCode n) (b : PolynomialCode n)
    (hP : ∀ i t, t ∈ P i → ExponentCode.totalDegree t.1 < ell)
    (hb : ∀ t ∈ b, ExponentCode.totalDegree t.1 < ell - 1) :
    HGAS.LyapunovStableWithExistence (PolynomialFieldCode.realize (fieldCode ell P b)) 0 ↔
    Stability.HasBoundedFiniteOutput (PolynomialFieldCode.realize P)
      (fun x ↦ eval₂Hom (algebraMap ℚ ℝ) x (PolynomialCode.decode b)) := by
  have hellOne : 1 ≤ ell := by obtain ⟨m, hm⟩ := hell; omega
  have hF : ContDiff ℝ 1 (PolynomialFieldCode.realize (fieldCode ell P b)) :=
    (contDiff_realize_fieldCode ell P b).of_le (by simp)
  have hhom : ScalesAsDegree ℝ (ell + 1 + 1)
      (PolynomialFieldCode.realize (fieldCode ell P b)) := by
    simpa only [Nat.add_assoc] using scalesAsDegree_realize_fieldCode ell hellOne P b
      (fun i t ht ↦ (hP i t ht).le) (fun t ht ↦ (hb t ht).le)
  rw [Stability.lyapunovStable_iff_boundedSourceAngularCocycle _ hF (ell + 1) hhom
    (realize_fieldCode_zero ell P b)]
  exact boundedSourceAngularCocycle_iff_boundedFiniteOutput ell hell P b hF hP hb

end

end Stability.ProjectivePolynomialCode
