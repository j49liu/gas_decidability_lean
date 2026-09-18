import HGAS.Dynamics.StateTimeChange
import HGAS.Modular.JacobiBlochRegularContinuation
import Mathlib.Tactic

/-!
# Forward reciprocal-chart continuation for Jacobi--Bloch paths

The global continuation theorem is stated for a Jacobi trajectory on the
whole real line.  Physical compact-source trajectories solve their ODE
only on `Set.Ici 0`.  This file proves the corresponding forward result.

The agreement set is considered in the connected subtype `Set.Ici 0`.
At a positive time, ordinary local ODE uniqueness makes agreement open.
At the boundary time zero, regularity is first obtained from the
reciprocal equation; continuity supplies a short regular interval, and
one-sided compact-interval uniqueness supplies agreement on that
interval.
-/

namespace HGAS.Modular

open HGAS
open Complex Real
open Filter Set Topology
open UpperHalfPlane hiding I
open scoped Topology

noncomputable section

namespace AffineBlochParameters

/-- **Forward reciprocal-chart continuation.**

A forward polynomial Jacobi trajectory which initially agrees with the
regular core of an affine Bloch formula, and which remains on
`U*T₁=1`, agrees with that formula at every nonnegative time. -/
theorem regular_and_eqOn_Ici_jacobiBlochPath_of_core_eq_zero
    (p : AffineBlochParameters)
    {z : ℝ → JacobiState ℂ}
    (hz :
      IsForwardTrajectory
        (jacobiCoordinateVectorField
          ((π : ℂ) * (p.nu : ℂ))
          ((π : ℂ) * I * (p.kappa : ℂ)))
        (fun t => JacobiPolynomialCode.point (z t))
        (JacobiPolynomialCode.point (z 0)))
    (hc0 : p.c0 ≠ 0)
    (hreciprocal :
      ∀ t, 0 ≤ t → (z t).U * (z t).T1 = 1)
    (hinitial :
      jacobiCorePoint (z 0) =
        jacobiCorePoint (p.jacobiBlochPath 0)) :
    (∀ t, 0 ≤ t →
      jacobiTheta1 (p.xi t) (p.tau t : ℂ) ≠ 0) ∧
      ∀ t, 0 ≤ t → z t = p.jacobiBlochPath t := by
  let forwardRay : Set ℝ := Ici 0
  let agreement : Set forwardRay :=
    {t |
      jacobiCorePoint (z t.1) =
        jacobiCorePoint (p.jacobiBlochPath t.1)}
  have hzPointContinuous :
      Continuous
        (fun t : forwardRay =>
          JacobiPolynomialCode.point (z t.1)) :=
    hz.2.continuousOn.restrict
  have hzCoreContinuous :
      Continuous
        (fun t : forwardRay => jacobiCorePoint (z t.1)) := by
    apply continuous_pi
    intro i
    fin_cases i
    · simpa only [jacobiCorePoint,
        JacobiPolynomialCode.point, Matrix.cons_val_zero] using
        (continuous_apply
          JacobiPolynomialCode.p2Index).comp hzPointContinuous
    · simpa only [jacobiCorePoint,
        JacobiPolynomialCode.point, Matrix.cons_val_one,
        Matrix.cons_val_zero] using
        (continuous_apply
          JacobiPolynomialCode.p3Index).comp hzPointContinuous
    · simpa only [jacobiCorePoint,
        JacobiPolynomialCode.point, Matrix.cons_val_one,
        Matrix.cons_val_zero] using
        (continuous_apply
          JacobiPolynomialCode.p4Index).comp hzPointContinuous
    · simpa only [jacobiCorePoint,
        JacobiPolynomialCode.point, Matrix.cons_val_one,
        Matrix.cons_val_zero] using
        (continuous_apply
          JacobiPolynomialCode.HIndex).comp hzPointContinuous
    · simpa only [jacobiCorePoint,
        JacobiPolynomialCode.point, Matrix.cons_val_one,
        Matrix.cons_val_zero] using
        (continuous_apply
          JacobiPolynomialCode.T1Index).comp hzPointContinuous
    · simpa only [jacobiCorePoint,
        JacobiPolynomialCode.point, Matrix.cons_val_one,
        Matrix.cons_val_zero] using
        (continuous_apply
          JacobiPolynomialCode.T2Index).comp hzPointContinuous
    · simpa only [jacobiCorePoint,
        JacobiPolynomialCode.point, Matrix.cons_val_one,
        Matrix.cons_val_zero] using
        (continuous_apply
          JacobiPolynomialCode.T3Index).comp hzPointContinuous
    · simpa only [jacobiCorePoint,
        JacobiPolynomialCode.point, Matrix.cons_val_one,
        Matrix.cons_val_zero] using
        (continuous_apply
          JacobiPolynomialCode.T4Index).comp hzPointContinuous
    · simpa only [jacobiCorePoint,
        JacobiPolynomialCode.point, Matrix.cons_val_one,
        Matrix.cons_val_zero] using
        (continuous_apply
          JacobiPolynomialCode.DeltaIndex).comp hzPointContinuous
  have hagreement_closed : IsClosed agreement := by
    exact isClosed_eq
      hzCoreContinuous
      (p.continuous_jacobiBlochCorePoint.comp
        continuous_subtype_val)
  have hagreement_open : IsOpen agreement := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    by_cases htzero : (t.1 : ℝ) = 0
    · have hregularZero :
          jacobiTheta1 (p.xi 0) (p.tau 0 : ℂ) ≠ 0 := by
        change
          jacobiCorePoint (z t.1) =
            jacobiCorePoint (p.jacobiBlochPath t.1) at ht
        exact p.regular_of_core_eq
          (by simpa only [htzero] using ht)
          (hreciprocal 0 le_rfl)
      have hregularEventually :
          ∀ᶠ s in nhds (0 : ℝ),
            jacobiTheta1 (p.xi s) (p.tau s : ℂ) ≠ 0 :=
        p.continuous_jacobiTheta1_comp.continuousAt.eventually
          (isOpen_compl_singleton.mem_nhds hregularZero)
      obtain ⟨ε, hεpos, hε⟩ :=
        Metric.mem_nhds_iff.mp hregularEventually
      have hnear :
          ∀ᶠ s : forwardRay in nhds t, (s.1 : ℝ) < ε := by
        have hzeroValue : (t.1 : ℝ) = 0 := htzero
        have hIio : Iio ε ∈ nhds (t.1 : ℝ) := by
          rw [hzeroValue]
          exact Iio_mem_nhds hεpos
        exact continuous_subtype_val.continuousAt hIio
      filter_upwards [hnear] with s hs
      have hsnonneg : 0 ≤ (s.1 : ℝ) := s.2
      have hsabs : |(s.1 : ℝ)| < ε := by
        rw [abs_of_nonneg hsnonneg]
        exact hs
      have hsregular :
          jacobiTheta1 (p.xi s.1) (p.tau s.1 : ℂ) ≠ 0 :=
        hε (by simpa [Real.dist_eq] using hsabs)
      have heqOn :=
        ode_solution_unique_Icc_right_of_contDiff
          (F :=
            jacobiCoordinateVectorField
              ((π : ℂ) * (p.nu : ℂ))
              ((π : ℂ) * I * (p.kappa : ℂ)))
          (γ := fun r => JacobiPolynomialCode.point (z r))
          (η := fun r =>
            JacobiPolynomialCode.point (p.jacobiBlochPath r))
          (a := 0) (b := s.1)
          (contDiff_jacobiCoordinateVectorField
            ((π : ℂ) * (p.nu : ℂ))
            ((π : ℂ) * I * (p.kappa : ℂ)))
          (hz.2.continuousOn.mono Icc_subset_Ici_self)
          (by
            intro r hr
            exact (hz.2 r hr.1).mono
              (Ici_subset_Ici.mpr hr.1))
          (by
            intro r hr
            have hrnonneg : 0 ≤ r := hr.1
            have hrlt : r < ε :=
              lt_of_le_of_lt hr.2 hs
            have hrregular :
                jacobiTheta1 (p.xi r) (p.tau r : ℂ) ≠ 0 := by
              apply hε
              simpa [Real.dist_eq, abs_of_nonneg hrnonneg] using
                hrlt
            exact
              ((p.jacobiBlochPath_isScaledAt
                hc0 hrregular).point_hasDerivAt).continuousAt
                |>.continuousWithinAt)
          (by
            intro r hr
            have hrnonneg : 0 ≤ r := hr.1
            have hrlt : r < ε := lt_trans hr.2 hs
            have hrregular :
                jacobiTheta1 (p.xi r) (p.tau r : ℂ) ≠ 0 := by
              apply hε
              simpa [Real.dist_eq, abs_of_nonneg hrnonneg] using
                hrlt
            exact
              ((p.jacobiBlochPath_isScaledAt
                hc0 hrregular).point_hasDerivAt).hasDerivWithinAt)
          (by
            exact congrArg JacobiPolynomialCode.point
              (p.state_eq_of_core_eq hc0 hinitial
                (hreciprocal 0 le_rfl)))
      have hpoint :=
        heqOn ⟨hsnonneg, le_rfl⟩
      have hstateCore :=
        congrArg
          (fun q =>
            jacobiCorePoint (JacobiPolynomialCode.state q))
          hpoint
      simpa only [agreement] using hstateCore
    · have htpos : 0 < (t.1 : ℝ) :=
        lt_of_le_of_ne t.2 (Ne.symm htzero)
      have hregular :
          jacobiTheta1 (p.xi t.1) (p.tau t.1 : ℂ) ≠ 0 :=
        p.regular_of_core_eq ht
          (hreciprocal t.1 t.2)
      have hregularEventually :
          ∀ᶠ s in nhds t.1,
            jacobiTheta1 (p.xi s) (p.tau s : ℂ) ≠ 0 :=
        p.continuous_jacobiTheta1_comp.continuousAt.eventually
          (isOpen_compl_singleton.mem_nhds hregular)
      have hpositiveEventually :
          ∀ᶠ s in nhds t.1, 0 < s :=
        Ioi_mem_nhds htpos
      have hstate :
          z t.1 = p.jacobiBlochPath t.1 :=
        p.state_eq_of_core_eq hc0 ht
          (hreciprocal t.1 t.2)
      have hleft :
          ∀ᶠ s in nhds t.1,
            HasDerivAt
              (fun u => JacobiPolynomialCode.point (z u))
              (jacobiCoordinateVectorField
                ((π : ℂ) * (p.nu : ℂ))
                ((π : ℂ) * I * (p.kappa : ℂ))
                (JacobiPolynomialCode.point (z s))) s := by
        filter_upwards [hpositiveEventually] with s hs
        exact (hz.2 s hs.le).hasDerivAt (Ici_mem_nhds hs)
      have hright :
          ∀ᶠ s in nhds t.1,
            HasDerivAt
              (fun u =>
                JacobiPolynomialCode.point
                  (p.jacobiBlochPath u))
              (jacobiCoordinateVectorField
                ((π : ℂ) * (p.nu : ℂ))
                ((π : ℂ) * I * (p.kappa : ℂ))
                (JacobiPolynomialCode.point
                  (p.jacobiBlochPath s))) s := by
        filter_upwards [hregularEventually] with s hs
        exact
          (p.jacobiBlochPath_isScaledAt
            hc0 hs).point_hasDerivAt
      have hpointEventually :
          (fun s => JacobiPolynomialCode.point (z s)) =ᶠ[nhds t.1]
            (fun s =>
              JacobiPolynomialCode.point
                (p.jacobiBlochPath s)) := by
        apply
          HGAS.Analysis.autonomousC1_ode_solution_eventuallyEq
            (contDiff_jacobiCoordinateVectorField
              ((π : ℂ) * (p.nu : ℂ))
              ((π : ℂ) * I * (p.kappa : ℂ)))
            hleft hright
        · exact
            ((hz.2 t.1 t.2).hasDerivAt
              (Ici_mem_nhds htpos)).continuousAt
        · exact
            ((p.jacobiBlochPath_isScaledAt
              hc0 hregular).point_hasDerivAt).continuousAt
        · exact congrArg JacobiPolynomialCode.point hstate
      have hpointSubtype :
          ∀ᶠ s : forwardRay in nhds t,
            JacobiPolynomialCode.point (z s.1) =
              JacobiPolynomialCode.point
                (p.jacobiBlochPath s.1) :=
        hpointEventually.comp_tendsto
          continuous_subtype_val.continuousAt
      filter_upwards [hpointSubtype] with s hs
      have hstateCore :=
        congrArg
          (fun q =>
            jacobiCorePoint (JacobiPolynomialCode.state q))
          hs
      simpa only [agreement] using hstateCore
  letI : PreconnectedSpace forwardRay :=
    Subtype.preconnectedSpace isPreconnected_Ici
  have hagreement_univ :
      agreement = Set.univ :=
    IsClopen.eq_univ
      ⟨hagreement_closed, hagreement_open⟩
      ⟨⟨0, by simp [forwardRay]⟩,
        by simpa only [agreement] using hinitial⟩
  have hcore :
      ∀ t, 0 ≤ t →
        jacobiCorePoint (z t) =
          jacobiCorePoint (p.jacobiBlochPath t) := by
    intro t ht
    have hmem : (⟨t, ht⟩ : forwardRay) ∈ agreement := by
      rw [hagreement_univ]
      exact Set.mem_univ _
    exact hmem
  have hregular :
      ∀ t, 0 ≤ t →
        jacobiTheta1 (p.xi t) (p.tau t : ℂ) ≠ 0 :=
    fun t ht => p.regular_of_core_eq
      (hcore t ht) (hreciprocal t ht)
  exact
    ⟨hregular, fun t ht =>
      p.state_eq_of_core_eq hc0
        (hcore t ht) (hreciprocal t ht)⟩

end AffineBlochParameters

end

end HGAS.Modular
