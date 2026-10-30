import HGAS.Stability.KordaLyapunov
import HGAS.Dynamics.AngularPhysicalTimeChange
import HGAS.Dynamics.ProductGAS
import Mathlib.Tactic

/-!
# The angular criterion for Lyapunov stability (Korda's Lemma 2.2)

Let `F` be homogeneous of degree `k+1` on a finite-dimensional real inner
product space.  On the unit sphere, the radial rate `a(u) = ⟪u, F u⟫` is
integrated along the angular flow `u' = F u - a(u) u` to the logarithmic
cocycle `A(τ,u)`.  Korda's Lemma 2.2 states that the origin is Lyapunov
stable (with existence of solutions) if and only if the cocycle is bounded
above on `τ ≥ 0`, uniformly in the initial direction.

The proof uses the angular reconstruction `x(τ) = exp(A(τ,u)) φ_τ(u)`, which
solves `x' = exp(-k A) F(x)`, together with compact-interval uniqueness:

* every forward trajectory from a unit vector, sampled at the physical clock,
  is the angular reconstruction (`reconstruction_eq_forwardTrajectory`);
* conversely, when the cocycle is bounded, inverting the physical clock turns
  the reconstruction into a forward trajectory.
-/

namespace HGAS

open Filter Set
open scoped Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The logarithmic radial cocycle is bounded above on forward angular time,
uniformly over the unit sphere. -/
def HasBoundedEuclideanAngularCocycle
    (F : E → E) (hF : ContDiff ℝ 1 F) : Prop :=
  ∃ M : ℝ, ∀ u : E, ‖u‖ = 1 → ∀ τ : ℝ, 0 ≤ τ →
    euclideanAngularLogRadius F hF τ u ≤ M

/-- Every forward trajectory from a unit vector, sampled at the physical
clock, is the angular reconstruction. -/
theorem reconstruction_eq_forwardTrajectory
    (F : E → E) (hF : ContDiff ℝ 1 F) (k : ℕ)
    (hFhom : ScalesAsDegree ℝ (k + 1) F)
    {u : E} (hu : ‖u‖ = 1) {γ : ℝ → E}
    (hγ : IsForwardTrajectory F γ u)
    {L : ℝ} (hL : 0 ≤ L) :
    euclideanAngularReconstruction F hF L u =
      γ (euclideanAngularPhysicalClock F hF k L u) := by
  let clock : ℝ → ℝ := fun τ ↦ euclideanAngularPhysicalClock F hF k τ u
  let ρ : ℝ → E := fun τ ↦ euclideanAngularReconstruction F hF τ u
  let η : ℝ → E := fun τ ↦ γ (clock τ)
  have hclock_cont : Continuous clock :=
    integralClock_continuous
      (contDiff_one_euclideanAngularPhysicalSpeed F hF k u).continuous
  have hclock_maps : ∀ {τ : ℝ}, 0 ≤ τ → MapsTo clock (Ici τ) (Ici 0) := by
    intro τ hτ s hs
    exact euclideanAngularPhysicalClock_nonneg F hF k u (le_trans hτ hs)
  have heqOn : EqOn ρ η (Icc (0 : ℝ) L) := by
    apply timeDependent_ode_solution_unique_Icc_right_of_contDiff
      (angularScaledPhysicalField F hF k u)
      (contDiff_one_uncurry_angularScaledPhysicalField F hF k u)
    · exact
        (contDiff_one_euclideanAngularReconstruction F hF u).continuous.continuousOn
    · intro τ hτ
      exact
        (hasDerivAt_euclideanAngularReconstruction
          F hF k hFhom u hu τ).hasDerivWithinAt
    · have hγc : ContinuousOn γ (Ici 0) := hγ.2.continuousOn
      exact hγc.comp hclock_cont.continuousOn
        ((hclock_maps le_rfl).mono_left Icc_subset_Ici_self)
    · intro τ hτ
      have hτ0 : 0 ≤ τ := hτ.1
      have hc0 : 0 ≤ clock τ := euclideanAngularPhysicalClock_nonneg F hF k u hτ0
      have hγd : HasDerivWithinAt γ (F (γ (clock τ))) (Ici 0) (clock τ) :=
        hγ.2 (clock τ) hc0
      have hcd : HasDerivWithinAt clock
          (euclideanAngularPhysicalSpeed F hF k τ u) (Ici τ) τ :=
        (hasDerivAt_euclideanAngularPhysicalClock F hF k u τ).hasDerivWithinAt
      have hcomp := hγd.scomp τ hcd (hclock_maps hτ0)
      simpa only [angularScaledPhysicalField, η] using hcomp
    · simp only [ρ, η, clock, euclideanAngularReconstruction_zero,
        euclideanAngularPhysicalClock_zero]
      exact hγ.1.symm
  exact heqOn ⟨hL, le_rfl⟩

/-- Lyapunov stability bounds the angular cocycle. -/
theorem hasBoundedEuclideanAngularCocycle_of_lyapunovStableWithExistence
    (F : E → E) (hF : ContDiff ℝ 1 F) (k : ℕ)
    (hFhom : ScalesAsDegree ℝ (k + 1) F)
    (hstable : LyapunovStableWithExistence F 0) :
    HasBoundedEuclideanAngularCocycle F hF := by
  obtain ⟨C, hC, hbound⟩ :=
    (lyapunovStableWithExistence_iff_uniformLinearTrajectoryBound F k
      (fun c x ↦ hFhom c x)).mp hstable
  refine ⟨Real.log C, ?_⟩
  intro u hu τ hτ
  obtain ⟨γ, hγ⟩ := (hbound u).1
  have hrec := reconstruction_eq_forwardTrajectory F hF k hFhom hu hγ hτ
  have hnorm : euclideanAngularRadius F hF τ u ≤ C := by
    rw [← norm_euclideanAngularReconstruction F hF u hu τ, hrec]
    have := (hbound u).2 γ hγ _
      (euclideanAngularPhysicalClock_nonneg F hF k u hτ)
    simpa [hu] using this
  have hlog := Real.log_le_log (euclideanAngularRadius_pos F hF τ u) hnorm
  simpa [euclideanAngularRadius, Real.log_exp] using hlog

/-- An integral clock whose speed is bounded below by a positive constant on
nonpositive times tends to `-∞`. -/
theorem integralClock_tendsto_atBot_of_ge_nonpos
    {w : ℝ → ℝ} (hw : Continuous w) {c : ℝ} (hc : 0 < c)
    (hge : ∀ t, t ≤ 0 → c ≤ w t) :
    Tendsto (integralClock w) atBot atBot := by
  apply tendsto_atBot_atBot.2
  intro M
  refine ⟨min 0 (M / c), ?_⟩
  intro t ht
  have ht0 : t ≤ 0 := le_trans ht (min_le_left _ _)
  have htM : t ≤ M / c := le_trans ht (min_le_right _ _)
  have hint : c * (0 - t) ≤ ∫ s in t..0, w s := by
    have hconst : (∫ _s in t..0, c) = c * (0 - t) := by
      simp [mul_comm]
    rw [← hconst]
    exact intervalIntegral.integral_mono_on ht0
      (continuous_const.intervalIntegrable t 0) (hw.intervalIntegrable t 0)
      (fun s hs ↦ hge s hs.2)
  have hclock : integralClock w t = -∫ s in t..0, w s := by
    simp only [integralClock]
    exact intervalIntegral.integral_symm (f := w) t 0
  rw [hclock]
  have hct : c * t ≤ M := by
    have := mul_le_mul_of_nonneg_left htM hc.le
    rwa [mul_div_cancel₀ M hc.ne'] at this
  linarith

/-- A bounded angular cocycle gives a forward trajectory through every unit
vector, obtained by inverting the physical clock of the reconstruction. -/
theorem exists_forwardTrajectory_of_boundedCocycle
    (F : E → E) (hF : ContDiff ℝ 1 F) (k : ℕ)
    (hFhom : ScalesAsDegree ℝ (k + 1) F)
    {M : ℝ}
    (hM : ∀ u : E, ‖u‖ = 1 → ∀ τ : ℝ, 0 ≤ τ →
      euclideanAngularLogRadius F hF τ u ≤ M)
    {u : E} (hu : ‖u‖ = 1) :
    ∃ γ : ℝ → E, IsForwardTrajectory F γ u := by
  let speed : ℝ → ℝ := fun τ ↦ euclideanAngularPhysicalSpeed F hF k τ u
  have hspeed_cont : Continuous speed :=
    (contDiff_one_euclideanAngularPhysicalSpeed F hF k u).continuous
  let w : ℝ → ℝ := fun τ ↦ speed |τ|
  have hw_cont : Continuous w := hspeed_cont.comp continuous_abs
  have hw_pos : ∀ τ, 0 < w τ := fun τ ↦
    euclideanAngularPhysicalSpeed_pos F hF k |τ| u
  set c : ℝ := Real.exp (-(k : ℝ) * M) with hc_def
  have hc : 0 < c := Real.exp_pos _
  have hw_ge : ∀ τ, c ≤ w τ := by
    intro τ
    simp only [w, speed, euclideanAngularPhysicalSpeed, hc_def]
    apply Real.exp_le_exp.mpr
    have hA := hM u hu |τ| (abs_nonneg τ)
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have hclock : PositiveIntegralClock w :=
    { continuous := hw_cont
      positive := hw_pos
      tendsto_atTop :=
        integralClock_tendsto_atTop_of_eventually_ge hw_cont hc
          (Eventually.of_forall hw_ge)
      tendsto_atBot :=
        integralClock_tendsto_atBot_of_ge_nonpos hw_cont hc
          (fun t _ ↦ hw_ge t) }
  let B : ℝ → ℝ := fun t ↦ (PositiveIntegralClock.orderIso hclock).symm t
  refine ⟨fun t ↦ euclideanAngularReconstruction F hF (B t) u, ?_, ?_⟩
  · simp [B, PositiveIntegralClock.symm_zero]
  · intro t ht
    have hB0 : 0 ≤ B t := PositiveIntegralClock.symm_nonneg hclock ht
    have hrec := hasDerivAt_euclideanAngularReconstruction F hF k hFhom u hu (B t)
    have hBd := PositiveIntegralClock.symm_hasDerivAt hclock t
    have hcomp := hrec.scomp t hBd
    have hwB : w (B t) = speed (B t) := by
      simp only [w, abs_of_nonneg hB0]
    have hspos : speed (B t) ≠ 0 := (euclideanAngularPhysicalSpeed_pos F hF k (B t) u).ne'
    have hval :
        (w (B t))⁻¹ • (euclideanAngularPhysicalSpeed F hF k (B t) u •
          F (euclideanAngularReconstruction F hF (B t) u)) =
        F (euclideanAngularReconstruction F hF (B t) u) := by
      rw [hwB, smul_smul]
      simp only [speed]
      rw [inv_mul_cancel₀ hspos, one_smul]
    rw [hval] at hcomp
    exact hcomp.hasDerivWithinAt

/-- A bounded angular cocycle bounds every forward trajectory from a unit
vector. -/
theorem norm_forwardTrajectory_le_of_boundedCocycle
    (F : E → E) (hF : ContDiff ℝ 1 F) (k : ℕ)
    (hFhom : ScalesAsDegree ℝ (k + 1) F)
    {M : ℝ}
    (hM : ∀ u : E, ‖u‖ = 1 → ∀ τ : ℝ, 0 ≤ τ →
      euclideanAngularLogRadius F hF τ u ≤ M)
    {u : E} (hu : ‖u‖ = 1) {γ : ℝ → E}
    (hγ : IsForwardTrajectory F γ u) {t : ℝ} (ht : 0 ≤ t) :
    ‖γ t‖ ≤ Real.exp M := by
  -- the physical clock on nonnegative angular time reaches every `t ≥ 0`
  let clock : ℝ → ℝ := fun τ ↦ euclideanAngularPhysicalClock F hF k τ u
  have hclock_cont : Continuous clock :=
    integralClock_continuous
      (contDiff_one_euclideanAngularPhysicalSpeed F hF k u).continuous
  set c : ℝ := Real.exp (-(k : ℝ) * M) with hc_def
  have hc : 0 < c := Real.exp_pos _
  have hspeed_ge : ∀ τ, 0 ≤ τ → c ≤ euclideanAngularPhysicalSpeed F hF k τ u := by
    intro τ hτ
    simp only [euclideanAngularPhysicalSpeed, hc_def]
    apply Real.exp_le_exp.mpr
    have hA := hM u hu τ hτ
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have hlower : c * (t / c) ≤ clock (t / c) := by
    have hτ : 0 ≤ t / c := div_nonneg ht hc.le
    have hconst : (∫ _s in (0 : ℝ)..(t / c), c) = c * (t / c) := by
      simp [mul_comm]
    simp only [clock, euclideanAngularPhysicalClock, integralClock]
    rw [← hconst]
    exact intervalIntegral.integral_mono_on hτ
      (continuous_const.intervalIntegrable _ _)
      ((contDiff_one_euclideanAngularPhysicalSpeed F hF k u).continuous.intervalIntegrable _ _)
      (fun s hs ↦ hspeed_ge s hs.1)
  have hct : c * (t / c) = t := by field_simp
  obtain ⟨L, hLmem, hLt⟩ :
      ∃ L ∈ Icc (0 : ℝ) (t / c), clock L = t := by
    have hivt := intermediate_value_Icc (div_nonneg ht hc.le)
      hclock_cont.continuousOn
    have h0 : clock 0 = 0 := euclideanAngularPhysicalClock_zero F hF k u
    have hmem : t ∈ Icc (clock 0) (clock (t / c)) := ⟨by rw [h0]; exact ht, by linarith⟩
    exact hivt hmem
  have hrec := reconstruction_eq_forwardTrajectory F hF k hFhom hu hγ hLmem.1
  rw [← hLt, ← hrec, norm_euclideanAngularReconstruction F hF u hu L]
  simp only [euclideanAngularRadius]
  exact Real.exp_le_exp.mpr (hM u hu L hLmem.1)

/-- **Korda's Lemma 2.2 (Euclidean form).**  For a `C¹` field homogeneous of
degree `k+1` with `F 0 = 0`, the origin is Lyapunov stable (with existence of
solutions) if and only if the logarithmic radial cocycle of the angular flow
is bounded above on forward angular time, uniformly on the unit sphere. -/
theorem lyapunovStableWithExistence_iff_boundedEuclideanAngularCocycle
    (F : E → E) (hF : ContDiff ℝ 1 F) (k : ℕ)
    (hFhom : ScalesAsDegree ℝ (k + 1) F) (hzero : F 0 = 0) :
    LyapunovStableWithExistence F 0 ↔
      HasBoundedEuclideanAngularCocycle F hF := by
  refine ⟨hasBoundedEuclideanAngularCocycle_of_lyapunovStableWithExistence
    F hF k hFhom, ?_⟩
  rintro ⟨M, hM⟩
  apply lyapunovStableWithExistence_of_uniformLinearTrajectoryBound
  refine ⟨Real.exp M, Real.exp_pos M, ?_⟩
  intro x₀
  by_cases hx₀ : x₀ = 0
  · subst hx₀
    refine ⟨⟨fun _ ↦ 0, isForwardTrajectory_const_of_equilibrium hzero⟩, ?_⟩
    intro γ hγ t ht
    -- uniqueness: the only forward trajectory from the origin is constant
    have hconst := isForwardTrajectory_const_of_equilibrium (F := F) hzero
    have heq : EqOn γ (fun _ ↦ (0 : E)) (Icc 0 t) := by
      apply ode_solution_unique_Icc_right_of_contDiff hF
      · exact hγ.2.continuousOn.mono Icc_subset_Ici_self
      · intro s hs
        exact (hγ.2 s hs.1).mono (Ici_subset_Ici.mpr hs.1)
      · exact continuousOn_const
      · intro s hs
        exact (hconst.2 s hs.1).mono (Ici_subset_Ici.mpr hs.1)
      · exact hγ.1
    have := heq ⟨ht, le_rfl⟩
    simp [this]
  · have hr : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀
    set r : ℝ := ‖x₀‖ with hr_def
    set u : E := r⁻¹ • x₀ with hu_def
    have hu : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le),
        inv_mul_cancel₀ hr.ne']
    have hx₀u : x₀ = r • u := by
      rw [hu_def, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hFscale : ∀ (c : ℝ) (x : E), F (c • x) = c ^ (k + 1) • F x :=
      fun c x ↦ hFhom c x
    constructor
    · obtain ⟨γ, hγ⟩ := exists_forwardTrajectory_of_boundedCocycle F hF k hFhom hM hu
      refine ⟨scaledForwardCurve k r γ, ?_⟩
      rw [hx₀u]
      exact hγ.scale_of_homogeneous F k hFscale r hr.le
    · intro γ hγ t ht
      -- rescale `γ` to a trajectory from the unit vector `u`
      have hγ' := hγ.scale_of_homogeneous F k hFscale r⁻¹ (inv_nonneg.mpr hr.le)
      have hstart : r⁻¹ • x₀ = u := rfl
      rw [hstart] at hγ'
      have hs : 0 ≤ t * (r⁻¹ ^ k)⁻¹ := mul_nonneg ht
        (inv_nonneg.mpr (pow_nonneg (inv_nonneg.mpr hr.le) k))
      have hb := norm_forwardTrajectory_le_of_boundedCocycle F hF k hFhom hM hu hγ' hs
      have hrk : (r⁻¹ ^ k) ≠ 0 := pow_ne_zero k (inv_ne_zero hr.ne')
      have htime : t * (r⁻¹ ^ k)⁻¹ * r⁻¹ ^ k = t := by field_simp
      simp only [scaledForwardCurve, htime, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hr.le)] at hb
      have : ‖γ t‖ ≤ r * Real.exp M := by
        have := mul_le_mul_of_nonneg_left hb hr.le
        rwa [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at this
      linarith [this, mul_comm r (Real.exp M)]

end

end HGAS
