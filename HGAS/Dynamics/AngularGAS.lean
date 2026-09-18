import HGAS.Dynamics.Angular
import HGAS.Dynamics.HomogeneousScaling
import HGAS.Dynamics.UniformNegativeBlocks
import HGAS.Dynamics.ForwardCompleteness
import HGAS.Dynamics.LyapunovDirect
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Angular criteria for homogeneous global asymptotic stability

This module formalizes the parts of the homogeneous angular criterion that
are internal to the present development.

* For a real inner-product space, it proves the exact radial and angular
  differential equations of a homogeneous physical trajectory.
* It proves the corresponding equations after the positive angular time
  change.
* It turns a uniform negative angular block into a uniform affine upper
  bound for the radial cocycle, hence exponential radial decay and a
  uniform overshoot estimate.
* It packages the final transfer to the trajectory-based GAS definition
  behind an explicit polar-realization interface.  This interface records
  precisely the ODE continuation, uniqueness, and time-change facts needed
  to transport the angular estimates to every physical trajectory.
* In the converse direction it proves Euler's identity for an explicitly
  homogeneous `C¹` Lyapunov function, the angular logarithmic coboundary
  identity, and the invariant-measure calculation.  No converse Lyapunov
  theorem is postulated here.

Thus the only missing ingredient for the unconditional reverse implication
from GAS is an independently formalized homogeneous converse Lyapunov
theorem (for example Rosier's theorem), together with its regularity
hypotheses.
-/

noncomputable section

open Function MeasureTheory Set Filter Topology
open scoped BoundedContinuousFunction Interval RealInnerProductSpace

namespace HGAS

/-! ## Inner-product radial and angular fields -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Radial reward in a real inner-product space. -/
def innerRadialReward (F : E → E) (u : E) : ℝ :=
  ⟪u, F u⟫

/-- Tangential component of a vector field relative to the unit sphere. -/
def innerAngularField (F : E → E) (u : E) : E :=
  F u - innerRadialReward F u • u

/-- Radial-angular decomposition in an inner-product space. -/
theorem innerAngularField_add_radial
    (F : E → E) (u : E) :
    innerAngularField F u + innerRadialReward F u • u = F u := by
  simp [innerAngularField]

/-- The inner angular field is tangent to the unit sphere. -/
theorem inner_innerAngularField
    (F : E → E) (u : E) (hu : ‖u‖ = 1) :
    ⟪u, innerAngularField F u⟫ = 0 := by
  simp [innerAngularField, innerRadialReward, inner_sub_right,
    real_inner_smul_right, hu]

/-- A differentiable curve constrained to the unit sphere has tangent
velocity. -/
theorem inner_eq_zero_of_hasDerivAt_of_norm_eq_one
    {u : ℝ → E} {u' : E} {t : ℝ}
    (hu : HasDerivAt u u' t)
    (hunit : ∀ s : ℝ, ‖u s‖ = 1) :
    ⟪u t, u'⟫ = 0 := by
  have hnorm :
      HasDerivAt (fun s ↦ ‖u s‖ ^ 2)
        (2 * ⟪u t, u'⟫) t :=
    hu.norm_sq
  have heq : (fun s : ℝ ↦ ‖u s‖ ^ 2) = fun _ ↦ (1 : ℝ) := by
    funext s
    rw [hunit s]
    norm_num
  rw [heq] at hnorm
  have hzero :
      (2 : ℝ) * ⟪u t, u'⟫ = 0 :=
    hnorm.unique (hasDerivAt_const t 1)
  linarith

/-- Exact physical-time polar equations at one time.

The field has homogeneous degree `k+1`.  If `γ = r • u`, `u` stays on the
unit sphere, and `r(t)>0`, then

`r' = r^(k+1) a(u)` and `u' = r^k Y(u)`.

No existence or uniqueness theorem is used: this is a pointwise chain-rule
identity for any supplied differentiable trajectory and polar
decomposition. -/
theorem polar_physical_equations_at
    (F : E → E) (k : ℕ)
    (hF : ScalesAsDegree ℝ (k + 1) F)
    {γ : ℝ → E} {r : ℝ → ℝ} {u : ℝ → E}
    {t r' : ℝ} {u' : E}
    (hγ : HasDerivAt γ (F (γ t)) t)
    (hr : HasDerivAt r r' t)
    (hu : HasDerivAt u u' t)
    (hpolar : γ = fun s ↦ r s • u s)
    (hunit : ∀ s : ℝ, ‖u s‖ = 1)
    (hrpos : 0 < r t) :
    r' = r t ^ (k + 1) * innerRadialReward F (u t) ∧
      u' = r t ^ k • innerAngularField F (u t) := by
  have htangent : ⟪u t, u'⟫ = 0 :=
    inner_eq_zero_of_hasDerivAt_of_norm_eq_one hu hunit
  have hproduct :
      HasDerivAt (fun s ↦ r s • u s)
        (r t • u' + r' • u t) t :=
    hr.smul hu
  rw [hpolar] at hγ
  have hvelocity :
      F (r t • u t) = r t • u' + r' • u t :=
    hγ.unique hproduct
  have hhom := hF (r t) (u t)
  rw [hhom] at hvelocity
  have hdot :=
    congrArg (fun z : E ↦ ⟪u t, z⟫) hvelocity
  have hradius :
      r' = r t ^ (k + 1) * innerRadialReward F (u t) := by
    simp only [inner_add_right, real_inner_smul_right,
      htangent, mul_zero, zero_add,
      real_inner_self_eq_norm_sq, hunit t, one_pow, mul_one] at hdot
    exact hdot.symm
  refine ⟨hradius, ?_⟩
  apply smul_right_injective E hrpos.ne'
  rw [hradius] at hvelocity
  change r t • u' = r t • (r t ^ k • innerAngularField F (u t))
  simp only [innerAngularField, smul_sub, smul_smul]
  rw [pow_succ] at hvelocity
  rw [eq_sub_iff_add_eq]
  convert hvelocity.symm using 1 <;> ring_nf

/-- Physical-time logarithmic radial equation. -/
theorem hasDerivAt_log_radius
    (F : E → E) (k : ℕ)
    (hF : ScalesAsDegree ℝ (k + 1) F)
    {γ : ℝ → E} {r : ℝ → ℝ} {u : ℝ → E}
    {t r' : ℝ} {u' : E}
    (hγ : HasDerivAt γ (F (γ t)) t)
    (hr : HasDerivAt r r' t)
    (hu : HasDerivAt u u' t)
    (hpolar : γ = fun s ↦ r s • u s)
    (hunit : ∀ s : ℝ, ‖u s‖ = 1)
    (hrpos : 0 < r t) :
    HasDerivAt (fun s ↦ Real.log (r s))
      (r t ^ k * innerRadialReward F (u t)) t := by
  have hradius :=
    (polar_physical_equations_at F k hF hγ hr hu hpolar hunit hrpos).1
  convert hr.log hrpos.ne' using 1
  rw [hradius, pow_succ]
  field_simp [hrpos.ne']

/-- Exact angular-time equations obtained by composing a physical polar
trajectory with a clock whose derivative is `r⁻ᵏ`.

This is the differential form of
`dτ/dt = r^k`, or equivalently `dt/dτ = r⁻ᵏ`. -/
theorem polar_angular_time_equations_at
    (F : E → E) (k : ℕ)
    (hF : ScalesAsDegree ℝ (k + 1) F)
    {γ : ℝ → E} {r : ℝ → ℝ} {u : ℝ → E}
    {clock : ℝ → ℝ} {τ r' : ℝ} {u' : E}
    (hγ : HasDerivAt γ (F (γ (clock τ))) (clock τ))
    (hr : HasDerivAt r r' (clock τ))
    (hu : HasDerivAt u u' (clock τ))
    (hpolar : γ = fun s ↦ r s • u s)
    (hunit : ∀ s : ℝ, ‖u s‖ = 1)
    (hrpos : 0 < r (clock τ))
    (hclock : HasDerivAt clock (r (clock τ) ^ k)⁻¹ τ) :
    HasDerivAt (u ∘ clock)
        (innerAngularField F (u (clock τ))) τ ∧
      HasDerivAt (fun s ↦ Real.log (r (clock s)))
        (innerRadialReward F (u (clock τ))) τ := by
  obtain ⟨hradius, huangular⟩ :=
    polar_physical_equations_at F k hF hγ hr hu hpolar hunit hrpos
  have hkpos : r (clock τ) ^ k ≠ 0 :=
    pow_ne_zero _ hrpos.ne'
  constructor
  · have hcomp := hu.scomp τ hclock
    convert hcomp using 1
    rw [huangular, inv_smul_smul₀ hkpos]
  · have hlog :=
      hasDerivAt_log_radius F k hF hγ hr hu hpolar hunit hrpos
    have hcomp := hlog.scomp τ hclock
    convert hcomp using 1
    simp [smul_eq_mul, hkpos, mul_comm]

end HGAS

namespace HGAS.Dynamics

/-! ## Quantitative consequences of a negative angular block -/

variable {K : Type*} [TopologicalSpace K]

/-- A negative block estimate controls every nonnegative orbit segment by
an affine function with strictly negative slope.

The proof writes `τ = nT + R`, with `n = ⌊τ/T⌋` and `0 ≤ R < T`.
The `n` complete blocks contribute at most `-nc`; the last incomplete
block can contribute at most `‖a‖T`. -/
theorem orbitIntegral_le_affine_of_uniformNegativeBlock
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) {T c : ℝ}
    (hT : 0 < T) (hc : 0 < c)
    (hblock : ∀ x : K, orbitIntegral ϕ a T x ≤ -c)
    {τ : ℝ} (hτ : 0 ≤ τ) (x : K) :
    orbitIntegral ϕ a τ x ≤
      c + ‖a‖ * T - (c / T) * τ := by
  let n : ℕ := ⌊τ / T⌋₊
  let R : ℝ := τ - (n : ℝ) * T
  have hratio_nonneg : 0 ≤ τ / T :=
    div_nonneg hτ hT.le
  have hn_le : (n : ℝ) ≤ τ / T := by
    exact Nat.floor_le hratio_nonneg
  have hratio_lt : τ / T < (n : ℝ) + 1 := by
    exact Nat.lt_floor_add_one (τ / T)
  have hnT_le : (n : ℝ) * T ≤ τ := by
    exact (le_div_iff₀ hT).mp hn_le
  have hR_nonneg : 0 ≤ R := by
    exact sub_nonneg.mpr hnT_le
  have hR_le : R ≤ T := by
    apply (sub_le_iff_le_add).2
    apply (div_lt_iff₀ hT).mp at hratio_lt
    simpa only [add_mul, one_mul, add_comm] using hratio_lt.le
  have hdecomp : τ = (n : ℝ) * T + R := by
    simp only [R]
    ring
  rw [hdecomp, orbitIntegral_add]
  have hfull :
      orbitIntegral ϕ a ((n : ℝ) * T) x ≤ -(n : ℝ) * c := by
    exact orbitIntegral_nat_mul_le ϕ a hblock n x
  have htail :
      orbitIntegral ϕ a R (ϕ ((n : ℝ) * T) x) ≤ ‖a‖ * T := by
    calc
      orbitIntegral ϕ a R (ϕ ((n : ℝ) * T) x) ≤
          |orbitIntegral ϕ a R (ϕ ((n : ℝ) * T) x)| :=
        le_abs_self _
      _ = ‖orbitIntegral ϕ a R (ϕ ((n : ℝ) * T) x)‖ := by
        rw [Real.norm_eq_abs]
      _ ≤ ‖a‖ * |R| :=
        norm_orbitIntegral_le ϕ a R _
      _ = ‖a‖ * R := by rw [abs_of_nonneg hR_nonneg]
      _ ≤ ‖a‖ * T :=
        mul_le_mul_of_nonneg_left hR_le (norm_nonneg a)
  have hscaled :
      c * (τ / T) ≤ c * ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hratio_lt.le hc.le
  have hquotient : (c / T) * τ = c * (τ / T) := by
    field_simp [hT.ne']
  rw [hdecomp] at hscaled hquotient
  calc
    orbitIntegral ϕ a ((n : ℝ) * T) x +
          orbitIntegral ϕ a R (ϕ ((n : ℝ) * T) x) ≤
        (-(n : ℝ) * c) + ‖a‖ * T :=
      add_le_add hfull htail
    _ ≤ c + ‖a‖ * T -
          (c / T) * ((n : ℝ) * T + R) := by
      rw [hquotient]
      nlinarith

end HGAS.Dynamics

namespace HGAS

/-! ## The angular radial cocycle and its transfer to physical trajectories -/

variable {K : Type*} [TopologicalSpace K]

/-- Radius reconstructed from an angular orbit and its logarithmic radial
cocycle.  In applications, `r₀` is the norm of the physical initial
condition. -/
def angularRadius
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ)
    (r₀ τ : ℝ) (u : K) : ℝ :=
  r₀ * Real.exp (Dynamics.orbitIntegral ϕ a τ u)

@[simp]
theorem angularRadius_zero
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) (τ : ℝ) (u : K) :
    angularRadius ϕ a 0 τ u = 0 := by
  simp [angularRadius]

theorem angularRadius_nonneg
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ)
    {r₀ τ : ℝ} (hr₀ : 0 ≤ r₀) (u : K) :
    0 ≤ angularRadius ϕ a r₀ τ u :=
  mul_nonneg hr₀ (Real.exp_pos _).le

/-- Quantitative exponential estimate obtained from a negative block. -/
theorem angularRadius_le_exp_decay
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) {T c r₀ τ : ℝ}
    (hT : 0 < T) (hc : 0 < c)
    (hblock : ∀ x : K, Dynamics.orbitIntegral ϕ a T x ≤ -c)
    (hr₀ : 0 ≤ r₀) (hτ : 0 ≤ τ) (u : K) :
    angularRadius ϕ a r₀ τ u ≤
      r₀ * Real.exp (c + ‖a‖ * T - (c / T) * τ) := by
  apply mul_le_mul_of_nonneg_left _ hr₀
  rw [Real.exp_le_exp]
  exact Dynamics.orbitIntegral_le_affine_of_uniformNegativeBlock
    ϕ a hT hc hblock hτ u

/-- Uniform overshoot estimate, independent of angular time and initial
direction.  This is the estimate used for Lyapunov stability. -/
theorem angularRadius_le_overshoot
    (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) {T c r₀ τ : ℝ}
    (hT : 0 < T) (hc : 0 < c)
    (hblock : ∀ x : K, Dynamics.orbitIntegral ϕ a T x ≤ -c)
    (hr₀ : 0 ≤ r₀) (hτ : 0 ≤ τ) (u : K) :
    angularRadius ϕ a r₀ τ u ≤
      r₀ * Real.exp (c + ‖a‖ * T) := by
  calc
    angularRadius ϕ a r₀ τ u ≤
        r₀ * Real.exp (c + ‖a‖ * T - (c / T) * τ) :=
      angularRadius_le_exp_decay ϕ a hT hc hblock hr₀ hτ u
    _ ≤ r₀ * Real.exp (c + ‖a‖ * T) := by
      apply mul_le_mul_of_nonneg_left _ hr₀
      rw [Real.exp_le_exp]
      have hrate : 0 ≤ c / T := (div_pos hc hT).le
      nlinarith [mul_nonneg hrate hτ]

/-- The exact interface between the angular cocycle and all physical
trajectories.

For every physical trajectory, `represent` supplies an initial angular
state and an angular clock.  The clock is nonnegative on forward physical
time and tends to infinity, and the physical distance to the origin is
exactly the angular radial cocycle.  The local differential identities
proved above explain how this interface is obtained from polar
coordinates.  Constructing it globally requires the standard ODE
existence/uniqueness, noncollision, inverse-clock, and continuation
arguments, so those facts are exposed here rather than hidden as axioms. -/
structure AngularCocycleRealization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (ϕ : Flow ℝ K) (a : K →ᵇ ℝ) : Prop where
  equilibrium : F 0 = 0
  forwardComplete : ForwardComplete F
  represent :
    ∀ (x₀ : E) (γ : ℝ → E), IsForwardTrajectory F γ x₀ →
      ∃ (u : K) (clock : ℝ → ℝ),
        clock 0 = 0 ∧
        (∀ t : ℝ, 0 ≤ t → 0 ≤ clock t) ∧
        Tendsto clock atTop atTop ∧
        ∀ t : ℝ, 0 ≤ t →
          dist (γ t) 0 =
            angularRadius ϕ a (dist x₀ 0) (clock t) u

/-- A uniform negative angular block implies GAS for every physical system
equipped with a global angular-cocycle realization. -/
theorem globallyAsymptoticallyStable_of_uniformNegativeAngularBlock
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Type*} [MetricSpace K]
    (F : E → E) (ϕ : Flow ℝ K) (a : K →ᵇ ℝ)
    (hrealize : AngularCocycleRealization F ϕ a)
    (hblock : Dynamics.HasUniformNegativeBlock ϕ a) :
    GloballyAsymptoticallyStable F 0 := by
  obtain ⟨T, c, hT, hc, hblock⟩ := hblock
  refine
    { equilibrium := hrealize.equilibrium
      forwardComplete := hrealize.forwardComplete
      stable := ?_
      attractive := ?_ }
  · intro ε hε
    let C : ℝ := Real.exp (c + ‖a‖ * T)
    have hC : 0 < C := Real.exp_pos _
    refine ⟨ε / C, div_pos hε hC, ?_⟩
    intro x₀ hx₀ γ hγ t ht
    obtain ⟨u, clock, _, hclock_nonneg, _, hradius⟩ :=
      hrealize.represent x₀ γ hγ
    rw [hradius t ht]
    calc
      angularRadius ϕ a (dist x₀ 0) (clock t) u ≤
          dist x₀ 0 * C := by
        exact angularRadius_le_overshoot ϕ a hT hc hblock
          (dist_nonneg) (hclock_nonneg t ht) u
      _ < (ε / C) * C :=
        mul_lt_mul_of_pos_right hx₀ hC
      _ = ε := by field_simp [hC.ne']
  · intro x₀ γ hγ ε hε
    obtain ⟨u, clock, _, hclock_nonneg, hclock_top, hradius⟩ :=
      hrealize.represent x₀ γ hγ
    by_cases hx₀ : dist x₀ 0 = 0
    · refine ⟨0, le_rfl, ?_⟩
      intro t ht
      rw [hradius t (le_trans le_rfl ht), hx₀, angularRadius_zero]
      exact hε
    · have hx₀pos : 0 < dist x₀ 0 :=
        lt_of_le_of_ne dist_nonneg (Ne.symm hx₀)
      have hratio : 0 < ε / dist x₀ 0 :=
        div_pos hε hx₀pos
      let rate : ℝ := c / T
      have hrate : 0 < rate := div_pos hc hT
      let threshold : ℝ :=
        (c + ‖a‖ * T - Real.log (ε / dist x₀ 0) + 1) / rate
      have heventually :
          ∀ᶠ t in atTop, threshold ≤ clock t :=
        hclock_top (eventually_ge_atTop threshold)
      obtain ⟨t₀, ht₀⟩ := (eventually_atTop.1 heventually)
      refine ⟨max 0 t₀, le_max_left _ _, ?_⟩
      intro t ht
      have ht_t₀ : t₀ ≤ t := le_trans (le_max_right _ _) ht
      have ht_nonneg : 0 ≤ t := le_trans (le_max_left _ _) ht
      have hclock_ge : threshold ≤ clock t := ht₀ t ht_t₀
      rw [hradius t ht_nonneg]
      have hcocycle :=
        angularRadius_le_exp_decay ϕ a hT hc hblock
          (dist_nonneg : 0 ≤ dist x₀ 0)
          (hclock_nonneg t ht_nonneg) u
      apply lt_of_le_of_lt hcocycle
      have hexponent :
          c + ‖a‖ * T - rate * clock t <
            Real.log (ε / dist x₀ 0) := by
        dsimp only [threshold] at hclock_ge
        have hmul := mul_le_mul_of_nonneg_left hclock_ge hrate.le
        have hcancel : rate *
            ((c + ‖a‖ * T - Real.log (ε / dist x₀ 0) + 1) /
              rate) =
            c + ‖a‖ * T - Real.log (ε / dist x₀ 0) + 1 := by
          field_simp [hrate.ne']
        rw [hcancel] at hmul
        dsimp only [rate]
        linarith
      calc
        dist x₀ 0 *
              Real.exp (c + ‖a‖ * T - (c / T) * clock t) <
            dist x₀ 0 *
              Real.exp (Real.log (ε / dist x₀ 0)) := by
          apply mul_lt_mul_of_pos_left _ hx₀pos
          rw [Real.exp_lt_exp]
          simpa only [rate] using hexponent
        _ = ε := by
          rw [Real.exp_log hratio]
          field_simp [hx₀pos.ne']

/-! ## A strict homogeneous `C¹` Lyapunov hypothesis -/

/-- Data supplied by a positive, strict, homogeneous `C¹` Lyapunov
function.

This is deliberately a hypothesis structure, not a converse Lyapunov
theorem.  In particular, constructing this data from GAS is the external
Rosier-type input needed for the reverse direction of the paper's angular
criterion. -/
structure StrictHomogeneousC1Lyapunov
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (degree : ℕ) where
  V : E → ℝ
  contDiff : ContDiff ℝ 1 V
  degree_pos : 0 < degree
  homogeneous :
    ∀ (s : ℝ), 0 < s → ∀ x : E,
      V (s • x) = s ^ degree * V x
  positive :
    ∀ x : E, x ≠ 0 → 0 < V x
  decreases :
    ∀ x : E, x ≠ 0 →
      fderiv ℝ V x (F x) < 0

namespace StrictHomogeneousC1Lyapunov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : E → E} {degree : ℕ}

/-- Euler's identity for a positively homogeneous `C¹` function:
`DV(x)[x] = degree · V(x)`.

Only positive homogeneity is needed: it gives equality of the two scalar
functions on a neighborhood of the positive point `s = 1`, hence equality
of their derivatives there. -/
theorem euler_identity
    (L : StrictHomogeneousC1Lyapunov F degree) (x : E) :
    fderiv ℝ L.V x x = (degree : ℝ) * L.V x := by
  have hscale :
      HasDerivAt (fun s : ℝ ↦ s • x) x 1 := by
    simpa using
      (HasDerivAt.smul_const (hasDerivAt_id (𝕜 := ℝ) 1) x)
  have hleft :
      HasDerivAt (fun s : ℝ ↦ L.V (s • x))
        (fderiv ℝ L.V x x) 1 := by
    have hV :
        HasFDerivAt L.V (fderiv ℝ L.V x) ((1 : ℝ) • x) := by
      simpa using
        (L.contDiff.differentiable (by norm_num) x).hasFDerivAt
    simpa only [one_smul, Function.comp_apply] using
      hV.comp_hasDerivAt 1 hscale
  have hright :
      HasDerivAt (fun s : ℝ ↦ s ^ degree * L.V x)
        ((degree : ℝ) * L.V x) 1 := by
    convert (hasDerivAt_pow degree (1 : ℝ)).mul_const (L.V x) using 1
    all_goals simp
  have heq :
      (fun s : ℝ ↦ L.V (s • x)) =ᶠ[𝓝 1]
        (fun s : ℝ ↦ s ^ degree * L.V x) := by
    filter_upwards [eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)]
      with s hs
    exact L.homogeneous s hs x
  exact hleft.unique (hright.congr_of_eventuallyEq heq)

/-- On a nonzero direction, the angular derivative of `log V` differs
from the physical Lie derivative of `log V` by
`degree · innerRadialReward`.

This pointwise calculation is the infinitesimal coboundary identity used
in the invariant-measure converse. -/
theorem angular_logarithmic_identity
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {G : H → H} {m : ℕ}
    (L : StrictHomogeneousC1Lyapunov G m)
    (u : H) (hu : u ≠ 0) :
    fderiv ℝ L.V u (innerAngularField G u) / L.V u =
      fderiv ℝ L.V u (G u) / L.V u -
        (m : ℝ) * innerRadialReward G u := by
  have hVpos : 0 < L.V u := L.positive u hu
  rw [innerAngularField, map_sub, map_smul,
    L.euler_identity u]
  field_simp [hVpos.ne']
  ring

/-- The normalized physical Lie derivative is strictly negative away from
the origin. -/
theorem normalized_lieDerivative_neg
    (L : StrictHomogeneousC1Lyapunov F degree)
    (u : E) (hu : u ≠ 0) :
    fderiv ℝ L.V u (F u) / L.V u < 0 :=
  div_neg_of_neg_of_pos (L.decreases u hu) (L.positive u hu)

end StrictHomogeneousC1Lyapunov

end HGAS

namespace HGAS.Dynamics

/-! ## Invariant averages of angular coboundaries -/

variable {K : Type*} [MetricSpace K] [MeasurableSpace K] [BorelSpace K]

/-- An orbit-integral coboundary has zero average against every invariant
probability.

The hypothesis is the integrated form of
`g = d/dt (w ∘ ϕ_t)|_{t=0}`.  Stating the result at the integrated level
keeps it independent of any manifold or differentiability structure on
the compact phase space. -/
theorem observableAverage_eq_zero_of_orbitIntegral_eq_coboundary
    [CompactSpace K]
    (ϕ : Flow ℝ K) (g w : K →ᵇ ℝ)
    (hcoboundary :
      ∀ x : K,
        orbitIntegral ϕ g 1 x = w (ϕ 1 x) - w x)
    (μ : InvariantProbabilityMeasure ϕ) :
    observableAverage g μ.measure = 0 := by
  have horbit :
      (∫ x, orbitIntegral ϕ g 1 x
          ∂(μ.measure : Measure K)) =
        ∫ x, g x ∂(μ.measure : Measure K) := by
    simpa using integral_orbitIntegral_eq ϕ g μ 1
  have hrewrite :
      (∫ x, orbitIntegral ϕ g 1 x
          ∂(μ.measure : Measure K)) =
        ∫ x, (w (ϕ 1 x) - w x)
          ∂(μ.measure : Measure K) := by
    apply integral_congr_ae
    exact ae_of_all _ hcoboundary
  have hcomp :
      (∫ x, w (ϕ 1 x) ∂(μ.measure : Measure K)) =
        ∫ x, w x ∂(μ.measure : Measure K) :=
    μ.integral_comp_time 1 w
  have hwi :
      Integrable (fun x : K ↦ w (ϕ 1 x))
        (μ.measure : Measure K) := by
    simpa only [BoundedContinuousFunction.compContinuous_apply,
      flowTimeContinuousMap_apply] using
      (w.compContinuous (flowTimeContinuousMap ϕ 1)).integrable
        (μ.measure : Measure K)
  rw [observableAverage, ← horbit, hrewrite]
  rw [integral_sub hwi (w.integrable _), hcomp, sub_self]

/-- A continuous function that is strictly negative everywhere on a
nonempty compact space has strictly negative expectation under every
probability measure.

Compactness upgrades pointwise strict negativity to a uniform negative
upper bound. -/
theorem observableAverage_neg_of_forall_neg
    [CompactSpace K] [Nonempty K]
    (q : K →ᵇ ℝ) (μ : ProbabilityMeasure K)
    (hq : ∀ x : K, q x < 0) :
    observableAverage q μ < 0 := by
  obtain ⟨xmax, _, hmax⟩ :=
    isCompact_univ.exists_isMaxOn
      (univ_nonempty : (univ : Set K).Nonempty)
      q.continuous.continuousOn
  have hintegral :
      (∫ x, q x ∂(μ : Measure K)) ≤
        ∫ _ : K, q xmax ∂(μ : Measure K) := by
    apply integral_mono (q.integrable _) (integrable_const _)
    intro x
    exact hmax (mem_univ x)
  have hconstant :
      (∫ _ : K, q xmax ∂(μ : Measure K)) = q xmax := by
    simp only [integral_const]
    rw [ProbabilityMeasure.measureReal_eq_coe_coeFn]
    norm_num [ProbabilityMeasure.coeFn_univ]
  rw [observableAverage]
  exact hintegral.trans_lt (hconstant.trans_lt (hq xmax))

/-- Abstract invariant-measure converse.

Suppose `g = q - d a`, where `q` is strictly negative and the orbit
integral of `g` is a coboundary.  Invariant probabilities annihilate the
coboundary, so

`d ∫a = ∫q < 0`.

When `d > 0`, every invariant average of `a` is negative; compactness and
the uniform-negative-block theorem then produce one common negative
block. -/
theorem uniformNegativeBlock_of_strictDissipation_coboundary
    [CompactSpace K] [Nonempty K]
    (ϕ : Flow ℝ K) (a q g w : K →ᵇ ℝ) (d : ℝ)
    (hd : 0 < d)
    (hgenerator : ∀ x : K, g x = q x - d * a x)
    (hq : ∀ x : K, q x < 0)
    (hcoboundary :
      ∀ x : K,
        orbitIntegral ϕ g 1 x = w (ϕ 1 x) - w x) :
    HasUniformNegativeBlock ϕ a := by
  apply uniformNegativeBlock_of_invariantAverage_neg ϕ a
  intro μ
  have hgzero :
      observableAverage g μ.measure = 0 :=
    observableAverage_eq_zero_of_orbitIntegral_eq_coboundary
      ϕ g w hcoboundary μ
  have hqneg :
      observableAverage q μ.measure < 0 :=
    observableAverage_neg_of_forall_neg q μ.measure hq
  have havgIdentity :
      observableAverage g μ.measure =
        observableAverage q μ.measure -
          d * observableAverage a μ.measure := by
    unfold observableAverage
    calc
      (∫ x, g x ∂(μ.measure : Measure K)) =
          ∫ x, (q x - d * a x)
            ∂(μ.measure : Measure K) := by
        apply integral_congr_ae
        exact ae_of_all _ hgenerator
      _ = (∫ x, q x ∂(μ.measure : Measure K)) -
            ∫ x, d * a x ∂(μ.measure : Measure K) := by
        rw [integral_sub (q.integrable _)
          (by
            exact
              (a.integrable
                (μ.measure : Measure K)).const_mul d)]
      _ = (∫ x, q x ∂(μ.measure : Measure K)) -
            d * ∫ x, a x ∂(μ.measure : Measure K) := by
        rw [integral_const_mul]
  nlinarith

end HGAS.Dynamics

namespace HGAS

/-- Conditional Lyapunov-to-angular-block theorem.

The continuous observables `a`, `q`, and `g` are respectively the radial
reward, normalized strict Lyapunov dissipation, and angular derivative of
`log V`, pulled back along `direction : K → E`.  The first three
pointwise hypotheses merely certify those pullbacks.  The last hypothesis
is the integrated fundamental-theorem-of-calculus statement along the
angular flow:

`∫₀¹ g(ϕ_t u)dt = w(ϕ_1u)-w(u)`.

Under these explicit assumptions, the strict homogeneous `C¹` Lyapunov
function forces a uniform negative angular block.  No converse Lyapunov
theorem is assumed or asserted. -/
theorem uniformNegativeAngularBlock_of_strictHomogeneousC1Lyapunov
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : E → E} {degree : ℕ}
    (L : StrictHomogeneousC1Lyapunov F degree)
    {K : Type*} [MetricSpace K] [MeasurableSpace K] [BorelSpace K]
    [CompactSpace K] [Nonempty K]
    (ϕ : Flow ℝ K) (direction : K → E)
    (a q g w : K →ᵇ ℝ)
    (hdirection : ∀ x : K, direction x ≠ 0)
    (ha :
      ∀ x : K,
        a x = innerRadialReward F (direction x))
    (hq :
      ∀ x : K,
        q x =
          fderiv ℝ L.V (direction x) (F (direction x)) /
            L.V (direction x))
    (hg :
      ∀ x : K,
        g x =
          fderiv ℝ L.V (direction x)
              (innerAngularField F (direction x)) /
            L.V (direction x))
    (hcoboundary :
      ∀ x : K,
        Dynamics.orbitIntegral ϕ g 1 x =
          w (ϕ 1 x) - w x) :
    Dynamics.HasUniformNegativeBlock ϕ a := by
  apply Dynamics.uniformNegativeBlock_of_strictDissipation_coboundary
    ϕ a q g w (degree : ℝ)
  · exact_mod_cast L.degree_pos
  · intro x
    rw [hg x, hq x, ha x]
    exact L.angular_logarithmic_identity
      (direction x) (hdirection x)
  · intro x
    rw [hq x]
    exact L.normalized_lieDerivative_neg
      (direction x) (hdirection x)
  · exact hcoboundary

end HGAS
