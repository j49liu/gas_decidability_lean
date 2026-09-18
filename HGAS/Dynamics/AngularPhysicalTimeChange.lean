import HGAS.Analysis.C1CurveFromVelocity
import HGAS.Dynamics.EuclideanAngularFlow
import HGAS.Dynamics.HomogeneousGASCutoffFlow
import HGAS.Dynamics.TimeDependentUniqueness
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# From angular time back to physical time

Let `F` be homogeneous of degree `k+1`.  On the unit sphere write

```
a(u) = ⟪u, F(u)⟫,
Y(u) = F(u) - a(u)u.
```

If `φ` is the angular flow `u' = Y(u)`, put

```
A(τ,u) = ∫₀ᵗ a(φ(s,u)) ds,
r(τ,u) = exp(A(τ,u)),
t(τ,u) = ∫₀ᵗ exp(-k A(s,u)) ds.
```

The reconstructed state

```
x(τ,u) = r(τ,u) φ(τ,u)
```

satisfies

```
x' = exp(-kA) F(x),       t' = exp(-kA).
```

Consequently `x(τ,u)` is the physical trajectory evaluated at physical
time `t(τ,u)`.  We prove this last assertion on each compact angular
interval by the reusable nonautonomous uniqueness theorem: both the
reconstruction and the time-changed physical flow solve the same `C¹`
time-dependent ODE.

The definitions in this file use the compactly supported ambient angular
flow and bounded reward from `EuclideanAngularFlow`.  On the unit sphere
the cutoff is exactly one, so the formulas are the original polar
equations.
-/

namespace HGAS

open Function Metric Set
open scoped BoundedContinuousFunction RealInnerProductSpace Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Logarithmic radial cocycle along the Euclidean angular flow. -/
def euclideanAngularLogRadius
    (F : E → E) (hF : ContDiff ℝ 1 F)
    (τ : ℝ) (u : E) : ℝ :=
  Dynamics.orbitIntegral
    (euclideanAngularFlow F hF)
    (boundedCutoffInnerRadialReward F hF) τ u

/-- Radius reconstructed from the angular cocycle, with initial radius
one. -/
def euclideanAngularRadius
    (F : E → E) (hF : ContDiff ℝ 1 F)
    (τ : ℝ) (u : E) : ℝ :=
  Real.exp (euclideanAngularLogRadius F hF τ u)

/-- Conversion factor `dt/dτ = r^{-k}` from angular time to physical
time.  The exponential form is everywhere positive and avoids a
case-split at zero. -/
def euclideanAngularPhysicalSpeed
    (F : E → E) (hF : ContDiff ℝ 1 F) (k : ℕ)
    (τ : ℝ) (u : E) : ℝ :=
  Real.exp (-(k : ℝ) * euclideanAngularLogRadius F hF τ u)

/-- Physical time elapsed during an angular interval. -/
def euclideanAngularPhysicalClock
    (F : E → E) (hF : ContDiff ℝ 1 F) (k : ℕ)
    (τ : ℝ) (u : E) : ℝ :=
  integralClock
    (fun s ↦ euclideanAngularPhysicalSpeed F hF k s u) τ

/-- State reconstructed from angular direction and radial cocycle. -/
def euclideanAngularReconstruction
    (F : E → E) (hF : ContDiff ℝ 1 F)
    (τ : ℝ) (u : E) : E :=
  euclideanAngularRadius F hF τ u •
    euclideanAngularFlow F hF τ u

@[simp]
theorem euclideanAngularLogRadius_zero
    (F : E → E) (hF : ContDiff ℝ 1 F) (u : E) :
    euclideanAngularLogRadius F hF 0 u = 0 := by
  simp [euclideanAngularLogRadius]

@[simp]
theorem euclideanAngularRadius_zero
    (F : E → E) (hF : ContDiff ℝ 1 F) (u : E) :
    euclideanAngularRadius F hF 0 u = 1 := by
  simp [euclideanAngularRadius]

@[simp]
theorem euclideanAngularPhysicalSpeed_zero
    (F : E → E) (hF : ContDiff ℝ 1 F) (k : ℕ) (u : E) :
    euclideanAngularPhysicalSpeed F hF k 0 u = 1 := by
  simp [euclideanAngularPhysicalSpeed]

@[simp]
theorem euclideanAngularPhysicalClock_zero
    (F : E → E) (hF : ContDiff ℝ 1 F) (k : ℕ) (u : E) :
    euclideanAngularPhysicalClock F hF k 0 u = 0 := by
  simp [euclideanAngularPhysicalClock]

@[simp]
theorem euclideanAngularReconstruction_zero
    (F : E → E) (hF : ContDiff ℝ 1 F) (u : E) :
    euclideanAngularReconstruction F hF 0 u = u := by
  simp [euclideanAngularReconstruction]

theorem euclideanAngularPhysicalSpeed_pos
    (F : E → E) (hF : ContDiff ℝ 1 F) (k : ℕ)
    (τ : ℝ) (u : E) :
    0 < euclideanAngularPhysicalSpeed F hF k τ u :=
  Real.exp_pos _

theorem euclideanAngularRadius_pos
    (F : E → E) (hF : ContDiff ℝ 1 F)
    (τ : ℝ) (u : E) :
    0 < euclideanAngularRadius F hF τ u :=
  Real.exp_pos _

/-- Every fixed orbit of the compactly supported angular field is `C¹`.
This uses only the orbit ODE and continuity of its velocity, not
differentiable dependence on the initial condition. -/
theorem contDiff_one_euclideanAngularFlow_orbit
    (F : E → E) (hF : ContDiff ℝ 1 F) (u : E) :
    ContDiff ℝ 1 (fun τ : ℝ ↦ euclideanAngularFlow F hF τ u) := by
  apply contDiff_one_curve_of_continuous_velocity
    (fun τ : ℝ ↦ euclideanAngularFlow F hF τ u)
    (fun τ : ℝ ↦
      cutoffInnerAngularField F
        (euclideanAngularFlow F hF τ u))
  · exact
      (contDiff_cutoffInnerAngularField hF).continuous.comp
        ((euclideanAngularFlow F hF).continuous
          continuous_id continuous_const)
  · intro τ
    exact euclideanAngularFlow_isIntegralCurve_cutoff F hF u τ

/-- The logarithmic radial cocycle is `C¹` in angular time. -/
theorem contDiff_one_euclideanAngularLogRadius
    (F : E → E) (hF : ContDiff ℝ 1 F) (u : E) :
    ContDiff ℝ 1
      (fun τ : ℝ ↦ euclideanAngularLogRadius F hF τ u) := by
  apply contDiff_one_curve_of_continuous_velocity
    (fun τ : ℝ ↦ euclideanAngularLogRadius F hF τ u)
    (fun τ : ℝ ↦
      boundedCutoffInnerRadialReward F hF
        (euclideanAngularFlow F hF τ u))
  · exact
      (boundedCutoffInnerRadialReward F hF).continuous.comp
        ((euclideanAngularFlow F hF).continuous
          continuous_id continuous_const)
  · intro τ
    exact Dynamics.hasDerivAt_orbitIntegral
      (euclideanAngularFlow F hF)
      (boundedCutoffInnerRadialReward F hF) u τ

theorem contDiff_one_euclideanAngularRadius
    (F : E → E) (hF : ContDiff ℝ 1 F) (u : E) :
    ContDiff ℝ 1
      (fun τ : ℝ ↦ euclideanAngularRadius F hF τ u) := by
  exact Real.contDiff_exp.comp
    (contDiff_one_euclideanAngularLogRadius F hF u)

theorem contDiff_one_euclideanAngularPhysicalSpeed
    (F : E → E) (hF : ContDiff ℝ 1 F) (k : ℕ) (u : E) :
    ContDiff ℝ 1
      (fun τ : ℝ ↦ euclideanAngularPhysicalSpeed F hF k τ u) := by
  exact Real.contDiff_exp.comp
    (contDiff_const.mul
      (contDiff_one_euclideanAngularLogRadius F hF u))

theorem hasDerivAt_euclideanAngularLogRadius
    (F : E → E) (hF : ContDiff ℝ 1 F)
    (u : E) (hu : ‖u‖ = 1) (τ : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ euclideanAngularLogRadius F hF s u)
      (innerRadialReward F
        (euclideanAngularFlow F hF τ u)) τ := by
  have hderiv :=
    Dynamics.hasDerivAt_orbitIntegral
      (euclideanAngularFlow F hF)
      (boundedCutoffInnerRadialReward F hF) u τ
  have hnorm :=
    euclideanAngularFlow_preserves_norm F hF u hu τ
  simpa only [euclideanAngularLogRadius,
    boundedCutoffInnerRadialReward_apply,
    cutoffInnerRadialReward_eq_of_norm_eq_one F _ hnorm] using hderiv

theorem hasDerivAt_euclideanAngularRadius
    (F : E → E) (hF : ContDiff ℝ 1 F)
    (u : E) (hu : ‖u‖ = 1) (τ : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ euclideanAngularRadius F hF s u)
      (euclideanAngularRadius F hF τ u *
        innerRadialReward F
          (euclideanAngularFlow F hF τ u)) τ := by
  simpa only [euclideanAngularRadius] using
    (hasDerivAt_euclideanAngularLogRadius F hF u hu τ).exp

theorem hasDerivAt_euclideanAngularPhysicalClock
    (F : E → E) (hF : ContDiff ℝ 1 F) (k : ℕ)
    (u : E) (τ : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ euclideanAngularPhysicalClock F hF k s u)
      (euclideanAngularPhysicalSpeed F hF k τ u) τ := by
  exact integralClock_hasDerivAt
    (contDiff_one_euclideanAngularPhysicalSpeed F hF k u).continuous τ

/-- The angular-to-physical clock is nonnegative at nonnegative angular
times. -/
theorem euclideanAngularPhysicalClock_nonneg
    (F : E → E) (hF : ContDiff ℝ 1 F) (k : ℕ)
    (u : E) {τ : ℝ} (hτ : 0 ≤ τ) :
    0 ≤ euclideanAngularPhysicalClock F hF k τ u := by
  have hmono :=
    integralClock_strictMono
      (contDiff_one_euclideanAngularPhysicalSpeed F hF k u).continuous
      (euclideanAngularPhysicalSpeed_pos F hF k · u)
  rw [← euclideanAngularPhysicalClock_zero F hF k u]
  exact hmono.monotone hτ

/-- The time-conversion factor cancels all but one radial power of a
degree-`k+1` homogeneous field. -/
theorem euclideanAngularPhysicalSpeed_mul_radius_pow
    (F : E → E) (hF : ContDiff ℝ 1 F) (k : ℕ)
    (τ : ℝ) (u : E) :
    euclideanAngularPhysicalSpeed F hF k τ u *
        euclideanAngularRadius F hF τ u ^ (k + 1) =
      euclideanAngularRadius F hF τ u := by
  rw [euclideanAngularPhysicalSpeed, euclideanAngularRadius,
    ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

theorem euclideanAngularPhysicalSpeed_eq_inv_radius_pow
    (F : E → E) (hF : ContDiff ℝ 1 F) (k : ℕ)
    (τ : ℝ) (u : E) :
    euclideanAngularPhysicalSpeed F hF k τ u =
      (euclideanAngularRadius F hF τ u ^ k)⁻¹ := by
  rw [euclideanAngularPhysicalSpeed, euclideanAngularRadius,
    ← Real.exp_nat_mul, ← Real.exp_neg]
  congr 1
  ring

/-- The norm of the reconstructed state is exactly its scalar radius. -/
theorem norm_euclideanAngularReconstruction
    (F : E → E) (hF : ContDiff ℝ 1 F)
    (u : E) (hu : ‖u‖ = 1) (τ : ℝ) :
    ‖euclideanAngularReconstruction F hF τ u‖ =
      euclideanAngularRadius F hF τ u := by
  rw [euclideanAngularReconstruction, norm_smul,
    Real.norm_eq_abs,
    abs_of_pos (euclideanAngularRadius_pos F hF τ u),
    euclideanAngularFlow_preserves_norm F hF u hu τ,
    mul_one]

/-- Exact differential equation for the angular reconstruction:

`x'(τ) = exp(-k A(τ)) • F(x(τ))`.
-/
theorem hasDerivAt_euclideanAngularReconstruction
    (F : E → E) (hF : ContDiff ℝ 1 F) (k : ℕ)
    (hFhom : ScalesAsDegree ℝ (k + 1) F)
    (u : E) (hu : ‖u‖ = 1) (τ : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ euclideanAngularReconstruction F hF s u)
      (euclideanAngularPhysicalSpeed F hF k τ u •
        F (euclideanAngularReconstruction F hF τ u)) τ := by
  let r : ℝ := euclideanAngularRadius F hF τ u
  let v : E := euclideanAngularFlow F hF τ u
  let a : ℝ := innerRadialReward F v
  have hr :
      HasDerivAt
        (fun s : ℝ ↦ euclideanAngularRadius F hF s u)
        (r * a) τ := by
    simpa only [r, a, v] using
      hasDerivAt_euclideanAngularRadius F hF u hu τ
  have hv :
      HasDerivAt
        (fun s : ℝ ↦ euclideanAngularFlow F hF s u)
        (innerAngularField F v) τ := by
    simpa only [v] using
      euclideanAngularFlow_isIntegralCurve F hF u hu τ
  have hproduct := hr.smul hv
  have hfield :
      euclideanAngularPhysicalSpeed F hF k τ u •
          F (euclideanAngularReconstruction F hF τ u) =
        r • F v := by
    rw [euclideanAngularReconstruction]
    change
      euclideanAngularPhysicalSpeed F hF k τ u •
          F (r • v) = r • F v
    rw [hFhom]
    simp only [smul_smul]
    rw [euclideanAngularPhysicalSpeed_mul_radius_pow]
  rw [hfield]
  convert hproduct using 1
  change
    r • F v =
      r • innerAngularField F v + (r * a) • v
  rw [← innerAngularField_add_radial F v]
  simp only [smul_add, smul_smul, a]

theorem contDiff_one_euclideanAngularReconstruction
    (F : E → E) (hF : ContDiff ℝ 1 F) (u : E) :
    ContDiff ℝ 1
      (fun τ : ℝ ↦ euclideanAngularReconstruction F hF τ u) := by
  exact
    (contDiff_one_euclideanAngularRadius F hF u).smul
      (contDiff_one_euclideanAngularFlow_orbit F hF u)

/-- The nonautonomous physical field seen in angular time. -/
def angularScaledPhysicalField
    (F : E → E) (hF : ContDiff ℝ 1 F) (k : ℕ)
    (u : E) (τ : ℝ) (x : E) : E :=
  euclideanAngularPhysicalSpeed F hF k τ u • F x

theorem contDiff_one_uncurry_angularScaledPhysicalField
    (F : E → E) (hF : ContDiff ℝ 1 F) (k : ℕ) (u : E) :
    ContDiff ℝ 1
      (Function.uncurry
        (angularScaledPhysicalField F hF k u)) := by
  exact
    ((contDiff_one_euclideanAngularPhysicalSpeed F hF k u).comp
      contDiff_fst).smul
      (hF.comp contDiff_snd)

/-- A physical flow, sampled at the reconstructed physical clock, solves
the same nonautonomous equation as the angular reconstruction. -/
theorem hasDerivAt_physicalFlow_comp_euclideanAngularPhysicalClock
    (F : E → E) (hF : ContDiff ℝ 1 F) (k : ℕ)
    (Ψ : Flow ℝ E)
    (u : E)
    (hΨ :
      ∀ t : ℝ, 0 ≤ t →
        HasDerivAt (fun s : ℝ ↦ Ψ s u)
          (F (Ψ t u)) t)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    HasDerivAt
      (fun s : ℝ ↦
        Ψ (euclideanAngularPhysicalClock F hF k s u) u)
      (angularScaledPhysicalField F hF k u τ
        (Ψ (euclideanAngularPhysicalClock F hF k τ u) u)) τ := by
  have hclock :=
    hasDerivAt_euclideanAngularPhysicalClock F hF k u τ
  have hphysical :=
    hΨ (euclideanAngularPhysicalClock F hF k τ u)
      (euclideanAngularPhysicalClock_nonneg F hF k u hτ)
  simpa only [angularScaledPhysicalField] using
    hphysical.scomp τ hclock

/-- **Angular-to-physical realization on a compact interval.**

At every nonnegative angular time `L`, the radial-angular reconstruction
equals the supplied physical flow at the elapsed physical clock. -/
theorem euclideanAngularReconstruction_eq_physicalFlow
    (F : E → E) (hF : ContDiff ℝ 1 F) (k : ℕ)
    (hFhom : ScalesAsDegree ℝ (k + 1) F)
    (Ψ : Flow ℝ E)
    (u : E) (hu : ‖u‖ = 1)
    (hΨ :
      ∀ t : ℝ, 0 ≤ t →
        HasDerivAt (fun s : ℝ ↦ Ψ s u)
          (F (Ψ t u)) t)
    {L : ℝ} (hL : 0 ≤ L) :
    euclideanAngularReconstruction F hF L u =
      Ψ (euclideanAngularPhysicalClock F hF k L u) u := by
  let γ : ℝ → E :=
    fun τ ↦ euclideanAngularReconstruction F hF τ u
  let η : ℝ → E :=
    fun τ ↦ Ψ (euclideanAngularPhysicalClock F hF k τ u) u
  have heqOn :
      EqOn γ η (Icc (0 : ℝ) L) := by
    apply timeDependent_ode_solution_unique_Icc_right_of_contDiff
      (angularScaledPhysicalField F hF k u)
      (contDiff_one_uncurry_angularScaledPhysicalField F hF k u)
    · exact
        (contDiff_one_euclideanAngularReconstruction F hF u).continuous.continuousOn
    · intro τ hτ
      exact
        (hasDerivAt_euclideanAngularReconstruction
          F hF k hFhom u hu τ).hasDerivWithinAt
    · exact
        ((Ψ.continuous continuous_id continuous_const).comp
          (integralClock_continuous
            (contDiff_one_euclideanAngularPhysicalSpeed
              F hF k u).continuous)).continuousOn
    · intro τ hτ
      exact
        (hasDerivAt_physicalFlow_comp_euclideanAngularPhysicalClock
          F hF k Ψ u hΨ hτ.1).hasDerivWithinAt
    · simp only [γ, η, euclideanAngularReconstruction_zero,
        euclideanAngularPhysicalClock_zero, Ψ.map_zero_apply]
  exact heqOn ⟨hL, le_rfl⟩

/-- A uniform physical radius bound gives a linear lower bound on the
elapsed physical time.  This is the quantitative continuation estimate
used to choose one common angular horizon. -/
theorem euclideanAngularPhysicalClock_ge_of_physical_bound
    (F : E → E) (hF : ContDiff ℝ 1 F) (k : ℕ)
    (hFhom : ScalesAsDegree ℝ (k + 1) F)
    (Ψ : Flow ℝ E)
    (u : E) (hu : ‖u‖ = 1)
    (hΨ :
      ∀ t : ℝ, 0 ≤ t →
        HasDerivAt (fun s : ℝ ↦ Ψ s u)
          (F (Ψ t u)) t)
    {B : ℝ} (hB : 0 < B)
    (hbound :
      ∀ t : ℝ, 0 ≤ t → ‖Ψ t u‖ < B)
    {L : ℝ} (hL : 0 ≤ L) :
    (B ^ k)⁻¹ * L ≤
      euclideanAngularPhysicalClock F hF k L u := by
  have hspeed :
      ∀ τ ∈ Icc (0 : ℝ) L,
        (B ^ k)⁻¹ ≤
          euclideanAngularPhysicalSpeed F hF k τ u := by
    intro τ hτ
    have hrealize :=
      euclideanAngularReconstruction_eq_physicalFlow
        F hF k hFhom Ψ u hu hΨ hτ.1
    have hclockNonneg :=
      euclideanAngularPhysicalClock_nonneg
        F hF k u hτ.1
    have hradius_lt :
        euclideanAngularRadius F hF τ u < B := by
      rw [← norm_euclideanAngularReconstruction F hF u hu τ,
        hrealize]
      exact hbound _ hclockNonneg
    have hpow :
        euclideanAngularRadius F hF τ u ^ k ≤ B ^ k :=
      pow_le_pow_left₀
        (euclideanAngularRadius_pos F hF τ u).le
        hradius_lt.le k
    rw [euclideanAngularPhysicalSpeed_eq_inv_radius_pow]
    exact
      (inv_le_inv₀ (pow_pos hB k)
        (pow_pos (euclideanAngularRadius_pos F hF τ u) k)).2
        hpow
  have hintegral :
      (∫ _τ in (0 : ℝ)..L, (B ^ k)⁻¹) ≤
        ∫ τ in (0 : ℝ)..L,
          euclideanAngularPhysicalSpeed F hF k τ u := by
    exact intervalIntegral.integral_mono_on hL
      (continuous_const.intervalIntegrable 0 L)
      ((contDiff_one_euclideanAngularPhysicalSpeed
        F hF k u).continuous.intervalIntegrable 0 L)
      hspeed
  simpa [euclideanAngularPhysicalClock, integralClock, mul_comm] using
    hintegral

end

end HGAS
