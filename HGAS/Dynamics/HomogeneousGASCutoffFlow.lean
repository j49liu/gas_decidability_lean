import HGAS.Dynamics.CompactlySupportedFlow
import HGAS.Dynamics.HomogeneousGASTrajectoryBounds
import HGAS.Dynamics.StateTimeChange
import HGAS.Dynamics.UniformAttractionOnCompact
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Tactic

/-!
# A global cutoff flow representing all unit-sphere trajectories

A homogeneous polynomial vector field which is GAS need not generate a
two-sided global flow: backward trajectories can blow up.  The angular
argument nevertheless benefits from a genuine `Flow ℝ E`.

The homogeneous stability estimate from
`HomogeneousGASTrajectoryBounds` gives a number `B` which contains every
forward trajectory starting on the unit sphere.  We multiply the field by
a smooth bump which equals one on the closed `B`-ball.  The cutoff field is
compactly supported and therefore has a global flow.  Uniqueness shows
that, for every unit initial condition and every nonnegative time, this
global cutoff flow is exactly the original physical trajectory.

Only the auxiliary ambient flow is modified; all statements on the
forward unit-sphere orbits concern the original field.
-/

namespace HGAS

open Metric Set
open scoped Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A smooth bump which is one on the closed ball of radius `B` and
vanishes outside a slightly larger ball. -/
noncomputable def homogeneousGASPhysicalBump
    (B : ℝ) (hB : 0 < B) :
    ContDiffBump (0 : E) where
  rIn := B
  rOut := B + 1
  rIn_pos := hB
  rIn_lt_rOut := by linarith

/-- Compactly supported replacement of the physical field. -/
def homogeneousGASCutoffField
    (F : E → E) (B : ℝ) (hB : 0 < B) : E → E :=
  fun x ↦ homogeneousGASPhysicalBump (E := E) B hB x • F x

theorem contDiff_homogeneousGASCutoffField
    {F : E → E} (hF : ContDiff ℝ 1 F)
    (B : ℝ) (hB : 0 < B) :
    ContDiff ℝ 1 (homogeneousGASCutoffField F B hB) := by
  exact (homogeneousGASPhysicalBump (E := E) B hB).contDiff.smul hF

theorem hasCompactSupport_homogeneousGASCutoffField
    (F : E → E) (B : ℝ) (hB : 0 < B) :
    HasCompactSupport (homogeneousGASCutoffField F B hB) := by
  exact
    (homogeneousGASPhysicalBump (E := E) B hB).hasCompactSupport.smul_right

theorem homogeneousGASCutoffField_eq_of_norm_le
    (F : E → E) (B : ℝ) (hB : 0 < B)
    {x : E} (hx : ‖x‖ ≤ B) :
    homogeneousGASCutoffField F B hB x = F x := by
  have hbump :
      homogeneousGASPhysicalBump (E := E) B hB x = 1 := by
    apply
      (homogeneousGASPhysicalBump (E := E) B hB).one_of_mem_closedBall
    simpa [Metric.mem_closedBall, dist_zero_right] using hx
  simp [homogeneousGASCutoffField, hbump]

/-- The global flow of the compactly supported physical replacement. -/
noncomputable def homogeneousGASCutoffFlow
    (F : E → E) (hF : ContDiff ℝ 1 F)
    (B : ℝ) (hB : 0 < B) : Flow ℝ E :=
  compactlySupportedContDiffFlow
    (homogeneousGASCutoffField F B hB)
    (contDiff_homogeneousGASCutoffField hF B hB)
    (hasCompactSupport_homogeneousGASCutoffField F B hB)

theorem homogeneousGASCutoffFlow_isIntegralCurve
    (F : E → E) (hF : ContDiff ℝ 1 F)
    (B : ℝ) (hB : 0 < B) (x : E) :
    IsIntegralCurve
      (fun t ↦ homogeneousGASCutoffFlow F hF B hB t x)
      (fun _ ↦ homogeneousGASCutoffField F B hB) :=
  compactlySupportedContDiffFlow_isIntegralCurve
    (homogeneousGASCutoffField F B hB)
    (contDiff_homogeneousGASCutoffField hF B hB)
    (hasCompactSupport_homogeneousGASCutoffField F B hB) x

/-- If `B` bounds every original unit-sphere trajectory, then the global
cutoff flow agrees with the original field on all such forward orbits. -/
theorem homogeneousGASCutoffFlow_isForwardTrajectory_on_unitSphere
    {F : E → E} (hF : ContDiff ℝ 1 F)
    (hgas : GloballyAsymptoticallyStable F 0)
    (B : ℝ) (hB : 0 < B)
    (hbound :
      ∀ (x₀ : E), ‖x₀‖ = 1 →
        ∀ (γ : ℝ → E), IsForwardTrajectory F γ x₀ →
          ∀ t : ℝ, 0 ≤ t → ‖γ t‖ < B)
    (x : E) (hx : ‖x‖ = 1) :
    IsForwardTrajectory F
      (fun t ↦ homogeneousGASCutoffFlow F hF B hB t x) x := by
  obtain ⟨γ, hγ⟩ := hgas.forwardComplete x
  have hγcutoff :
      IsForwardTrajectory
        (homogeneousGASCutoffField F B hB) γ x := by
    refine ⟨hγ.1, ?_⟩
    intro t ht
    have heq :
        homogeneousGASCutoffField F B hB (γ t) = F (γ t) :=
      homogeneousGASCutoffField_eq_of_norm_le
        F B hB (hbound x hx γ hγ t ht).le
    simpa only [heq] using hγ.2 t ht
  let ζ : ℝ → E :=
    fun t ↦ homogeneousGASCutoffFlow F hF B hB t x
  have hζcutoff :
      IsForwardTrajectory
        (homogeneousGASCutoffField F B hB) ζ x := by
    refine ⟨?_, ?_⟩
    · simp [ζ, homogeneousGASCutoffFlow]
    · intro t _ht
      exact
        (homogeneousGASCutoffFlow_isIntegralCurve
          F hF B hB x t).hasDerivWithinAt
  have heq :
      EqOn ζ γ (Ici (0 : ℝ)) :=
    hζcutoff.eqOn_Ici_of_contDiff
      (contDiff_homogeneousGASCutoffField hF B hB)
      hγcutoff
  refine ⟨hζcutoff.1, ?_⟩
  intro t ht
  have hζbound : ‖ζ t‖ < B := by
    rw [heq ht]
    exact hbound x hx γ hγ t ht
  have hfield :
      homogeneousGASCutoffField F B hB (ζ t) = F (ζ t) :=
    homogeneousGASCutoffField_eq_of_norm_le
      F B hB hζbound.le
  simpa only [hfield] using hζcutoff.2 t ht

/-- The global cutoff orbit itself inherits the uniform bound. -/
theorem norm_homogeneousGASCutoffFlow_lt
    {F : E → E} (hF : ContDiff ℝ 1 F)
    (hgas : GloballyAsymptoticallyStable F 0)
    (B : ℝ) (hB : 0 < B)
    (hbound :
      ∀ (x₀ : E), ‖x₀‖ = 1 →
        ∀ (γ : ℝ → E), IsForwardTrajectory F γ x₀ →
          ∀ t : ℝ, 0 ≤ t → ‖γ t‖ < B)
    (x : E) (hx : ‖x‖ = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖homogeneousGASCutoffFlow F hF B hB t x‖ < B := by
  exact hbound x hx
    (fun s ↦ homogeneousGASCutoffFlow F hF B hB s x)
    (homogeneousGASCutoffFlow_isForwardTrajectory_on_unitSphere
      hF hgas B hB hbound x hx)
    t ht

/-- A GAS homogeneous field admits one global auxiliary flow which
simultaneously has a uniform forward bound on the unit sphere and contracts
that sphere into the radius-`1/2` ball after one common physical time. -/
theorem GloballyAsymptoticallyStable.exists_cutoffFlow_unit_contraction
    {F : E → E} {k : ℕ}
    (hgas : GloballyAsymptoticallyStable F 0)
    (hFhom : ScalesAsDegree ℝ (k + 1) F)
    (hF : ContDiff ℝ 1 F) :
    ∃ (B : ℝ) (hB : 0 < B) (T : ℝ),
      0 ≤ T ∧
      (∀ (x : E), ‖x‖ = 1 → ∀ t : ℝ, 0 ≤ t →
        ‖homogeneousGASCutoffFlow F hF B hB t x‖ < B) ∧
      (∀ (x : E), ‖x‖ = 1 → ∀ t : ℝ, T ≤ t →
        ‖homogeneousGASCutoffFlow F hF B hB t x‖ < (1 / 2 : ℝ)) := by
  obtain ⟨B, hB, hbound⟩ :=
    hgas.exists_uniform_unit_trajectory_bound hFhom
  let ϕ : Flow ℝ E :=
    homogeneousGASCutoffFlow F hF B hB
  have hflow :
      ∀ x ∈ sphere (0 : E) 1,
        IsForwardTrajectory F (fun t : ℝ ↦ ϕ t x) x := by
    intro x hx
    have hxnorm : ‖x‖ = 1 := by
      simpa [mem_sphere, dist_zero_right] using hx
    exact homogeneousGASCutoffFlow_isForwardTrajectory_on_unitSphere
      hF hgas B hB hbound x hxnorm
  obtain ⟨T, hT, hcontract⟩ :=
    hgas.uniformAttractionOnCompact_of_orbits
      ϕ (isCompact_sphere (0 : E) 1) hflow
      (show 0 < (1 / 2 : ℝ) by norm_num)
  refine ⟨B, hB, T, hT, ?_, ?_⟩
  · intro x hx t ht
    exact norm_homogeneousGASCutoffFlow_lt
      hF hgas B hB hbound x hx t ht
  · intro x hx t ht
    have hxmem : x ∈ sphere (0 : E) 1 := by
      simpa [mem_sphere, dist_zero_right] using hx
    simpa only [ϕ, dist_zero_right] using
      hcontract x hxmem t ht

end

end HGAS
