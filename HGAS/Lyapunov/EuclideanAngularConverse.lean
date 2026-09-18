import HGAS.Dynamics.C1CompactlySupportedFlow
import HGAS.Dynamics.HomogeneousGASNegativeAngularBlock
import HGAS.Lyapunov.FiniteCocycleHomogeneousLyapunov
import Mathlib.Tactic

/-!
# An unconditional homogeneous `C¹` converse Lyapunov theorem

This module assembles the analytic development into a single constructive
converse theorem for finite-dimensional Euclidean spaces.

For a `C²` homogeneous field `F` whose origin is GAS:

1. `HomogeneousGASNegativeAngularBlock` produces one common negative block
   for the radial reward along the angular flow.
2. The angular field is multiplied by a smooth compactly supported bump.
   Since the resulting field is `C²`,
   `c1ODEFlowOfCompactSupportC2` supplies its genuine jointly `C¹` flow,
   with differentiable dependence on initial conditions.
3. `FiniteCocycleHomogeneousLyapunov` integrates a finite exponential
   cocycle profile and extends it quadratically along rays.

The result is a positive, degree-two homogeneous `C¹` function whose Lie
derivative along `F` is strictly negative away from the origin.  No
converse-Lyapunov theorem is postulated: every regularity, compactness, and
time-change input has been proved in the imported modules.
-/

namespace HGAS

open scoped BoundedContinuousFunction RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem contDiff_two_innerRadialReward
    {F : E → E} (hF : ContDiff ℝ 2 F) :
    ContDiff ℝ 2 (innerRadialReward F) := by
  unfold innerRadialReward
  exact contDiff_id.inner ℝ hF

omit [FiniteDimensional ℝ E] in
theorem contDiff_two_innerAngularField
    {F : E → E} (hF : ContDiff ℝ 2 F) :
    ContDiff ℝ 2 (innerAngularField F) := by
  unfold innerAngularField
  exact hF.sub ((contDiff_two_innerRadialReward hF).smul contDiff_id)

theorem contDiff_two_cutoffInnerAngularField
    {F : E → E} (hF : ContDiff ℝ 2 F) :
    ContDiff ℝ 2 (cutoffInnerAngularField F) := by
  unfold cutoffInnerAngularField
  exact (euclideanAngularBump (E := E)).contDiff.smul
    (contDiff_two_innerAngularField hF)

theorem cutoffInnerAngularField_eq_of_norm_eq_one
    (F : E → E) (x : E) (hx : ‖x‖ = 1) :
    cutoffInnerAngularField F x = innerAngularField F x := by
  simp [cutoffInnerAngularField,
    euclideanAngularBump_eq_one_of_norm_eq_one x hx]

/-- The cutoff Euclidean angular field, bundled with its jointly `C¹`
global ODE flow. -/
noncomputable def euclideanAngularC1ODEFlow
    (F : E → E) (hF : ContDiff ℝ 2 F) :
    Dynamics.C1ODEFlow E :=
  Dynamics.c1ODEFlowOfCompactSupportC2
    (cutoffInnerAngularField F)
    (contDiff_two_cutoffInnerAngularField hF)
    (hasCompactSupport_cutoffInnerAngularField F)

@[simp]
theorem euclideanAngularC1ODEFlow_generator
    (F : E → E) (hF : ContDiff ℝ 2 F) :
    (euclideanAngularC1ODEFlow F hF).generator =
      cutoffInnerAngularField F :=
  rfl

@[simp]
theorem euclideanAngularC1ODEFlow_flow
    (F : E → E) (hF : ContDiff ℝ 2 F) :
    (euclideanAngularC1ODEFlow F hF).flow =
      euclideanAngularFlow F (hF.of_le (by norm_num)) := by
  rfl

/-- A common negative angular block gives the strict homogeneous `C¹`
Lyapunov function, with no remaining flow-regularity hypothesis. -/
noncomputable def strictHomogeneousC1Lyapunov_of_uniformNegativeEuclideanAngularBlock
    (F : E → E) (d : ℕ)
    (hFhom : ScalesAsDegree ℝ d F)
    (hF : ContDiff ℝ 2 F)
    {T c : ℝ} (hT : 0 < T) (hc : 0 < c)
    (hblock :
      ∀ u : E, ‖u‖ = 1 →
        Dynamics.orbitIntegral
          (euclideanAngularFlow F (hF.of_le (by norm_num)))
          (boundedCutoffInnerRadialReward F
            (hF.of_le (by norm_num))) T u ≤ -c) :
    StrictHomogeneousC1Lyapunov F 2 := by
  let hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  let Φ : Dynamics.C1ODEFlow E :=
    euclideanAngularC1ODEFlow F hF
  let a : E →ᵇ ℝ :=
    boundedCutoffInnerRadialReward F hF1
  apply strictHomogeneousC1Lyapunov_of_C1ODEFlow_negativeBlock
    F d hFhom Φ a
    (by
      simpa only [a] using
        contDiff_cutoffInnerRadialReward hF1)
    hT hc
  · intro u hu
    simp only [Φ, euclideanAngularC1ODEFlow_generator]
    exact cutoffInnerAngularField_eq_of_norm_eq_one F u hu
  · intro u hu
    simpa only [a, boundedCutoffInnerRadialReward_apply] using
      cutoffInnerRadialReward_eq_of_norm_eq_one F u hu
  · intro u hu
    simpa only [Φ, a, euclideanAngularC1ODEFlow_flow] using
      hblock u hu

/-- **Constructive homogeneous converse Lyapunov theorem.**

A GAS `C²` field homogeneous of positive degree `k+1` admits a strict
degree-two homogeneous `C¹` Lyapunov function. -/
noncomputable def
    GloballyAsymptoticallyStable.strictHomogeneousC1Lyapunov
    {F : E → E} {k : ℕ}
    (hgas : GloballyAsymptoticallyStable F 0)
    (hFhom : ScalesAsDegree ℝ (k + 1) F)
    (hF : ContDiff ℝ 2 F) :
    StrictHomogeneousC1Lyapunov F 2 := by
  let hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  let hex :=
    hgas.exists_uniformNegativeEuclideanAngularBlock hFhom hF1
  let T : ℝ := Classical.choose hex
  let hexC :=
    Classical.choose_spec hex
  let c : ℝ := Classical.choose hexC
  have hspec :
      0 < T ∧ 0 < c ∧
        ∀ u : E, ‖u‖ = 1 →
          Dynamics.orbitIntegral
            (euclideanAngularFlow F hF1)
            (boundedCutoffInnerRadialReward F hF1) T u ≤ -c :=
    Classical.choose_spec hexC
  exact
    strictHomogeneousC1Lyapunov_of_uniformNegativeEuclideanAngularBlock
      F (k + 1) hFhom hF hspec.1 hspec.2.1 hspec.2.2

end

end HGAS
