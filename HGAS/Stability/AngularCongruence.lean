import HGAS.Stability.AngularLyapunov
import Mathlib.Tactic

/-!
# Fields that agree on the unit sphere

If two `C¹` vector fields agree on the Euclidean unit sphere, their angular
flows agree on the sphere (for nonnegative time) and so do their radial
cocycles.  Consequently two homogeneous fields, possibly of different degrees,
which agree on the unit sphere are simultaneously Lyapunov stable or not.
This is the angular part of the degree-raising Lemma 6.1 of the paper: the
factor `(‖x‖² + ‖z‖²)^j` equals one on the unit sphere.
-/

namespace HGAS

open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Fields agreeing on the unit sphere have the same angular orbits there,
for nonnegative time. -/
theorem euclideanAngularFlow_eq_of_eqOn_sphere
    (F G : E → E) (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G)
    (hFG : ∀ v : E, ‖v‖ = 1 → F v = G v)
    {u : E} (hu : ‖u‖ = 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    euclideanAngularFlow F hF τ u = euclideanAngularFlow G hG τ u := by
  have hfield : ∀ v : E, ‖v‖ = 1 →
      innerAngularField F v = cutoffInnerAngularField G v := by
    intro v hv
    simp [cutoffInnerAngularField, euclideanAngularBump_eq_one_of_norm_eq_one v hv,
      innerAngularField, innerRadialReward, hFG v hv]
  have hfieldG : ∀ v : E, ‖v‖ = 1 →
      innerAngularField G v = cutoffInnerAngularField G v := by
    intro v hv
    simp [cutoffInnerAngularField, euclideanAngularBump_eq_one_of_norm_eq_one v hv]
  have heq : EqOn (fun t ↦ euclideanAngularFlow F hF t u)
      (fun t ↦ euclideanAngularFlow G hG t u) (Icc 0 τ) := by
    apply ode_solution_unique_Icc_right_of_contDiff
      (contDiff_cutoffInnerAngularField hG)
    · exact (euclideanAngularFlow_isIntegralCurve F hF u hu).continuous.continuousOn
    · intro t _
      have hd : HasDerivAt (fun t ↦ euclideanAngularFlow F hF t u)
          (innerAngularField F (euclideanAngularFlow F hF t u)) t :=
        euclideanAngularFlow_isIntegralCurve F hF u hu t
      rw [hfield _ (euclideanAngularFlow_preserves_norm F hF u hu t)] at hd
      exact hd.hasDerivWithinAt
    · exact (euclideanAngularFlow_isIntegralCurve G hG u hu).continuous.continuousOn
    · intro t _
      have hd : HasDerivAt (fun t ↦ euclideanAngularFlow G hG t u)
          (innerAngularField G (euclideanAngularFlow G hG t u)) t :=
        euclideanAngularFlow_isIntegralCurve G hG u hu t
      rw [hfieldG _ (euclideanAngularFlow_preserves_norm G hG u hu t)] at hd
      exact hd.hasDerivWithinAt
    · simp
  exact heq ⟨hτ, le_rfl⟩

/-- Fields agreeing on the unit sphere have the same radial cocycle there,
for nonnegative time. -/
theorem euclideanAngularLogRadius_eq_of_eqOn_sphere
    (F G : E → E) (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G)
    (hFG : ∀ v : E, ‖v‖ = 1 → F v = G v)
    {u : E} (hu : ‖u‖ = 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    euclideanAngularLogRadius F hF τ u = euclideanAngularLogRadius G hG τ u := by
  unfold euclideanAngularLogRadius Dynamics.orbitIntegral
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hτ] at hs
  have hflow := euclideanAngularFlow_eq_of_eqOn_sphere F G hF hG hFG hu hs.1
  have hnorm := euclideanAngularFlow_preserves_norm F hF u hu s
  simp only [boundedCutoffInnerRadialReward_apply]
  rw [cutoffInnerRadialReward_eq_of_norm_eq_one F _ hnorm, ← hflow,
    cutoffInnerRadialReward_eq_of_norm_eq_one G _ hnorm]
  simp [innerRadialReward, hFG _ hnorm]

/-- Two homogeneous `C¹` fields (of possibly different degrees) that agree
on the unit sphere are simultaneously Lyapunov stable. -/
theorem lyapunovStableWithExistence_iff_of_eqOn_sphere
    (F G : E → E) (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G)
    (k l : ℕ)
    (hFhom : ScalesAsDegree ℝ (k + 1) F) (hGhom : ScalesAsDegree ℝ (l + 1) G)
    (hF0 : F 0 = 0) (hG0 : G 0 = 0)
    (hFG : ∀ v : E, ‖v‖ = 1 → F v = G v) :
    LyapunovStableWithExistence F 0 ↔ LyapunovStableWithExistence G 0 := by
  rw [lyapunovStableWithExistence_iff_boundedEuclideanAngularCocycle F hF k hFhom hF0,
    lyapunovStableWithExistence_iff_boundedEuclideanAngularCocycle G hG l hGhom hG0]
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M, fun u hu τ hτ ↦ ?_⟩
    rw [← euclideanAngularLogRadius_eq_of_eqOn_sphere F G hF hG hFG hu hτ]
    exact hM u hu τ hτ
  · rintro ⟨M, hM⟩
    refine ⟨M, fun u hu τ hτ ↦ ?_⟩
    rw [euclideanAngularLogRadius_eq_of_eqOn_sphere F G hF hG hFG hu hτ]
    exact hM u hu τ hτ

end

end HGAS
