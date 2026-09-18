import HGAS.Dynamics.CompactlySupportedFlow
import HGAS.Veronese.CoordinateFieldSmoothness
import HGAS.Veronese.CubicLiftConjugacy
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-!
# The source angular flow on the Euclidean unit sphere

This is the Euclidean analogue of `WeightedAngularFlow`.  For a `C¹` field
`G` on `Fin n → ℝ`, we multiply its angular component by a smooth compact
cutoff which is one on the unit ball.  The resulting global ambient flow
preserves

```
sourceRadiusSq u = ∑ i, uᵢ² = 1,
```

because the level error again satisfies a scalar linear equation
`z'=b(t)z`.  Restricting gives an actual continuous flow on the compact
source unit sphere, and its orbits solve the original uncut angular ODE.

The construction is stated for an arbitrary `C¹` field so it can be reused
outside the Veronese reduction.
-/

namespace HGAS.Veronese

open Set Filter Function Metric
open scoped Topology NNReal BigOperators

noncomputable section

variable {n : ℕ}

/-- The source Euclidean unit sphere, expressed using the quadratic
polynomial used by the Veronese normalization. -/
def sourceUnitSphere (n : ℕ) : Set (Fin n → ℝ) :=
  {u | sourceRadiusSq u = 1}

theorem continuous_sourceRadiusSq :
    Continuous (sourceRadiusSq : (Fin n → ℝ) → ℝ) := by
  unfold sourceRadiusSq
  fun_prop

theorem isClosed_sourceUnitSphere :
    IsClosed (sourceUnitSphere n) :=
  isClosed_eq continuous_sourceRadiusSq continuous_const

theorem source_norm_le_one_of_radiusSq_eq_one
    (u : Fin n → ℝ) (hu : sourceRadiusSq u = 1) :
    ‖u‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  rw [Real.norm_eq_abs]
  have hterm : u i ^ 2 ≤ sourceRadiusSq u := by
    unfold sourceRadiusSq
    exact Finset.single_le_sum
      (fun j _ ↦ sq_nonneg (u j)) (Finset.mem_univ i)
  rw [hu] at hterm
  exact (sq_le_one_iff_abs_le_one (u i)).mp hterm

theorem isBounded_sourceUnitSphere :
    Bornology.IsBounded (sourceUnitSphere n) := by
  rw [isBounded_iff_forall_norm_le]
  exact
    ⟨1, fun u hu ↦
      source_norm_le_one_of_radiusSq_eq_one u hu⟩

theorem isCompact_sourceUnitSphere :
    IsCompact (sourceUnitSphere n) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact ⟨isClosed_sourceUnitSphere, isBounded_sourceUnitSphere⟩

/-! ## Smoothness and the compact cutoff -/

theorem contDiff_sourceRadialReward
    {G : (Fin n → ℝ) → (Fin n → ℝ)}
    (hG : ContDiff ℝ 1 G) :
    ContDiff ℝ 1 (HGAS.radialReward G) := by
  unfold HGAS.radialReward HGAS.dot
  fun_prop

theorem contDiff_sourceAngularField
    {G : (Fin n → ℝ) → (Fin n → ℝ)}
    (hG : ContDiff ℝ 1 G) :
    ContDiff ℝ 1 (HGAS.angularField G) := by
  unfold HGAS.angularField
  exact hG.sub
    ((contDiff_sourceRadialReward hG).smul contDiff_id)

noncomputable def sourceAngularBump :
    ContDiffBump (0 : Fin n → ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def cutoffSourceAngularField
    (G : (Fin n → ℝ) → (Fin n → ℝ)) :
    (Fin n → ℝ) → (Fin n → ℝ) :=
  fun u ↦
    sourceAngularBump (n := n) u • HGAS.angularField G u

theorem contDiff_cutoffSourceAngularField
    {G : (Fin n → ℝ) → (Fin n → ℝ)}
    (hG : ContDiff ℝ 1 G) :
    ContDiff ℝ 1 (cutoffSourceAngularField G) := by
  unfold cutoffSourceAngularField
  exact (sourceAngularBump (n := n)).contDiff.smul
    (contDiff_sourceAngularField hG)

theorem hasCompactSupport_cutoffSourceAngularField
    (G : (Fin n → ℝ) → (Fin n → ℝ)) :
    HasCompactSupport (cutoffSourceAngularField G) := by
  unfold cutoffSourceAngularField
  exact (sourceAngularBump (n := n)).hasCompactSupport.smul_right

theorem sourceAngularBump_eq_one_of_radiusSq_eq_one
    (u : Fin n → ℝ) (hu : sourceRadiusSq u = 1) :
    sourceAngularBump (n := n) u = 1 := by
  apply (sourceAngularBump (n := n)).one_of_mem_closedBall
  simpa [Metric.mem_closedBall, dist_zero_right] using
    source_norm_le_one_of_radiusSq_eq_one u hu

/-! ## Ambient and restricted flows -/

noncomputable def sourceAngularAmbientFlow
    (G : (Fin n → ℝ) → (Fin n → ℝ))
    (hG : ContDiff ℝ 1 G) :
    Flow ℝ (Fin n → ℝ) :=
  HGAS.compactlySupportedContDiffFlow
    (cutoffSourceAngularField G)
    (contDiff_cutoffSourceAngularField hG)
    (hasCompactSupport_cutoffSourceAngularField G)

theorem sourceAngularAmbientFlow_isIntegralCurve_cutoff
    (G : (Fin n → ℝ) → (Fin n → ℝ))
    (hG : ContDiff ℝ 1 G) (u : Fin n → ℝ) :
    IsIntegralCurve
      (fun t ↦ sourceAngularAmbientFlow G hG t u)
      (fun _ ↦ cutoffSourceAngularField G) :=
  HGAS.compactlySupportedContDiffFlow_isIntegralCurve
    (cutoffSourceAngularField G)
    (contDiff_cutoffSourceAngularField hG)
    (hasCompactSupport_cutoffSourceAngularField G) u

/-- The two squared-radius conventions used in the source development
coincide. -/
theorem HGAS.normSq_eq_sourceRadiusSq
    (u : Fin n → ℝ) :
    HGAS.normSq u = sourceRadiusSq u := by
  unfold HGAS.normSq HGAS.dot sourceRadiusSq
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sourceDot_cutoffAngularField
    (G : (Fin n → ℝ) → (Fin n → ℝ))
    (u : Fin n → ℝ) :
    HGAS.dot u (cutoffSourceAngularField G u) =
      sourceAngularBump (n := n) u *
        HGAS.radialReward G u * (1 - sourceRadiusSq u) := by
  rw [cutoffSourceAngularField, HGAS.dot_smul_right,
    HGAS.dot_angularField, HGAS.normSq_eq_sourceRadiusSq]
  ring

/-- The cutoff flow preserves the source unit sphere in both time
directions. -/
theorem sourceAngularAmbientFlow_preserves_radiusSq
    (G : (Fin n → ℝ) → (Fin n → ℝ))
    (hG : ContDiff ℝ 1 G)
    (u : Fin n → ℝ) (hu : sourceRadiusSq u = 1) :
    ∀ t, sourceRadiusSq (sourceAngularAmbientFlow G hG t u) = 1 := by
  let γ : ℝ → (Fin n → ℝ) :=
    fun t ↦ sourceAngularAmbientFlow G hG t u
  let z : ℝ → ℝ := fun t ↦ sourceRadiusSq (γ t) - 1
  let b : ℝ → ℝ := fun t ↦
    -2 * sourceAngularBump (n := n) (γ t) *
      HGAS.radialReward G (γ t)
  have hγ :
      IsIntegralCurve γ (fun _ ↦ cutoffSourceAngularField G) := by
    simpa [γ] using
      sourceAngularAmbientFlow_isIntegralCurve_cutoff G hG u
  have hz : ∀ t, HasDerivAt z (b t * z t) t := by
    intro t
    have hR := HasDerivAt.sourceRadiusSq (hγ t)
    have hsub := hR.sub_const (1 : ℝ)
    convert hsub using 1
    rw [sourceDot_cutoffAngularField]
    simp only [z, b, γ]
    ring
  have hγcont : Continuous γ := hγ.continuous
  have hb : Continuous b := by
    have hbump :
        Continuous
          (fun t ↦ sourceAngularBump (n := n) (γ t)) :=
      (sourceAngularBump (n := n)).continuous.comp hγcont
    have hreward :
        Continuous (fun t ↦ HGAS.radialReward G (γ t)) :=
      (contDiff_sourceRadialReward hG).continuous.comp hγcont
    dsimp [b]
    fun_prop
  have hzzero : z 0 = 0 := by
    simp [z, γ, Flow.map_zero_apply, hu]
  have hall :=
    HGAS.eq_zero_of_hasDerivAt_eq_mul_self z b hz hb hzzero
  intro t
  have := hall t
  dsimp [z, γ] at this
  linarith

theorem isInvariant_sourceUnitSphere
    (G : (Fin n → ℝ) → (Fin n → ℝ))
    (hG : ContDiff ℝ 1 G) :
    IsInvariant (sourceAngularAmbientFlow G hG)
      (sourceUnitSphere n) := by
  intro t u hu
  exact sourceAngularAmbientFlow_preserves_radiusSq G hG u hu t

/-- The continuous angular flow on the compact source unit sphere. -/
noncomputable def sourceAngularFlow
    (G : (Fin n → ℝ) → (Fin n → ℝ))
    (hG : ContDiff ℝ 1 G) :
    Flow ℝ (sourceUnitSphere n) :=
  (sourceAngularAmbientFlow G hG).restrict
    (isInvariant_sourceUnitSphere G hG)

/-- On a unit-sphere orbit the cutoff is one, so the ambient orbit solves
the original source angular ODE. -/
theorem sourceAngularAmbientFlow_isIntegralCurve
    (G : (Fin n → ℝ) → (Fin n → ℝ))
    (hG : ContDiff ℝ 1 G)
    (u : Fin n → ℝ) (hu : sourceRadiusSq u = 1) :
    IsIntegralCurve
      (fun t ↦ sourceAngularAmbientFlow G hG t u)
      (fun _ ↦ HGAS.angularField G) := by
  intro t
  have hcut :=
    sourceAngularAmbientFlow_isIntegralCurve_cutoff G hG u t
  have hRt :=
    sourceAngularAmbientFlow_preserves_radiusSq G hG u hu t
  have hbump :=
    sourceAngularBump_eq_one_of_radiusSq_eq_one
      (sourceAngularAmbientFlow G hG t u) hRt
  simpa [cutoffSourceAngularField, hbump] using hcut

end

end HGAS.Veronese
