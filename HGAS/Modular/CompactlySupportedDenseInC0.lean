import HGAS.Modular.CountableC0Tests
import Mathlib.Topology.UrysohnsLemma

/-!
# Compactly supported functions are dense in `C₀`

On a locally compact Hausdorff space, a continuous function vanishing at
infinity can be cut off outside a compact set with arbitrarily small
uniform error.  This file records that elementary approximation in the
exact bundled form needed to pass between the usual `C_c` statement of
horocycle equidistribution and the convenient Banach space `C₀`.
-/

namespace HGAS.Dynamics

open Filter Function Set Topology
open scoped BoundedContinuousFunction CompactlySupported ZeroAtInfty

noncomputable section

variable {X : Type*}
  [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]

/-- Every `C₀` function admits a compactly supported continuous uniform
approximation. -/
theorem exists_compactlySupported_dist_lt
    (f : C₀(X, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C_c(X, ℝ),
      dist (compactlySupportedToC0 g) f < ε := by
  have heventually :
      ∀ᶠ x in cocompact X,
        f x ∈ Metric.ball (0 : ℝ) (ε / 2) :=
    (zero_at_infty f)
      (Metric.ball_mem_nhds 0 (half_pos hε))
  obtain ⟨K, hKcompact, hKoutside⟩ :=
    mem_cocompact.mp heventually
  obtain ⟨c, hcK, _hcEmpty, hcCompact, hcRange⟩ :=
    exists_continuous_one_zero_of_isCompact
      hKcompact isClosed_empty (disjoint_empty K)
  let g : C_c(X, ℝ) :=
    { toFun := fun x ↦ c x * f x
      continuous_toFun :=
        c.continuous.mul f.continuous
      hasCompactSupport' := hcCompact.mul_right }
  refine ⟨g, ?_⟩
  rw [← ZeroAtInftyContinuousMap.dist_toBCF_eq_dist]
  apply lt_of_le_of_lt
    ((BoundedContinuousFunction.dist_le
      (half_pos hε).le).mpr ?_)
    (half_lt_self hε)
  intro x
  rw [Real.dist_eq]
  change |c x * f x - f x| ≤ ε / 2
  by_cases hx : x ∈ K
  · rw [hcK hx]
    simp only [Pi.one_apply, one_mul, sub_self, abs_zero]
    exact (half_pos hε).le
  · have hfx :
        |f x| < ε / 2 := by
      have hxBall := hKoutside hx
      simpa only [mem_preimage, Metric.mem_ball,
        Real.dist_eq, sub_zero] using hxBall
    have hcabs : |c x - 1| ≤ 1 := by
      obtain ⟨hc0, hc1⟩ := hcRange x
      rw [abs_le]
      constructor <;> linarith
    rw [show c x * f x - f x =
      (c x - 1) * f x by ring, abs_mul]
    calc
      |c x - 1| * |f x| ≤ 1 * |f x| :=
        mul_le_mul_of_nonneg_right hcabs (abs_nonneg _)
      _ ≤ ε / 2 := by
        simpa only [one_mul] using hfx.le

/-- Equivalently, the image of `C_c(X, ℝ)` is dense in `C₀(X, ℝ)`. -/
theorem denseRange_compactlySupportedToC0 :
    DenseRange (compactlySupportedToC0 :
      C_c(X, ℝ) → C₀(X, ℝ)) := by
  rw [Metric.denseRange_iff]
  intro f ε hε
  obtain ⟨g, hg⟩ :=
    exists_compactlySupported_dist_lt f hε
  exact ⟨g, by simpa only [dist_comm] using hg⟩

end

end HGAS.Dynamics
