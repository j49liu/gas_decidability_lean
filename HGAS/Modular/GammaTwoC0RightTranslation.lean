import HGAS.Modular.CompactlySupportedDenseInC0
import HGAS.Modular.GammaTwoShearFlowBoxes
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic

/-!
# Strong continuity of right translation on `C₀(Γ(2) \ SL(2, ℝ))`

The good-return-time argument compares an observable at two orbit points
which differ by a group element tending to the identity.  The required
estimate is uniform in the orbit point, so pointwise continuity of the
action is not enough.  This module proves the stronger statement that the
right regular action is strongly continuous in the `C₀` supremum norm.

For a compactly supported observable, choose a compact neighborhood `C`
of the identity.  All points at which either `f(q)` or `f(q a)` can be
nonzero for `a ∈ C` lie in one compact set, namely the image of
`C × tsupport f` under `(a,x) ↦ x a⁻¹`.  Joint continuity of the quotient
action is uniform on this compact set, while both functions vanish off it.
This proves the compact-support case.  Density of `C_c` in `C₀` and the
isometry of every right translation give the general case.

The construction and the continuity theorem are reusable in subsequent
shearing estimates.
-/

namespace HGAS.Modular

open Filter Function Set Topology
open scoped CompactlySupported ZeroAtInfty

noncomputable section

local instance gammaTwoFrameQuotientMetricSpaceForC0Translation :
    MetricSpace GammaTwoFrameQuotient :=
  TopologicalSpace.metrizableSpaceMetric GammaTwoFrameQuotient

local instance realModularFrameMetricSpace :
    MetricSpace RealModularFrame :=
  TopologicalSpace.metrizableSpaceMetric RealModularFrame

def gammaTwoC0RightTranslate
    (a : RealModularFrame)
    (f : C₀(GammaTwoFrameQuotient, ℝ)) :
    C₀(GammaTwoFrameQuotient, ℝ) :=
  f.comp (gammaTwoFrameRightMulHomeomorph a).toCocompactMap

@[simp]
theorem gammaTwoC0RightTranslate_apply
    (a : RealModularFrame)
    (f : C₀(GammaTwoFrameQuotient, ℝ))
    (q : GammaTwoFrameQuotient) :
    gammaTwoC0RightTranslate a f q =
      f (gammaTwoFrameRightMul a q) :=
  rfl

@[simp]
theorem gammaTwoC0RightTranslate_one
    (f : C₀(GammaTwoFrameQuotient, ℝ)) :
    gammaTwoC0RightTranslate 1 f = f := by
  ext q
  simp [gammaTwoC0RightTranslate_apply,
    gammaTwoFrameRightMul_one]

theorem norm_gammaTwoC0RightTranslate_le
    (a : RealModularFrame)
    (f : C₀(GammaTwoFrameQuotient, ℝ)) :
    ‖gammaTwoC0RightTranslate a f‖ ≤ ‖f‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
    BoundedContinuousFunction.norm_le]
  · intro q
    exact f.toBCF.norm_coe_le_norm _
  · exact norm_nonneg _

@[simp]
theorem norm_gammaTwoC0RightTranslate
    (a : RealModularFrame)
    (f : C₀(GammaTwoFrameQuotient, ℝ)) :
    ‖gammaTwoC0RightTranslate a f‖ = ‖f‖ := by
  apply le_antisymm
  · exact norm_gammaTwoC0RightTranslate_le a f
  · have h :=
      norm_gammaTwoC0RightTranslate_le a⁻¹
        (gammaTwoC0RightTranslate a f)
    have hcancel :
        gammaTwoC0RightTranslate a⁻¹
            (gammaTwoC0RightTranslate a f) = f := by
      ext q
      simp only [gammaTwoC0RightTranslate_apply]
      have hmul :=
        congrFun
          (gammaTwoFrameRightMul_mul a⁻¹ a) q
      apply congrArg f
      simpa only [inv_mul_cancel, gammaTwoFrameRightMul_one,
        id_eq, Function.comp_apply] using hmul.symm
    simpa only [hcancel] using h

set_option maxHeartbeats 800000 in
-- Compact-subtype elaboration and uniform-convergence filter normalization
-- are substantially more expensive than the mathematical argument.
theorem tendsto_gammaTwoC0RightTranslate_one_compactlySupported
    (f : C_c(GammaTwoFrameQuotient, ℝ)) :
    Tendsto
      (fun a : RealModularFrame ↦
        gammaTwoC0RightTranslate a
          (HGAS.Dynamics.compactlySupportedToC0 f))
      (𝓝 1)
      (𝓝 (HGAS.Dynamics.compactlySupportedToC0 f)) := by
  let K : Set GammaTwoFrameQuotient := tsupport f
  have hK : IsCompact K := f.hasCompactSupport
  obtain ⟨C, hCcompact, hCnhds⟩ :=
    exists_compact_mem_nhds (1 : RealModularFrame)
  have hCmem : (1 : RealModularFrame) ∈ C :=
    mem_of_mem_nhds hCnhds
  let L : Set GammaTwoFrameQuotient :=
    (fun p : RealModularFrame × GammaTwoFrameQuotient ↦
      gammaTwoFrameRightMul p.1⁻¹ p.2) '' (C ×ˢ K)
  have hLcompact : IsCompact L := by
    apply (hCcompact.prod hK).image
    exact gammaTwoFrameRightMul_joint_continuous.comp
      ((continuous_inv.comp continuous_fst).prodMk continuous_snd)
  letI : CompactSpace L :=
    isCompact_iff_compactSpace.mp hLcompact
  let F : RealModularFrame → L → ℝ :=
    fun a q ↦ f (gammaTwoFrameRightMul a q.1)
  have hFcontinuous : Continuous ↿F := by
    exact f.continuous.comp
      (gammaTwoFrameRightMul_joint_continuous.comp
        (continuous_fst.prodMk
          (continuous_subtype_val.comp continuous_snd)))
  have hFuniform :
      TendstoUniformly F (F 1) (𝓝 (1 : RealModularFrame)) :=
    Continuous.tendstoUniformly F hFcontinuous 1
  rw [ZeroAtInftyContinuousMap.tendsto_iff_tendstoUniformly]
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hcompactEventually :
      ∀ᶠ a in 𝓝 (1 : RealModularFrame),
        ∀ q : L,
          dist (F 1 q) (F a q) < ε :=
    (Metric.tendstoUniformly_iff.mp hFuniform) ε hε
  filter_upwards [hCnhds, hcompactEventually] with a haC ha
  intro q
  by_cases hqL : q ∈ L
  · let qL : L := ⟨q, hqL⟩
    simpa only [gammaTwoC0RightTranslate_apply,
      HGAS.Dynamics.compactlySupportedToC0_apply,
      F, qL, gammaTwoFrameRightMul_one] using ha qL
  · have hqK : q ∉ K := by
      intro hqK
      apply hqL
      refine ⟨((1 : RealModularFrame), q),
        ⟨hCmem, hqK⟩, ?_⟩
      simp only [inv_one, gammaTwoFrameRightMul_one]
      rfl
    have hqaK :
        gammaTwoFrameRightMul a q ∉ K := by
      intro hqaK
      apply hqL
      refine ⟨(a, gammaTwoFrameRightMul a q),
        ⟨haC, hqaK⟩, ?_⟩
      have hmul :=
        congrFun
          (gammaTwoFrameRightMul_mul a a⁻¹) q
      simpa only [mul_inv_cancel, gammaTwoFrameRightMul_one,
        id_eq, Function.comp_apply] using hmul.symm
    have hfq : f q = 0 :=
      image_eq_zero_of_notMem_tsupport hqK
    have hfqa :
        f (gammaTwoFrameRightMul a q) = 0 :=
      image_eq_zero_of_notMem_tsupport hqaK
    simp only [gammaTwoC0RightTranslate_apply,
      HGAS.Dynamics.compactlySupportedToC0_apply,
      hfq, hfqa, dist_self]
    exact hε

theorem tendsto_gammaTwoC0RightTranslate_one
    (f : C₀(GammaTwoFrameQuotient, ℝ)) :
    Tendsto
      (fun a : RealModularFrame ↦
        gammaTwoC0RightTranslate a f)
      (𝓝 1) (𝓝 f) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨g, hg⟩ :=
    HGAS.Dynamics.exists_compactlySupported_dist_lt
      f (show 0 < ε / 3 by positivity)
  have hg' :
      ‖HGAS.Dynamics.compactlySupportedToC0 g - f‖ <
        ε / 3 := by
    simpa only [dist_eq_norm] using hg
  have hcompact :=
    tendsto_gammaTwoC0RightTranslate_one_compactlySupported g
  have hevent :
      ∀ᶠ a in 𝓝 (1 : RealModularFrame),
        dist
          (gammaTwoC0RightTranslate a
            (HGAS.Dynamics.compactlySupportedToC0 g))
          (HGAS.Dynamics.compactlySupportedToC0 g) <
        ε / 3 :=
    (Metric.tendsto_nhds.mp hcompact (ε / 3)
      (by positivity))
  filter_upwards [hevent] with a ha
  rw [dist_eq_norm] at ha ⊢
  have hsub :
      gammaTwoC0RightTranslate a f -
          gammaTwoC0RightTranslate a
            (HGAS.Dynamics.compactlySupportedToC0 g) =
        gammaTwoC0RightTranslate a
          (f - HGAS.Dynamics.compactlySupportedToC0 g) := by
    rfl
  have hfirst :
      ‖gammaTwoC0RightTranslate a f -
          gammaTwoC0RightTranslate a
            (HGAS.Dynamics.compactlySupportedToC0 g)‖ =
        ‖f - HGAS.Dynamics.compactlySupportedToC0 g‖ := by
    rw [hsub, norm_gammaTwoC0RightTranslate]
  calc
    ‖gammaTwoC0RightTranslate a f - f‖ ≤
        ‖gammaTwoC0RightTranslate a f -
            gammaTwoC0RightTranslate a
              (HGAS.Dynamics.compactlySupportedToC0 g)‖ +
          ‖gammaTwoC0RightTranslate a
              (HGAS.Dynamics.compactlySupportedToC0 g) -
            f‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤
        ‖gammaTwoC0RightTranslate a f -
            gammaTwoC0RightTranslate a
              (HGAS.Dynamics.compactlySupportedToC0 g)‖ +
          (‖gammaTwoC0RightTranslate a
              (HGAS.Dynamics.compactlySupportedToC0 g) -
              HGAS.Dynamics.compactlySupportedToC0 g‖ +
            ‖HGAS.Dynamics.compactlySupportedToC0 g - f‖) := by
      gcongr
      exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ =
        ‖f - HGAS.Dynamics.compactlySupportedToC0 g‖ +
          (‖gammaTwoC0RightTranslate a
              (HGAS.Dynamics.compactlySupportedToC0 g) -
              HGAS.Dynamics.compactlySupportedToC0 g‖ +
            ‖HGAS.Dynamics.compactlySupportedToC0 g - f‖) := by
      rw [hfirst]
    _ < ε / 3 + (ε / 3 + ε / 3) := by
      gcongr
      · simpa only [norm_sub_rev] using hg'
    _ = ε := by ring

end

end HGAS.Modular
