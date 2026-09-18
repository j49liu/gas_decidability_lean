import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Separability of continuous functions vanishing at infinity

For a second-countable locally compact Hausdorff space `X`, this file
proves that the normed space `C₀(X, ℝ)` is separable.

The proof is concrete.  A compact exhaustion supplies a countable
neighborhood basis at the point at infinity, so the one-point
compactification is second countable.  A function vanishing at infinity
extends continuously by zero to that compactification, and extension is a
linear isometry into its space of continuous real functions.

The two ingredients are useful independently of the modular quotient.
-/

namespace HGAS.Dynamics

open Function Set Filter Topology TopologicalSpace
open scoped OnePoint ZeroAtInfty

noncomputable section

variable (X : Type*) [TopologicalSpace X]
  [T2Space X] [SecondCountableTopology X]
  [LocallyCompactSpace X]

/-- A countable basis for the one-point compactification consists of
images of a countable basis in `X` and complements of the members of a
compact exhaustion. -/
theorem onePoint_hasCountableBasis :
    ∃ b : Set (Set (OnePoint X)),
      b.Countable ∧ IsTopologicalBasis b := by
  let K : CompactExhaustion X := CompactExhaustion.choice X
  let b : Set (Set (OnePoint X)) :=
    Set.range
        (fun U : countableBasis X ↦
          OnePoint.some '' (U : Set X)) ∪
      Set.range
        (fun n : ℕ ↦
          (OnePoint.some '' K n)ᶜ)
  refine ⟨b, ?_, ?_⟩
  · exact (countable_range _).union (countable_range _)
  · apply isTopologicalBasis_of_isOpen_of_nhds
    · intro u hu
      rcases hu with hu | hu
      · obtain ⟨U, rfl⟩ := hu
        exact OnePoint.isOpen_image_coe.mpr
          (isOpen_of_mem_countableBasis U.property)
      · obtain ⟨n, rfl⟩ := hu
        exact OnePoint.isOpen_compl_image_coe.mpr
          ⟨(K.isCompact n).isClosed, K.isCompact n⟩
    · intro z u hzu hu
      induction z using OnePoint.rec with
      | infty =>
          have hu_nhds : u ∈ 𝓝 (∞ : OnePoint X) :=
            hu.mem_nhds hzu
          obtain ⟨s, ⟨hsclosed, hscompact⟩, hsu⟩ :=
            OnePoint.hasBasis_nhds_infty.mem_iff.mp hu_nhds
          obtain ⟨n, hsn⟩ :=
            K.exists_superset_of_isCompact hscompact
          refine
            ⟨(OnePoint.some '' K n)ᶜ,
              Or.inr ⟨n, rfl⟩, ?_, ?_⟩
          · exact OnePoint.infty_notMem_image_coe
          · rw [OnePoint.compl_image_coe]
            exact
              (union_subset_union_left
                ({∞} : Set (OnePoint X))
                (image_mono (compl_subset_compl.mpr hsn))).trans
                hsu
      | coe x =>
          have hxpre : x ∈ OnePoint.some ⁻¹' u := hzu
          have hopenpre :
              IsOpen (OnePoint.some ⁻¹' u) :=
            hu.preimage OnePoint.continuous_coe
          obtain ⟨V, hVbasis, hxV, hVsub⟩ :=
            (isBasis_countableBasis X).exists_subset_of_mem_open
              hxpre hopenpre
          let V' : countableBasis X := ⟨V, hVbasis⟩
          refine
            ⟨OnePoint.some '' V,
              Or.inl ⟨V', rfl⟩, ⟨x, hxV, rfl⟩, ?_⟩
          rintro _ ⟨y, hy, rfl⟩
          exact hVsub hy

/-- The one-point compactification of a second-countable locally compact
Hausdorff space is second countable. -/
noncomputable instance onePointSecondCountableTopology :
    SecondCountableTopology (OnePoint X) := by
  obtain ⟨b, hbcountable, hb⟩ :=
    onePoint_hasCountableBasis X
  exact hb.secondCountableTopology hbcountable

/-- Extension by zero at infinity. -/
def zeroAtInftyExtension (f : C₀(X, ℝ)) :
    C(OnePoint X, ℝ) :=
  OnePoint.continuousMapMk f.toContinuousMap 0 <| by
    rw [Filter.coclosedCompact_eq_cocompact]
    exact f.zero_at_infty'

omit [SecondCountableTopology X] [LocallyCompactSpace X] in
@[simp]
theorem zeroAtInftyExtension_coe
    (f : C₀(X, ℝ)) (x : X) :
    zeroAtInftyExtension X f (x : OnePoint X) = f x :=
  rfl

omit [SecondCountableTopology X] [LocallyCompactSpace X] in
@[simp]
theorem zeroAtInftyExtension_infty
    (f : C₀(X, ℝ)) :
    zeroAtInftyExtension X f (∞ : OnePoint X) = 0 :=
  rfl

/-- Extension by zero is a real-linear isometry. -/
def zeroAtInftyExtensionLinearIsometry :
    C₀(X, ℝ) →ₗᵢ[ℝ] C(OnePoint X, ℝ) where
  toFun := zeroAtInftyExtension X
  map_add' f g := by
    ext z
    induction z using OnePoint.rec <;> simp
  map_smul' c f := by
    ext z
    induction z using OnePoint.rec <;> simp
  norm_map' f := by
    apply le_antisymm
    · change ‖zeroAtInftyExtension X f‖ ≤ ‖f‖
      rw [(zeroAtInftyExtension X f).norm_le (norm_nonneg f)]
      intro z
      induction z using OnePoint.rec with
      | infty => simp
      | coe x =>
          simpa only [zeroAtInftyExtension_coe] using
            f.toBCF.norm_coe_le_norm x
    · rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
      rw [BoundedContinuousFunction.norm_le (norm_nonneg _)]
      intro x
      simpa only [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
        zeroAtInftyExtension_coe] using
        (zeroAtInftyExtension X f).norm_coe_le_norm
          (x : OnePoint X)

/-- `C₀(X, ℝ)` is separable in its supremum norm. -/
noncomputable instance zeroAtInftySeparableSpace :
    SeparableSpace C₀(X, ℝ) :=
  (zeroAtInftyExtensionLinearIsometry X).isEmbedding.separableSpace

end

end HGAS.Dynamics
