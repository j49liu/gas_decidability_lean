import Mathlib.Topology.IsLocalHomeomorph

/-!
# Pointwise recovery of a local homeomorphism from a coordinate

Suppose that `g ∘ f` is locally invertible at one point and that `g`
is injective on a neighborhood of the corresponding target point.
Then `f` is locally invertible at that point.

This is the pointwise form of the familiar coordinate-chart argument:
the local inverse of `g ∘ f` reconstructs a candidate source point,
and local injectivity of `g` proves that this candidate maps back to
the requested point of the intermediate space.

Unlike a global statement, this theorem permits the useful coordinate
`g` to depend on the source point.
-/

namespace HGAS.Topology

open Function Set Topology

variable {X Y Z : Type*}
  [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

/-- Pointwise locally-injective factor criterion for a local
homeomorphism. -/
theorem exists_localHomeomorph_of_comp_of_injOn
    {f : X → Y} {g : Y → Z} (x : X)
    (hf : Continuous f)
    (hg : Continuous g)
    (hgf :
      ∃ e : OpenPartialHomeomorph X Z,
        x ∈ e.source ∧
          (e : X → Z) = g ∘ f)
    (hginj :
      ∃ V : Set Y,
        IsOpen V ∧ f x ∈ V ∧ Set.InjOn g V) :
    ∃ chart : OpenPartialHomeomorph X Y,
      x ∈ chart.source ∧
        (chart : X → Y) = f := by
  obtain ⟨e, hxe, he⟩ := hgf
  obtain ⟨V, hVopen, hfxV, hVinj⟩ := hginj
  let S : Set X := e.source ∩ f ⁻¹' V
  have hSopen : IsOpen S :=
    e.open_source.inter (hVopen.preimage hf)
  have hSsource : S ⊆ e.source :=
    inter_subset_left
  have hxS : x ∈ S :=
    ⟨hxe, hfxV⟩
  let O : Set Z := e '' S
  have hOopen : IsOpen O :=
    e.isOpen_image_of_subset_source hSopen hSsource
  have hOtarget : O ⊆ e.target := by
    rintro _ ⟨u, hu, rfl⟩
    exact e.map_source (hSsource hu)
  let W : Set Y := V ∩ g ⁻¹' O
  have hWopen : IsOpen W :=
    hVopen.inter (hOopen.preimage hg)
  have hmapSource :
      ∀ u ∈ S, f u ∈ W := by
    intro u hu
    refine ⟨hu.2, ?_⟩
    exact ⟨u, hu, congrFun he u⟩
  have hgyTarget :
      ∀ y ∈ W, g y ∈ e.target := by
    intro y hy
    exact hOtarget hy.2
  have hmapTarget :
      ∀ y ∈ W, e.symm (g y) ∈ S := by
    intro y hy
    obtain ⟨u, hu, heu⟩ := hy.2
    have hinverse :
        e.symm (g y) = u := by
      rw [← heu]
      exact e.left_inv (hSsource hu)
    rw [hinverse]
    exact hu
  let chart : OpenPartialHomeomorph X Y :=
    { toFun := f
      invFun := fun y ↦ e.symm (g y)
      source := S
      target := W
      map_source' := hmapSource
      map_target' := hmapTarget
      left_inv' := by
        intro u hu
        calc
          e.symm (g (f u)) =
              e.symm (e u) :=
            congrArg e.symm (congrFun he u).symm
          _ = u :=
            e.left_inv (hSsource hu)
      right_inv' := by
        intro y hy
        apply hVinj (hmapTarget y hy).2 hy.1
        calc
          g (f (e.symm (g y))) =
              e (e.symm (g y)) :=
            (congrFun he (e.symm (g y))).symm
          _ = g y :=
            e.right_inv (hgyTarget y hy)
      open_source := hSopen
      open_target := hWopen
      continuousOn_toFun :=
        hf.continuousOn
      continuousOn_invFun :=
        e.continuousOn_invFun.comp
          hg.continuousOn hgyTarget }
  exact ⟨chart, hxS, rfl⟩

end HGAS.Topology
