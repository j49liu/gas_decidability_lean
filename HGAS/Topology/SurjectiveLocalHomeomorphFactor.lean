import Mathlib.Topology.IsLocalHomeomorph

/-!
# Recovering a local homeomorphism from a locally injective factor

Suppose `f : X → Y` is continuous, `g : Y → Z` is
continuous and locally injective, and the composite `g ∘ f` is a local
homeomorphism.  Then `f` is itself a local homeomorphism.

The point is that a local inverse for the composite already reconstructs
the source point from `g y`.  Local injectivity of `g` shows that every
nearby `y` in the resulting open target is hit by this local inverse.

This criterion is useful for parametrized algebraic curves.  One first
projects the curve to a convenient local coordinate, proves that the
parametrization followed by the projection is a local homeomorphism,
and proves local injectivity of the projection from the defining
equations.  The theorem below then recovers a local homeomorphism into
the full curve without explicitly writing every square-root branch.
-/

namespace HGAS.Topology

open Function Set Topology

variable {X Y Z : Type*}
  [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

/-- A continuous map is a local homeomorphism if a continuous locally
injective postcomposition is a local homeomorphism. -/
theorem isLocalHomeomorph_of_comp_of_locallyInjective
    {f : X → Y} {g : Y → Z}
    (hf : Continuous f)
    (hg : Continuous g)
    (hgf : IsLocalHomeomorph (g ∘ f))
    (hglocallyInjective : IsLocallyInjective g) :
    IsLocalHomeomorph f := by
  intro x
  obtain ⟨e, hxe, he⟩ := hgf x
  obtain ⟨V, hVopen, hfxV, hVinj⟩ :=
    hglocallyInjective (f x)
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
    exact
      ⟨u, hu, (congrFun he u).symm⟩
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
            congrArg e.symm (congrFun he u)
          _ = u :=
            e.left_inv (hSsource hu)
      right_inv' := by
        intro y hy
        apply hVinj (hmapTarget y hy).2 hy.1
        calc
          g (f (e.symm (g y))) =
              e (e.symm (g y)) :=
            congrFun he (e.symm (g y))
          _ = g y :=
            e.right_inv (hgyTarget y hy)
      open_source := hSopen
      open_target := hWopen
      continuousOn_toFun :=
        hf.continuousOn
      continuousOn_invFun :=
        e.continuousOn_invFun.comp
          hg.continuousOn hgyTarget }
  refine ⟨chart, hxS, ?_⟩
  rfl

end HGAS.Topology
