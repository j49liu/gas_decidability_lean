import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Elementary constructions for local homeomorphisms

This file records two standard closure properties in the precise form
needed by the theta-quotient argument.

* The product of two local homeomorphisms is a local homeomorphism.
* Restricting a local homeomorphism over an open subset of its target
  is again a local homeomorphism.

Both statements are topological and independent of the modular-form
application.
-/

namespace HGAS.Topology

open Function Set Topology

variable {X X' Y Y' : Type*}
  [TopologicalSpace X] [TopologicalSpace X']
  [TopologicalSpace Y] [TopologicalSpace Y']

/-- Products preserve local homeomorphisms. -/
theorem IsLocalHomeomorph.prodMap
    {f : X → X'} {g : Y → Y'}
    (hf : IsLocalHomeomorph f)
    (hg : IsLocalHomeomorph g) :
    IsLocalHomeomorph (Prod.map f g) := by
  rintro ⟨x, y⟩
  obtain ⟨ef, hxef, hef⟩ := hf x
  obtain ⟨eg, hyeg, heg⟩ := hg y
  refine ⟨ef.prod eg, ⟨hxef, hyeg⟩, ?_⟩
  funext p
  exact Prod.ext
    (congrFun hef p.1)
    (congrFun heg p.2)

/-- Restrict a local homeomorphism to the inverse image of an open
target set. -/
theorem IsLocalHomeomorph.restrictPreimage
    {f : X → Y} (hf : IsLocalHomeomorph f)
    {s : Set Y} (hs : IsOpen s) :
    IsLocalHomeomorph (s.restrictPreimage f) := by
  have hsourceOpen :
      IsOpen (f ⁻¹' s) :=
    hs.preimage hf.continuous
  have hsource :
      IsLocalHomeomorph
        ((↑) : f ⁻¹' s → X) :=
    hsourceOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have htarget :
      IsLocalHomeomorph
        ((↑) : s → Y) :=
    hs.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hcomposite :
      IsLocalHomeomorph
        (f ∘ ((↑) : f ⁻¹' s → X)) :=
    hf.comp hsource
  have hrestrictedComposite :
      IsLocalHomeomorph
        (((↑) : s → Y) ∘
          s.restrictPreimage f) := by
    simpa only [Function.comp_apply,
      Set.restrictPreimage] using hcomposite
  exact
    hrestrictedComposite.of_comp htarget
      (hf.continuous.restrictPreimage)

end HGAS.Topology
