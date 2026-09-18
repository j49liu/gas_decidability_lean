import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Proper local homeomorphisms are covering maps

A local homeomorphism need not be a covering map: infinitely many
local sheets can disappear while one moves in the target.  Properness
rules out precisely that escape.

Indeed, every fiber of a proper map is compact.  A local
homeomorphism has discrete fibers, so a Hausdorff source makes each
fiber finite.  Properness also makes the map closed.  Mathlib's
finite-fiber gluing theorem then shrinks the finitely many local
inverse charts to one common evenly covered neighborhood.

This small wrapper is useful whenever a geometric parametrization is
proved locally invertible by an inverse-function theorem and globally
proper by compactness.
-/

namespace HGAS.Topology

open Set Topology

variable {X Y : Type*}
  [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X]
  {f : X → Y}

/-- A proper local homeomorphism with Hausdorff source is a covering
map.  Surjectivity is not needed: Mathlib's definition permits empty
fibers away from the range. -/
theorem IsProperMap.isCoveringMap_of_isLocalHomeomorph
    (hproper : IsProperMap f)
    (hlocal : IsLocalHomeomorph f) :
    IsCoveringMap f := by
  intro y
  have hcharts :
      ∀ x ∈ f ⁻¹' ({y} : Set Y),
        ∃ e : OpenPartialHomeomorph X Y,
          x ∈ e.source ∧ e = f := by
    intro x _
    obtain ⟨e, hxe, he⟩ := hlocal x
    exact ⟨e, hxe, he.symm⟩
  have hdiscrete :
      IsDiscrete (f ⁻¹' ({y} : Set Y)) :=
    IsDiscrete.of_openPartialHomeomorph
      f subset_rfl hcharts
  have hfinite :
      (f ⁻¹' ({y} : Set Y)).Finite :=
    (hproper.isCompact_preimage isCompact_singleton).finite
      hdiscrete
  exact
    hproper.isClosedMap.isEvenlyCovered_of_openPartialHomeomorph
      hfinite hcharts

end HGAS.Topology
