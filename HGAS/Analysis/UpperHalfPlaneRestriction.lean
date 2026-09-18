import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Geometry.Manifold.Notation

/-!
# Restricting holomorphic functions to the upper half-plane

Mathlib characterizes manifold differentiability of a map from the upper
half-plane by ordinary complex differentiability after composing with the
local inverse `ofComplex`.  The small adapters below package the direction
used repeatedly by modular-form calculations: a holomorphic ambient
function remains holomorphic after restriction to `ℍ`.
-/

namespace HGAS.Analysis

open Complex UpperHalfPlane
open scoped Manifold

/-- A complex-differentiable ambient function is manifold-differentiable
after restriction to the upper half-plane. -/
theorem mdifferentiableAt_restrict
    {G : ℂ → ℂ} {z : ℍ}
    (hG : DifferentiableAt ℂ G z) :
    MDiffAt (fun u : ℍ ↦ G (u : ℂ)) z := by
  rw [UpperHalfPlane.mdifferentiableAt_iff]
  apply hG.congr_of_eventuallyEq
  filter_upwards
    [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp [Function.comp_apply, ofComplex_apply_of_im_pos hw]

/-- A function holomorphic on the open upper half-plane restricts to an
everywhere manifold-differentiable function on `ℍ`. -/
theorem mdifferentiable_restrict
    {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G upperHalfPlaneSet) :
    MDiff (fun u : ℍ ↦ G (u : ℂ)) := fun z ↦
  mdifferentiableAt_restrict
    ((hG z z.im_pos).differentiableAt
      (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos))

end HGAS.Analysis
