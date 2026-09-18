import HGAS.Analysis.QuadraticHomogeneousRegularity
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-!
# Quadratic radial extension of a smooth angular profile

A function defined on the unit sphere can be extended along rays by

```
V(x) = ‖x‖² v(x / ‖x‖),    x ≠ 0,
V(0) = 0.
```

This file packages the elementary but frequently reused facts about this
construction.  The normalized direction is smooth away from the origin,
the radial extension is positively homogeneous of degree two, and a
globally `C¹` ambient profile gives a globally `C¹` radial extension.  The
last assertion includes the nontrivial regularity statement at the
origin; it follows from the quadratic homogeneous cone theorem in
`HGAS.Analysis.QuadraticHomogeneousRegularity`.

The ambient profile is allowed to have arbitrary values away from the
unit sphere.  Thus, in applications one only needs to construct a smooth
extension of the desired angular data.
-/

namespace HGAS

open Metric Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance : DecidableEq E := Classical.decEq E

/-- The direction obtained by dividing a vector by its norm.  We set the
direction of the zero vector to zero, as forced by scalar multiplication. -/
def normDirection (x : E) : E :=
  (‖x‖ : ℝ)⁻¹ • x

/-- Extend an angular profile quadratically along every nonzero ray, and
give the extension value zero at the origin. -/
def quadraticRadialExtension (v : E → ℝ) (x : E) : ℝ :=
  if x = 0 then 0 else ‖x‖ ^ 2 * v (normDirection x)

@[simp]
theorem normDirection_zero :
    normDirection (0 : E) = 0 := by
  simp [normDirection]

@[simp]
theorem quadraticRadialExtension_zero (v : E → ℝ) :
    quadraticRadialExtension v 0 = 0 := by
  simp [quadraticRadialExtension]

theorem quadraticRadialExtension_of_ne
    (v : E → ℝ) {x : E} (hx : x ≠ 0) :
    quadraticRadialExtension v x =
      ‖x‖ ^ 2 * v (normDirection x) := by
  simp [quadraticRadialExtension, hx]

/-- The normalized direction of a nonzero vector has norm one. -/
theorem norm_normDirection {x : E} (hx : x ≠ 0) :
    ‖normDirection x‖ = 1 := by
  rw [normDirection, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

/-- Normalization does not change when a ray is rescaled by a positive
real number. -/
theorem normDirection_pos_smul
    (a : ℝ) (ha : 0 < a) (x : E) :
    normDirection (a • x) = normDirection x := by
  by_cases hx : x = 0
  · simp [hx]
  · have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    simp only [normDirection, norm_smul, Real.norm_eq_abs,
      abs_of_pos ha, smul_smul]
    congr 1
    field_simp

/-- Quadratic radial extension is positively homogeneous of degree two. -/
theorem quadraticRadialExtension_twoHomogeneous
    (v : E → ℝ) (a : ℝ) (ha : 0 < a) (x : E) :
    quadraticRadialExtension v (a • x) =
      a ^ 2 * quadraticRadialExtension v x := by
  by_cases hx : x = 0
  · simp [hx]
  · have hax : a • x ≠ 0 := smul_ne_zero ha.ne' hx
    rw [quadraticRadialExtension_of_ne v hax,
      quadraticRadialExtension_of_ne v hx,
      normDirection_pos_smul a ha x, norm_smul,
      Real.norm_eq_abs, abs_of_pos ha]
    ring

variable [InnerProductSpace ℝ E]

/-- The normalized-direction map is `Cⁿ` on the punctured space. -/
theorem contDiffOn_normDirection_compl_zero (n : WithTop ℕ∞) :
    ContDiffOn ℝ n normDirection ({0} : Set E)ᶜ := by
  have hid :
      ContDiffOn ℝ n (fun x : E ↦ x) ({0} : Set E)ᶜ :=
    contDiff_id.contDiffOn
  have hnorm :
      ContDiffOn ℝ n (fun x : E ↦ ‖x‖) ({0} : Set E)ᶜ :=
    hid.norm ℝ (by
      intro x hx
      simpa only [mem_compl_iff, mem_singleton_iff] using hx)
  have hinv :
      ContDiffOn ℝ n (fun x : E ↦ (‖x‖ : ℝ)⁻¹)
        ({0} : Set E)ᶜ :=
    hnorm.inv (by
      intro x hx
      exact norm_ne_zero_iff.mpr (by
        simpa only [mem_compl_iff, mem_singleton_iff] using hx))
  simpa only [normDirection] using hinv.smul hid

/-- If the ambient angular profile is `Cⁿ`, then its quadratic radial
extension is `Cⁿ` away from the origin. -/
theorem contDiffOn_quadraticRadialExtension_compl_zero
    (n : WithTop ℕ∞) (v : E → ℝ) (hv : ContDiff ℝ n v) :
    ContDiffOn ℝ n (quadraticRadialExtension v)
      ({0} : Set E)ᶜ := by
  have hnormSq :
      ContDiffOn ℝ n (fun x : E ↦ ‖x‖ ^ 2)
        ({0} : Set E)ᶜ :=
    (contDiff_id.norm_sq ℝ).contDiffOn
  have hprofile :
      ContDiffOn ℝ n (fun x : E ↦ v (normDirection x))
        ({0} : Set E)ᶜ :=
    hv.comp_contDiffOn (contDiffOn_normDirection_compl_zero n)
  apply (hnormSq.mul hprofile).congr
  intro x hx
  apply quadraticRadialExtension_of_ne
  simpa only [mem_compl_iff, mem_singleton_iff] using hx

variable [FiniteDimensional ℝ E]

/-- A `C¹` ambient angular profile has a globally `C¹` quadratic radial
extension, including at the cone tip. -/
theorem contDiff_one_quadraticRadialExtension
    (v : E → ℝ) (hv : ContDiff ℝ 1 v) :
    ContDiff ℝ 1 (quadraticRadialExtension v) := by
  apply contDiff_one_of_twoHomogeneous_contDiffOn_compl_zero
      (quadraticRadialExtension v)
  · exact quadraticRadialExtension_zero v
  · exact contDiffOn_quadraticRadialExtension_compl_zero 1 v hv
  · exact quadraticRadialExtension_twoHomogeneous v

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Strict positivity of the angular profile on the unit sphere transfers
to strict positivity of the radial extension away from the origin. -/
theorem quadraticRadialExtension_pos_of_unitSphere_pos
    (v : E → ℝ)
    (hv : ∀ u : E, ‖u‖ = 1 → 0 < v u)
    {x : E} (hx : x ≠ 0) :
    0 < quadraticRadialExtension v x := by
  rw [quadraticRadialExtension_of_ne v hx]
  exact mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hx))
    (hv (normDirection x) (norm_normDirection hx))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Under strict positivity on the sphere, the radial extension is
nonnegative everywhere. -/
theorem quadraticRadialExtension_nonneg_of_unitSphere_pos
    (v : E → ℝ)
    (hv : ∀ u : E, ‖u‖ = 1 → 0 < v u)
    (x : E) :
    0 ≤ quadraticRadialExtension v x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (quadraticRadialExtension_pos_of_unitSphere_pos v hv hx).le

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Under strict positivity on the sphere, the quadratic radial extension
vanishes exactly at the origin. -/
theorem quadraticRadialExtension_eq_zero_iff
    (v : E → ℝ)
    (hv : ∀ u : E, ‖u‖ = 1 → 0 < v u)
    (x : E) :
    quadraticRadialExtension v x = 0 ↔ x = 0 := by
  constructor
  · intro hV
    by_contra hx
    exact (quadraticRadialExtension_pos_of_unitSphere_pos
      v hv hx).ne' hV
  · rintro rfl
    exact quadraticRadialExtension_zero v

end

end HGAS
