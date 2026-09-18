import HGAS.Compactification.AllAffinePolynomialCode
import HGAS.Compactification.CentralSphere
import HGAS.Compiler.CompactAccumulatorPipelineFactor
import Mathlib.Tactic

/-!
# The finite affine chart of a one-block compact source

The fixed detector places every uncompactified coordinate in one affine
central block.  A point of the compact base therefore consists of

```
                         (x,w),       ‖x‖² + w² = 1.
```

On the finite interior `w ≠ 0`, the original affine point is recovered as
`z = x / w`.  This file identifies that chart with the reusable
`FiniteCentralChart` from `Compactification.CentralSphere`.

The denominator-clearing exponent used by the fixed detector is even,
say `2K`.  The common compact-time speed is consequently

```
                     w^(2K) = (1 + ‖z‖²)⁻ᴷ.
```

The right-hand expression depends only on the recovered affine point.  It
is everywhere strictly positive and at most one.  These facts are the
measure- and trajectory-level bridge from the compact source back to the
uncompactified polynomial system.
-/

namespace HGAS

open Set
open scoped BoundedContinuousFunction NNReal

noncomputable section

namespace CompactAccumulatorPipelineCode

namespace AllAffineCompactSourceChart

variable {n m : ℕ}

/-- The single-affine-block layout, with no pre-existing compact block. -/
abbrev layout (n : ℕ) :
    Fin n → Fin 1 ⊕ Fin 0 :=
  MixedCentralPolynomialCode.oneBlockAllAffineLayout n

/-- Complete compact source used by the accumulator pipeline in the
one-block all-affine specialization. -/
abbrev SourceSpace (n m : ℕ) :=
  UnitSpherePolynomialWrapper.SourceProductSphere
    (sourceBlock (m := m) (layout n))

/-- Its invariant finite interior. -/
abbrev FiniteSourceSpace (n m : ℕ) :=
  sourceFiniteInteriorSet (m := m) (layout n)

/-- The old compact coordinates `x`. -/
def oldPoint (v : SourceSpace n m) : Fin n → ℝ :=
  sourceOldPoint v

/-- The unique central coordinate `w`. -/
def weight (v : SourceSpace n m) : ℝ :=
  sourceChartWeight v 0

theorem continuous_oldPoint :
    Continuous (oldPoint : SourceSpace n m → (Fin n → ℝ)) := by
  apply continuous_pi
  intro j
  exact
    (continuous_apply
      (AccumulatorPolynomialCode.baseIndex
        (m := m)
        (MixedCentralPolynomialCode.xIndex (k := 1) j))).comp
      continuous_subtype_val

theorem continuous_weight :
    Continuous (weight : SourceSpace n m → ℝ) := by
  simpa only [weight] using
    (continuous_sourceChartWeight
      (m := m) (layout n) (0 : Fin 1))

/-- In the one-block layout, the mixed affine-block squared norm is the
ordinary finite-dimensional squared norm. -/
theorem affineBlockNormSq_eq_normSq
    (x : Fin n → ℝ) :
    MixedCentralPolynomialCode.affineBlockNormSq
        (layout n) x 0 =
      normSq x := by
  simp [MixedCentralPolynomialCode.affineBlockNormSq,
    normSq, dot, pow_two]

/-- The compact base coordinates belonging to the all-affine block form
the canonical central sphere. -/
def centralSpherePoint (v : SourceSpace n m) :
    CentralSphere n := by
  let x : Fin n → ℝ := oldPoint v
  let w : Fin 1 → ℝ := fun b ↦ sourceChartWeight v b
  have hy :
      MixedCentralPolynomialCode.chartPoint x w =
        sourceBasePoint v := by
    exact MixedCentralPolynomialCode.chartPoint_decompose
      (sourceBasePoint v)
  have hspheres :
      UnitSpherePolynomialWrapper.OnSourceProductSpheres
        (MixedCentralPolynomialCode.targetBlock (layout n))
        (MixedCentralPolynomialCode.chartPoint x w) := by
    rw [hy]
    exact sourceBasePoint_onSourceProductSpheres (layout n) v
  have haffine :=
    (MixedCentralPolynomialCode.onSourceProductSpheres_targetBlock_iff
      (layout n) x w).mp hspheres |>.1
  refine ⟨(x, w 0), ?_⟩
  have h := haffine (0 : Fin 1)
  simpa only [affineBlockNormSq_eq_normSq, x, w, weight,
    oldPoint] using h

@[simp]
theorem centralSpherePoint_x
    (v : SourceSpace n m) :
    (centralSpherePoint v).1.1 = oldPoint v :=
  rfl

@[simp]
theorem centralSpherePoint_w
    (v : SourceSpace n m) :
    (centralSpherePoint v).1.2 = weight v :=
  rfl

theorem continuous_centralSpherePoint :
    Continuous
      (centralSpherePoint : SourceSpace n m → CentralSphere n) := by
  apply Continuous.subtype_mk
  exact continuous_oldPoint.prodMk continuous_weight

/-- Membership in the pipeline finite interior supplies `w ≠ 0`. -/
theorem weight_ne_zero
    (v : FiniteSourceSpace n m) :
    weight v.1 ≠ 0 := by
  have h :=
    (sourceFiniteInteriorSet_iff
      (m := m) (layout n) v.1).mp v.2 |>.1 (0 : Fin 1)
  simpa only [weight] using h

/-- The canonical finite central chart associated with a finite pipeline
source point. -/
def finiteCentralChartPoint
    (v : FiniteSourceSpace n m) :
    FiniteCentralChart n :=
  ⟨centralSpherePoint v.1, weight_ne_zero v⟩

theorem continuous_finiteCentralChartPoint :
    Continuous
      (finiteCentralChartPoint :
        FiniteSourceSpace n m → FiniteCentralChart n) := by
  apply Continuous.subtype_mk
  exact continuous_centralSpherePoint.comp continuous_subtype_val

/-- Recover the original affine state `z=x/w`. -/
def affinePoint
    (v : FiniteSourceSpace n m) :
    Fin n → ℝ :=
  centralChartCoordinate (finiteCentralChartPoint v)

@[simp]
theorem affinePoint_apply
    (v : FiniteSourceSpace n m) (j : Fin n) :
    affinePoint v j = oldPoint v.1 j / weight v.1 :=
  rfl

theorem continuous_affinePoint :
    Continuous
      (affinePoint : FiniteSourceSpace n m → (Fin n → ℝ)) :=
  continuous_centralChartCoordinate.comp
    continuous_finiteCentralChartPoint

/-- The compact coordinates are exactly `x=wz`. -/
theorem oldPoint_eq_weight_mul_affinePoint
    (v : FiniteSourceSpace n m) (j : Fin n) :
    oldPoint v.1 j = weight v.1 * affinePoint v j := by
  rw [affinePoint_apply]
  field_simp [weight_ne_zero v]

/-- The old compact coordinates are the scaled source coordinates of the
recovered affine point. -/
theorem scaledSourcePoint_affinePoint
    (v : FiniteSourceSpace n m) :
    MixedCentralPolynomialCode.scaledSourcePoint
        (layout n) (fun _ ↦ weight v.1) (affinePoint v) =
      oldPoint v.1 := by
  funext j
  simp only [MixedCentralPolynomialCode.scaledSourcePoint,
    MixedCentralPolynomialCode.oneBlockAllAffineLayout]
  exact (oldPoint_eq_weight_mul_affinePoint v j).symm

/-- The complete compact base point is the scaled chart of its recovered
affine point. -/
theorem scaledChartPoint_affinePoint
    (v : FiniteSourceSpace n m) :
    MixedCentralPolynomialCode.scaledChartPoint
        (layout n) (fun _ ↦ weight v.1) (affinePoint v) =
      sourceBasePoint v.1 := by
  have hw :
      (fun _ : Fin 1 ↦ weight v.1) =
        fun b ↦ sourceChartWeight v.1 b := by
    funext b
    have hb : b = 0 := Subsingleton.elim _ _
    subst b
    rfl
  rw [MixedCentralPolynomialCode.scaledChartPoint,
    scaledSourcePoint_affinePoint, hw]
  exact
    MixedCentralPolynomialCode.chartPoint_decompose
      (sourceBasePoint v.1)

/-- The positive affine-space expression for the even projective
slowdown. -/
def affineSpeed (K : ℕ) (z : Fin n → ℝ) : ℝ :=
  (1 + normSq z)⁻¹ ^ K

theorem one_add_normSq_pos
    (z : Fin n → ℝ) :
    0 < 1 + normSq z := by
  have hnorm : 0 ≤ normSq z := normSq_nonneg z
  linarith

theorem affineSpeed_pos
    (K : ℕ) (z : Fin n → ℝ) :
    0 < affineSpeed K z := by
  exact pow_pos
    (inv_pos.mpr (one_add_normSq_pos z)) K

theorem affineSpeed_nonneg
    (K : ℕ) (z : Fin n → ℝ) :
    0 ≤ affineSpeed K z :=
  (affineSpeed_pos K z).le

theorem affineSpeed_le_one
    (K : ℕ) (z : Fin n → ℝ) :
    affineSpeed K z ≤ 1 := by
  have hdenom : 1 ≤ 1 + normSq z := by
    have hnorm : 0 ≤ normSq z := normSq_nonneg z
    linarith
  have hinv :
      (1 + normSq z)⁻¹ ≤ (1 : ℝ) := by
    exact inv_le_one_of_one_le₀ hdenom
  simpa only [one_pow] using
    pow_le_pow_left₀ (inv_nonneg.mpr
      (one_add_normSq_pos z).le) hinv K

theorem contDiff_normSq :
    ContDiff ℝ ⊤ (normSq : (Fin n → ℝ) → ℝ) := by
  unfold normSq dot
  fun_prop

theorem contDiff_affineSpeed
    (K : ℕ) :
    ContDiff ℝ ⊤ (affineSpeed (n := n) K) := by
  unfold affineSpeed
  have hbase :
      ContDiff ℝ ⊤ (fun z : Fin n → ℝ ↦ 1 + normSq z) :=
    contDiff_const.add contDiff_normSq
  exact
    (hbase.inv fun z ↦
      ne_of_gt (one_add_normSq_pos z)).pow K

theorem continuous_affineSpeed
    (K : ℕ) :
    Continuous (affineSpeed (n := n) K) :=
  (contDiff_affineSpeed K).continuous

/-- The sphere equation written in affine coordinates. -/
theorem weight_sq_mul_one_add_normSq
    (v : FiniteSourceSpace n m) :
    weight v.1 ^ 2 * (1 + normSq (affinePoint v)) = 1 := by
  have hsphere := (centralSpherePoint v.1).2
  change
    normSq (oldPoint v.1) + weight v.1 ^ 2 = 1 at hsphere
  have hx :
      normSq (oldPoint v.1) =
        weight v.1 ^ 2 * normSq (affinePoint v) := by
    unfold normSq dot
    simp_rw [oldPoint_eq_weight_mul_affinePoint]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hx] at hsphere
  nlinarith

/-- Exact identity between denominator-clearing time and the intrinsic
positive speed on the recovered affine space. -/
theorem weight_evenPow_eq_affineSpeed
    (K : ℕ) (v : FiniteSourceSpace n m) :
    weight v.1 ^ (2 * K) =
      affineSpeed K (affinePoint v) := by
  have hdenom :
      1 + normSq (affinePoint v) ≠ 0 :=
    ne_of_gt (one_add_normSq_pos (affinePoint v))
  have hsq :
      weight v.1 ^ 2 =
        (1 + normSq (affinePoint v))⁻¹ := by
    exact
      (mul_eq_one_iff_eq_inv₀ hdenom).mp
        (weight_sq_mul_one_add_normSq v)
  rw [pow_mul, hsq]
  rfl

/-- The intrinsic speed as a nonnegative real. -/
def affineSpeedNNReal
    (K : ℕ) (z : Fin n → ℝ) : ℝ≥0 :=
  ⟨affineSpeed K z, affineSpeed_nonneg K z⟩

@[simp]
theorem affineSpeedNNReal_coe
    (K : ℕ) (z : Fin n → ℝ) :
    (affineSpeedNNReal K z : ℝ) = affineSpeed K z :=
  rfl

theorem continuous_affineSpeedNNReal
    (K : ℕ) :
    Continuous (affineSpeedNNReal (n := n) K) :=
  (continuous_affineSpeed K).subtype_mk _

end AllAffineCompactSourceChart

end CompactAccumulatorPipelineCode

end

end HGAS
