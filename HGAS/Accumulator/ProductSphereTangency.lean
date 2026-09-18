import HGAS.Accumulator.PolynomialCode
import HGAS.Wrapper.UnitSphereWrapperChart
import Mathlib.Tactic

/-!
# Product-sphere assembly for the compact accumulator

Suppose that the base variables are already arranged in a product of
`k` unit-sphere blocks.  The compact accumulator adds the coordinates
`(U₁, ..., Uₘ, W)`, which form one further unit sphere.  This file records
the resulting block assignment

```
 base coordinate j       ↦ old block sourceBlock j,
 accumulator coordinate  ↦ the new final block.
```

The two decomposition theorems below say exactly what this assignment
means:

* membership in the enlarged product of spheres is equivalent to base
  membership together with `‖U‖² + W² = 1`;
* the block dot product in an old block is the original base block dot
  product, while the dot product in the new block is precisely the
  accumulator tangency expression.

Consequently, a base field tangent to its source product of spheres and
the stereographically compactified accumulator field combine to a field
tangent to every enlarged source block.  This is the interface required
by the homogeneous unit-sphere wrapper.
-/

namespace HGAS

open _root_.MvPolynomial
open scoped BigOperators

noncomputable section

namespace AccumulatorPolynomialCode

variable {N m k : ℕ}

/-- Index of an old base sphere in the enlarged list of `k+1` spheres. -/
def baseSphereIndex (b : Fin k) : Fin (k + 1) :=
  finSumFinEquiv (Sum.inl b)

/-- Index of the new accumulator sphere. -/
def accumulatorSphereIndex (k : ℕ) : Fin (k + 1) :=
  finSumFinEquiv (Sum.inr (0 : Fin 1))

@[simp]
theorem baseSphereIndex_inj
    (a b : Fin k) :
    baseSphereIndex a = baseSphereIndex b ↔ a = b := by
  simp [baseSphereIndex]

@[simp]
theorem baseSphereIndex_ne_accumulatorSphereIndex
    (b : Fin k) :
    baseSphereIndex b ≠ accumulatorSphereIndex k := by
  intro h
  have hv := congrArg Fin.val h
  simp [baseSphereIndex, accumulatorSphereIndex] at hv
  omega

@[simp]
theorem accumulatorSphereIndex_ne_baseSphereIndex
    (b : Fin k) :
    accumulatorSphereIndex k ≠ baseSphereIndex b := by
  exact (baseSphereIndex_ne_accumulatorSphereIndex b).symm

/-- Assign every base coordinate to its old sphere block and every
accumulator coordinate to one new final sphere block. -/
def productSphereBlock
    (sourceBlock : Fin N → Fin k) :
    Fin (N + (m + 1)) → Fin (k + 1) :=
  fun q ↦
    match finSumFinEquiv.symm q with
    | Sum.inl j => baseSphereIndex (sourceBlock j)
    | Sum.inr _ => accumulatorSphereIndex k

@[simp]
theorem productSphereBlock_baseIndex
    (sourceBlock : Fin N → Fin k) (j : Fin N) :
    productSphereBlock (m := m) sourceBlock
        (baseIndex (m := m) j) =
      baseSphereIndex (sourceBlock j) := by
  simp [productSphereBlock]

@[simp]
theorem productSphereBlock_uIndex
    (sourceBlock : Fin N → Fin k) (i : Fin m) :
    productSphereBlock sourceBlock (uIndex (n := N) i) =
      accumulatorSphereIndex k := by
  simp [productSphereBlock]

@[simp]
theorem productSphereBlock_wIndex
    (sourceBlock : Fin N → Fin k) :
    productSphereBlock sourceBlock (wIndex N m) =
      accumulatorSphereIndex k := by
  simp [productSphereBlock]

@[simp]
theorem sourceBlockNormSq_productSphereBlock_base
    (sourceBlock : Fin N → Fin k)
    (y : Fin N → ℝ) (u : Fin m → ℝ) (w : ℝ)
    (b : Fin k) :
    UnitSpherePolynomialWrapper.sourceBlockNormSq
        (productSphereBlock sourceBlock)
        (combinedPoint y u w) (baseSphereIndex b) =
      UnitSpherePolynomialWrapper.sourceBlockNormSq
        sourceBlock y b := by
  unfold UnitSpherePolynomialWrapper.sourceBlockNormSq
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp [productSphereBlock, combinedPoint]

@[simp]
theorem sourceBlockNormSq_productSphereBlock_accumulator
    (sourceBlock : Fin N → Fin k)
    (y : Fin N → ℝ) (u : Fin m → ℝ) (w : ℝ) :
    UnitSpherePolynomialWrapper.sourceBlockNormSq
        (productSphereBlock sourceBlock)
        (combinedPoint y u w) (accumulatorSphereIndex k) =
      normSq u + w ^ 2 := by
  unfold UnitSpherePolynomialWrapper.sourceBlockNormSq
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [productSphereBlock, Equiv.symm_apply_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp [combinedPoint, normSq, dot, pow_two,
    baseSphereIndex_ne_accumulatorSphereIndex]

/-- Exact decomposition of the enlarged product-of-spheres predicate. -/
theorem onSourceProductSpheres_productSphereBlock_iff
    (sourceBlock : Fin N → Fin k)
    (y : Fin N → ℝ) (u : Fin m → ℝ) (w : ℝ) :
    UnitSpherePolynomialWrapper.OnSourceProductSpheres
        (productSphereBlock sourceBlock) (combinedPoint y u w) ↔
      UnitSpherePolynomialWrapper.OnSourceProductSpheres sourceBlock y ∧
        normSq u + w ^ 2 = 1 := by
  constructor
  · intro h
    constructor
    · intro b
      rw [← sourceBlockNormSq_productSphereBlock_base
        sourceBlock y u w b]
      exact h (baseSphereIndex b)
    · rw [← sourceBlockNormSq_productSphereBlock_accumulator
        sourceBlock y u w]
      exact h (accumulatorSphereIndex k)
  · rintro ⟨hbase, haccumulator⟩ d
    obtain ⟨b | r, rfl⟩ := finSumFinEquiv.surjective d
    · change
        UnitSpherePolynomialWrapper.sourceBlockNormSq
          (productSphereBlock sourceBlock) (combinedPoint y u w)
          (baseSphereIndex b) = 1
      rw [sourceBlockNormSq_productSphereBlock_base]
      exact hbase b
    · fin_cases r
      change
        UnitSpherePolynomialWrapper.sourceBlockNormSq
          (productSphereBlock sourceBlock) (combinedPoint y u w)
          (accumulatorSphereIndex k) = 1
      rw [sourceBlockNormSq_productSphereBlock_accumulator]
      exact haccumulator

@[simp]
theorem sourceBlockDot_productSphereBlock_base
    (sourceBlock : Fin N → Fin k)
    (P : PolynomialFieldCode N)
    (g : Fin m → PolynomialCode N)
    (y : Fin N → ℝ) (u : Fin m → ℝ) (w : ℝ)
    (b : Fin k) :
    UnitSpherePolynomialWrapper.sourceBlockDot
        (productSphereBlock sourceBlock)
        (combinedPoint y u w)
        (PolynomialFieldCode.realize (fieldCode P g)
          (combinedPoint y u w))
        (baseSphereIndex b) =
      UnitSpherePolynomialWrapper.sourceBlockDot
        sourceBlock y (PolynomialFieldCode.realize P y) b := by
  unfold UnitSpherePolynomialWrapper.sourceBlockDot
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [productSphereBlock, Equiv.symm_apply_apply]
  simp only [baseSphereIndex_inj,
    accumulatorSphereIndex_ne_baseSphereIndex, ↓reduceIte,
    Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : sourceBlock j = b
  · simp only [hj, ↓reduceIte]
    rw [show
      finSumFinEquiv (Sum.inl j : Fin N ⊕ Fin (m + 1)) =
        baseIndex (m := m) j by rfl]
    rw [combinedPoint_baseIndex,
      PolynomialFieldCode.realize_apply,
      eval₂Hom_fieldCode_base]
    rfl
  · simp [hj]

@[simp]
theorem sourceBlockDot_productSphereBlock_accumulator
    (sourceBlock : Fin N → Fin k)
    (P : PolynomialFieldCode N)
    (g : Fin m → PolynomialCode N)
    (y : Fin N → ℝ) (u : Fin m → ℝ) (w : ℝ) :
    UnitSpherePolynomialWrapper.sourceBlockDot
        (productSphereBlock sourceBlock)
        (combinedPoint y u w)
        (PolynomialFieldCode.realize (fieldCode P g)
          (combinedPoint y u w))
        (accumulatorSphereIndex k) =
      (∑ i, u i *
        eval₂Hom (algebraMap ℚ ℝ) (combinedPoint y u w)
          (PolynomialCode.decode
            (fieldCode P g (uIndex (n := N) i)))) +
        w *
          eval₂Hom (algebraMap ℚ ℝ) (combinedPoint y u w)
            (PolynomialCode.decode
              (fieldCode P g (wIndex N m))) := by
  unfold UnitSpherePolynomialWrapper.sourceBlockDot
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [productSphereBlock, Equiv.symm_apply_apply]
  simp only [baseSphereIndex_ne_accumulatorSphereIndex,
    ↓reduceIte, Finset.sum_const_zero, zero_add]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp [combinedPoint, PolynomialFieldCode.realize_apply, uIndex,
    wIndex, uAuxIndex, wAuxIndex, DegreePaddingCode.sinkIndex]

/-- The base field and compact accumulator field together are tangent to
all `k+1` source spheres.  The only geometric input beyond base tangency
is the accumulator sphere equation. -/
theorem fieldCode_sourceTangentAt
    (sourceBlock : Fin N → Fin k)
    (P : PolynomialFieldCode N)
    (g : Fin m → PolynomialCode N)
    (y : Fin N → ℝ) (u : Fin m → ℝ) (w : ℝ)
    (hbase :
      UnitSpherePolynomialWrapper.SourceTangentAt sourceBlock y
        (PolynomialFieldCode.realize P y))
    (haccumulator : normSq u + w ^ 2 = 1) :
    UnitSpherePolynomialWrapper.SourceTangentAt
        (productSphereBlock sourceBlock)
        (combinedPoint y u w)
        (PolynomialFieldCode.realize (fieldCode P g)
          (combinedPoint y u w)) := by
  intro d
  obtain ⟨b | r, rfl⟩ := finSumFinEquiv.surjective d
  · change
      UnitSpherePolynomialWrapper.sourceBlockDot
        (productSphereBlock sourceBlock)
        (combinedPoint y u w)
        (PolynomialFieldCode.realize (fieldCode P g)
          (combinedPoint y u w))
        (baseSphereIndex b) = 0
    rw [sourceBlockDot_productSphereBlock_base]
    exact hbase b
  · fin_cases r
    change
      UnitSpherePolynomialWrapper.sourceBlockDot
        (productSphereBlock sourceBlock)
        (combinedPoint y u w)
        (PolynomialFieldCode.realize (fieldCode P g)
          (combinedPoint y u w))
        (accumulatorSphereIndex k) = 0
    rw [sourceBlockDot_productSphereBlock_accumulator]
    exact fieldCode_accumulator_tangent P g y u w haccumulator

end AccumulatorPolynomialCode

end

end HGAS
