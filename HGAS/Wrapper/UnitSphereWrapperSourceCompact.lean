import HGAS.Wrapper.UnitSphereWrapperChartHomeomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-!
# Compactness of the source product sphere and the two wrapper sheets

The source phase space used by the product-sphere wrapper is a finite
intersection of quadratic level sets.  Each source coordinate belongs to
one of the blocks, so the equation for that block bounds the coordinate
by one.  Hence the source phase space is closed and bounded, and therefore
compact.

The two normalized wrapper sheets are homeomorphic to this source phase
space.  We transport compactness, and (when the source space is inhabited)
nonemptiness, through those homeomorphisms.  These instances are separated
from the algebraic chart construction so that the latter remains usable
without any compact-flow machinery.
-/

namespace HGAS

open Function Metric Set
open scoped BigOperators BoundedContinuousFunction

noncomputable section

namespace UnitSpherePolynomialWrapper

variable {n k : ℕ}

/-- Squared norm of one source block is a continuous polynomial. -/
theorem continuous_sourceBlockNormSq
    (sourceBlock : Fin n → Fin k) (i : Fin k) :
    Continuous
      (fun y : Fin n → ℝ ↦
        sourceBlockNormSq sourceBlock y i) := by
  unfold sourceBlockNormSq
  apply continuous_finsetSum
  intro j _
  by_cases hj : sourceBlock j = i
  · simp only [hj, ↓reduceIte]
    fun_prop
  · simp only [hj, ↓reduceIte]
    exact continuous_const

/-- The source product of spheres is closed in its raw coordinate space. -/
theorem isClosed_onSourceProductSpheres
    (sourceBlock : Fin n → Fin k) :
    IsClosed
      {y : Fin n → ℝ |
        OnSourceProductSpheres sourceBlock y} := by
  rw [show
      {y : Fin n → ℝ |
        OnSourceProductSpheres sourceBlock y} =
        ⋂ i : Fin k,
          {y : Fin n → ℝ |
            sourceBlockNormSq sourceBlock y i = 1} by
    ext y
    simp [OnSourceProductSpheres]]
  exact isClosed_iInter fun i ↦
    isClosed_eq
      (continuous_sourceBlockNormSq sourceBlock i)
      continuous_const

/-- A coordinate square is one of the nonnegative summands in its block
norm. -/
theorem source_coordinate_sq_le_blockNormSq
    (sourceBlock : Fin n → Fin k)
    (y : Fin n → ℝ) (j : Fin n) :
    y j ^ 2 ≤
      sourceBlockNormSq sourceBlock y (sourceBlock j) := by
  unfold sourceBlockNormSq
  have hsingle :
      (if sourceBlock j = sourceBlock j then y j ^ 2 else 0) ≤
        ∑ q : Fin n,
          if sourceBlock q = sourceBlock j then y q ^ 2 else 0 :=
    Finset.single_le_sum
      (s := Finset.univ)
      (f := fun q : Fin n ↦
        if sourceBlock q = sourceBlock j then y q ^ 2 else 0)
      (fun q _ ↦ by
        by_cases hq : sourceBlock q = sourceBlock j
        · simp [hq, sq_nonneg]
        · simp [hq])
      (Finset.mem_univ j)
  simpa using hsingle

/-- Every point of the source product sphere has sup norm at most one. -/
theorem source_norm_le_one_of_onSourceProductSpheres
    (sourceBlock : Fin n → Fin k)
    (y : Fin n → ℝ)
    (hy : OnSourceProductSpheres sourceBlock y) :
    ‖y‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro j
  rw [Real.norm_eq_abs]
  have hsq :
      y j ^ 2 ≤ 1 := by
    calc
      y j ^ 2 ≤
          sourceBlockNormSq sourceBlock y (sourceBlock j) :=
        source_coordinate_sq_le_blockNormSq sourceBlock y j
      _ = 1 := hy (sourceBlock j)
  exact (sq_le_one_iff_abs_le_one (y j)).mp hsq

/-- The source product sphere is bounded. -/
theorem isBounded_onSourceProductSpheres
    (sourceBlock : Fin n → Fin k) :
    Bornology.IsBounded
      {y : Fin n → ℝ |
        OnSourceProductSpheres sourceBlock y} := by
  rw [isBounded_iff_forall_norm_le]
  exact
    ⟨1, fun y hy ↦
      source_norm_le_one_of_onSourceProductSpheres
        sourceBlock y hy⟩

/-- The source product sphere is compact, even when it is empty. -/
theorem isCompact_onSourceProductSpheres
    (sourceBlock : Fin n → Fin k) :
    IsCompact
      {y : Fin n → ℝ |
        OnSourceProductSpheres sourceBlock y} := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact
    ⟨isClosed_onSourceProductSpheres sourceBlock,
      isBounded_onSourceProductSpheres sourceBlock⟩

/-- The source product sphere is inhabited exactly when every advertised
block contains a source coordinate. -/
theorem nonempty_sourceProductSphere_iff_surjective
    (sourceBlock : Fin n → Fin k) :
    Nonempty (SourceProductSphere sourceBlock) ↔
      Function.Surjective sourceBlock := by
  constructor
  · rintro ⟨y⟩ i
    by_contra hnone
    have hall : ∀ j : Fin n, sourceBlock j ≠ i := by
      intro j hj
      exact hnone ⟨j, hj⟩
    have hi := y.property i
    unfold sourceBlockNormSq at hi
    simp [hall] at hi
  · intro hsurj
    classical
    let rep : Fin k → Fin n :=
      fun i ↦ Classical.choose (hsurj i)
    have hrep : ∀ i, sourceBlock (rep i) = i :=
      fun i ↦ Classical.choose_spec (hsurj i)
    let y : Fin n → ℝ :=
      fun j ↦ if j = rep (sourceBlock j) then 1 else 0
    refine ⟨⟨y, ?_⟩⟩
    intro i
    unfold sourceBlockNormSq
    rw [Finset.sum_eq_single (rep i)]
    · simp [y, hrep]
    · intro j _ hj
      by_cases hji : sourceBlock j = i
      · simp [hji, y, hj]
      · simp [hji]
    · intro hnotmem
      exact (hnotmem (Finset.mem_univ (rep i))).elim

noncomputable instance sourceProductSphereMeasurableSpace
    (sourceBlock : Fin n → Fin k) :
    MeasurableSpace (SourceProductSphere sourceBlock) :=
  borel (SourceProductSphere sourceBlock)

instance sourceProductSphereBorelSpace
    (sourceBlock : Fin n → Fin k) :
    BorelSpace (SourceProductSphere sourceBlock) :=
  ⟨rfl⟩

noncomputable instance sourceProductSphereCompactSpace
    (sourceBlock : Fin n → Fin k) :
    CompactSpace (SourceProductSphere sourceBlock) :=
  isCompact_iff_compactSpace.mp
    (isCompact_onSourceProductSpheres sourceBlock)

/-- Compactness of the positive wrapper sheet, transported through its
explicit chart homeomorphism. -/
noncomputable instance positiveFullSheetCompactSpace
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    CompactSpace (positiveFullSheet sourceBlock D P a) :=
  (positiveSheetHomeomorph sourceBlock D P a).compactSpace

/-- Compactness of the negative wrapper sheet. -/
noncomputable instance negativeFullSheetCompactSpace
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    CompactSpace (negativeFullSheet sourceBlock D P a) :=
  (negativeSheetHomeomorph sourceBlock D P a).compactSpace

/-- An inhabited source product sphere gives an inhabited positive sheet. -/
noncomputable instance positiveFullSheetNonempty
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    [Nonempty (SourceProductSphere sourceBlock)] :
    Nonempty (positiveFullSheet sourceBlock D P a) :=
  ⟨positiveSheetHomeomorph sourceBlock D P a
    (Classical.choice inferInstance)⟩

/-- An inhabited source product sphere gives an inhabited negative sheet. -/
noncomputable instance negativeFullSheetNonempty
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    [Nonempty (SourceProductSphere sourceBlock)] :
    Nonempty (negativeFullSheet sourceBlock D P a) :=
  ⟨negativeSheetHomeomorph sourceBlock D P a
    (Classical.choice inferInstance)⟩

end UnitSpherePolynomialWrapper

end

end HGAS
