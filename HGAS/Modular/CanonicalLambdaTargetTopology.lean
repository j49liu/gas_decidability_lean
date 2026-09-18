import HGAS.Modular.CanonicalLambdaCovering
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Topology of the modular-lambda target

The honest target of canonical lambda is the twice-punctured plane

```
                         ℂ ∖ {0,1}.
```

This small reusable module supplies the global topological instances that
covering and continuation arguments need.  The main point is path
connectedness.  Mathlib proves that the complement of any countable subset
of a real topological vector space of dimension greater than one is path
connected; applying this to the two-point set `{0,1} ⊂ ℂ` gives the result
immediately.
-/

namespace HGAS.Modular

open Complex Topology

noncomputable section

/-- The twice-punctured plane is path connected. -/
theorem isPathConnected_lambdaPuncturedPlane :
    IsPathConnected {z : ℂ | z ≠ 0 ∧ z ≠ 1} := by
  have hcount :
      ({0, 1} : Set ℂ).Countable :=
    (Set.toFinite ({0, 1} : Set ℂ)).countable
  have hcomplement :=
    hcount.isPathConnected_compl_of_one_lt_rank
      (show 1 < Module.rank ℝ ℂ by
        rw [Complex.rank_real_complex]
        norm_num)
  convert hcomplement using 1
  ext z
  simp

/-- The punctured lambda target is path connected. -/
noncomputable instance :
    PathConnectedSpace LambdaPuncturedPlane := by
  change PathConnectedSpace
    {z : ℂ // z ≠ 0 ∧ z ≠ 1}
  exact
    isPathConnected_iff_pathConnectedSpace.mp
      isPathConnected_lambdaPuncturedPlane

/-- The punctured lambda target is locally path connected because it is an
open subspace of `ℂ`. -/
noncomputable instance :
    LocPathConnectedSpace LambdaPuncturedPlane :=
  isOpen_lambdaPuncturedPlane.locPathConnectedSpace

/-- The punctured lambda target is locally compact because it is an open
subspace of the locally compact plane. -/
noncomputable instance :
    LocallyCompactSpace LambdaPuncturedPlane :=
  isOpen_lambdaPuncturedPlane.locallyCompactSpace

/-- A precise closed-image reduction for global surjectivity.  The local
inverse theorem already makes the image of canonical lambda open.  Since
the target is connected and the image is nonempty, proving that image
closed would force it to be the whole twice-punctured plane. -/
theorem canonicalLambdaPunctured_surjective_of_isClosed_range
    (hclosed :
      IsClosed (Set.range canonicalLambdaPunctured)) :
    Function.Surjective canonicalLambdaPunctured := by
  have hopen :
      IsOpen (Set.range canonicalLambdaPunctured) := by
    rw [← Set.image_univ]
    exact
      canonicalLambdaPunctured_isOpenMap
        Set.univ isOpen_univ
  have hclopen :
      IsClopen
        (Set.range canonicalLambdaPunctured) :=
    ⟨hclosed, hopen⟩
  have hrange :
      Set.range canonicalLambdaPunctured =
        Set.univ :=
    hclopen.eq_univ
      (Set.range_nonempty canonicalLambdaPunctured)
  exact Set.range_eq_univ.mp hrange

end

end HGAS.Modular
