import HGAS.Algebra.PolynomialBlockDegrees
import HGAS.Compactification.MixedCentralPolynomialCode
import HGAS.Compactification.MixedCentralPolynomialCompactSupport
import Mathlib.Tactic

/-!
# One right affine block with compact coordinates on the left

Many source compilers use the canonical split `Fin (m + p)`:

* the left `m` coordinates already belong to specified compact sphere
  blocks; and
* the right `p` coordinates form one affine block which must be
  projectively compactified.

This module provides that mixed-central layout and connects its
affine-block degree to the right degree from
`PolynomialBlockDegrees`.  Consequently a previously proved bidegree
bound immediately supplies the denominator-clearing premise for the mixed
compactification.
-/

namespace HGAS

open scoped BigOperators

namespace RightAffineLeftCompactLayout

variable {m p l : ℕ}

/-- Put every right coordinate in the unique affine block and distribute
the left coordinates among the prescribed compact blocks. -/
def layout
    (leftBlock : Fin m → Fin l) :
    Fin (m + p) → Fin 1 ⊕ Fin l :=
  fun q ↦
    match finSumFinEquiv.symm q with
    | Sum.inl i => Sum.inr (leftBlock i)
    | Sum.inr _ => Sum.inl 0

@[simp]
theorem layout_leftEmbedding
    (leftBlock : Fin m → Fin l) (i : Fin m) :
    layout (p := p) leftBlock
        (PolynomialBlockCode.leftEmbedding (p := p) i) =
      Sum.inr (leftBlock i) := by
  simp [layout]

@[simp]
theorem layout_rightEmbedding
    (leftBlock : Fin m → Fin l) (j : Fin p) :
    layout (m := m) leftBlock
        (PolynomialBlockCode.rightEmbedding (m := m) j) =
      Sum.inl 0 := by
  simp [layout]

/-- For the unique affine block, mixed affine degree is exactly ordinary
degree in the canonical right variables. -/
theorem affineBlockDegree_eq_rightDegree
    (leftBlock : Fin m → Fin l)
    (e : ExponentCode (m + p)) (b : Fin 1) :
    MixedCentralPolynomialCode.affineBlockDegree
        (layout leftBlock) e b =
      PolynomialBlockCode.rightDegree e := by
  fin_cases b
  unfold MixedCentralPolynomialCode.affineBlockDegree
  unfold PolynomialBlockCode.rightDegree
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp [layout, PolynomialBlockCode.rightEmbedding]

/-- A right-degree bound supplies the sole affine-block degree premise. -/
theorem termsAffineBlockDegreeLE_of_termsBidegreeLE
    (leftBlock : Fin m → Fin l)
    {DL DR : ℕ} {q : PolynomialCode (m + p)}
    (hq : PolynomialBlockCode.TermsBidegreeLE DL DR q) :
    MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
      (layout leftBlock) DR q := by
  intro t ht b
  rw [affineBlockDegree_eq_rightDegree leftBlock t.1 b]
  exact (hq t ht).2

/-- The same implication after promoting the advertised clearing
exponent. -/
theorem termsAffineBlockDegreeLE_of_termsBidegreeLE_of_le
    (leftBlock : Fin m → Fin l)
    {DL DR M : ℕ} {q : PolynomialCode (m + p)}
    (hq : PolynomialBlockCode.TermsBidegreeLE DL DR q)
    (hDM : DR ≤ M) :
    MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
      (layout leftBlock) M q := by
  intro t ht b
  rw [affineBlockDegree_eq_rightDegree leftBlock t.1 b]
  exact (hq t ht).2.trans hDM

/-- Right degree zero means that a polynomial uses only the already
compact left variables.  This is the precise hypothesis needed by the
global compact-block tangency transfer at an affine equator. -/
theorem termsAffineDegreeZero_of_termsBidegreeLE
    (leftBlock : Fin m → Fin l)
    {DL : ℕ} {q : PolynomialCode (m + p)}
    (hq : PolynomialBlockCode.TermsBidegreeLE DL 0 q) :
    MixedCentralPolynomialCode.TermsAffineDegreeZero
      (layout leftBlock) q := by
  intro t ht b
  rw [affineBlockDegree_eq_rightDegree leftBlock t.1 b]
  exact Nat.eq_zero_of_le_zero (hq t ht).2

/-- The compact-block dot product for the canonical layout is exactly the
dot product over the left coordinates assigned to that block; the right
affine coordinates contribute no terms. -/
theorem compactBlockDot_layout
    {R : Type*} [CommRing R]
    (leftBlock : Fin m → Fin l)
    (x v : Fin (m + p) → R) (c : Fin l) :
    MixedCentralPolynomialCode.compactBlockDot
        (layout leftBlock) x v c =
      ∑ i : Fin m,
        if leftBlock i = c then
          x (PolynomialBlockCode.leftEmbedding (p := p) i) *
            v (PolynomialBlockCode.leftEmbedding (p := p) i)
        else 0 := by
  unfold MixedCentralPolynomialCode.compactBlockDot
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp [layout, PolynomialBlockCode.leftEmbedding]

end RightAffineLeftCompactLayout

end HGAS
