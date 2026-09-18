import HGAS.Compactification.MixedCentralPolynomialCode
import Mathlib.Tactic

/-!
# The mixed polynomial central field

This module turns the mixed denominator-clearing operation into the
paper's vector field.  Coordinates assigned to an affine block are
centrally compactified:

```
x_j' = f w_b (P_j - D_b x_j),       layout j = Sum.inl b,
w_b' = -f w_b² D_b,
D_b  = ∑_{layout i = Sum.inl b} x_i P_i.
```

Coordinates in an already compact block are not projectivized:

```
x_j' = f P_j,                       layout j = Sum.inr c.
```

Here `f=∏_b w_b^M` is produced automatically by sparse denominator
clearing.  The final theorems prove exact scaled-chart semantics and
tangency to every target sphere block.  Thus existing compact blocks are
preserved, while each affine block becomes a new sphere after adjoining
its `w_b` coordinate.
-/

namespace HGAS

open _root_.MvPolynomial
open scoped BigOperators

noncomputable section

namespace MixedCentralPolynomialCode

variable {n k l : ℕ}

/-- Dot product over the old coordinates belonging to affine block `b`. -/
def affineBlockDot
    {R : Type*} [CommRing R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (x p : Fin n → R) (b : Fin k) : R :=
  ∑ j, if layout j = Sum.inl b then x j * p j else 0

/-- Squared norm over the old coordinates belonging to affine block `b`. -/
def affineBlockNormSq
    {R : Type*} [CommRing R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (x : Fin n → R) (b : Fin k) : R :=
  ∑ j, if layout j = Sum.inl b then x j ^ 2 else 0

/-- Dot product over an already compact source block. -/
def compactBlockDot
    {R : Type*} [CommRing R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (x p : Fin n → R) (c : Fin l) : R :=
  ∑ j, if layout j = Sum.inr c then x j * p j else 0

/-- Squared norm over an already compact source block. -/
def compactBlockNormSq
    {R : Type*} [CommRing R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (x : Fin n → R) (c : Fin l) : R :=
  ∑ j, if layout j = Sum.inr c then x j ^ 2 else 0

/-- Old-coordinate part of the mixed semantic field. -/
def mixedXField
    {R : Type*} [CommRing R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (f : R) (w : Fin k → R)
    (x p : Fin n → R) (j : Fin n) : R :=
  match layout j with
  | Sum.inl b =>
      f * w b * (p j - affineBlockDot layout x p b * x j)
  | Sum.inr _ => f * p j

/-- New chart-coordinate part of the mixed semantic field. -/
def mixedWField
    {R : Type*} [CommRing R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (f : R) (w : Fin k → R)
    (x p : Fin n → R) (b : Fin k) : R :=
  -f * w b ^ 2 * affineBlockDot layout x p b

/-- Complete ambient semantic field: old coordinates, then the new
affine chart coordinates. -/
def mixedAmbientField
    {R : Type*} [CommRing R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (f : R) (w : Fin k → R)
    (x p : Fin n → R) :
    Fin (n + k) → R :=
  fun q ↦
    match finSumFinEquiv.symm q with
    | Sum.inl j => mixedXField layout f w x p j
    | Sum.inr b => mixedWField layout f w x p b

/-- Canonical assignment of ambient coordinates to the `k+l` target
sphere blocks.  A new `w_b` lies in the same target block as the affine
coordinates it compactifies. -/
def targetBlock
    (layout : Fin n → Fin k ⊕ Fin l) :
    Fin (n + k) → Fin (k + l) :=
  fun q ↦
    match finSumFinEquiv.symm q with
    | Sum.inl j => finSumFinEquiv (layout j)
    | Sum.inr b => finSumFinEquiv (Sum.inl b)

@[simp]
theorem targetBlock_xIndex
    (layout : Fin n → Fin k ⊕ Fin l) (j : Fin n) :
    targetBlock layout (xIndex (k := k) j) =
      finSumFinEquiv (layout j) := by
  simp [targetBlock]

@[simp]
theorem targetBlock_wIndex
    (layout : Fin n → Fin k ⊕ Fin l) (b : Fin k) :
    targetBlock layout (wIndex (n := n) b) =
      finSumFinEquiv (Sum.inl b : Fin k ⊕ Fin l) := by
  simp [targetBlock]

/-- Dot product of an ambient position and velocity in one target block. -/
def targetBlockDot
    {R : Type*} [CommRing R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (y v : Fin (n + k) → R) (d : Fin (k + l)) : R :=
  ∑ q, if targetBlock layout q = d then y q * v q else 0

/-- Squared norm in one target block.  Defining it as the self-dot makes
the relation to tangency completely explicit. -/
def targetBlockNormSq
    {R : Type*} [CommRing R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (y : Fin (n + k) → R) (d : Fin (k + l)) : R :=
  targetBlockDot layout y y d

/-- Target-block dot product for a new affine sphere. -/
theorem targetBlockDot_affine
    {R : Type*} [CommRing R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (x : Fin n → R) (w : Fin k → R)
    (v : Fin (n + k) → R) (b : Fin k) :
    targetBlockDot layout (chartPoint x w) v
        (finSumFinEquiv (Sum.inl b : Fin k ⊕ Fin l)) =
      affineBlockDot layout x
          (fun j ↦ v (xIndex (k := k) j)) b +
        w b * v (wIndex (n := n) b) := by
  unfold targetBlockDot affineBlockDot
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [targetBlock, Equiv.symm_apply_apply]
  simp_rw [Equiv.apply_eq_iff_eq]
  simp [chartPoint, xIndex, wIndex,
    MultiCentralPolynomialCode.chartPoint,
    MultiCentralPolynomialCode.xIndex,
    MultiCentralPolynomialCode.wIndex]

/-- Target-block dot product for an already compact source sphere. -/
theorem targetBlockDot_compact
    {R : Type*} [CommRing R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (x : Fin n → R) (w : Fin k → R)
    (v : Fin (n + k) → R) (c : Fin l) :
    targetBlockDot layout (chartPoint x w) v
        (finSumFinEquiv (Sum.inr c : Fin k ⊕ Fin l)) =
      compactBlockDot layout x
        (fun j ↦ v (xIndex (k := k) j)) c := by
  unfold targetBlockDot compactBlockDot
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [targetBlock, Equiv.symm_apply_apply]
  simp_rw [Equiv.apply_eq_iff_eq]
  simp [chartPoint, xIndex,
    MultiCentralPolynomialCode.chartPoint,
    MultiCentralPolynomialCode.xIndex]

/-- The norm of a new affine target block is the old affine norm plus
the square of its new chart coordinate. -/
theorem targetBlockNormSq_affine
    {R : Type*} [CommRing R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (x : Fin n → R) (w : Fin k → R) (b : Fin k) :
    targetBlockNormSq layout (chartPoint x w)
        (finSumFinEquiv (Sum.inl b : Fin k ⊕ Fin l)) =
      affineBlockNormSq layout x b + w b ^ 2 := by
  rw [targetBlockNormSq, targetBlockDot_affine]
  unfold affineBlockNormSq affineBlockDot
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    by_cases hj : layout j = Sum.inl b
    · simp [hj, pow_two]
    · simp [hj]
  · simp [pow_two]

/-- An already compact block has exactly its original squared norm. -/
theorem targetBlockNormSq_compact
    {R : Type*} [CommRing R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (x : Fin n → R) (w : Fin k → R) (c : Fin l) :
    targetBlockNormSq layout (chartPoint x w)
        (finSumFinEquiv (Sum.inr c : Fin k ⊕ Fin l)) =
      compactBlockNormSq layout x c := by
  rw [targetBlockNormSq, targetBlockDot_compact]
  unfold compactBlockNormSq compactBlockDot
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : layout j = Sum.inr c
  · simp [hj, pow_two]
  · simp [hj]

/-- Central compactification is tangent to every newly created affine
sphere. -/
theorem affineCentralField_tangent
    {R : Type*} [CommRing R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (f : R) (w : Fin k → R)
    (x p : Fin n → R)
    (hsphere :
      ∀ b, affineBlockNormSq layout x b + w b ^ 2 = 1) :
    ∀ b,
      affineBlockDot layout x (mixedXField layout f w x p) b +
        w b * mixedWField layout f w x p b = 0 := by
  intro b
  let d := affineBlockDot layout x p b
  let s := affineBlockNormSq layout x b
  have hxdot :
      affineBlockDot layout x (mixedXField layout f w x p) b =
        f * w b * d - f * w b * d * s := by
    unfold affineBlockDot
    calc
      (∑ j,
          if layout j = Sum.inl b then
            x j * mixedXField layout f w x p j
          else 0) =
          ∑ j, (
            (if layout j = Sum.inl b then
              f * w b * (x j * p j) else 0) -
            (if layout j = Sum.inl b then
              f * w b * d * x j ^ 2 else 0)) := by
                apply Finset.sum_congr rfl
                intro j _
                by_cases hj : layout j = Sum.inl b
                · simp only [hj, ↓reduceIte, mixedXField, d]
                  ring
                · simp [hj]
      _ =
          (∑ j, if layout j = Sum.inl b then
              f * w b * (x j * p j) else 0) -
            ∑ j, if layout j = Sum.inl b then
              f * w b * d * x j ^ 2 else 0 := by
                rw [Finset.sum_sub_distrib]
      _ =
          f * w b *
              (∑ j, if layout j = Sum.inl b then
                x j * p j else 0) -
            f * w b * d *
              ∑ j, if layout j = Sum.inl b then
                x j ^ 2 else 0 := by
                  rw [Finset.mul_sum, Finset.mul_sum]
                  congr 1
                  · apply Finset.sum_congr rfl
                    intro j _
                    by_cases hj : layout j = Sum.inl b <;> simp [hj]
                  · apply Finset.sum_congr rfl
                    intro j _
                    by_cases hj : layout j = Sum.inl b <;> simp [hj]
      _ = f * w b * d - f * w b * d * s := by
            change
              f * w b * affineBlockDot layout x p b -
                  f * w b * d * affineBlockNormSq layout x b = _
            rfl
  rw [hxdot]
  simp only [mixedWField]
  change
    (f * w b * d - f * w b * d * s) +
        w b * (-f * w b ^ 2 * d) = 0
  calc
    (f * w b * d - f * w b * d * s) +
        w b * (-f * w b ^ 2 * d) =
      f * w b * d * (1 - (s + w b ^ 2)) := by ring
    _ = 0 := by
      have hs : s + w b ^ 2 = 1 := hsphere b
      rw [hs]
      ring

/-- Already compact blocks receive only the common scalar slowdown, so
their tangency relation is preserved verbatim. -/
theorem compactBlockDot_mixedXField
    {R : Type*} [CommRing R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (f : R) (w : Fin k → R)
    (x p : Fin n → R) (c : Fin l) :
    compactBlockDot layout x (mixedXField layout f w x p) c =
      f * compactBlockDot layout x p c := by
  unfold compactBlockDot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : layout j = Sum.inr c
  · simp [hj, mixedXField]
    ring
  · simp [hj]

/-- Compact source coordinates really are unchanged in the mixed chart. -/
theorem compactBlockDot_scaledSourcePoint
    {R : Type*} [CommRing R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (w : Fin k → R) (z p : Fin n → R) (c : Fin l) :
    compactBlockDot layout (scaledSourcePoint layout w z) p c =
      compactBlockDot layout z p c := by
  unfold compactBlockDot
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : layout j = Sum.inr c
  · simp [hj, scaledSourcePoint]
  · simp [hj]

/-- Mixed charts preserve the squared norm of every already compact
source block. -/
theorem compactBlockNormSq_scaledSourcePoint
    {R : Type*} [CommRing R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (w : Fin k → R) (z : Fin n → R) (c : Fin l) :
    compactBlockNormSq layout (scaledSourcePoint layout w z) c =
      compactBlockNormSq layout z c := by
  unfold compactBlockNormSq
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : layout j = Sum.inr c
  · simp [hj, scaledSourcePoint]
  · simp [hj]

/-- The mixed chart lands in the target product of unit spheres whenever
the new affine spheres and the old compact spheres have unit norm. -/
theorem scaledChartPoint_on_target_spheres
    {R : Type*} [CommRing R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (w : Fin k → R) (z : Fin n → R)
    (haffine :
      ∀ b, affineBlockNormSq layout
          (scaledSourcePoint layout w z) b + w b ^ 2 = 1)
    (hcompact :
      ∀ c, compactBlockNormSq layout z c = 1) :
    ∀ d, targetBlockNormSq layout (scaledChartPoint layout w z) d = 1 := by
  intro d
  change
    targetBlockNormSq layout
      (chartPoint (scaledSourcePoint layout w z) w) d = 1
  cases hd : finSumFinEquiv.symm d with
  | inl b =>
      have hd' :
          d = finSumFinEquiv (Sum.inl b : Fin k ⊕ Fin l) := by
        rw [← hd]
        simp
      rw [hd']
      exact targetBlockNormSq_affine layout
        (scaledSourcePoint layout w z) w b |>.trans (haffine b)
  | inr c =>
      have hd' :
          d = finSumFinEquiv (Sum.inr c : Fin k ⊕ Fin l) := by
        rw [← hd]
        simp
      rw [hd', targetBlockNormSq_compact,
        compactBlockNormSq_scaledSourcePoint]
      exact hcompact c

/-- Semantic mixed field is tangent to all `k+l` target blocks. -/
theorem mixedAmbientField_target_tangent
    {R : Type*} [CommRing R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (f : R) (w : Fin k → R)
    (x p : Fin n → R)
    (haffine :
      ∀ b, affineBlockNormSq layout x b + w b ^ 2 = 1)
    (hcompact :
      ∀ c, compactBlockDot layout x p c = 0) :
    ∀ d,
      targetBlockDot layout (chartPoint x w)
        (mixedAmbientField layout f w x p) d = 0 := by
  intro d
  cases hd : finSumFinEquiv.symm d with
  | inl b =>
      have hd' :
          d = finSumFinEquiv (Sum.inl b : Fin k ⊕ Fin l) := by
        rw [← hd]
        simp
      rw [hd', targetBlockDot_affine]
      simpa [mixedAmbientField, xIndex, wIndex,
        MultiCentralPolynomialCode.xIndex,
        MultiCentralPolynomialCode.wIndex] using
        (affineCentralField_tangent layout f w x p haffine b)
  | inr c =>
      have hd' :
          d = finSumFinEquiv (Sum.inr c : Fin k ⊕ Fin l) := by
        rw [← hd]
        simp
      rw [hd', targetBlockDot_compact]
      simp [mixedAmbientField, xIndex,
        MultiCentralPolynomialCode.xIndex,
        compactBlockDot_mixedXField, hcompact c]

/-! ## Sparse field compiler -/

/-- Sparse code for the affine block dot product `D_b`. -/
def affineBlockDotCode
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (P : PolynomialFieldCode n)
    (b : Fin k) :
    PolynomialCode (n + k) :=
  PolynomialCode.sumCodes
    (List.ofFn fun j : Fin n ↦
      if layout j = Sum.inl b then
        PolynomialCode.mul
          (PolynomialCode.varCode (xIndex (k := k) j))
          (homogenize layout M (P j))
      else
        PolynomialCode.zero)

/-- Emitted equation for one old coordinate.  Compact coordinates use
the cleared source equation directly; affine coordinates use the central
tangent formula. -/
def xFieldCode
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (P : PolynomialFieldCode n)
    (j : Fin n) :
    PolynomialCode (n + k) :=
  match layout j with
  | Sum.inl b =>
      PolynomialCode.mul
        (PolynomialCode.varCode (wIndex (n := n) b))
        (PolynomialCode.sub
          (homogenize layout M (P j))
          (PolynomialCode.mul
            (PolynomialCode.varCode (xIndex (k := k) j))
            (affineBlockDotCode layout M P b)))
  | Sum.inr _ => homogenize layout M (P j)

/-- Emitted equation for one new chart coordinate. -/
def wFieldCode
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (P : PolynomialFieldCode n)
    (b : Fin k) :
    PolynomialCode (n + k) :=
  PolynomialCode.neg
    (PolynomialCode.mul
      (PolynomialCode.pow
        (PolynomialCode.varCode (wIndex (n := n) b)) 2)
      (affineBlockDotCode layout M P b))

/-- Complete paper-exact mixed central compiler. -/
def fieldCode
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (P : PolynomialFieldCode n) :
    PolynomialFieldCode (n + k) :=
  fun q ↦
    match finSumFinEquiv.symm q with
    | Sum.inl j => xFieldCode layout M P j
    | Sum.inr b => wFieldCode layout M P b

private theorem eval_sumCodes_ofFn
    {R : Type*} [CommRing R] [Algebra ℚ R]
    {m N : ℕ} (p : Fin m → PolynomialCode N)
    (y : Fin N → R) :
    eval₂Hom (algebraMap ℚ R) y
        (PolynomialCode.decode
          (PolynomialCode.sumCodes (List.ofFn p))) =
      ∑ i, eval₂Hom (algebraMap ℚ R) y
        (PolynomialCode.decode (p i)) := by
  rw [PolynomialCode.decode_sumCodes, List.map_ofFn,
    List.sum_ofFn, map_sum]
  rfl

/-- Evaluation of the coded affine block dot product. -/
theorem eval₂Hom_affineBlockDotCode
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (P : PolynomialFieldCode n)
    (b : Fin k) (y : Fin (n + k) → R) :
    eval₂Hom (algebraMap ℚ R) y
        (PolynomialCode.decode (affineBlockDotCode layout M P b)) =
      ∑ j, if layout j = Sum.inl b then
        y (xIndex (k := k) j) *
          eval₂Hom (algebraMap ℚ R) y
            (PolynomialCode.decode (homogenize layout M (P j)))
        else 0 := by
  rw [affineBlockDotCode, eval_sumCodes_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : layout j = Sum.inl b <;> simp [hj]

/-- Scaled-chart semantics of the coded affine block dot product. -/
theorem eval₂Hom_affineBlockDotCode_scaledChart
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ j, TermsAffineBlockDegreeLE layout M (P j))
    (b : Fin k) (w : Fin k → R) (z : Fin n → R) :
    eval₂Hom (algebraMap ℚ R)
        (scaledChartPoint layout w z)
        (PolynomialCode.decode (affineBlockDotCode layout M P b)) =
      slowdown M w *
        affineBlockDot layout (scaledSourcePoint layout w z)
          (fun j ↦ eval₂Hom (algebraMap ℚ R) z
            (PolynomialCode.decode (P j))) b := by
  rw [eval₂Hom_affineBlockDotCode]
  unfold affineBlockDot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : layout j = Sum.inl b
  · simp only [hj, ↓reduceIte, scaledChartPoint_xIndex,
      scaledSourcePoint]
    rw [eval₂Hom_homogenize_scaledChart
      layout M (P j) (hP j) w z]
    ring
  · simp [hj]

/-- Exact scaled-chart semantics of every old-coordinate equation. -/
theorem eval₂Hom_xFieldCode_scaledChart
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ j, TermsAffineBlockDegreeLE layout M (P j))
    (j : Fin n) (w : Fin k → R) (z : Fin n → R) :
    eval₂Hom (algebraMap ℚ R)
        (scaledChartPoint layout w z)
        (PolynomialCode.decode (xFieldCode layout M P j)) =
      mixedXField layout (slowdown M w) w
        (scaledSourcePoint layout w z)
        (fun i ↦ eval₂Hom (algebraMap ℚ R) z
          (PolynomialCode.decode (P i))) j := by
  cases hj : layout j with
  | inl b =>
      simp only [xFieldCode, hj,
        PolynomialCode.decode_mul_code,
        PolynomialCode.decode_sub_code,
        PolynomialCode.decode_varCode, map_mul, map_sub,
        eval₂Hom_X', scaledChartPoint_xIndex]
      rw [eval₂Hom_homogenize_scaledChart
        layout M (P j) (hP j) w z]
      rw [eval₂Hom_affineBlockDotCode_scaledChart
        layout M P hP b w z]
      simp only [mixedXField, hj, scaledSourcePoint]
      rw [scaledChartPoint_wIndex]
      ring
  | inr c =>
      simp only [xFieldCode, hj, mixedXField]
      rw [eval₂Hom_homogenize_scaledChart
        layout M (P j) (hP j) w z]

/-- Exact scaled-chart semantics of every new chart equation. -/
theorem eval₂Hom_wFieldCode_scaledChart
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ j, TermsAffineBlockDegreeLE layout M (P j))
    (b : Fin k) (w : Fin k → R) (z : Fin n → R) :
    eval₂Hom (algebraMap ℚ R)
        (scaledChartPoint layout w z)
        (PolynomialCode.decode (wFieldCode layout M P b)) =
      mixedWField layout (slowdown M w) w
        (scaledSourcePoint layout w z)
        (fun i ↦ eval₂Hom (algebraMap ℚ R) z
          (PolynomialCode.decode (P i))) b := by
  simp only [wFieldCode, PolynomialCode.decode_neg_code,
    PolynomialCode.decode_mul_code,
    PolynomialCode.decode_pow_code,
    PolynomialCode.decode_varCode, map_neg, map_mul,
    map_pow, eval₂Hom_X', scaledChartPoint_wIndex]
  rw [eval₂Hom_affineBlockDotCode_scaledChart
    layout M P hP b w z]
  simp only [mixedWField]
  ring

/-- Exact scaled-chart semantics of the complete compiled field. -/
theorem eval₂Hom_fieldCode_scaledChart
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ j, TermsAffineBlockDegreeLE layout M (P j))
    (q : Fin (n + k)) (w : Fin k → R) (z : Fin n → R) :
    eval₂Hom (algebraMap ℚ R)
        (scaledChartPoint layout w z)
        (PolynomialCode.decode (fieldCode layout M P q)) =
      mixedAmbientField layout (slowdown M w) w
        (scaledSourcePoint layout w z)
        (fun i ↦ eval₂Hom (algebraMap ℚ R) z
          (PolynomialCode.decode (P i))) q := by
  cases hq : finSumFinEquiv.symm q with
  | inl j =>
      have hq' : q = xIndex (k := k) j := by
        rw [xIndex, MultiCentralPolynomialCode.xIndex, ← hq]
        simp
      rw [hq']
      simpa [fieldCode, xIndex,
        MultiCentralPolynomialCode.xIndex, mixedAmbientField]
        using
          (eval₂Hom_xFieldCode_scaledChart layout M P hP j w z)
  | inr b =>
      have hq' : q = wIndex (n := n) b := by
        rw [wIndex, MultiCentralPolynomialCode.wIndex, ← hq]
        simp
      rw [hq']
      simpa [fieldCode, wIndex,
        MultiCentralPolynomialCode.wIndex, mixedAmbientField]
        using
          (eval₂Hom_wFieldCode_scaledChart layout M P hP b w z)

/-- The compiled field is tangent to every target block at every mixed
scaled-chart point satisfying the source sphere equations and source
compact-block tangency. -/
theorem fieldCode_target_tangent_scaledChart
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ j, TermsAffineBlockDegreeLE layout M (P j))
    (w : Fin k → R) (z : Fin n → R)
    (haffine :
      ∀ b, affineBlockNormSq layout
          (scaledSourcePoint layout w z) b + w b ^ 2 = 1)
    (hcompact :
      ∀ c, compactBlockDot layout z
        (fun i ↦ eval₂Hom (algebraMap ℚ R) z
          (PolynomialCode.decode (P i))) c = 0) :
    ∀ d,
      targetBlockDot layout (scaledChartPoint layout w z)
        (fun q ↦ eval₂Hom (algebraMap ℚ R)
          (scaledChartPoint layout w z)
          (PolynomialCode.decode (fieldCode layout M P q))) d = 0 := by
  have hcompact' :
      ∀ c, compactBlockDot layout
        (scaledSourcePoint layout w z)
        (fun i ↦ eval₂Hom (algebraMap ℚ R) z
          (PolynomialCode.decode (P i))) c = 0 := by
    intro c
    rw [compactBlockDot_scaledSourcePoint]
    exact hcompact c
  intro d
  have hvelocity :
      (fun q ↦ eval₂Hom (algebraMap ℚ R)
        (scaledChartPoint layout w z)
        (PolynomialCode.decode (fieldCode layout M P q))) =
      mixedAmbientField layout (slowdown M w) w
        (scaledSourcePoint layout w z)
        (fun i ↦ eval₂Hom (algebraMap ℚ R) z
          (PolynomialCode.decode (P i))) := by
    funext q
    exact eval₂Hom_fieldCode_scaledChart layout M P hP q w z
  rw [hvelocity]
  exact mixedAmbientField_target_tangent layout
    (slowdown M w) w (scaledSourcePoint layout w z)
    (fun i ↦ eval₂Hom (algebraMap ℚ R) z
      (PolynomialCode.decode (P i))) haffine hcompact' d

end MixedCentralPolynomialCode

end

end HGAS
