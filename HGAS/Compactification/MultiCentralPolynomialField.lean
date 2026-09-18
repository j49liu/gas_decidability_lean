import HGAS.Compactification.MultiCentralPolynomialCode
import Mathlib.Tactic

/-!
# The polynomial multi-block central field

`MultiCentralPolynomialCode` clears all affine denominators.  This module
assembles those cleared coordinates into the actual tangent sphere field.

For a source field `P` and a block `b`, let

```
D_b = ∑_{sourceBlock j=b} x_j · (f P_j).
```

The emitted coordinates are

```
x_j' = w_b ((f P_j) - x_j D_b),      b = sourceBlock j,
w_b' = -w_b² D_b.
```

At a scaled chart point `x_j=w_b z_j`, the sparse code evaluates exactly
to the central compactification formulas with common slowdown
`f=∏_b w_b^M`.  All coefficients remain rational and the construction is
defined directly on finite raw syntax.
-/

namespace HGAS

open _root_.MvPolynomial
open scoped BigOperators

noncomputable section

namespace MultiCentralPolynomialCode

variable {n k : ℕ}

/-- Dot product restricted to one source block. -/
def sourceBlockDot
    {R : Type*} [CommRing R]
    (sourceBlock : Fin n → Fin k)
    (x p : Fin n → R) (b : Fin k) : R :=
  ∑ j, if sourceBlock j = b then x j * p j else 0

/-- Squared norm restricted to one source block. -/
def sourceBlockNormSq
    {R : Type*} [CommRing R]
    (sourceBlock : Fin n → Fin k)
    (x : Fin n → R) (b : Fin k) : R :=
  ∑ j, if sourceBlock j = b then x j ^ 2 else 0

/-- Semantic vector-coordinate formula for the centrally compactified
source field. -/
def sourceCentralXField
    {R : Type*} [CommRing R]
    (sourceBlock : Fin n → Fin k)
    (f : R) (w : Fin k → R)
    (x p : Fin n → R) (j : Fin n) : R :=
  f * w (sourceBlock j) *
    (p j - sourceBlockDot sourceBlock x p (sourceBlock j) * x j)

/-- Semantic chart-coordinate formula for one block. -/
def sourceCentralWField
    {R : Type*} [CommRing R]
    (sourceBlock : Fin n → Fin k)
    (f : R) (w : Fin k → R)
    (x p : Fin n → R) (b : Fin k) : R :=
  -f * w b ^ 2 * sourceBlockDot sourceBlock x p b

/-- Blockwise sphere tangency of the semantic central field. -/
theorem sourceCentralField_tangent
    {R : Type*} [CommRing R]
    (sourceBlock : Fin n → Fin k)
    (f : R) (w : Fin k → R)
    (x p : Fin n → R)
    (hsphere :
      ∀ b, sourceBlockNormSq sourceBlock x b + w b ^ 2 = 1) :
    ∀ b,
      sourceBlockDot sourceBlock x
          (sourceCentralXField sourceBlock f w x p) b +
        w b * sourceCentralWField sourceBlock f w x p b = 0 := by
  intro b
  let d := sourceBlockDot sourceBlock x p b
  let s := sourceBlockNormSq sourceBlock x b
  have hxdot :
      sourceBlockDot sourceBlock x
          (sourceCentralXField sourceBlock f w x p) b =
        f * w b * d - f * w b * d * s := by
    unfold sourceBlockDot
    calc
      (∑ j,
          if sourceBlock j = b then
            x j *
              sourceCentralXField sourceBlock f w x p j
          else 0) =
          ∑ j, (
              (if sourceBlock j = b then
                f * w b * (x j * p j)
              else 0) -
              (if sourceBlock j = b then
                f * w b * d * x j ^ 2
              else 0)) := by
              apply Finset.sum_congr rfl
              intro j _
              by_cases hj : sourceBlock j = b
              · simp only [hj, ↓reduceIte,
                  sourceCentralXField, d]
                ring
              · simp [hj]
      _ =
          (∑ j, if sourceBlock j = b then
              f * w b * (x j * p j) else 0) -
            ∑ j, if sourceBlock j = b then
              f * w b * d * x j ^ 2 else 0 := by
                rw [Finset.sum_sub_distrib]
      _ =
          f * w b *
              (∑ j, if sourceBlock j = b then
                x j * p j else 0) -
            f * w b * d *
              ∑ j, if sourceBlock j = b then
                x j ^ 2 else 0 := by
                  rw [Finset.mul_sum, Finset.mul_sum]
                  congr 1
                  · apply Finset.sum_congr rfl
                    intro j _
                    by_cases hj : sourceBlock j = b <;>
                      simp [hj]
                  · apply Finset.sum_congr rfl
                    intro j _
                    by_cases hj : sourceBlock j = b <;>
                      simp [hj]
      _ = f * w b * d - f * w b * d * s := by
            change
              f * w b * sourceBlockDot sourceBlock x p b -
                  f * w b * d *
                    sourceBlockNormSq sourceBlock x b =
                _
            rfl
  rw [hxdot]
  simp only [sourceCentralWField]
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

/-- Sparse code for `D_b`, using the already cleared coordinates of `P`. -/
def blockDotCode
    (sourceBlock : Fin n → Fin k)
    (M : ℕ) (P : PolynomialFieldCode n)
    (b : Fin k) :
    PolynomialCode (n + k) :=
  PolynomialCode.sumCodes
    (List.ofFn fun j : Fin n ↦
      if sourceBlock j = b then
        PolynomialCode.mul
          (PolynomialCode.varCode (xIndex (k := k) j))
          (homogenize sourceBlock M (P j))
      else
        PolynomialCode.zero)

/-- Coordinate of the complete compactified field corresponding to an old
affine variable. -/
def xFieldCode
    (sourceBlock : Fin n → Fin k)
    (M : ℕ) (P : PolynomialFieldCode n)
    (j : Fin n) :
    PolynomialCode (n + k) :=
  let b := sourceBlock j
  PolynomialCode.mul
    (PolynomialCode.varCode (wIndex (n := n) b))
    (PolynomialCode.sub
      (homogenize sourceBlock M (P j))
      (PolynomialCode.mul
        (PolynomialCode.varCode (xIndex (k := k) j))
        (blockDotCode sourceBlock M P b)))

/-- Coordinate of the complete compactified field corresponding to a
central chart variable. -/
def wFieldCode
    (sourceBlock : Fin n → Fin k)
    (M : ℕ) (P : PolynomialFieldCode n)
    (b : Fin k) :
    PolynomialCode (n + k) :=
  PolynomialCode.neg
    (PolynomialCode.mul
      (PolynomialCode.pow
        (PolynomialCode.varCode (wIndex (n := n) b)) 2)
      (blockDotCode sourceBlock M P b))

/-- Complete rational polynomial central compactification of an affine
source field. -/
def fieldCode
    (sourceBlock : Fin n → Fin k)
    (M : ℕ) (P : PolynomialFieldCode n) :
    PolynomialFieldCode (n + k) :=
  fun q ↦
    match finSumFinEquiv.symm q with
    | Sum.inl j => xFieldCode sourceBlock M P j
    | Sum.inr b => wFieldCode sourceBlock M P b

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

/-- Evaluation of the coded block dot product at an arbitrary ambient
point. -/
theorem eval₂Hom_blockDotCode
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (sourceBlock : Fin n → Fin k)
    (M : ℕ) (P : PolynomialFieldCode n)
    (b : Fin k) (y : Fin (n + k) → R) :
    eval₂Hom (algebraMap ℚ R) y
        (PolynomialCode.decode
          (blockDotCode sourceBlock M P b)) =
      ∑ j, if sourceBlock j = b then
        y (xIndex (k := k) j) *
          eval₂Hom (algebraMap ℚ R) y
            (PolynomialCode.decode
              (homogenize sourceBlock M (P j)))
        else 0 := by
  rw [blockDotCode, eval_sumCodes_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : sourceBlock j = b
  · simp [hj]
  · simp [hj]

/-- At a scaled central chart point, the coded dot product is the common
slowdown times the affine block dot product. -/
theorem eval₂Hom_blockDotCode_scaledChart
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (sourceBlock : Fin n → Fin k)
    (M : ℕ) (P : PolynomialFieldCode n)
    (hP :
      ∀ j, TermsBlockDegreeLE sourceBlock M (P j))
    (b : Fin k) (w : Fin k → R) (z : Fin n → R) :
    eval₂Hom (algebraMap ℚ R)
        (scaledChartPoint sourceBlock w z)
        (PolynomialCode.decode
          (blockDotCode sourceBlock M P b)) =
      slowdown M w *
        sourceBlockDot sourceBlock
          (fun j ↦ w (sourceBlock j) * z j)
          (fun j ↦
            eval₂Hom (algebraMap ℚ R) z
              (PolynomialCode.decode (P j))) b := by
  rw [eval₂Hom_blockDotCode]
  unfold sourceBlockDot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : sourceBlock j = b
  · simp only [hj, ↓reduceIte,
      scaledChartPoint_xIndex]
    rw [eval₂Hom_homogenize_scaledChart
      sourceBlock M (P j) (hP j) w z]
    ring
  · simp [hj]

/-- Evaluation of an emitted old-coordinate equation is exactly the
semantic central compactification formula. -/
theorem eval₂Hom_xFieldCode_scaledChart
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (sourceBlock : Fin n → Fin k)
    (M : ℕ) (P : PolynomialFieldCode n)
    (hP :
      ∀ j, TermsBlockDegreeLE sourceBlock M (P j))
    (j : Fin n) (w : Fin k → R) (z : Fin n → R) :
    eval₂Hom (algebraMap ℚ R)
        (scaledChartPoint sourceBlock w z)
        (PolynomialCode.decode
          (xFieldCode sourceBlock M P j)) =
      sourceCentralXField sourceBlock (slowdown M w) w
        (fun i ↦ w (sourceBlock i) * z i)
        (fun i ↦
          eval₂Hom (algebraMap ℚ R) z
            (PolynomialCode.decode (P i))) j := by
  simp only [xFieldCode, PolynomialCode.decode_mul_code,
    PolynomialCode.decode_sub_code,
    PolynomialCode.decode_varCode, map_mul, map_sub,
    eval₂Hom_X', scaledChartPoint_xIndex,
    scaledChartPoint_wIndex]
  rw [eval₂Hom_homogenize_scaledChart
    sourceBlock M (P j) (hP j) w z]
  rw [eval₂Hom_blockDotCode_scaledChart
    sourceBlock M P hP (sourceBlock j) w z]
  simp only [sourceCentralXField]
  ring

/-- Evaluation of an emitted chart-coordinate equation is exactly the
semantic central compactification formula. -/
theorem eval₂Hom_wFieldCode_scaledChart
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (sourceBlock : Fin n → Fin k)
    (M : ℕ) (P : PolynomialFieldCode n)
    (hP :
      ∀ j, TermsBlockDegreeLE sourceBlock M (P j))
    (b : Fin k) (w : Fin k → R) (z : Fin n → R) :
    eval₂Hom (algebraMap ℚ R)
        (scaledChartPoint sourceBlock w z)
        (PolynomialCode.decode
          (wFieldCode sourceBlock M P b)) =
      sourceCentralWField sourceBlock (slowdown M w) w
        (fun i ↦ w (sourceBlock i) * z i)
        (fun i ↦
          eval₂Hom (algebraMap ℚ R) z
            (PolynomialCode.decode (P i))) b := by
  simp only [wFieldCode, PolynomialCode.decode_neg_code,
    PolynomialCode.decode_mul_code,
    PolynomialCode.decode_pow_code,
    PolynomialCode.decode_varCode, map_neg, map_mul,
    map_pow, eval₂Hom_X', scaledChartPoint_wIndex]
  rw [eval₂Hom_blockDotCode_scaledChart
    sourceBlock M P hP b w z]
  simp only [sourceCentralWField]
  ring

end MultiCentralPolynomialCode

end

end HGAS
