import HGAS.Compactification.Stereographic
import HGAS.Propagation.DegreePaddingCode
import Mathlib.Tactic

/-!
# Sparse polynomial compiler for the compact vector accumulator

Let `P` be a polynomial vector field in `n` base variables and let
`g = (g₁,...,gₘ)` be a polynomial drift observable on the same base.
Adjoin one stereographic accumulator sphere with coordinates
`(U₁,...,Uₘ,W)`.  The compiler in this file emits

```
 y'   = P(y),
 Uᵢ'  = (1+W) gᵢ(y) - (U·g(y)) Uᵢ,
 W'   = -(1+W) (U·g(y)).
```

All operations are performed on raw finite rational sparse syntax.  The
evaluation theorems identify every emitted coordinate with the semantic
field from `Compactification.Stereographic`, and the final theorem proves
tangency to the accumulator sphere.

This is the missing syntactic counterpart of equation (11.2) in the
paper.  It is independent of the modular selector and can be reused for
any finite-dimensional polynomial cocycle.
-/

namespace HGAS

open _root_.MvPolynomial
open scoped BigOperators

namespace AccumulatorPolynomialCode

variable {n m : ℕ}

/-- Auxiliary index of an accumulator vector coordinate inside
`Fin (m+1)`. -/
def uAuxIndex (i : Fin m) : Fin (m + 1) :=
  finSumFinEquiv (Sum.inl i)

/-- Auxiliary index of the stereographic scalar coordinate. -/
def wAuxIndex (m : ℕ) : Fin (m + 1) :=
  finSumFinEquiv (Sum.inr (0 : Fin 1))

/-- Ambient index of a base coordinate. -/
def baseIndex (j : Fin n) : Fin (n + (m + 1)) :=
  DegreePaddingCode.baseIndex n (m + 1) j

/-- Ambient index of an accumulator vector coordinate. -/
def uIndex (i : Fin m) : Fin (n + (m + 1)) :=
  DegreePaddingCode.sinkIndex n (m + 1) (uAuxIndex i)

/-- Ambient index of the stereographic scalar coordinate. -/
def wIndex (n m : ℕ) : Fin (n + (m + 1)) :=
  DegreePaddingCode.sinkIndex n (m + 1) (wAuxIndex m)

@[simp]
theorem finSumFinEquiv_symm_uAuxIndex (i : Fin m) :
    finSumFinEquiv.symm (uAuxIndex i) = Sum.inl i := by
  simp [uAuxIndex]

@[simp]
theorem finSumFinEquiv_symm_wAuxIndex :
    finSumFinEquiv.symm (wAuxIndex m) =
      Sum.inr (0 : Fin 1) := by
  simp [wAuxIndex]

@[simp]
theorem outer_symm_baseIndex (j : Fin n) :
    finSumFinEquiv.symm (baseIndex (m := m) j) =
      Sum.inl j := by
  simp [baseIndex, DegreePaddingCode.baseIndex]

@[simp]
theorem outer_symm_uIndex (i : Fin m) :
    finSumFinEquiv.symm (uIndex (n := n) i) =
      Sum.inr (uAuxIndex i) := by
  simp [uIndex, DegreePaddingCode.sinkIndex]

@[simp]
theorem outer_symm_wIndex :
    finSumFinEquiv.symm (wIndex n m) =
      Sum.inr (wAuxIndex m) := by
  simp [wIndex, DegreePaddingCode.sinkIndex]

/-- Flat ambient point corresponding to base coordinates `y` and one
accumulator sphere coordinate `(u,w)`. -/
def combinedPoint
    {R : Type*}
    (y : Fin n → R) (u : Fin m → R) (w : R) :
    Fin (n + (m + 1)) → R :=
  fun q ↦
    match finSumFinEquiv.symm q with
    | Sum.inl j => y j
    | Sum.inr r =>
        match finSumFinEquiv.symm r with
        | Sum.inl i => u i
        | Sum.inr _ => w

@[simp]
theorem combinedPoint_baseIndex
    {R : Type*}
    (y : Fin n → R) (u : Fin m → R) (w : R)
    (j : Fin n) :
    combinedPoint y u w (baseIndex (m := m) j) = y j := by
  simp [combinedPoint]

@[simp]
theorem combinedPoint_uIndex
    {R : Type*}
    (y : Fin n → R) (u : Fin m → R) (w : R)
    (i : Fin m) :
    combinedPoint y u w (uIndex (n := n) i) = u i := by
  simp [combinedPoint]

@[simp]
theorem combinedPoint_wIndex
    {R : Type*}
    (y : Fin n → R) (u : Fin m → R) (w : R) :
    combinedPoint y u w (wIndex n m) = w := by
  simp [combinedPoint]

/-- Insert a base polynomial into the larger base-plus-accumulator
variable set. -/
def liftBase (p : PolynomialCode n) :
    PolynomialCode (n + (m + 1)) :=
  PolynomialCode.dimensionEmbed (m + 1) p

/-- Lift one drift coordinate. -/
def driftCode
    (g : Fin m → PolynomialCode n) (i : Fin m) :
    PolynomialCode (n + (m + 1)) :=
  liftBase (m := m) (g i)

/-- Sparse code of `1+W`. -/
def onePlusWCode : PolynomialCode (n + (m + 1)) :=
  PolynomialCode.add PolynomialCode.one
    (PolynomialCode.varCode (wIndex n m))

/-- Sparse code of the dot product `U·g(y)`. -/
def dotCode
    (g : Fin m → PolynomialCode n) :
    PolynomialCode (n + (m + 1)) :=
  PolynomialCode.sumCodes
    (List.ofFn fun i : Fin m ↦
      PolynomialCode.mul
        (PolynomialCode.varCode (uIndex (n := n) i))
        (driftCode g i))

/-- Emitted equation for one accumulator vector coordinate. -/
def uFieldCode
    (g : Fin m → PolynomialCode n) (i : Fin m) :
    PolynomialCode (n + (m + 1)) :=
  PolynomialCode.sub
    (PolynomialCode.mul onePlusWCode (driftCode g i))
    (PolynomialCode.mul
      (dotCode g)
      (PolynomialCode.varCode (uIndex (n := n) i)))

/-- Emitted equation for the stereographic scalar coordinate. -/
def wFieldCode
    (g : Fin m → PolynomialCode n) :
    PolynomialCode (n + (m + 1)) :=
  PolynomialCode.neg
    (PolynomialCode.mul onePlusWCode (dotCode g))

/-- Complete base-plus-accumulator polynomial field. -/
def fieldCode
    (P : PolynomialFieldCode n)
    (g : Fin m → PolynomialCode n) :
    PolynomialFieldCode (n + (m + 1)) :=
  fun q ↦
    match finSumFinEquiv.symm q with
    | Sum.inl j => liftBase (m := m) (P j)
    | Sum.inr r =>
        match finSumFinEquiv.symm r with
        | Sum.inl i => uFieldCode g i
        | Sum.inr _ => wFieldCode g

/-! ## Exact semantics -/

private theorem eval_sumCodes_ofFn
    {R : Type*} [CommRing R] [Algebra ℚ R]
    {r N : ℕ} (p : Fin r → PolynomialCode N)
    (x : Fin N → R) :
    eval₂Hom (algebraMap ℚ R) x
        (PolynomialCode.decode
          (PolynomialCode.sumCodes (List.ofFn p))) =
      ∑ i, eval₂Hom (algebraMap ℚ R) x
        (PolynomialCode.decode (p i)) := by
  rw [PolynomialCode.decode_sumCodes, List.map_ofFn,
    List.sum_ofFn, map_sum]
  rfl

/-- Evaluation of an inserted base polynomial ignores the accumulator
coordinates. -/
theorem eval₂Hom_liftBase
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (p : PolynomialCode n)
    (y : Fin n → R) (u : Fin m → R) (w : R) :
    eval₂Hom (algebraMap ℚ R) (combinedPoint y u w)
        (PolynomialCode.decode (liftBase (m := m) p)) =
      eval₂Hom (algebraMap ℚ R) y
        (PolynomialCode.decode p) := by
  rw [liftBase, PolynomialCode.decode_dimensionEmbed,
    eval₂Hom_rename]
  have hcoords :
      combinedPoint y u w ∘
          DegreePaddingCode.baseIndex n (m + 1) =
        y := by
    funext j
    exact combinedPoint_baseIndex y u w j
  rw [hcoords]

@[simp]
theorem eval₂Hom_onePlusWCode
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (y : Fin n → R) (u : Fin m → R) (w : R) :
    eval₂Hom (algebraMap ℚ R) (combinedPoint y u w)
        (PolynomialCode.decode
          (onePlusWCode (n := n) (m := m))) =
      1 + w := by
  simp [onePlusWCode]

/-- Exact evaluation of the coded accumulator dot product. -/
theorem eval₂Hom_dotCode
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (g : Fin m → PolynomialCode n)
    (y : Fin n → R) (u : Fin m → R) (w : R) :
    eval₂Hom (algebraMap ℚ R) (combinedPoint y u w)
        (PolynomialCode.decode (dotCode g)) =
      ∑ i, u i *
        eval₂Hom (algebraMap ℚ R) y
          (PolynomialCode.decode (g i)) := by
  rw [dotCode, eval_sumCodes_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  simp only [PolynomialCode.decode_mul_code, map_mul,
    PolynomialCode.decode_varCode, eval₂Hom_X',
    combinedPoint_uIndex, driftCode]
  rw [eval₂Hom_liftBase]

/-- Exact evaluation of an accumulator vector equation. -/
theorem eval₂Hom_uFieldCode
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (g : Fin m → PolynomialCode n)
    (y : Fin n → R) (u : Fin m → R) (w : R)
    (i : Fin m) :
    eval₂Hom (algebraMap ℚ R) (combinedPoint y u w)
        (PolynomialCode.decode (uFieldCode g i)) =
      (1 + w) *
          eval₂Hom (algebraMap ℚ R) y
            (PolynomialCode.decode (g i)) -
        (∑ j, u j *
          eval₂Hom (algebraMap ℚ R) y
            (PolynomialCode.decode (g j))) * u i := by
  simp only [uFieldCode, PolynomialCode.decode_sub_code,
    PolynomialCode.decode_mul_code, map_sub, map_mul,
    PolynomialCode.decode_varCode, eval₂Hom_X',
    combinedPoint_uIndex, driftCode]
  rw [eval₂Hom_onePlusWCode, eval₂Hom_liftBase,
    eval₂Hom_dotCode]

/-- Exact evaluation of the stereographic scalar equation. -/
theorem eval₂Hom_wFieldCode
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (g : Fin m → PolynomialCode n)
    (y : Fin n → R) (u : Fin m → R) (w : R) :
    eval₂Hom (algebraMap ℚ R) (combinedPoint y u w)
        (PolynomialCode.decode (wFieldCode g)) =
      -(1 + w) *
        ∑ j, u j *
          eval₂Hom (algebraMap ℚ R) y
            (PolynomialCode.decode (g j)) := by
  simp only [wFieldCode, PolynomialCode.decode_neg_code,
    PolynomialCode.decode_mul_code, map_neg, map_mul]
  rw [eval₂Hom_onePlusWCode, eval₂Hom_dotCode]
  ring

/-- Base equations are preserved literally. -/
theorem eval₂Hom_fieldCode_base
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (P : PolynomialFieldCode n)
    (g : Fin m → PolynomialCode n)
    (y : Fin n → R) (u : Fin m → R) (w : R)
    (j : Fin n) :
    eval₂Hom (algebraMap ℚ R) (combinedPoint y u w)
        (PolynomialCode.decode
          (fieldCode P g (baseIndex (m := m) j))) =
      eval₂Hom (algebraMap ℚ R) y
        (PolynomialCode.decode (P j)) := by
  rw [fieldCode, outer_symm_baseIndex]
  exact eval₂Hom_liftBase (P j) y u w

/-- Accumulator vector equations realize `accumulatorUField`. -/
theorem eval₂Hom_fieldCode_u
    (P : PolynomialFieldCode n)
    (g : Fin m → PolynomialCode n)
    (y : Fin n → ℝ) (u : Fin m → ℝ) (w : ℝ)
    (i : Fin m) :
    eval₂Hom (algebraMap ℚ ℝ) (combinedPoint y u w)
        (PolynomialCode.decode
          (fieldCode P g (uIndex (n := n) i))) =
      accumulatorUField u w
        (fun j ↦
          eval₂Hom (algebraMap ℚ ℝ) y
            (PolynomialCode.decode (g j))) i := by
  simp only [fieldCode, outer_symm_uIndex,
    finSumFinEquiv_symm_uAuxIndex]
  rw [eval₂Hom_uFieldCode]
  rfl

/-- The scalar equation realizes `accumulatorWField`. -/
theorem eval₂Hom_fieldCode_w
    (P : PolynomialFieldCode n)
    (g : Fin m → PolynomialCode n)
    (y : Fin n → ℝ) (u : Fin m → ℝ) (w : ℝ) :
    eval₂Hom (algebraMap ℚ ℝ) (combinedPoint y u w)
        (PolynomialCode.decode
          (fieldCode P g (wIndex n m))) =
      accumulatorWField u w
        (fun j ↦
          eval₂Hom (algebraMap ℚ ℝ) y
            (PolynomialCode.decode (g j))) := by
  simp only [fieldCode, outer_symm_wIndex,
    finSumFinEquiv_symm_wAuxIndex]
  rw [eval₂Hom_wFieldCode]
  rfl

/-- The emitted accumulator block is tangent to its unit sphere. -/
theorem fieldCode_accumulator_tangent
    (P : PolynomialFieldCode n)
    (g : Fin m → PolynomialCode n)
    (y : Fin n → ℝ) (u : Fin m → ℝ) (w : ℝ)
    (hsphere : normSq u + w ^ 2 = 1) :
    (∑ i, u i *
      eval₂Hom (algebraMap ℚ ℝ) (combinedPoint y u w)
        (PolynomialCode.decode
          (fieldCode P g (uIndex (n := n) i)))) +
      w *
        eval₂Hom (algebraMap ℚ ℝ) (combinedPoint y u w)
          (PolynomialCode.decode
            (fieldCode P g (wIndex n m))) = 0 := by
  have hdot :
      (∑ i, u i *
        eval₂Hom (algebraMap ℚ ℝ) (combinedPoint y u w)
          (PolynomialCode.decode
            (fieldCode P g (uIndex (n := n) i)))) =
        dot u
          (accumulatorUField u w
            (fun j ↦
              eval₂Hom (algebraMap ℚ ℝ) y
                (PolynomialCode.decode (g j)))) := by
    unfold dot
    apply Finset.sum_congr rfl
    intro i _
    rw [eval₂Hom_fieldCode_u]
  rw [hdot]
  rw [eval₂Hom_fieldCode_w]
  exact accumulator_tangent u w
    (fun j ↦
      eval₂Hom (algebraMap ℚ ℝ) y
        (PolynomialCode.decode (g j)))
    hsphere

end AccumulatorPolynomialCode

end HGAS
