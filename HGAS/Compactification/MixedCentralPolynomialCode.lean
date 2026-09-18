import HGAS.Compactification.MultiCentralPolynomialCode
import Mathlib.Tactic

/-!
# Mixed central compactification: finite sparse polynomial syntax

The source variables need not all be affine.  A fixed layout

```
layout : Fin n → Fin k ⊕ Fin l
```

marks `Sum.inl b` as an affine coordinate in central block `b`, and
`Sum.inr c` as a coordinate in an already compact sphere block `c`.
Only affine blocks acquire new chart coordinates `w_b`.  Compact source
coordinates are left unchanged.

For a source monomial `z^e`, the exponent of `w_b` in its lift is

```
M - ∑_{layout j = Sum.inl b} e_j.
```

Consequently, at the mixed chart

```
x_j = w_b z_j  if layout j = Sum.inl b,
x_j = z_j      if layout j = Sum.inr c,
```

every lifted monomial is exactly

```
(∏_b w_b^M) z^e.
```

The construction below is on raw finite sparse syntax and is total.
The explicit termwise degree predicate records when natural subtraction
really performs denominator clearing.
-/

namespace HGAS

open _root_.MvPolynomial
open scoped BigOperators

namespace MixedCentralPolynomialCode

variable {n k l : ℕ}

/-- Ambient index of an old source coordinate. -/
def xIndex (j : Fin n) : Fin (n + k) :=
  MultiCentralPolynomialCode.xIndex (k := k) j

/-- Ambient index of the new chart coordinate of affine block `b`. -/
def wIndex (b : Fin k) : Fin (n + k) :=
  MultiCentralPolynomialCode.wIndex (n := n) b

@[simp]
theorem finSumFinEquiv_symm_xIndex (j : Fin n) :
    finSumFinEquiv.symm (xIndex (k := k) j) = Sum.inl j := by
  simp [xIndex]

@[simp]
theorem finSumFinEquiv_symm_wIndex (b : Fin k) :
    finSumFinEquiv.symm (wIndex (n := n) b) = Sum.inr b := by
  simp [wIndex]

/-- Degree of an exponent vector in one *affine* source block.  Exponents
of already compact coordinates do not contribute denominators. -/
def affineBlockDegree
    (layout : Fin n → Fin k ⊕ Fin l)
    (e : ExponentCode n) (b : Fin k) : ℕ :=
  ∑ j, if layout j = Sum.inl b then e j else 0

/-- Raw termwise denominator-clearing condition. -/
def TermsAffineBlockDegreeLE
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (p : PolynomialCode n) : Prop :=
  ∀ t ∈ p, ∀ b, affineBlockDegree layout t.1 b ≤ M

/-- Lift one exponent into the old coordinates followed by the `k` new
affine chart coordinates. -/
def liftExponent
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (e : ExponentCode n) :
    ExponentCode (n + k) :=
  fun q ↦
    match finSumFinEquiv.symm q with
    | Sum.inl j => e j
    | Sum.inr b => M - affineBlockDegree layout e b

@[simp]
theorem liftExponent_xIndex
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (e : ExponentCode n) (j : Fin n) :
    liftExponent layout M e (xIndex (k := k) j) = e j := by
  simp [liftExponent]

@[simp]
theorem liftExponent_wIndex
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (e : ExponentCode n) (b : Fin k) :
    liftExponent layout M e (wIndex (n := n) b) =
      M - affineBlockDegree layout e b := by
  simp [liftExponent]

@[simp]
theorem liftExponent_finSum_inl
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (e : ExponentCode n) (j : Fin n) :
    liftExponent layout M e (finSumFinEquiv (Sum.inl j)) = e j := by
  simp [liftExponent]

@[simp]
theorem liftExponent_finSum_inr
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (e : ExponentCode n) (b : Fin k) :
    liftExponent layout M e (finSumFinEquiv (Sum.inr b)) =
      M - affineBlockDegree layout e b := by
  simp [liftExponent]

/-- Lift one raw sparse term. -/
def liftTerm
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ)
    (t : ExponentCode n × RationalCode) :
    ExponentCode (n + k) × RationalCode :=
  (liftExponent layout M t.1, t.2)

/-- Executable mixed denominator clearing. -/
def homogenize
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (p : PolynomialCode n) :
    PolynomialCode (n + k) :=
  p.map (liftTerm layout M)

/-- An arbitrary assignment of old and chart coordinates. -/
def chartPoint
    {R : Type*}
    (x : Fin n → R) (w : Fin k → R) :
    Fin (n + k) → R :=
  MultiCentralPolynomialCode.chartPoint x w

@[simp]
theorem chartPoint_xIndex
    {R : Type*} (x : Fin n → R) (w : Fin k → R) (j : Fin n) :
    chartPoint x w (xIndex (k := k) j) = x j := by
  simp [chartPoint, xIndex, MultiCentralPolynomialCode.chartPoint,
    MultiCentralPolynomialCode.xIndex]

@[simp]
theorem chartPoint_wIndex
    {R : Type*} (x : Fin n → R) (w : Fin k → R) (b : Fin k) :
    chartPoint x w (wIndex (n := n) b) = w b := by
  simp [chartPoint, wIndex, MultiCentralPolynomialCode.chartPoint,
    MultiCentralPolynomialCode.wIndex]

/-- Old coordinates in the mixed scaled chart. -/
def scaledSourcePoint
    {R : Type*} [Mul R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (w : Fin k → R) (z : Fin n → R) :
    Fin n → R :=
  fun j ↦
    match layout j with
    | Sum.inl b => w b * z j
    | Sum.inr _ => z j

/-- Complete mixed scaled-chart assignment. -/
def scaledChartPoint
    {R : Type*} [Mul R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (w : Fin k → R) (z : Fin n → R) :
    Fin (n + k) → R :=
  chartPoint (scaledSourcePoint layout w z) w

@[simp]
theorem scaledChartPoint_xIndex
    {R : Type*} [Mul R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (w : Fin k → R) (z : Fin n → R) (j : Fin n) :
    scaledChartPoint layout w z (xIndex (k := k) j) =
      match layout j with
      | Sum.inl b => w b * z j
      | Sum.inr _ => z j := by
  simp [scaledChartPoint, scaledSourcePoint]

@[simp]
theorem scaledChartPoint_wIndex
    {R : Type*} [Mul R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (w : Fin k → R) (z : Fin n → R) (b : Fin k) :
    scaledChartPoint layout w z (wIndex (n := n) b) = w b := by
  simp [scaledChartPoint]

@[simp]
theorem scaledChartPoint_finSum_inl
    {R : Type*} [Mul R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (w : Fin k → R) (z : Fin n → R) (j : Fin n) :
    scaledChartPoint layout w z (finSumFinEquiv (Sum.inl j)) =
      scaledSourcePoint layout w z j := by
  simp [scaledChartPoint, chartPoint,
    MultiCentralPolynomialCode.chartPoint]

@[simp]
theorem scaledChartPoint_finSum_inr
    {R : Type*} [Mul R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (w : Fin k → R) (z : Fin n → R) (b : Fin k) :
    scaledChartPoint layout w z (finSumFinEquiv (Sum.inr b)) =
      w b := by
  simp [scaledChartPoint, chartPoint,
    MultiCentralPolynomialCode.chartPoint]

/-- The common time slowdown contributed by all newly compactified affine
blocks. -/
def slowdown
    {R : Type*} [CommMonoid R]
    (M : ℕ) (w : Fin k → R) : R :=
  ∏ b, w b ^ M

/-- The scale contributed by one old coordinate. -/
def sourceScale
    {R : Type*} [One R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (w : Fin k → R) (j : Fin n) : R :=
  match layout j with
  | Sum.inl b => w b
  | Sum.inr _ => 1

@[simp]
theorem scaledSourcePoint_eq_sourceScale_mul
    {R : Type*} [Monoid R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (w : Fin k → R) (z : Fin n → R) (j : Fin n) :
    scaledSourcePoint layout w z j =
      sourceScale layout w j * z j := by
  cases h : layout j <;> simp [scaledSourcePoint, sourceScale, h]

/-- Regroup exactly the affine-coordinate scale powers by their affine
block.  Compact coordinates contribute the unit factor. -/
theorem prod_sourceScale_pow_eq
    {R : Type*} [CommMonoid R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (e : ExponentCode n) (w : Fin k → R) :
    (∏ j, sourceScale layout w j ^ e j) =
      ∏ b, w b ^ affineBlockDegree layout e b := by
  rw [← Finset.prod_fiberwise Finset.univ layout
    (fun j ↦ sourceScale layout w j ^ e j)]
  rw [Fintype.prod_sum_type]
  have haff :
      (∏ b : Fin k,
          ∏ j ∈ Finset.univ with layout j = Sum.inl b,
            sourceScale layout w j ^ e j) =
        ∏ b, w b ^ affineBlockDegree layout e b := by
    apply Finset.prod_congr rfl
    intro b _
    calc
      (∏ j ∈ Finset.univ with layout j = Sum.inl b,
          sourceScale layout w j ^ e j) =
          ∏ j ∈ Finset.univ with layout j = Sum.inl b,
            w b ^ e j := by
              apply Finset.prod_congr rfl
              intro j hj
              have hj' := (Finset.mem_filter.mp hj).2
              simp [sourceScale, hj']
      _ = w b ^
          ∑ j ∈ Finset.univ with layout j = Sum.inl b, e j := by
            rw [Finset.prod_pow_eq_pow_sum]
      _ = w b ^ affineBlockDegree layout e b := by
            congr 1
            rw [Finset.sum_filter]
            rfl
  have hcompact :
      (∏ c : Fin l,
          ∏ j ∈ Finset.univ with layout j = Sum.inr c,
            sourceScale layout w j ^ e j) = 1 := by
    apply Finset.prod_eq_one
    intro c _
    apply Finset.prod_eq_one
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    simp [sourceScale, hj']
  rw [haff, hcompact, mul_one]

/-- Clearing powers and old-coordinate scales combine to the common
slowdown. -/
theorem prod_clearing_mul_sourceScale_pow
    {R : Type*} [CommMonoid R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (e : ExponentCode n)
    (hdegree : ∀ b, affineBlockDegree layout e b ≤ M)
    (w : Fin k → R) :
    (∏ b, w b ^ (M - affineBlockDegree layout e b)) *
        (∏ j, sourceScale layout w j ^ e j) =
      slowdown M w := by
  rw [prod_sourceScale_pow_eq layout e w]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro b _
  rw [← pow_add, Nat.sub_add_cancel (hdegree b)]

/-- A lifted monomial agrees with its source monomial when every new
chart coordinate equals one. -/
theorem eval₂Hom_decodeTerm_liftTerm_unitChart
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (t : ExponentCode n × RationalCode)
    (z : Fin n → R) :
    eval₂Hom (algebraMap ℚ R)
        (chartPoint z (fun _ ↦ 1))
        (PolynomialCode.decodeTerm (liftTerm layout M t)) =
      eval₂Hom (algebraMap ℚ R) z
        (PolynomialCode.decodeTerm t) := by
  simp only [PolynomialCode.decodeTerm, liftTerm, eval₂Hom_monomial]
  congr 1
  rw [Finsupp.prod_of_support_subset
      (ExponentCode.decode (liftExponent layout M t.1))
      (Finset.subset_univ _) _ (by simp),
    Finsupp.prod_of_support_subset
      (ExponentCode.decode t.1)
      (Finset.subset_univ _) _ (by simp)]
  simp only [ExponentCode.decode]
  rw [← finSumFinEquiv.prod_comp, Fintype.prod_sum_type]
  simp [chartPoint, MultiCentralPolynomialCode.chartPoint,
    liftExponent]

/-- Setting every new chart coordinate to one recovers the source
polynomial exactly. -/
theorem eval₂Hom_homogenize_unitChart
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (p : PolynomialCode n) (z : Fin n → R) :
    eval₂Hom (algebraMap ℚ R)
        (chartPoint z (fun _ ↦ 1))
        (PolynomialCode.decode (homogenize layout M p)) =
      eval₂Hom (algebraMap ℚ R) z
        (PolynomialCode.decode p) := by
  induction p with
  | nil => simp [homogenize]
  | cons t p ih =>
      simp only [homogenize, List.map_cons,
        PolynomialCode.decode_cons, map_add]
      rw [eval₂Hom_decodeTerm_liftTerm_unitChart]
      change
        eval₂Hom (algebraMap ℚ R) z
              (PolynomialCode.decodeTerm t) +
            eval₂Hom (algebraMap ℚ R)
              (chartPoint z (fun _ ↦ 1))
              (PolynomialCode.decode (homogenize layout M p)) =
          eval₂Hom (algebraMap ℚ R) z
              (PolynomialCode.decodeTerm t) +
            eval₂Hom (algebraMap ℚ R) z
              (PolynomialCode.decode p)
      rw [ih]

/-- Exact mixed scaled-chart identity for a lifted monomial. -/
theorem eval₂Hom_decodeTerm_liftTerm_scaledChart
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ)
    (t : ExponentCode n × RationalCode)
    (hdegree :
      ∀ b, affineBlockDegree layout t.1 b ≤ M)
    (w : Fin k → R) (z : Fin n → R) :
    eval₂Hom (algebraMap ℚ R)
        (scaledChartPoint layout w z)
        (PolynomialCode.decodeTerm (liftTerm layout M t)) =
      slowdown M w *
        eval₂Hom (algebraMap ℚ R) z
          (PolynomialCode.decodeTerm t) := by
  simp only [PolynomialCode.decodeTerm, liftTerm, eval₂Hom_monomial]
  rw [Finsupp.prod_of_support_subset
      (ExponentCode.decode (liftExponent layout M t.1))
      (Finset.subset_univ _) _ (by simp),
    Finsupp.prod_of_support_subset
      (ExponentCode.decode t.1)
      (Finset.subset_univ _) _ (by simp)]
  simp only [ExponentCode.decode]
  rw [← finSumFinEquiv.prod_comp, Fintype.prod_sum_type]
  simp only [ne_eq, Finsupp.coe_mk,
    scaledChartPoint_finSum_inl,
    scaledChartPoint_finSum_inr, liftExponent_finSum_inl,
    liftExponent_finSum_inr]
  have hsource :
      (∏ j, scaledSourcePoint layout w z j ^ t.1 j) =
        (∏ j, sourceScale layout w j ^ t.1 j) *
          ∏ j, z j ^ t.1 j := by
    simp_rw [scaledSourcePoint_eq_sourceScale_mul, mul_pow]
    exact Finset.prod_mul_distrib
  rw [hsource]
  have hclear :
      (∏ j, sourceScale layout w j ^ t.1 j) *
          (∏ b, w b ^ (M - affineBlockDegree layout t.1 b)) =
        slowdown M w := by
    simpa only [mul_comm] using
      (prod_clearing_mul_sourceScale_pow
        layout M t.1 hdegree w)
  rw [show
      ((∏ j, sourceScale layout w j ^ t.1 j) *
          (∏ j, z j ^ t.1 j)) *
          (∏ b, w b ^ (M - affineBlockDegree layout t.1 b)) =
        ((∏ j, sourceScale layout w j ^ t.1 j) *
          (∏ b, w b ^ (M - affineBlockDegree layout t.1 b))) *
          (∏ j, z j ^ t.1 j) by ring,
    hclear]
  ring

/-- Exact denominator-clearing identity for a complete sparse
polynomial. -/
theorem eval₂Hom_homogenize_scaledChart
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (p : PolynomialCode n)
    (hp : TermsAffineBlockDegreeLE layout M p)
    (w : Fin k → R) (z : Fin n → R) :
    eval₂Hom (algebraMap ℚ R)
        (scaledChartPoint layout w z)
        (PolynomialCode.decode (homogenize layout M p)) =
      slowdown M w *
        eval₂Hom (algebraMap ℚ R) z
          (PolynomialCode.decode p) := by
  induction p with
  | nil => simp [homogenize]
  | cons t p ih =>
      have ht : ∀ b, affineBlockDegree layout t.1 b ≤ M := by
        intro b
        exact hp t (by simp) b
      have hp' : TermsAffineBlockDegreeLE layout M p := by
        intro u hu b
        exact hp u (by simp [hu]) b
      simp only [homogenize, List.map_cons,
        PolynomialCode.decode_cons, map_add]
      rw [eval₂Hom_decodeTerm_liftTerm_scaledChart
        layout M t ht w z]
      change
        slowdown M w *
              eval₂Hom (algebraMap ℚ R) z
                (PolynomialCode.decodeTerm t) +
            eval₂Hom (algebraMap ℚ R)
              (scaledChartPoint layout w z)
              (PolynomialCode.decode (homogenize layout M p)) =
          slowdown M w *
            (eval₂Hom (algebraMap ℚ R) z
                (PolynomialCode.decodeTerm t) +
              eval₂Hom (algebraMap ℚ R) z
                (PolynomialCode.decode p))
      rw [ih hp']
      ring

end MixedCentralPolynomialCode

end HGAS
