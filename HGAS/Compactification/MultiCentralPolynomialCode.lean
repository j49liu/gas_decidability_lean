import HGAS.Compactification.CentralProduct
import HGAS.Wrapper.TwoSheetPolynomialCode
import Mathlib.Tactic

/-!
# Sparse polynomial syntax for multi-block central compactification

Let the affine variables be assigned to blocks by

```
sourceBlock : Fin n → Fin k.
```

The compactified polynomial ring has `n+k` variables: `x_j` for every old
affine coordinate and one chart variable `w_b` for every block.  For a
source monomial with exponent `e`, define its degree in block `b` by

```
d_b(e) = ∑_{sourceBlock j = b} e_j.
```

Given a common clearing degree `M`, its central lift keeps exponent `e_j`
on `x_j` and puts exponent `M-d_b(e)` on `w_b`.  Thus it represents

```
(∏_b w_b^M) · monomial(x_j / w_{sourceBlock j})
```

whenever every `d_b(e) ≤ M`.  Natural subtraction makes the raw compiler
total on malformed inputs.

This first layer defines the executable sparse transformation and proves
its exact unit-chart semantics.  Later lemmas add the full independently
scaled-chart identity and assemble the tangent compactified vector field.
-/

namespace HGAS

open _root_.MvPolynomial
open scoped BigOperators

namespace MultiCentralPolynomialCode

variable {n k : ℕ}

/-- Ambient index of an old affine coordinate. -/
def xIndex (j : Fin n) : Fin (n + k) :=
  finSumFinEquiv (Sum.inl j)

/-- Ambient index of the chart coordinate belonging to block `b`. -/
def wIndex (b : Fin k) : Fin (n + k) :=
  finSumFinEquiv (Sum.inr b)

@[simp]
theorem finSumFinEquiv_symm_xIndex (j : Fin n) :
    finSumFinEquiv.symm (xIndex (k := k) j) = Sum.inl j := by
  simp [xIndex]

@[simp]
theorem finSumFinEquiv_symm_wIndex (b : Fin k) :
    finSumFinEquiv.symm (wIndex (n := n) b) = Sum.inr b := by
  simp [wIndex]

/-- Degree of one exponent vector in one affine block. -/
def blockDegree
    (sourceBlock : Fin n → Fin k)
    (e : ExponentCode n) (b : Fin k) : ℕ :=
  ∑ j, if sourceBlock j = b then e j else 0

/-- Raw termwise condition guaranteeing that `M-d_b(e)` is genuine
denominator clearing in every block. -/
def TermsBlockDegreeLE
    (sourceBlock : Fin n → Fin k)
    (M : ℕ) (p : PolynomialCode n) : Prop :=
  ∀ t ∈ p, ∀ b, blockDegree sourceBlock t.1 b ≤ M

/-- Lift one source exponent to the `n+k` central variables. -/
def liftExponent
    (sourceBlock : Fin n → Fin k)
    (M : ℕ) (e : ExponentCode n) :
    ExponentCode (n + k) :=
  fun q ↦
    match finSumFinEquiv.symm q with
    | Sum.inl j => e j
    | Sum.inr b => M - blockDegree sourceBlock e b

@[simp]
theorem liftExponent_xIndex
    (sourceBlock : Fin n → Fin k)
    (M : ℕ) (e : ExponentCode n) (j : Fin n) :
    liftExponent sourceBlock M e (xIndex (k := k) j) = e j := by
  simp [liftExponent]

@[simp]
theorem liftExponent_wIndex
    (sourceBlock : Fin n → Fin k)
    (M : ℕ) (e : ExponentCode n) (b : Fin k) :
    liftExponent sourceBlock M e (wIndex (n := n) b) =
      M - blockDegree sourceBlock e b := by
  simp [liftExponent]

@[simp]
theorem liftExponent_finSum_inl
    (sourceBlock : Fin n → Fin k)
    (M : ℕ) (e : ExponentCode n) (j : Fin n) :
    liftExponent sourceBlock M e
        (finSumFinEquiv (Sum.inl j)) = e j := by
  simp [liftExponent]

@[simp]
theorem liftExponent_finSum_inr
    (sourceBlock : Fin n → Fin k)
    (M : ℕ) (e : ExponentCode n) (b : Fin k) :
    liftExponent sourceBlock M e
        (finSumFinEquiv (Sum.inr b)) =
      M - blockDegree sourceBlock e b := by
  simp [liftExponent]

/-- Lift one raw sparse term. -/
def liftTerm
    (sourceBlock : Fin n → Fin k)
    (M : ℕ)
    (t : ExponentCode n × RationalCode) :
    ExponentCode (n + k) × RationalCode :=
  (liftExponent sourceBlock M t.1, t.2)

/-- Executable simultaneous denominator clearing for every affine block. -/
def homogenize
    (sourceBlock : Fin n → Fin k)
    (M : ℕ)
    (p : PolynomialCode n) :
    PolynomialCode (n + k) :=
  p.map (liftTerm sourceBlock M)

/-- Assignment with old coordinates `x` and all chart variables equal to
one. -/
def unitChartPoint
    {R : Type*} [One R]
    (x : Fin n → R) :
    Fin (n + k) → R :=
  fun q ↦
    match finSumFinEquiv.symm q with
    | Sum.inl j => x j
    | Sum.inr _ => 1

@[simp]
theorem unitChartPoint_xIndex
    {R : Type*} [One R]
    (x : Fin n → R) (j : Fin n) :
    unitChartPoint (k := k) x (xIndex (k := k) j) = x j := by
  simp [unitChartPoint]

@[simp]
theorem unitChartPoint_wIndex
    {R : Type*} [One R]
    (x : Fin n → R) (b : Fin k) :
    unitChartPoint (k := k) x (wIndex (n := n) b) = 1 := by
  simp [unitChartPoint]

/-- General assignment of vector and chart coordinates. -/
def chartPoint
    {R : Type*}
    (x : Fin n → R) (w : Fin k → R) :
    Fin (n + k) → R :=
  fun q ↦
    match finSumFinEquiv.symm q with
    | Sum.inl j => x j
    | Sum.inr b => w b

/-- A source point `z` represented in independent central charts:
`x_j=w_{block(j)}z_j`. -/
def scaledChartPoint
    {R : Type*} [Mul R]
    (sourceBlock : Fin n → Fin k)
    (w : Fin k → R) (z : Fin n → R) :
    Fin (n + k) → R :=
  chartPoint (fun j ↦ w (sourceBlock j) * z j) w

@[simp]
theorem scaledChartPoint_finSum_inl
    {R : Type*} [Mul R]
    (sourceBlock : Fin n → Fin k)
    (w : Fin k → R) (z : Fin n → R) (j : Fin n) :
    scaledChartPoint sourceBlock w z
        (finSumFinEquiv (Sum.inl j)) =
      w (sourceBlock j) * z j := by
  simp [scaledChartPoint, chartPoint]

@[simp]
theorem scaledChartPoint_finSum_inr
    {R : Type*} [Mul R]
    (sourceBlock : Fin n → Fin k)
    (w : Fin k → R) (z : Fin n → R) (b : Fin k) :
    scaledChartPoint sourceBlock w z
        (finSumFinEquiv (Sum.inr b)) =
      w b := by
  simp [scaledChartPoint, chartPoint]

@[simp]
theorem scaledChartPoint_xIndex
    {R : Type*} [Mul R]
    (sourceBlock : Fin n → Fin k)
    (w : Fin k → R) (z : Fin n → R) (j : Fin n) :
    scaledChartPoint sourceBlock w z (xIndex (k := k) j) =
      w (sourceBlock j) * z j := by
  exact scaledChartPoint_finSum_inl sourceBlock w z j

@[simp]
theorem scaledChartPoint_wIndex
    {R : Type*} [Mul R]
    (sourceBlock : Fin n → Fin k)
    (w : Fin k → R) (z : Fin n → R) (b : Fin k) :
    scaledChartPoint sourceBlock w z (wIndex (n := n) b) =
      w b := by
  exact scaledChartPoint_finSum_inr sourceBlock w z b

/-- Common multi-block slowdown `∏_b w_b^M`. -/
def slowdown
    {R : Type*} [CommMonoid R]
    (M : ℕ) (w : Fin k → R) : R :=
  ∏ b, w b ^ M

/-- Regroup powers of chart variables by the source block map. -/
theorem prod_sourceBlock_pow_eq
    {R : Type*} [CommMonoid R]
    (sourceBlock : Fin n → Fin k)
    (e : ExponentCode n) (w : Fin k → R) :
    (∏ j, w (sourceBlock j) ^ e j) =
      ∏ b, w b ^ blockDegree sourceBlock e b := by
  rw [← Finset.prod_fiberwise Finset.univ sourceBlock
    (fun j ↦ w (sourceBlock j) ^ e j)]
  apply Finset.prod_congr rfl
  intro b _
  rw [Finset.prod_congr rfl (fun j hj ↦ by
    rw [(Finset.mem_filter.mp hj).2])]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Finset.sum_filter]
  rfl

/-- The clearing powers and the powers contributed by scaled affine
coordinates combine to the common slowdown. -/
theorem prod_clearing_mul_sourceBlock_pow
    {R : Type*} [CommMonoid R]
    (sourceBlock : Fin n → Fin k)
    (M : ℕ) (e : ExponentCode n)
    (hdegree : ∀ b, blockDegree sourceBlock e b ≤ M)
    (w : Fin k → R) :
    (∏ b, w b ^ (M - blockDegree sourceBlock e b)) *
        (∏ j, w (sourceBlock j) ^ e j) =
      slowdown M w := by
  rw [prod_sourceBlock_pow_eq sourceBlock e w]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro b _
  rw [← pow_add, Nat.sub_add_cancel (hdegree b)]

/-- A lifted monomial has exactly the original value when every central
chart coordinate is one. -/
theorem eval₂Hom_decodeTerm_liftTerm_unitChart
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (sourceBlock : Fin n → Fin k)
    (M : ℕ)
    (t : ExponentCode n × RationalCode)
    (x : Fin n → R) :
    eval₂Hom (algebraMap ℚ R) (unitChartPoint (k := k) x)
        (PolynomialCode.decodeTerm
          (liftTerm sourceBlock M t)) =
      eval₂Hom (algebraMap ℚ R) x
        (PolynomialCode.decodeTerm t) := by
  simp only [PolynomialCode.decodeTerm, liftTerm,
    eval₂Hom_monomial]
  congr 1
  rw [Finsupp.prod_of_support_subset
      (ExponentCode.decode
        (liftExponent sourceBlock M t.1))
      (Finset.subset_univ _) _ (by simp),
    Finsupp.prod_of_support_subset
      (ExponentCode.decode t.1)
      (Finset.subset_univ _) _ (by simp)]
  simp only [ExponentCode.decode]
  rw [← finSumFinEquiv.prod_comp, Fintype.prod_sum_type]
  simp [unitChartPoint, liftExponent]

/-- Unit-chart evaluation recovers the complete source polynomial. -/
theorem eval₂Hom_homogenize_unitChart
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (sourceBlock : Fin n → Fin k)
    (M : ℕ)
    (p : PolynomialCode n)
    (x : Fin n → R) :
    eval₂Hom (algebraMap ℚ R) (unitChartPoint (k := k) x)
        (PolynomialCode.decode
          (homogenize sourceBlock M p)) =
      eval₂Hom (algebraMap ℚ R) x
        (PolynomialCode.decode p) := by
  induction p with
  | nil =>
      simp [homogenize]
  | cons t p ih =>
      simp only [homogenize, List.map_cons,
        PolynomialCode.decode_cons, map_add]
      rw [eval₂Hom_decodeTerm_liftTerm_unitChart]
      change
        _ + eval₂Hom (algebraMap ℚ R)
            (unitChartPoint (k := k) x)
            (PolynomialCode.decode
              (homogenize sourceBlock M p)) =
          _ + _
      rw [ih]

/-- Exact independently scaled-chart identity for one lifted monomial. -/
theorem eval₂Hom_decodeTerm_liftTerm_scaledChart
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (sourceBlock : Fin n → Fin k)
    (M : ℕ)
    (t : ExponentCode n × RationalCode)
    (hdegree :
      ∀ b, blockDegree sourceBlock t.1 b ≤ M)
    (w : Fin k → R) (z : Fin n → R) :
    eval₂Hom (algebraMap ℚ R)
        (scaledChartPoint sourceBlock w z)
        (PolynomialCode.decodeTerm
          (liftTerm sourceBlock M t)) =
      slowdown M w *
        eval₂Hom (algebraMap ℚ R) z
          (PolynomialCode.decodeTerm t) := by
  simp only [PolynomialCode.decodeTerm, liftTerm,
    eval₂Hom_monomial]
  rw [Finsupp.prod_of_support_subset
      (ExponentCode.decode
        (liftExponent sourceBlock M t.1))
      (Finset.subset_univ _) _ (by simp),
    Finsupp.prod_of_support_subset
      (ExponentCode.decode t.1)
      (Finset.subset_univ _) _ (by simp)]
  simp only [ExponentCode.decode]
  rw [← finSumFinEquiv.prod_comp, Fintype.prod_sum_type]
  simp only [ne_eq, Finsupp.coe_mk,
    scaledChartPoint_finSum_inl,
    scaledChartPoint_finSum_inr,
    liftExponent_finSum_inl,
    liftExponent_finSum_inr]
  have hsplit :
      (∏ j, (w (sourceBlock j) * z j) ^ t.1 j) =
        (∏ j, w (sourceBlock j) ^ t.1 j) *
          ∏ j, z j ^ t.1 j := by
    simp_rw [mul_pow]
    exact Finset.prod_mul_distrib
  rw [hsplit]
  have hclear :
      (∏ j, w (sourceBlock j) ^ t.1 j) *
          (∏ b, w b ^ (M - blockDegree sourceBlock t.1 b)) =
        slowdown M w := by
    simpa only [mul_comm] using
      (prod_clearing_mul_sourceBlock_pow
        sourceBlock M t.1 hdegree w)
  rw [show
      ((∏ j, w (sourceBlock j) ^ t.1 j) *
          (∏ j, z j ^ t.1 j)) *
          (∏ b, w b ^ (M - blockDegree sourceBlock t.1 b)) =
        ((∏ j, w (sourceBlock j) ^ t.1 j) *
          (∏ b, w b ^ (M - blockDegree sourceBlock t.1 b))) *
          (∏ j, z j ^ t.1 j) by ring,
    hclear]
  ring

/-- Exact denominator-clearing identity for a complete sparse polynomial. -/
theorem eval₂Hom_homogenize_scaledChart
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (sourceBlock : Fin n → Fin k)
    (M : ℕ) (p : PolynomialCode n)
    (hp : TermsBlockDegreeLE sourceBlock M p)
    (w : Fin k → R) (z : Fin n → R) :
    eval₂Hom (algebraMap ℚ R)
        (scaledChartPoint sourceBlock w z)
        (PolynomialCode.decode
          (homogenize sourceBlock M p)) =
      slowdown M w *
        eval₂Hom (algebraMap ℚ R) z
          (PolynomialCode.decode p) := by
  induction p with
  | nil =>
      simp [homogenize]
  | cons t p ih =>
      have ht : ∀ b, blockDegree sourceBlock t.1 b ≤ M := by
        intro b
        exact hp t (by simp) b
      have hp' : TermsBlockDegreeLE sourceBlock M p := by
        intro u hu b
        exact hp u (by simp [hu]) b
      simp only [homogenize, List.map_cons,
        PolynomialCode.decode_cons, map_add]
      rw [eval₂Hom_decodeTerm_liftTerm_scaledChart
        sourceBlock M t ht w z]
      change
        slowdown M w *
              eval₂Hom (algebraMap ℚ R) z
                (PolynomialCode.decodeTerm t) +
            eval₂Hom (algebraMap ℚ R)
              (scaledChartPoint sourceBlock w z)
              (PolynomialCode.decode
                (homogenize sourceBlock M p)) =
          slowdown M w *
            (eval₂Hom (algebraMap ℚ R) z
                (PolynomialCode.decodeTerm t) +
              eval₂Hom (algebraMap ℚ R) z
                (PolynomialCode.decode p))
      rw [ih hp']
      ring

end MultiCentralPolynomialCode

end HGAS
