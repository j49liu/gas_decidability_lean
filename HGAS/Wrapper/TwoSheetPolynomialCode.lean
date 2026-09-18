import HGAS.Foundation.PolynomialDifferentiationCode
import HGAS.Algebra.HomogeneousEvaluation
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Executable two-sheet homogenization

Let `p(y₀,…,yₙ₋₁)` be a rational polynomial of degree at most `D`.
The projective chart used by the product-sphere wrapper is

```
Π(z,x) = zᴰ p(x/z).
```

Monomial by monomial this simply inserts the exponent
`D - |e|` in a new zeroth coordinate and moves every old exponent one
place to the right.  This file implements that operation directly on the
raw sparse polynomial codes.  In particular, the construction is
executable and does not inspect semantic `MvPolynomial` support.

The principal semantic facts are:

* every output monomial has degree exactly `D`, provided the input terms
  have degree at most `D`;
* setting the new chart coordinate to one recovers the original
  polynomial exactly.

The usual formula at an arbitrary nonzero `z` then follows from
homogeneity, without any division inside the compiler.
-/

namespace HGAS

open _root_.MvPolynomial

namespace ExponentCode

variable {n : ℕ}

/-- Insert a new zeroth exponent so that the total degree becomes `D`.
Old variables are shifted by `Fin.succ`.  Natural subtraction makes this
a total executable operation; the intended theorem assumes
`totalDegree e ≤ D`. -/
def chartLift (D : ℕ) (e : ExponentCode n) : ExponentCode (n + 1) :=
  Fin.cases (D - totalDegree e) e

@[simp]
theorem chartLift_zero (D : ℕ) (e : ExponentCode n) :
    chartLift D e 0 = D - totalDegree e :=
  rfl

@[simp]
theorem chartLift_succ (D : ℕ) (e : ExponentCode n) (i : Fin n) :
    chartLift D e i.succ = e i :=
  rfl

/-- A bounded source monomial becomes a monomial of degree exactly `D`. -/
theorem totalDegree_chartLift
    (D : ℕ) (e : ExponentCode n) (he : totalDegree e ≤ D) :
    totalDegree (chartLift D e) = D := by
  simp only [totalDegree, List.sum_ofFn]
  rw [Fin.sum_univ_succ]
  simp only [chartLift_zero, chartLift_succ]
  have hsum : (∑ i, e i) = totalDegree e := by
    simp [totalDegree, List.sum_ofFn]
  rw [hsum]
  exact Nat.sub_add_cancel he

end ExponentCode

namespace PolynomialCode

variable {n : ℕ}

/-- Lift one coded monomial into the two-sheet chart. -/
def chartLiftTerm (D : ℕ)
    (t : ExponentCode n × RationalCode) :
    ExponentCode (n + 1) × RationalCode :=
  (ExponentCode.chartLift D t.1, t.2)

/-- Executable two-sheet homogenization of a sparse polynomial code. -/
def twoSheetHomogenize (D : ℕ)
    (p : PolynomialCode n) : PolynomialCode (n + 1) :=
  p.map (chartLiftTerm D)

/-- The explicit syntactic degree bound needed by the total compiler.
For normalized inputs this is the ordinary bound on polynomial degree;
the stronger raw-list formulation also handles duplicate terms without
having to normalize noncomputably. -/
def TermsDegreeLE (D : ℕ) (p : PolynomialCode n) : Prop :=
  ∀ t ∈ p, ExponentCode.totalDegree t.1 ≤ D

theorem termsDegreeLE_cons_iff
    (D : ℕ) (t : ExponentCode n × RationalCode)
    (p : PolynomialCode n) :
    TermsDegreeLE D (t :: p) ↔
      ExponentCode.totalDegree t.1 ≤ D ∧ TermsDegreeLE D p := by
  simp [TermsDegreeLE]

/-- Each lifted coded term decodes to a homogeneous monomial of degree
`D`. -/
theorem decodeTerm_chartLiftTerm_isHomogeneous
    (D : ℕ) (t : ExponentCode n × RationalCode)
    (ht : ExponentCode.totalDegree t.1 ≤ D) :
    (decodeTerm (chartLiftTerm D t)).IsHomogeneous D := by
  apply isHomogeneous_monomial
  simp only [chartLiftTerm]
  rw [ExponentCode.degree_decode,
    ExponentCode.totalDegree_chartLift D t.1 ht]

/-- The complete lifted polynomial is homogeneous of degree `D`. -/
theorem decode_twoSheetHomogenize_isHomogeneous
    (D : ℕ) (p : PolynomialCode n)
    (hp : TermsDegreeLE D p) :
    (decode (twoSheetHomogenize D p)).IsHomogeneous D := by
  induction p with
  | nil =>
      simpa [twoSheetHomogenize] using
        (isHomogeneous_zero (Fin (n + 1)) ℚ D)
  | cons t p ih =>
      rw [termsDegreeLE_cons_iff] at hp
      simp only [twoSheetHomogenize, List.map_cons, decode_cons]
      exact
        (decodeTerm_chartLiftTerm_isHomogeneous D t hp.1).add
          (ih hp.2)

/-- Coordinates in the affine chart `z=1`. -/
def unitChartPoint {R : Type*} (one : R) (x : Fin n → R) :
    Fin (n + 1) → R :=
  Fin.cases one x

@[simp]
theorem unitChartPoint_zero {R : Type*} (one : R) (x : Fin n → R) :
    unitChartPoint one x 0 = one :=
  rfl

@[simp]
theorem unitChartPoint_succ {R : Type*} (one : R) (x : Fin n → R)
    (i : Fin n) :
    unitChartPoint one x i.succ = x i :=
  rfl

/-- Evaluation of a lifted monomial at `z=1` is evaluation of the source
monomial. -/
theorem eval₂Hom_decodeTerm_chartLiftTerm_unitChart
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (D : ℕ) (t : ExponentCode n × RationalCode)
    (x : Fin n → R) :
    eval₂Hom (algebraMap ℚ R) (unitChartPoint 1 x)
        (decodeTerm (chartLiftTerm D t)) =
      eval₂Hom (algebraMap ℚ R) x (decodeTerm t) := by
  simp only [decodeTerm, chartLiftTerm, eval₂Hom_monomial]
  congr 1
  rw [Finsupp.prod_of_support_subset
      (ExponentCode.decode (ExponentCode.chartLift D t.1))
      (Finset.subset_univ _) _ (by simp),
    Finsupp.prod_of_support_subset
      (ExponentCode.decode t.1)
      (Finset.subset_univ _) _ (by simp)]
  simp only [ExponentCode.decode]
  rw [Fin.prod_univ_succ]
  simp

/-- Setting the chart coordinate to one recovers the source polynomial. -/
theorem eval₂Hom_twoSheetHomogenize_unitChart
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (D : ℕ) (p : PolynomialCode n) (x : Fin n → R) :
    eval₂Hom (algebraMap ℚ R) (unitChartPoint 1 x)
        (decode (twoSheetHomogenize D p)) =
      eval₂Hom (algebraMap ℚ R) x (decode p) := by
  induction p with
  | nil => simp [twoSheetHomogenize]
  | cons t p ih =>
      simp only [twoSheetHomogenize, List.map_cons, decode_cons, map_add]
      rw [eval₂Hom_decodeTerm_chartLiftTerm_unitChart]
      change
        _ + eval₂Hom (algebraMap ℚ R) (unitChartPoint 1 x)
            (decode (twoSheetHomogenize D p)) =
          _ + _
      rw [ih]

/-- The chart point `(z, z • y)` is the scalar multiple by `z` of the
unit-chart point `(1,y)`. -/
theorem unitChartPoint_scaled
    {R : Type*} [Monoid R]
    (z : R) (y : Fin n → R) :
    unitChartPoint z (z • y) =
      z • unitChartPoint 1 y := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simp

/-- Division-free form of the usual two-sheet identity:

`Π(z,z y) = zᴰ p(y)`.

This is the exact statement needed on both projective sheets. -/
theorem eval₂Hom_twoSheetHomogenize_scaledChart
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (D : ℕ) (p : PolynomialCode n)
    (hp : TermsDegreeLE D p)
    (z : R) (y : Fin n → R) :
    eval₂Hom (algebraMap ℚ R) (unitChartPoint z (z • y))
        (decode (twoSheetHomogenize D p)) =
      z ^ D * eval₂Hom (algebraMap ℚ R) y (decode p) := by
  rw [unitChartPoint_scaled]
  rw [HGAS.MvPolynomial.IsHomogeneous.eval₂Hom_smul
    (decode_twoSheetHomogenize_isHomogeneous D p hp)]
  rw [eval₂Hom_twoSheetHomogenize_unitChart]

/-! ## Effectivity -/

theorem ExponentCode.chartLift_primrec {n : ℕ} :
    Primrec₂ (ExponentCode.chartLift :
      ℕ → ExponentCode n → ExponentCode (n + 1)) := by
  change
    Primrec
      (fun q : ℕ × ExponentCode n ↦
        ExponentCode.chartLift q.1 q.2)
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · exact
      Primrec.nat_sub.comp
        Primrec.fst
        (ExponentCode.totalDegree_primrec.comp Primrec.snd)
  · exact
      (Primrec.fin_app.comp
        Primrec.snd (Primrec.const i)).of_eq
          fun _ ↦ rfl

theorem chartLiftTerm_primrec {n : ℕ} :
    Primrec₂ (chartLiftTerm :
      ℕ → (ExponentCode n × RationalCode) →
        ExponentCode (n + 1) × RationalCode) := by
  change
    Primrec
      (fun q : ℕ × (ExponentCode n × RationalCode) ↦
        chartLiftTerm q.1 q.2)
  exact
    Primrec.pair
      (ExponentCode.chartLift_primrec.comp
        Primrec.fst
        (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)

theorem twoSheetHomogenize_primrec {n : ℕ} :
    Primrec₂ (twoSheetHomogenize :
      ℕ → PolynomialCode n → PolynomialCode (n + 1)) := by
  have hterm :
      Primrec₂
        (fun (q : ℕ × PolynomialCode n)
          (t : ExponentCode n × RationalCode) ↦
            chartLiftTerm q.1 t) :=
    chartLiftTerm_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.left)
      Primrec₂.right
  exact
    (Primrec.list_map Primrec.snd hterm).to₂.of_eq
      fun _ _ ↦ rfl

/-- In particular, the two-sheet sparse-code transformation is a total
computable function. -/
theorem twoSheetHomogenize_computable {n : ℕ} :
    Computable₂ (twoSheetHomogenize :
      ℕ → PolynomialCode n → PolynomialCode (n + 1)) :=
  twoSheetHomogenize_primrec.to_comp

end PolynomialCode

end HGAS
