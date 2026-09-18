import HGAS.Foundation.FiniteCode
import HGAS.Propagation.DegreePadding
import Mathlib.Tactic

/-!
# Evaluation and scaling of homogeneous polynomials

The polar arguments in the paper repeatedly use one elementary fact: if
`p` is homogeneous of degree `d`, then

```
p(c x) = c^d p(x).
```

Mathlib's `MvPolynomial.IsHomogeneous` records the syntactic hypothesis.
This module supplies the semantic evaluation theorem, first for one
polynomial over general commutative semirings and then componentwise for the
rational vector-field codes used by the decision problem.
-/

namespace HGAS

open MvPolynomial

noncomputable section

/-- Evaluation of a homogeneous multivariate polynomial commutes with scalar
dilation of every variable. -/
theorem MvPolynomial.IsHomogeneous.eval₂Hom_smul
    {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    {p : MvPolynomial σ R} {d : ℕ}
    (hp : p.IsHomogeneous d) (f : R →+* S)
    (x : σ → S) (c : S) :
    eval₂Hom f (c • x) p = c ^ d * eval₂Hom f x p := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero =>
      simp
  | add p q hp hq ihp ihq =>
      simp only [map_add, ihp, ihq, mul_add]
  | monomial e r he =>
      simp only [eval₂Hom_monomial, Pi.smul_apply, smul_eq_mul, mul_pow,
        Finsupp.prod, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum]
      have hdegree : ∑ i ∈ e.support, e i = d := by
        change Finsupp.degree e = d
        rw [Finsupp.degree_eq_weight_one]
        exact he
      rw [hdegree]
      ring

/-- A homogeneous rational polynomial field has the expected semantic
scaling degree over every rational algebra. -/
theorem evalPolynomialField_smul
    {n d : ℕ} {S : Type*} [CommRing S] [Algebra ℚ S]
    (F : PolynomialField n) (hF : IsHomogeneousOfDegree d F)
    (c : S) (x : Fin n → S) :
    evalPolynomialField F (c • x) =
      c ^ d • evalPolynomialField F x := by
  funext i
  simp only [evalPolynomialField_apply, Pi.smul_apply, smul_eq_mul]
  exact MvPolynomial.IsHomogeneous.eval₂Hom_smul
    (hF i) (algebraMap ℚ S) x c

/-- The realized real field of a valid code scales by its declared
homogeneous degree. -/
theorem HomogeneousFieldCode.realize_smul
    {n d : ℕ} (F : HomogeneousFieldCode n d)
    (c : ℝ) (x : Fin n → ℝ) :
    F.realize (c • x) = c ^ d • F.realize x :=
  evalPolynomialField_smul F.field F.homogeneous c x

/-- Compatibility with the representation-independent scaling predicate
used by the degree-padding module. -/
theorem HomogeneousFieldCode.realize_scalesAsDegree
    {n d : ℕ} (F : HomogeneousFieldCode n d) :
    ScalesAsDegree ℝ d F.realize :=
  fun c x ↦ F.realize_smul c x

end

end HGAS
