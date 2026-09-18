import HGAS.Algebra.FiniteEuclidean
import HGAS.Foundation.FiniteCode
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic

/-!
# Polynomial algebra for rational homogeneous Lyapunov certificates

Section 3 searches for Lyapunov functions

```
V(x) = p(x) / ρ(x)^r,       ρ(x)=∑ᵢxᵢ².
```

Differentiating formally along a polynomial field `F` gives

```
-V̇ = q(F,p,r) / ρ^(r+1),
q = -ρ (∇p·F) + 2r p (x·F).
```

This file defines the numerator entirely in `MvPolynomial`, proves its
evaluation formula, and checks its homogeneous degree.  The analytic
chain-rule statement and the implication from a strict certificate to GAS
belong in later modules.
-/

namespace HGAS

open MvPolynomial
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- Polynomial `ρ=∑ᵢXᵢ²`. -/
def rhoPolynomial : MvPolynomial (Fin n) ℚ :=
  ∑ i, X i ^ 2

/-- Polynomial directional derivative `∇p·F`. -/
def gradientDotField
    (p : MvPolynomial (Fin n) ℚ) (F : PolynomialField n) :
    MvPolynomial (Fin n) ℚ :=
  ∑ i, pderiv i p * F i

/-- Polynomial radial dot product `x·F(x)`. -/
def radialDotPolynomial (F : PolynomialField n) :
    MvPolynomial (Fin n) ℚ :=
  ∑ i, X i * F i

/-- Numerator `q(F,p,r)` in equation (3.2). -/
def rationalLyapunovNumerator
    (F : PolynomialField n) (p : MvPolynomial (Fin n) ℚ) (r : ℕ) :
    MvPolynomial (Fin n) ℚ :=
  -(rhoPolynomial * gradientDotField p F) +
    C (2 * (r : ℚ)) * p * radialDotPolynomial F

/-- Evaluation of `ρ` is the coordinate squared norm. -/
theorem eval₂Hom_rhoPolynomial
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (x : Fin n → S) :
    eval₂Hom (algebraMap ℚ S) x rhoPolynomial = normSq x := by
  simp only [rhoPolynomial, map_sum, map_mul, eval₂Hom_X',
    normSq, dot, pow_two]

/-- Evaluation formula for `∇p·F`. -/
theorem eval₂Hom_gradientDotField
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (p : MvPolynomial (Fin n) ℚ) (F : PolynomialField n)
    (x : Fin n → S) :
    eval₂Hom (algebraMap ℚ S) x (gradientDotField p F) =
      ∑ i, eval₂Hom (algebraMap ℚ S) x (pderiv i p) *
        evalPolynomialField F x i := by
  simp [gradientDotField]

/-- Evaluation formula for `x·F(x)`. -/
theorem eval₂Hom_radialDotPolynomial
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (F : PolynomialField n) (x : Fin n → S) :
    eval₂Hom (algebraMap ℚ S) x (radialDotPolynomial F) =
      dot x (evalPolynomialField F x) := by
  simp [radialDotPolynomial, dot]

/-- Exact evaluation of the certificate numerator. -/
theorem eval₂Hom_rationalLyapunovNumerator
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (F : PolynomialField n) (p : MvPolynomial (Fin n) ℚ)
    (r : ℕ) (x : Fin n → S) :
    eval₂Hom (algebraMap ℚ S) x
        (rationalLyapunovNumerator F p r) =
      -normSq x *
          (∑ i, eval₂Hom (algebraMap ℚ S) x (pderiv i p) *
            evalPolynomialField F x i) +
        (2 * (r : S)) * eval₂Hom (algebraMap ℚ S) x p *
          dot x (evalPolynomialField F x) := by
  simp only [rationalLyapunovNumerator, map_add, map_neg, map_mul,
    eval₂Hom_rhoPolynomial, eval₂Hom_gradientDotField,
    eval₂Hom_radialDotPolynomial, map_ofNat,
    map_natCast]
  ring

/-- `ρ` is homogeneous of degree two. -/
theorem rhoPolynomial_isHomogeneous :
    (rhoPolynomial (n := n)).IsHomogeneous 2 := by
  apply IsHomogeneous.sum Finset.univ (fun i : Fin n ↦ X i ^ 2) 2
  intro i _
  exact isHomogeneous_X_pow i 2

/-- If `p` and `F` are homogeneous, then `∇p·F` has the expected degree. -/
theorem gradientDotField_isHomogeneous
    {pDegree fieldDegree : ℕ}
    (p : MvPolynomial (Fin n) ℚ) (F : PolynomialField n)
    (hp : p.IsHomogeneous pDegree)
    (hF : IsHomogeneousOfDegree fieldDegree F) :
    (gradientDotField p F).IsHomogeneous
      ((pDegree - 1) + fieldDegree) := by
  apply IsHomogeneous.sum Finset.univ
    (fun i : Fin n ↦ pderiv i p * F i)
    ((pDegree - 1) + fieldDegree)
  intro i _
  exact (hp.pderiv (i := i)).mul (hF i)

/-- The radial dot polynomial has degree one more than the field. -/
theorem radialDotPolynomial_isHomogeneous
    {fieldDegree : ℕ} (F : PolynomialField n)
    (hF : IsHomogeneousOfDegree fieldDegree F) :
    (radialDotPolynomial F).IsHomogeneous (fieldDegree + 1) := by
  have h :
      (radialDotPolynomial F).IsHomogeneous (1 + fieldDegree) := by
    apply IsHomogeneous.sum Finset.univ
      (fun i : Fin n ↦ X i * F i) (1 + fieldDegree)
    intro i _
    exact (isHomogeneous_X ℚ i).mul (hF i)
  simpa [Nat.add_comm] using h

/-- For `deg p = 2r+2` and `deg F=d`, the numerator has degree
`2r+d+3`. -/
theorem rationalLyapunovNumerator_isHomogeneous
    {fieldDegree : ℕ} (F : PolynomialField n)
    (p : MvPolynomial (Fin n) ℚ) (r : ℕ)
    (hF : IsHomogeneousOfDegree fieldDegree F)
    (hp : p.IsHomogeneous (2 * r + 2)) :
    (rationalLyapunovNumerator F p r).IsHomogeneous
      (2 * r + fieldDegree + 3) := by
  have hgrad := gradientDotField_isHomogeneous p F hp hF
  have hrad := radialDotPolynomial_isHomogeneous F hF
  have hfirst :
      (rhoPolynomial * gradientDotField p F).IsHomogeneous
        (2 * r + fieldDegree + 3) := by
    convert rhoPolynomial_isHomogeneous.mul hgrad using 1
    omega
  have hsecond :
      (C (2 * (r : ℚ)) * p * radialDotPolynomial F).IsHomogeneous
        (2 * r + fieldDegree + 3) := by
    have hc : (C (2 * (r : ℚ)) :
        MvPolynomial (Fin n) ℚ).IsHomogeneous 0 :=
      isHomogeneous_C _ _
    convert (hc.mul hp).mul hrad using 1
    omega
  exact hfirst.neg.add hsecond

end

end HGAS
