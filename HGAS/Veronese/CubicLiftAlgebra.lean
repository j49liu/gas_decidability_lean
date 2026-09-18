import HGAS.Algebra.HomogeneousEvaluation
import HGAS.Veronese.Differential
import HGAS.Veronese.ToricRelations
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic

/-!
# Algebraic construction of the cubic Veronese lift

This module formalizes the coefficient-level construction in equations
(16.1)--(16.3).  Suppose that `F` is a rational polynomial vector field on
`Fin n`, homogeneous of degree `2*k+1`, with `k ≥ 1`.  The source
polynomial

```
∑ i, (∂ᵢ x^a) Fᵢ
```

represents the `a`-coordinate of `Dνₖ(x) F(x)` and is homogeneous of
degree `3*k`.  Every exponent vector of total degree `3*k` can be split
into three exponent vectors of degree `k`.  Replacing the corresponding
source monomial by a product of three Veronese coordinates gives a
rational cubic polynomial.  Applying this operation componentwise produces
the ambient field `cubicLiftField`.

The construction below is explicit:

1. turn an exponent vector into a sorted list of variable indices;
2. split that list into three consecutive blocks of length `k`;
3. count the indices in each block to obtain three degree-`k`
   multiindices;
4. replace the source monomial by the product of the three associated
   target variables.

We prove the exact identity over every commutative `ℚ`-algebra:

```
eval(cubicLiftField F, νₖ(x)) = Dνₖ(x) eval(F,x).
```

The target field is homogeneous cubic, so evaluation on the negative sheet
is the negative of the displayed vector.  We also prove the elementary
tangency identity for every indexed quadratic relation along both signed
Veronese images.

Finally, the module constructs the rational cubic weighted gradient of the
quartic toric penalty and the stabilized polynomial field

```
G - K grad_Q W.
```

The penalty contribution vanishes on every common zero of the indexed
quadrics, so the stabilized field agrees with `G` on both signed images.

## Deliberate analytic boundary

The results here are polynomial identities.  They do not claim:

* the converse real-cone parametrization of all common real zeros;
* Morse--Bott nondegeneracy or a uniform transverse inequality;
* the existence/effectivity of the constants used in the global
  invariant-measure argument.

Those are separate geometric and analytic obligations.  In particular,
tangency is proved here on the two explicitly parametrized sheets; it is
not silently extended to every real common zero.
-/

namespace HGAS.Veronese

open scoped BigOperators

variable {n k : ℕ}

/-! ## Rational polynomial fields on an arbitrary finite coordinate type -/

/-- A rational polynomial vector field whose input and output coordinates
are both indexed by `ι`. -/
abbrev RationalCoordinateField (ι : Type*) :=
  ι → MvPolynomial ι ℚ

/-- Componentwise homogeneity for a rational coordinate field. -/
def IsHomogeneousCoordinateField {ι : Type*}
    (d : ℕ) (G : RationalCoordinateField ι) : Prop :=
  ∀ i, (G i).IsHomogeneous d

/-- Evaluate a rational coordinate field over an arbitrary commutative
`ℚ`-algebra. -/
noncomputable def evalCoordinateField
    {ι S : Type*} [CommRing S] [Algebra ℚ S]
    (G : RationalCoordinateField ι) (y : ι → S) : ι → S :=
  fun i ↦ MvPolynomial.eval₂Hom (algebraMap ℚ S) y (G i)

@[simp]
theorem evalCoordinateField_apply
    {ι S : Type*} [CommRing S] [Algebra ℚ S]
    (G : RationalCoordinateField ι) (y : ι → S) (i : ι) :
    evalCoordinateField G y i =
      MvPolynomial.eval₂Hom (algebraMap ℚ S) y (G i) :=
  rfl

/-- Semantic scaling of a homogeneous rational coordinate field. -/
theorem evalCoordinateField_smul
    {ι S : Type*} [CommRing S] [Algebra ℚ S]
    {G : RationalCoordinateField ι} {d : ℕ}
    (hG : IsHomogeneousCoordinateField d G)
    (c : S) (y : ι → S) :
    evalCoordinateField G (c • y) =
      c ^ d • evalCoordinateField G y := by
  funext i
  exact HGAS.MvPolynomial.IsHomogeneous.eval₂Hom_smul
    (hG i) (algebraMap ℚ S) y c

/-! ## Splitting a degree-`3k` exponent into three degree-`k` blocks -/

/-- Turn a list of exactly `k` variable indices into its multiplicity
multiindex. -/
noncomputable def multiIndexOfList
    {n k : ℕ} (l : List (Fin n)) (hl : l.length = k) :
    MultiIndex n k :=
  ⟨fun i ↦ Multiset.toFinsupp (l : Multiset (Fin n)) i, by
    rw [multiIndexFinset, Finset.mem_piAntidiag]
    constructor
    · calc
        (∑ i, Multiset.toFinsupp
            (l : Multiset (Fin n)) i) =
            (Multiset.toFinsupp
              (l : Multiset (Fin n))).sum
                (fun _ m ↦ m) := by
                  symm
                  apply Finsupp.sum_fintype
                  intro i
                  rfl
        _ = (l : Multiset (Fin n)).card :=
          Multiset.toFinsupp_sum_eq (l : Multiset (Fin n))
        _ = l.length := rfl
        _ = k := hl
    · intro i _
      exact Finset.mem_univ i⟩

@[simp]
theorem multiIndexOfList_apply
    {n k : ℕ} (l : List (Fin n)) (hl : l.length = k)
    (i : Fin n) :
    (multiIndexOfList l hl).1 i = l.count i := by
  simp [multiIndexOfList, Multiset.toFinsupp_apply]

/-- A canonical ordered list containing each source variable with the
multiplicity prescribed by `e`. -/
noncomputable def exponentList
    {n : ℕ} (e : Fin n →₀ ℕ) : List (Fin n) :=
  (Finsupp.toMultiset e).sort (· ≤ ·)

/-- The length of `exponentList e` is the total degree of `e`. -/
theorem exponentList_length
    {n : ℕ} (e : Fin n →₀ ℕ) :
    (exponentList e).length = Finsupp.degree e := by
  rw [exponentList, Multiset.length_sort,
    Finsupp.card_toMultiset]
  rfl

/-- Data witnessing a decomposition of a degree-`3k` exponent vector into
three degree-`k` multiindices. -/
structure CubicFactorization
    {n : ℕ} (k : ℕ) (e : Fin n →₀ ℕ) where
  first : MultiIndex n k
  second : MultiIndex n k
  third : MultiIndex n k
  sum_eq :
    ∀ i, first.1 i + second.1 i + third.1 i = e i

/-- The explicit three-block factorization of a degree-`3k` exponent. -/
noncomputable def cubicFactorization
    {n k : ℕ} (e : Fin n →₀ ℕ)
    (hdegree : Finsupp.degree e = 3 * k) :
    CubicFactorization k e := by
  let L := exponentList e
  have hL : L.length = 3 * k := by
    rw [show L.length = Finsupp.degree e by
      exact exponentList_length e]
    exact hdegree
  have hfirst : (L.take k).length = k := by
    simp only [List.length_take, hL]
    omega
  have hdrop : (L.drop k).length = 2 * k := by
    simp only [List.length_drop, hL]
    omega
  have hsecond : ((L.drop k).take k).length = k := by
    simp only [List.length_take, hdrop]
    omega
  have hthird : ((L.drop k).drop k).length = k := by
    simp only [List.length_drop, hdrop]
    omega
  refine
    ⟨multiIndexOfList (L.take k) hfirst,
      multiIndexOfList ((L.drop k).take k) hsecond,
      multiIndexOfList ((L.drop k).drop k) hthird, ?_⟩
  intro i
  simp only [multiIndexOfList_apply]
  have hdecomp :
      L.take k ++ (L.drop k).take k ++
          (L.drop k).drop k = L := by
    rw [List.append_assoc, List.take_append_drop,
      List.take_append_drop]
  have hcounts := congrArg (List.count i) hdecomp
  simp only [List.count_append] at hcounts
  rw [hcounts]
  have hsort :
      (↑L : Multiset (Fin n)) = Finsupp.toMultiset e :=
    Multiset.sort_eq (Finsupp.toMultiset e) (· ≤ ·)
  have hcount :=
    congrArg (fun s : Multiset (Fin n) ↦ s.count i) hsort
  change
    Multiset.count i (↑L : Multiset (Fin n)) =
      Multiset.count i (Finsupp.toMultiset e) at hcount
  rw [Multiset.coe_count, Finsupp.count_toMultiset] at hcount
  exact hcount

/-- The cubic target monomial associated with a three-block
factorization. -/
noncomputable def cubicCoordinateMonomial
    {n k : ℕ} {e : Fin n →₀ ℕ}
    (f : CubicFactorization k e) :
    MvPolynomial (MultiIndex n k) ℚ :=
  MvPolynomial.X f.first *
    MvPolynomial.X f.second *
      MvPolynomial.X f.third

/-- Each factorized target monomial is homogeneous cubic. -/
theorem cubicCoordinateMonomial_isHomogeneous
    {n k : ℕ} {e : Fin n →₀ ℕ}
    (f : CubicFactorization k e) :
    (cubicCoordinateMonomial f).IsHomogeneous 3 := by
  unfold cubicCoordinateMonomial
  have hfirstSecond :=
    (MvPolynomial.isHomogeneous_X (R := ℚ) f.first).mul
      (MvPolynomial.isHomogeneous_X (R := ℚ) f.second)
  have hall :=
    hfirstSecond.mul
      (MvPolynomial.isHomogeneous_X (R := ℚ) f.third)
  norm_num at hall ⊢
  exact hall

/-- Substitution by the Veronese map turns the factorized cubic monomial
back into the original source monomial. -/
theorem eval₂Hom_cubicCoordinateMonomial_veronese
    {S : Type*} [CommRing S] [Algebra ℚ S]
    {e : Fin n →₀ ℕ}
    (f : CubicFactorization k e) (x : Fin n → S) :
    MvPolynomial.eval₂Hom (algebraMap ℚ S)
        (veroneseMap (k := k) x)
        (cubicCoordinateMonomial f) =
      e.prod (fun i m ↦ x i ^ m) := by
  simp only [cubicCoordinateMonomial, map_mul,
    MvPolynomial.eval₂Hom_X']
  rw [Finsupp.prod_fintype]
  · simp only [veroneseMap_apply]
    rw [← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_add, ← pow_add, f.sum_eq i]
  · intro i
    simp

/-- Lift one source exponent to a cubic target monomial when its degree is
`3k`, and to zero otherwise.  The conditional makes this a total
coefficient-level operation on arbitrary polynomials. -/
noncomputable def cubicLiftMonomial
    {n : ℕ} (k : ℕ) (e : Fin n →₀ ℕ) :
    MvPolynomial (MultiIndex n k) ℚ :=
  if hdegree : Finsupp.degree e = 3 * k then
    cubicCoordinateMonomial (cubicFactorization e hdegree)
  else
    0

/-- Every output of the total monomial lift is homogeneous cubic, including
the zero output used for source monomials of the wrong degree. -/
theorem cubicLiftMonomial_isHomogeneous
    {n : ℕ} (k : ℕ) (e : Fin n →₀ ℕ) :
    (cubicLiftMonomial k e).IsHomogeneous 3 := by
  by_cases hdegree : Finsupp.degree e = 3 * k
  · rw [cubicLiftMonomial, dif_pos hdegree]
    exact cubicCoordinateMonomial_isHomogeneous _
  · rw [cubicLiftMonomial, dif_neg hdegree]
    exact MvPolynomial.isHomogeneous_zero _ _ 3

/-- Exact evaluation of a correctly graded lifted monomial. -/
theorem eval₂Hom_cubicLiftMonomial_veronese
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (e : Fin n →₀ ℕ)
    (hdegree : Finsupp.degree e = 3 * k)
    (x : Fin n → S) :
    MvPolynomial.eval₂Hom (algebraMap ℚ S)
        (veroneseMap (k := k) x)
        (cubicLiftMonomial k e) =
      e.prod (fun i m ↦ x i ^ m) := by
  rw [cubicLiftMonomial, dif_pos hdegree]
  exact eval₂Hom_cubicCoordinateMonomial_veronese _ x

/-- Coefficientwise cubic lift of a rational source polynomial.

Only its degree-`3k` monomials survive.  For a homogeneous polynomial of
that degree, no term is discarded. -/
noncomputable def cubicLiftPolynomial
    {n : ℕ} (k : ℕ) (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial (MultiIndex n k) ℚ :=
  ∑ e ∈ p.support,
    MvPolynomial.C (p.coeff e) * cubicLiftMonomial k e

/-- The coefficientwise lift is always a homogeneous cubic target
polynomial. -/
theorem cubicLiftPolynomial_isHomogeneous
    {n : ℕ} (k : ℕ) (p : MvPolynomial (Fin n) ℚ) :
    (cubicLiftPolynomial k p).IsHomogeneous 3 := by
  unfold cubicLiftPolynomial
  refine MvPolynomial.IsHomogeneous.sum p.support
    (fun e ↦
      MvPolynomial.C (p.coeff e) *
        cubicLiftMonomial k e) 3 ?_
  intro e _
  exact (cubicLiftMonomial_isHomogeneous k e).C_mul _

/-- A homogeneous degree-`d` polynomial has only degree-`d` exponent
vectors in its support. -/
theorem finsuppDegree_eq_of_isHomogeneous
    {p : MvPolynomial (Fin n) ℚ} {d : ℕ}
    (hp : p.IsHomogeneous d) {e : Fin n →₀ ℕ}
    (he : e ∈ p.support) :
    Finsupp.degree e = d := by
  rw [Finsupp.degree_eq_weight_one]
  exact hp (MvPolynomial.mem_support_iff.mp he)

/-- Exact substitution theorem for the coefficientwise cubic lift. -/
theorem eval₂Hom_cubicLiftPolynomial_veronese
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (p : MvPolynomial (Fin n) ℚ)
    (hp : p.IsHomogeneous (3 * k))
    (x : Fin n → S) :
    MvPolynomial.eval₂Hom (algebraMap ℚ S)
        (veroneseMap (k := k) x)
        (cubicLiftPolynomial k p) =
      MvPolynomial.eval₂Hom (algebraMap ℚ S) x p := by
  calc
    _ =
        ∑ e ∈ p.support,
          algebraMap ℚ S (p.coeff e) *
            e.prod (fun i m ↦ x i ^ m) := by
      simp only [cubicLiftPolynomial, map_sum, map_mul,
        MvPolynomial.eval₂Hom_C]
      apply Finset.sum_congr rfl
      intro e he
      rw [eval₂Hom_cubicLiftMonomial_veronese e
        (finsuppDegree_eq_of_isHomogeneous hp he)]
    _ =
        ∑ e ∈ p.support,
          MvPolynomial.eval₂Hom (algebraMap ℚ S) x
            (MvPolynomial.monomial e (p.coeff e)) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [MvPolynomial.eval₂Hom_monomial]
    _ = MvPolynomial.eval₂Hom (algebraMap ℚ S) x p := by
      simpa only [map_sum] using
        congrArg
          (MvPolynomial.eval₂Hom (algebraMap ℚ S) x)
          (MvPolynomial.as_sum p).symm

/-! ## The transported source field `Dνₖ F` -/

/-- The finitely supported exponent corresponding to a bundled
multiindex. -/
noncomputable def multiIndexFinsupp
    (a : MultiIndex n k) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm a.1

@[simp]
theorem multiIndexFinsupp_apply
    (a : MultiIndex n k) (i : Fin n) :
    multiIndexFinsupp a i = a.1 i := by
  simp [multiIndexFinsupp]

theorem multiIndexFinsupp_degree
    (a : MultiIndex n k) :
    Finsupp.degree (multiIndexFinsupp a) = k := by
  rw [Finsupp.degree_eq_sum]
  simp only [multiIndexFinsupp_apply]
  exact multiIndex_degree a

/-- The source polynomial `x^a` belonging to a Veronese coordinate. -/
noncomputable def sourceVeronesePolynomial
    (a : MultiIndex n k) : MvPolynomial (Fin n) ℚ :=
  MvPolynomial.monomial (multiIndexFinsupp a) 1

theorem sourceVeronesePolynomial_isHomogeneous
    (a : MultiIndex n k) :
    (sourceVeronesePolynomial a).IsHomogeneous k :=
  MvPolynomial.isHomogeneous_monomial 1
    (multiIndexFinsupp_degree a)

/-- Evaluation of the source polynomial is the corresponding monomial. -/
theorem eval₂Hom_sourceVeronesePolynomial
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (a : MultiIndex n k) (x : Fin n → S) :
    MvPolynomial.eval₂Hom (algebraMap ℚ S) x
        (sourceVeronesePolynomial a) =
      monomial x a := by
  simp only [sourceVeronesePolynomial,
    MvPolynomial.eval₂Hom_monomial, map_one, one_mul,
    monomial]
  rw [Finsupp.prod_fintype]
  · simp only [multiIndexFinsupp_apply]
  · intro i
    simp

/-- Coordinate formula for the evaluated formal derivative of `x^a`. -/
theorem eval₂Hom_pderiv_sourceVeronesePolynomial
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (a : MultiIndex n k) (x : Fin n → S) (i : Fin n) :
    MvPolynomial.eval₂Hom (algebraMap ℚ S) x
        (MvPolynomial.pderiv i (sourceVeronesePolynomial a)) =
      (a.1 i : S) * x i ^ (a.1 i - 1) *
        (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          x j ^ a.1 j) := by
  simp only [sourceVeronesePolynomial,
    MvPolynomial.pderiv_monomial,
    MvPolynomial.eval₂Hom_monomial, map_mul]
  simp only [map_one, one_mul, map_natCast]
  rw [Finsupp.prod_fintype]
  · have hp :=
      Finset.mul_prod_erase
        (Finset.univ : Finset (Fin n))
        (fun j ↦
          x j ^
            (((multiIndexFinsupp a -
                Finsupp.single i 1) : Fin n →₀ ℕ) j))
        (Finset.mem_univ i)
    rw [← hp]
    simp only [multiIndexFinsupp_apply]
    have hi :
        ((multiIndexFinsupp a -
            Finsupp.single i 1) : Fin n →₀ ℕ) i =
          a.1 i - 1 := by
      simp
    have hprod :
        (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          x j ^
            (((multiIndexFinsupp a -
                Finsupp.single i 1) : Fin n →₀ ℕ) j)) =
        ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          x j ^ a.1 j := by
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      have hjexp :
          ((multiIndexFinsupp a -
              Finsupp.single i 1) : Fin n →₀ ℕ) j =
            a.1 j := by
        simp [hji]
      rw [hjexp]
    change
      (a.1 i : S) *
          (x i ^
              (((multiIndexFinsupp a -
                  Finsupp.single i 1) : Fin n →₀ ℕ) i) *
            ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
              x j ^
                (((multiIndexFinsupp a -
                    Finsupp.single i 1) : Fin n →₀ ℕ) j)) =
        _
    rw [hi, hprod]
    ring
  · intro j
    simp

/-- Evaluate a rational source vector field over a commutative
`ℚ`-algebra. -/
noncomputable def evalSourceField
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (F : HGAS.PolynomialField n) (x : Fin n → S) :
    Fin n → S :=
  fun i ↦ MvPolynomial.eval₂Hom (algebraMap ℚ S) x (F i)

@[simp]
theorem evalSourceField_apply
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (F : HGAS.PolynomialField n) (x : Fin n → S)
    (i : Fin n) :
    evalSourceField F x i =
      MvPolynomial.eval₂Hom (algebraMap ℚ S) x (F i) :=
  rfl

/-- Equation (16.1), represented as a source polynomial:
the `a`-coordinate of `Dνₖ(x)F(x)`. -/
noncomputable def transportedSourcePolynomial
    (F : HGAS.PolynomialField n) (a : MultiIndex n k) :
    MvPolynomial (Fin n) ℚ :=
  ∑ i,
    MvPolynomial.pderiv i (sourceVeronesePolynomial a) *
      F i

/-- The coordinate polynomial in (16.1) has source degree `3k` when
`F` has degree `2k+1` and `k ≥ 1`. -/
theorem transportedSourcePolynomial_isHomogeneous
    (F : HGAS.PolynomialField n)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k) (a : MultiIndex n k) :
    (transportedSourcePolynomial F a).IsHomogeneous
      (3 * k) := by
  unfold transportedSourcePolynomial
  refine MvPolynomial.IsHomogeneous.sum Finset.univ
    (fun i ↦
      MvPolynomial.pderiv i (sourceVeronesePolynomial a) *
        F i) (3 * k) ?_
  intro i _
  have hp :=
    (sourceVeronesePolynomial_isHomogeneous a).pderiv
      (i := i)
  have hm := hp.mul (hF i)
  have hdegree :
      (k - 1) + (2 * k + 1) = 3 * k := by
    omega
  rw [← hdegree]
  exact hm

/-- Evaluation of the transported source polynomial is exactly the
coordinate formula for `Dνₖ(x)F(x)`. -/
theorem eval₂Hom_transportedSourcePolynomial
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (F : HGAS.PolynomialField n)
    (a : MultiIndex n k) (x : Fin n → S) :
    MvPolynomial.eval₂Hom (algebraMap ℚ S) x
        (transportedSourcePolynomial F a) =
      dMonomial x (evalSourceField F x) a := by
  simp only [transportedSourcePolynomial, map_sum, map_mul,
    dMonomial, evalSourceField]
  apply Finset.sum_congr rfl
  intro i _
  rw [eval₂Hom_pderiv_sourceVeronesePolynomial]
  ring

/-! ## The ambient cubic lift `G` -/

/-- Equation (16.2): apply the coefficientwise monomial factorization to
every coordinate of the transported source field. -/
noncomputable def cubicLiftField
    (F : HGAS.PolynomialField n) :
    RationalCoordinateField (MultiIndex n k) :=
  fun a ↦ cubicLiftPolynomial k
    (transportedSourcePolynomial F a)

/-- The lifted field is a rational homogeneous cubic field. -/
theorem cubicLiftField_isHomogeneous
    (F : HGAS.PolynomialField n) :
    IsHomogeneousCoordinateField 3
      (cubicLiftField (k := k) F) := by
  intro a
  exact cubicLiftPolynomial_isHomogeneous k
    (transportedSourcePolynomial F a)

/-- Equation (16.3), over every commutative `ℚ`-algebra. -/
theorem eval_cubicLiftField_veronese
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (F : HGAS.PolynomialField n)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k) (x : Fin n → S) :
    evalCoordinateField (cubicLiftField (k := k) F)
        (veroneseMap (k := k) x) =
      dVeronese x (evalSourceField F x) := by
  funext a
  rw [evalCoordinateField_apply, cubicLiftField,
    eval₂Hom_cubicLiftPolynomial_veronese
      (transportedSourcePolynomial F a)
      (transportedSourcePolynomial_isHomogeneous
        F hF hk a)]
  exact eval₂Hom_transportedSourcePolynomial F a x

/-- Signed form of (16.3).  Cubic homogeneity makes the lifted vector at
`-νₖ(x)` the negative of the transported vector. -/
theorem eval_cubicLiftField_neg_veronese
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (F : HGAS.PolynomialField n)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k) (x : Fin n → S) :
    evalCoordinateField (cubicLiftField (k := k) F)
        (-veroneseMap (k := k) x) =
      -dVeronese x (evalSourceField F x) := by
  have hscale :=
    evalCoordinateField_smul
      (cubicLiftField_isHomogeneous (k := k) F)
      (-1 : S) (veroneseMap (k := k) x)
  rw [eval_cubicLiftField_veronese F hF hk x] at hscale
  have hneg :
      (-1 : S) ^ 3 •
          dVeronese (k := k) x (evalSourceField F x) =
        -dVeronese (k := k) x (evalSourceField F x) := by
    funext a
    simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  rw [hneg] at hscale
  simpa using hscale

/-! ## Tangency on the explicitly parametrized Veronese sheets -/

/-- Algebraic directional derivative of a rational source polynomial. -/
noncomputable def sourcePolynomialDirectional
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (p : MvPolynomial (Fin n) ℚ)
    (x h : Fin n → S) : S :=
  ∑ i,
    MvPolynomial.eval₂Hom (algebraMap ℚ S) x
        (MvPolynomial.pderiv i p) *
      h i

theorem sourcePolynomialDirectional_mul
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (p q : MvPolynomial (Fin n) ℚ)
    (x h : Fin n → S) :
    sourcePolynomialDirectional (p * q) x h =
      sourcePolynomialDirectional p x h *
          MvPolynomial.eval₂Hom (algebraMap ℚ S) x q +
        MvPolynomial.eval₂Hom (algebraMap ℚ S) x p *
          sourcePolynomialDirectional q x h := by
  simp only [sourcePolynomialDirectional,
    MvPolynomial.pderiv_mul, map_add, map_mul, add_mul,
    Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem sourcePolynomialDirectional_sub
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (p q : MvPolynomial (Fin n) ℚ)
    (x h : Fin n → S) :
    sourcePolynomialDirectional (p - q) x h =
      sourcePolynomialDirectional p x h -
        sourcePolynomialDirectional q x h := by
  simp only [sourcePolynomialDirectional, map_sub, sub_mul,
    Finset.sum_sub_distrib]

theorem sourcePolynomialDirectional_sourceVeronesePolynomial
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (a : MultiIndex n k) (x h : Fin n → S) :
    sourcePolynomialDirectional
        (sourceVeronesePolynomial a) x h =
      dMonomial x h a := by
  simp only [sourcePolynomialDirectional, dMonomial]
  apply Finset.sum_congr rfl
  intro i _
  rw [eval₂Hom_pderiv_sourceVeronesePolynomial]
  ring

/-- Balanced target quadrics come from literal equalities of source
monomial products. -/
theorem sourceVeronesePolynomial_relation
    (r : ToricRelationIndex n k) :
    sourceVeronesePolynomial r.alpha *
        sourceVeronesePolynomial r.beta =
      sourceVeronesePolynomial r.gamma *
        sourceVeronesePolynomial r.delta := by
  have hfs :
      multiIndexFinsupp r.alpha +
          multiIndexFinsupp r.beta =
        multiIndexFinsupp r.gamma +
          multiIndexFinsupp r.delta := by
    ext i
    simp only [Finsupp.add_apply, multiIndexFinsupp_apply]
    exact r.balanced i
  simp only [sourceVeronesePolynomial,
    MvPolynomial.monomial_mul, one_mul]
  rw [hfs]

/-- Directional differential of an indexed quadratic target relation. -/
def toricRelationDifferential
    {R : Type*} [CommRing R]
    (r : ToricRelationIndex n k)
    (y h : MultiIndex n k → R) : R :=
  h r.alpha * y r.beta +
      y r.alpha * h r.beta -
    (h r.gamma * y r.delta +
      y r.gamma * h r.delta)

/-- The differential of every quadratic relation vanishes along the
transported tangent vector `Dνₖ(x)h`. -/
theorem toricRelationDifferential_veronese_dVeronese
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (r : ToricRelationIndex n k)
    (x h : Fin n → S) :
    toricRelationDifferential r
        (veroneseMap (k := k) x) (dVeronese x h) = 0 := by
  have hzero :
      sourcePolynomialDirectional
          (sourceVeronesePolynomial r.alpha *
              sourceVeronesePolynomial r.beta -
            sourceVeronesePolynomial r.gamma *
              sourceVeronesePolynomial r.delta) x h = 0 := by
    rw [sourceVeronesePolynomial_relation r]
    simp [sourcePolynomialDirectional]
  rw [sourcePolynomialDirectional_sub,
    sourcePolynomialDirectional_mul,
    sourcePolynomialDirectional_mul,
    sourcePolynomialDirectional_sourceVeronesePolynomial,
    sourcePolynomialDirectional_sourceVeronesePolynomial,
    sourcePolynomialDirectional_sourceVeronesePolynomial,
    sourcePolynomialDirectional_sourceVeronesePolynomial,
    eval₂Hom_sourceVeronesePolynomial,
    eval₂Hom_sourceVeronesePolynomial,
    eval₂Hom_sourceVeronesePolynomial,
    eval₂Hom_sourceVeronesePolynomial] at hzero
  simpa [toricRelationDifferential, dVeronese, monomial] using hzero

/-- Negating both the base point and direction leaves the differential of
a quadratic relation unchanged. -/
@[simp]
theorem toricRelationDifferential_neg_neg
    {R : Type*} [CommRing R]
    (r : ToricRelationIndex n k)
    (y h : MultiIndex n k → R) :
    toricRelationDifferential r (-y) (-h) =
      toricRelationDifferential r y h := by
  simp only [toricRelationDifferential, Pi.neg_apply]
  ring

/-- The cubic lift is tangent to every indexed relation on the positive
Veronese sheet. -/
theorem toricRelationDifferential_cubicLiftField_veronese
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (F : HGAS.PolynomialField n)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k) (r : ToricRelationIndex n k)
    (x : Fin n → S) :
    toricRelationDifferential r
        (veroneseMap (k := k) x)
        (evalCoordinateField (cubicLiftField (k := k) F)
          (veroneseMap (k := k) x)) = 0 := by
  rw [eval_cubicLiftField_veronese F hF hk x]
  exact toricRelationDifferential_veronese_dVeronese
    r x (evalSourceField F x)

/-- The same tangency identity holds on the negative sheet. -/
theorem toricRelationDifferential_cubicLiftField_neg_veronese
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (F : HGAS.PolynomialField n)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k) (r : ToricRelationIndex n k)
    (x : Fin n → S) :
    toricRelationDifferential r
        (-veroneseMap (k := k) x)
        (evalCoordinateField (cubicLiftField (k := k) F)
          (-veroneseMap (k := k) x)) = 0 := by
  rw [eval_cubicLiftField_neg_veronese F hF hk x]
  rw [toricRelationDifferential_neg_neg]
  exact toricRelationDifferential_veronese_dVeronese
    r x (evalSourceField F x)

/-! ## Cubic weighted gradient of the quartic constraint penalty -/

/-- The ordinary formal partial derivative of the rational toric penalty. -/
noncomputable def ordinaryPenaltyGradientPolynomial
    (n k : ℕ) (a : MultiIndex n k) :
    MvPolynomial (MultiIndex n k) ℚ :=
  MvPolynomial.pderiv a (toricPenaltyPolynomial n k)

/-- The `Q`-metric gradient divides the ordinary partial derivative by the
positive multinomial weight.  This is a rational polynomial coordinate. -/
noncomputable def penaltyQGradientPolynomial
    (n k : ℕ) (a : MultiIndex n k) :
    MvPolynomial (MultiIndex n k) ℚ :=
  MvPolynomial.C ((multinomialWeight a : ℚ)⁻¹) *
    ordinaryPenaltyGradientPolynomial n k a

/-- The rational polynomial field `grad_Q W`. -/
noncomputable def penaltyQGradientField
    (n k : ℕ) :
    RationalCoordinateField (MultiIndex n k) :=
  fun a ↦ penaltyQGradientPolynomial n k a

/-- Every coordinate of the weighted penalty gradient is homogeneous
cubic. -/
theorem penaltyQGradientPolynomial_isHomogeneous
    (a : MultiIndex n k) :
    (penaltyQGradientPolynomial n k a).IsHomogeneous 3 := by
  unfold penaltyQGradientPolynomial
  exact
    ((toricPenaltyPolynomial_isHomogeneous n k).pderiv
      (i := a)).C_mul _

theorem penaltyQGradientField_isHomogeneous (n k : ℕ) :
    IsHomogeneousCoordinateField 3
      (penaltyQGradientField n k) := by
  intro a
  exact penaltyQGradientPolynomial_isHomogeneous a

/-- Formal derivative of the sum-of-squares penalty. -/
theorem eval₂Hom_pderiv_toricPenaltyPolynomial
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (y : MultiIndex n k → S) (a : MultiIndex n k) :
    MvPolynomial.eval₂Hom (algebraMap ℚ S) y
        (MvPolynomial.pderiv a
          (toricPenaltyPolynomial n k)) =
      ∑ r : ToricRelationIndex n k,
        2 *
          MvPolynomial.eval₂Hom (algebraMap ℚ S) y
            (toricBinomial r) *
          MvPolynomial.eval₂Hom (algebraMap ℚ S) y
            (MvPolynomial.pderiv a (toricBinomial r)) := by
  simp only [toricPenaltyPolynomial, map_sum,
    MvPolynomial.pderiv_pow, map_mul]
  apply Finset.sum_congr rfl
  intro r _
  norm_num

/-- Generic-algebra evaluation of a rational toric binomial. -/
theorem eval₂Hom_toricBinomial
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (r : ToricRelationIndex n k)
    (y : MultiIndex n k → S) :
    MvPolynomial.eval₂Hom (algebraMap ℚ S) y
        (toricBinomial r) =
      toricRelation r y := by
  simp [toricBinomial, toricRelation]

/-- All ordinary partial derivatives of the sum-of-squares penalty vanish
at a common zero of the quadratic family. -/
theorem eval₂Hom_pderiv_toricPenaltyPolynomial_eq_zero
    {S : Type*} [CommRing S] [Algebra ℚ S]
    {y : MultiIndex n k → S}
    (hy : y ∈ toricZeroSet (R := S) n k)
    (a : MultiIndex n k) :
    MvPolynomial.eval₂Hom (algebraMap ℚ S) y
        (MvPolynomial.pderiv a
          (toricPenaltyPolynomial n k)) = 0 := by
  rw [eval₂Hom_pderiv_toricPenaltyPolynomial]
  apply Finset.sum_eq_zero
  intro r _
  rw [eval₂Hom_toricBinomial, hy r]
  ring

/-- The weighted penalty-gradient field vanishes on the complete
quadratic zero set. -/
theorem eval_penaltyQGradientField_eq_zero
    {S : Type*} [CommRing S] [Algebra ℚ S]
    {y : MultiIndex n k → S}
    (hy : y ∈ toricZeroSet (R := S) n k) :
    evalCoordinateField (penaltyQGradientField n k) y = 0 := by
  funext a
  simp only [evalCoordinateField_apply,
    penaltyQGradientField, penaltyQGradientPolynomial,
    ordinaryPenaltyGradientPolynomial, map_mul,
    MvPolynomial.eval₂Hom_C, Pi.zero_apply]
  rw [eval₂Hom_pderiv_toricPenaltyPolynomial_eq_zero hy]
  ring

/-- The ordinary real gradient obtained by evaluating the rational formal
partial derivatives. -/
noncomputable def ordinaryPenaltyGradientReal
    (y : MultiIndex n k → ℝ) :
    MultiIndex n k → ℝ :=
  fun a ↦
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) y
      (ordinaryPenaltyGradientPolynomial n k a)

/-- Evaluation of the rational polynomial field agrees exactly with the
weighted-gradient coordinate formula from equation (15.8). -/
theorem eval_penaltyQGradientField_real
    (y : MultiIndex n k → ℝ) :
    evalCoordinateField (penaltyQGradientField n k) y =
      ambientQGradient (ordinaryPenaltyGradientReal y) := by
  funext a
  simp only [evalCoordinateField_apply,
    penaltyQGradientField, penaltyQGradientPolynomial,
    map_mul, MvPolynomial.eval₂Hom_C,
    ordinaryPenaltyGradientReal, ambientQGradient_apply]
  rw [map_inv₀]
  simp only [map_natCast]
  rw [div_eq_mul_inv]
  ring

/-! ## The rational stabilized cubic field -/

/-- Add the cubic constraint-penalty contribution with rational gain `K`.
This is the polynomial field `G - K grad_Q W`. -/
noncomputable def stabilizedCubicField
    (F : HGAS.PolynomialField n) (K : ℚ) :
    RationalCoordinateField (MultiIndex n k) :=
  fun a ↦
    cubicLiftField (k := k) F a -
      MvPolynomial.C K * penaltyQGradientField n k a

/-- The stabilized field still has rational homogeneous cubic
coordinates. -/
theorem stabilizedCubicField_isHomogeneous
    (F : HGAS.PolynomialField n) (K : ℚ) :
    IsHomogeneousCoordinateField 3
      (stabilizedCubicField (k := k) F K) := by
  intro a
  exact
    (cubicLiftField_isHomogeneous (k := k) F a).sub
      ((penaltyQGradientField_isHomogeneous n k a).C_mul K)

/-- On the common zero set, the penalty contribution is zero and the
stabilized field agrees with the pure cubic lift. -/
theorem eval_stabilizedCubicField_of_mem_toricZeroSet
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (F : HGAS.PolynomialField n) (K : ℚ)
    {y : MultiIndex n k → S}
    (hy : y ∈ toricZeroSet (R := S) n k) :
    evalCoordinateField (stabilizedCubicField
        (k := k) F K) y =
      evalCoordinateField (cubicLiftField (k := k) F) y := by
  have hgradient :=
    eval_penaltyQGradientField_eq_zero
      (n := n) (k := k) hy
  funext a
  have ha :
      MvPolynomial.eval₂Hom (algebraMap ℚ S) y
          (penaltyQGradientField n k a) = 0 := by
    simpa only [evalCoordinateField_apply, Pi.zero_apply] using
      congrFun hgradient a
  simp only [evalCoordinateField_apply,
    stabilizedCubicField, map_sub, map_mul,
    MvPolynomial.eval₂Hom_C]
  rw [ha]
  ring

/-- Exact stabilized lift identity on the positive signed sheet. -/
theorem eval_stabilizedCubicField_veronese
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (F : HGAS.PolynomialField n)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k) (K : ℚ) (x : Fin n → S) :
    evalCoordinateField
        (stabilizedCubicField (k := k) F K)
        (veroneseMap (k := k) x) =
      dVeronese x (evalSourceField F x) := by
  rw [eval_stabilizedCubicField_of_mem_toricZeroSet
    F K (veronese_mem_toricZeroSet x)]
  exact eval_cubicLiftField_veronese F hF hk x

/-- Exact stabilized lift identity on the negative signed sheet. -/
theorem eval_stabilizedCubicField_neg_veronese
    {S : Type*} [CommRing S] [Algebra ℚ S]
    (F : HGAS.PolynomialField n)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k) (K : ℚ) (x : Fin n → S) :
    evalCoordinateField
        (stabilizedCubicField (k := k) F K)
        (-veroneseMap (k := k) x) =
      -dVeronese x (evalSourceField F x) := by
  rw [eval_stabilizedCubicField_of_mem_toricZeroSet
    F K (neg_veronese_mem_toricZeroSet x)]
  exact eval_cubicLiftField_neg_veronese F hF hk x

end HGAS.Veronese
