import HGAS.Veronese.CubicLiftGASConjugacy
import HGAS.Computability.HGASLanguage
import HGAS.Foundation.PolynomialDifferentiationCode
import Mathlib.Computability.Primrec.List
import Mathlib.Tactic

/-!
# A finite-code compiler for the stabilized cubic Veronese lift

This module turns the semantic cubic construction into an actual operation
on finite sparse rational polynomial codes.  For fixed source dimension
`n` and Veronese order `k`, its target dimension is the cardinality of the
degree-`k` multiindex type.  The main design choice is to enumerate every
source exponent of degree `3*k` and extract its coefficient from the raw
input code.  This automatically combines duplicate monomials and
cancellations before emitting the corresponding canonical cubic target
monomial.

The equivalences between finite multiindex types and `Fin` are allowed to
be chosen noncanonically.  This does not compromise effectivity at fixed
`n,k`: every map out of a fixed `Fin` type is primitive recursive, and all
chosen finite tables are constants in the resulting program.

The fixed toric penalty field is likewise stored as a finite constant.
Only the source field and the rational gain vary.  We prove:

* exact decoding of the coefficientwise cubic lift;
* primitive recursiveness of the pure and stabilized field compilers;
* exact decoding as a coordinate renaming of `stabilizedCubicField`;
* unconditional cubic homogeneity of every compiled output;
* equality of the realized target field with the linear conjugate of the
  semantic stabilized field, hence exact preservation of GAS under the
  finite coordinate reindexing.

Selecting a sufficiently large gain as a computable function of the input
field is deliberately a separate quantitative theorem.
-/

namespace HGAS.Veronese

noncomputable section

def cubicLiftCodeDimension (n k : ℕ) : ℕ :=
  Fintype.card (MultiIndex n k)

def cubicLiftIndexEquiv (n k : ℕ) :
    MultiIndex n k ≃ Fin (cubicLiftCodeDimension n k) :=
  Fintype.equivFin _

def cubicLiftReindexEquiv (n k : ℕ) :
    (MultiIndex n k → ℝ) ≃L[ℝ]
      (Fin (cubicLiftCodeDimension n k) → ℝ) :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ => ℝ)
    (cubicLiftIndexEquiv n k)

@[simp] theorem cubicLiftReindexEquiv_apply
    (n k : ℕ) (x : MultiIndex n k → ℝ)
    (j : Fin (cubicLiftCodeDimension n k)) :
    cubicLiftReindexEquiv n k x j =
      x ((cubicLiftIndexEquiv n k).symm j) := by
  change
    (Equiv.piCongrLeft (fun _ => ℝ)
      (cubicLiftIndexEquiv n k)) x j =
      x ((cubicLiftIndexEquiv n k).symm j)
  rw [Equiv.piCongrLeft_apply]
  simp

def degreeIndexEquiv (n d : ℕ) :
    MultiIndex n d ≃ Fin (cubicLiftCodeDimension n d) :=
  cubicLiftIndexEquiv n d

def sourceExponentAt (n d : ℕ)
    (j : Fin (cubicLiftCodeDimension n d)) : HGAS.ExponentCode n :=
  (degreeIndexEquiv n d).symm j |>.1

theorem sourceExponentAt_primrec (n d : ℕ) :
    Primrec (sourceExponentAt n d) :=
  Primrec.dom_finite _

def targetCubicExponent
    (e : MultiIndex n k ≃ Fin (cubicLiftCodeDimension n k))
    (a : MultiIndex n (3 * k)) :
    HGAS.ExponentCode (cubicLiftCodeDimension n k) :=
  let f := cubicFactorization (multiIndexFinsupp a)
    (multiIndexFinsupp_degree a)
  HGAS.ExponentCode.encode
    (Finsupp.single (e f.first) 1 +
      Finsupp.single (e f.second) 1 +
      Finsupp.single (e f.third) 1)

def targetCubicExponentAt (n k : ℕ)
    (j : Fin (cubicLiftCodeDimension n (3 * k))) :
    HGAS.ExponentCode (cubicLiftCodeDimension n k) :=
  targetCubicExponent (cubicLiftIndexEquiv n k)
    ((degreeIndexEquiv n (3 * k)).symm j)

theorem targetCubicExponentAt_primrec (n k : ℕ) :
    Primrec (targetCubicExponentAt n k) :=
  Primrec.dom_finite _

def cubicLiftPolynomialCode (n k : ℕ)
    (p : HGAS.PolynomialCode n) :
    HGAS.PolynomialCode (cubicLiftCodeDimension n k) :=
  List.ofFn fun j : Fin (cubicLiftCodeDimension n (3 * k)) =>
    (targetCubicExponentAt n k j,
      HGAS.PolynomialCode.coefficient (sourceExponentAt n (3 * k) j) p)

theorem cubicLiftPolynomialCode_primrec (n k : ℕ) :
    Primrec (cubicLiftPolynomialCode n k) := by
  apply Primrec.list_ofFn
  intro j
  exact Primrec.pair
    (Primrec.const (targetCubicExponentAt n k j))
    (HGAS.PolynomialCode.coefficient_primrec.comp
      (Primrec.const (sourceExponentAt n (3 * k) j))
      Primrec.id)

@[simp] theorem decode_targetCubicExponent
    (e : MultiIndex n k ≃ Fin (cubicLiftCodeDimension n k))
    (a : MultiIndex n (3 * k)) :
    HGAS.ExponentCode.decode (targetCubicExponent e a) =
      Finsupp.single
          (e (cubicFactorization (multiIndexFinsupp a)
            (multiIndexFinsupp_degree a)).first) 1 +
        Finsupp.single
          (e (cubicFactorization (multiIndexFinsupp a)
            (multiIndexFinsupp_degree a)).second) 1 +
        Finsupp.single
          (e (cubicFactorization (multiIndexFinsupp a)
            (multiIndexFinsupp_degree a)).third) 1 := by
  simp [targetCubicExponent]

theorem decode_targetCubicMonomial
    (e : MultiIndex n k ≃ Fin (cubicLiftCodeDimension n k))
    (a : MultiIndex n (3 * k)) :
    HGAS.PolynomialCode.decode
        ([(targetCubicExponent e a, HGAS.RationalCode.one)] :
          HGAS.PolynomialCode (cubicLiftCodeDimension n k)) =
      MvPolynomial.rename e
        (cubicLiftMonomial k (multiIndexFinsupp a)) := by
  rw [HGAS.PolynomialCode.decode_cons,
    HGAS.PolynomialCode.decode_nil, add_zero]
  simp only [HGAS.PolynomialCode.decodeTerm,
    HGAS.RationalCode.decode_one, decode_targetCubicExponent]
  rw [cubicLiftMonomial, dif_pos (multiIndexFinsupp_degree a)]
  simp only [cubicCoordinateMonomial, map_mul,
    MvPolynomial.rename_X]
  let f := cubicFactorization (multiIndexFinsupp a)
    (multiIndexFinsupp_degree a)
  have hX (i : Fin (cubicLiftCodeDimension n k)) :
      MvPolynomial.monomial (Finsupp.single i 1) (1 : ℚ) =
        MvPolynomial.X i := by
    simpa using
      (MvPolynomial.X_pow_eq_monomial
        (R := ℚ) (n := i) (e := 1)).symm
  change
    MvPolynomial.monomial
        (Finsupp.single (e f.first) 1 +
          Finsupp.single (e f.second) 1 +
          Finsupp.single (e f.third) 1) 1 =
      MvPolynomial.X (e f.first) *
        MvPolynomial.X (e f.second) *
          MvPolynomial.X (e f.third)
  rw [← hX, ← hX, ← hX,
    MvPolynomial.monomial_mul, MvPolynomial.monomial_mul]
  norm_num

theorem decode_cubicLiftTerm
    (e : MultiIndex n k ≃ Fin (cubicLiftCodeDimension n k))
    (a : MultiIndex n (3 * k))
    (p : HGAS.PolynomialCode n) :
    HGAS.PolynomialCode.decodeTerm
        (targetCubicExponent e a,
          HGAS.PolynomialCode.coefficient
            (HGAS.ExponentCode.encode (multiIndexFinsupp a)) p) =
      MvPolynomial.C
          (MvPolynomial.coeff (multiIndexFinsupp a)
            (HGAS.PolynomialCode.decode p)) *
        MvPolynomial.rename e
          (cubicLiftMonomial k (multiIndexFinsupp a)) := by
  rw [← decode_targetCubicMonomial e a]
  simp only [HGAS.PolynomialCode.decode_cons,
    HGAS.PolynomialCode.decode_nil, add_zero,
    HGAS.PolynomialCode.decodeTerm,
    HGAS.PolynomialCode.decode_coefficient,
    HGAS.ExponentCode.decode_encode,
    HGAS.RationalCode.decode_one]
  rw [MvPolynomial.C_mul_monomial]
  norm_num

theorem decode_cubicLiftPolynomialCode
    (n k : ℕ) (p : HGAS.PolynomialCode n) :
    HGAS.PolynomialCode.decode
        (cubicLiftPolynomialCode n k p) =
      ∑ a : MultiIndex n (3 * k),
        MvPolynomial.C
            (MvPolynomial.coeff (multiIndexFinsupp a)
              (HGAS.PolynomialCode.decode p)) *
          MvPolynomial.rename (cubicLiftIndexEquiv n k)
            (cubicLiftMonomial k (multiIndexFinsupp a)) := by
  rw [cubicLiftPolynomialCode, HGAS.PolynomialCode.decode,
    List.map_ofFn, List.sum_ofFn]
  symm
  apply Fintype.sum_equiv (degreeIndexEquiv n (3 * k))
  intro a
  simp only [Function.comp_apply]
  simp only [targetCubicExponentAt, sourceExponentAt,
    degreeIndexEquiv, Equiv.symm_apply_apply]
  exact (decode_cubicLiftTerm (cubicLiftIndexEquiv n k) a p).symm

def multiIndexOfFinsupp
    (e : Fin n →₀ ℕ) (hdegree : Finsupp.degree e = d) :
    MultiIndex n d :=
  ⟨fun i => e i, by
    rw [multiIndexFinset, Finset.mem_piAntidiag]
    constructor
    · rw [← hdegree, Finsupp.degree_eq_sum]
    · intro i _
      exact Finset.mem_univ i⟩

@[simp] theorem multiIndexOfFinsupp_apply
    (e : Fin n →₀ ℕ) (hdegree : Finsupp.degree e = d)
    (i : Fin n) :
    (multiIndexOfFinsupp e hdegree).1 i = e i :=
  rfl

@[simp] theorem multiIndexFinsupp_multiIndexOfFinsupp
    (e : Fin n →₀ ℕ) (hdegree : Finsupp.degree e = d) :
    multiIndexFinsupp (multiIndexOfFinsupp e hdegree) = e := by
  ext i
  simp

theorem cubicLiftPolynomial_eq_sum_multiIndex
    (p : MvPolynomial (Fin n) ℚ) :
    cubicLiftPolynomial k p =
      ∑ a : MultiIndex n (3 * k),
        MvPolynomial.C (MvPolynomial.coeff
          (multiIndexFinsupp a) p) *
          cubicLiftMonomial k (multiIndexFinsupp a) := by
  classical
  let term : (Fin n →₀ ℕ) →
      MvPolynomial (MultiIndex n k) ℚ :=
    fun m => MvPolynomial.C (MvPolynomial.coeff m p) *
      cubicLiftMonomial k m
  let source : Finset (Fin n →₀ ℕ) :=
    p.support.filter fun m => Finsupp.degree m = 3 * k
  let target : Finset (MultiIndex n (3 * k)) :=
    Finset.univ.filter fun a => multiIndexFinsupp a ∈ p.support
  have hsource :
      (∑ m ∈ source, term m) =
        ∑ m ∈ p.support, term m := by
    apply Finset.sum_subset
    · intro m hm
      exact (Finset.mem_filter.mp hm).1
    · intro m hm hnot
      have hdegree : Finsupp.degree m ≠ 3 * k := by
        intro h
        exact hnot (Finset.mem_filter.mpr ⟨hm, h⟩)
      simp [term, cubicLiftMonomial, hdegree]
  have hreindex :
      (∑ m ∈ source, term m) =
        ∑ a ∈ target,
          MvPolynomial.C (MvPolynomial.coeff
            (multiIndexFinsupp a) p) *
            cubicLiftMonomial k (multiIndexFinsupp a) := by
    apply Finset.sum_bij
      (fun m hm =>
        multiIndexOfFinsupp m (Finset.mem_filter.mp hm).2)
    · intro m hm
      simp only [target, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa using (Finset.mem_filter.mp hm).1
    · intro m₁ hm₁ m₂ hm₂ heq
      have := congrArg multiIndexFinsupp heq
      simpa using this
    · intro a ha
      refine ⟨multiIndexFinsupp a, ?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp ha).2,
            multiIndexFinsupp_degree a⟩
      · apply Subtype.ext
        funext i
        simp
    · intro m hm
      simp [term]
  have htarget :
      (∑ a ∈ target,
          MvPolynomial.C (MvPolynomial.coeff
            (multiIndexFinsupp a) p) *
            cubicLiftMonomial k (multiIndexFinsupp a)) =
        ∑ a : MultiIndex n (3 * k),
          MvPolynomial.C (MvPolynomial.coeff
            (multiIndexFinsupp a) p) *
            cubicLiftMonomial k (multiIndexFinsupp a) := by
    change
      (∑ a ∈ target,
          MvPolynomial.C (MvPolynomial.coeff
            (multiIndexFinsupp a) p) *
            cubicLiftMonomial k (multiIndexFinsupp a)) =
        ∑ a ∈ (Finset.univ : Finset (MultiIndex n (3 * k))),
          MvPolynomial.C (MvPolynomial.coeff
            (multiIndexFinsupp a) p) *
            cubicLiftMonomial k (multiIndexFinsupp a)
    apply Finset.sum_subset
    · intro a ha
      exact Finset.mem_univ a
    · intro a _ hnot
      have hsupport : multiIndexFinsupp a ∉ p.support := by
        intro h
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ a, h⟩)
      have hcoeff :
          MvPolynomial.coeff (multiIndexFinsupp a) p = 0 := by
        by_contra hne
        exact hsupport (MvPolynomial.mem_support_iff.mpr hne)
      rw [hcoeff]
      simp
  unfold cubicLiftPolynomial
  exact hsource.symm.trans (hreindex.trans htarget)

@[simp] theorem decode_cubicLiftPolynomialCode_eq_rename
    (n k : ℕ) (p : HGAS.PolynomialCode n) :
    HGAS.PolynomialCode.decode
        (cubicLiftPolynomialCode n k p) =
      MvPolynomial.rename (cubicLiftIndexEquiv n k)
        (cubicLiftPolynomial k
          (HGAS.PolynomialCode.decode p)) := by
  rw [decode_cubicLiftPolynomialCode,
    cubicLiftPolynomial_eq_sum_multiIndex]
  simp only [map_sum, map_mul, MvPolynomial.rename_C]

def sourceVeronesePolynomialCode
    (a : MultiIndex n k) : HGAS.PolynomialCode n :=
  [(a.1, HGAS.RationalCode.one)]

@[simp] theorem decode_sourceVeronesePolynomialCode
    (a : MultiIndex n k) :
    HGAS.PolynomialCode.decode
        (sourceVeronesePolynomialCode a) =
      sourceVeronesePolynomial a := by
  rw [sourceVeronesePolynomialCode,
    HGAS.PolynomialCode.decode_cons,
    HGAS.PolynomialCode.decode_nil, add_zero]
  simp only [HGAS.PolynomialCode.decodeTerm,
    HGAS.RationalCode.decode_one, sourceVeronesePolynomial]
  have hexponent :
      HGAS.ExponentCode.decode a.1 = multiIndexFinsupp a := by
    ext i
    simp [HGAS.ExponentCode.decode]
  rw [hexponent]

def transportedSourcePolynomialCode
    (F : HGAS.PolynomialFieldCode n)
    (a : MultiIndex n k) : HGAS.PolynomialCode n :=
  HGAS.PolynomialCode.sumCodes
    (List.ofFn fun i : Fin n =>
      HGAS.PolynomialCode.mul
        (HGAS.PolynomialCode.pderiv i
          (sourceVeronesePolynomialCode a))
        (F i))

@[simp] theorem decode_transportedSourcePolynomialCode
    (F : HGAS.PolynomialFieldCode n)
    (a : MultiIndex n k) :
    HGAS.PolynomialCode.decode
        (transportedSourcePolynomialCode F a) =
      transportedSourcePolynomial
        (HGAS.PolynomialFieldCode.decode F) a := by
  rw [transportedSourcePolynomialCode,
    HGAS.PolynomialCode.decode_sumCodes,
    List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply,
    HGAS.PolynomialCode.decode_mul_code,
    HGAS.PolynomialCode.decode_pderiv,
    decode_sourceVeronesePolynomialCode]
  rfl

theorem transportedSourcePolynomialCode_primrec
    (a : MultiIndex n k) :
    Primrec (fun F : HGAS.PolynomialFieldCode n =>
      transportedSourcePolynomialCode F a) := by
  apply HGAS.PolynomialCode.sumCodes_primrec.comp
  apply Primrec.list_ofFn
  intro i
  apply HGAS.PolynomialCode.mul_primrec.comp
  · exact Primrec.const _
  · exact Primrec.fin_app.comp Primrec.id (Primrec.const i)

def cubicLiftFieldCode
    (n k : ℕ) (F : HGAS.PolynomialFieldCode n) :
    HGAS.PolynomialFieldCode (cubicLiftCodeDimension n k) :=
  fun j =>
    cubicLiftPolynomialCode n k
      (transportedSourcePolynomialCode F
        ((cubicLiftIndexEquiv n k).symm j))

theorem cubicLiftFieldCode_primrec
    (n k : ℕ) :
    Primrec (cubicLiftFieldCode n k) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro j
  exact (cubicLiftPolynomialCode_primrec n k).comp
    (transportedSourcePolynomialCode_primrec
      ((cubicLiftIndexEquiv n k).symm j))

@[simp] theorem decode_cubicLiftFieldCode
    (n k : ℕ) (F : HGAS.PolynomialFieldCode n)
    (j : Fin (cubicLiftCodeDimension n k)) :
    HGAS.PolynomialCode.decode
        (cubicLiftFieldCode n k F j) =
      MvPolynomial.rename (cubicLiftIndexEquiv n k)
        (cubicLiftField (k := k)
          (HGAS.PolynomialFieldCode.decode F)
          ((cubicLiftIndexEquiv n k).symm j)) := by
  simp [cubicLiftFieldCode, cubicLiftField]

def penaltyQGradientFieldCode
    (n k : ℕ) :
    HGAS.PolynomialFieldCode (cubicLiftCodeDimension n k) :=
  fun j =>
    HGAS.PolynomialCode.encode
      (MvPolynomial.rename (cubicLiftIndexEquiv n k)
        (penaltyQGradientField n k
          ((cubicLiftIndexEquiv n k).symm j)))

@[simp] theorem decode_penaltyQGradientFieldCode
    (n k : ℕ) (j : Fin (cubicLiftCodeDimension n k)) :
    HGAS.PolynomialCode.decode
        (penaltyQGradientFieldCode n k j) =
      MvPolynomial.rename (cubicLiftIndexEquiv n k)
        (penaltyQGradientField n k
          ((cubicLiftIndexEquiv n k).symm j)) := by
  simp [penaltyQGradientFieldCode]

def stabilizedCubicFieldCode
    (n k : ℕ) (F : HGAS.PolynomialFieldCode n)
    (K : HGAS.RationalCode) :
    HGAS.PolynomialFieldCode (cubicLiftCodeDimension n k) :=
  fun j =>
    HGAS.PolynomialCode.sub
      (cubicLiftFieldCode n k F j)
      (HGAS.PolynomialCode.mul
        (HGAS.PolynomialCode.constant K)
        (penaltyQGradientFieldCode n k j))

theorem stabilizedCubicFieldCode_primrec
    (n k : ℕ) :
    Primrec₂ (stabilizedCubicFieldCode n k) := by
  change Primrec
    (fun q : HGAS.PolynomialFieldCode n × HGAS.RationalCode =>
      stabilizedCubicFieldCode n k q.1 q.2)
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro j
  apply HGAS.PolynomialCode.sub_primrec.comp
  · exact Primrec.fin_app.comp
      ((cubicLiftFieldCode_primrec n k).comp Primrec.fst)
      (Primrec.const j)
  · apply HGAS.PolynomialCode.mul_primrec.comp
    · exact HGAS.PolynomialCode.constant_primrec.comp Primrec.snd
    · exact Primrec.const _

@[simp] theorem decode_stabilizedCubicFieldCode
    (n k : ℕ) (F : HGAS.PolynomialFieldCode n)
    (K : HGAS.RationalCode)
    (j : Fin (cubicLiftCodeDimension n k)) :
    HGAS.PolynomialCode.decode
        (stabilizedCubicFieldCode n k F K j) =
      MvPolynomial.rename (cubicLiftIndexEquiv n k)
        (stabilizedCubicField (k := k)
          (HGAS.PolynomialFieldCode.decode F)
          (HGAS.RationalCode.decode K)
          ((cubicLiftIndexEquiv n k).symm j)) := by
  simp [stabilizedCubicFieldCode, stabilizedCubicField]

theorem stabilizedCubicFieldCode_homogeneous
    (n k : ℕ) (F : HGAS.PolynomialFieldCode n)
    (K : HGAS.RationalCode) :
    HGAS.PolynomialFieldCode.homogeneous 3
        (stabilizedCubicFieldCode n k F K) = true := by
  rw [HGAS.PolynomialFieldCode.homogeneous_eq_true_iff]
  intro j
  rw [decode_stabilizedCubicFieldCode]
  exact MvPolynomial.IsHomogeneous.rename_isHomogeneous
    (stabilizedCubicField_isHomogeneous
      (HGAS.PolynomialFieldCode.decode F)
      (HGAS.RationalCode.decode K)
      ((cubicLiftIndexEquiv n k).symm j))

theorem realize_stabilizedCubicFieldCode
    (n k : ℕ) (F : HGAS.PolynomialFieldCode n)
    (K : HGAS.RationalCode) :
    HGAS.PolynomialFieldCode.realize
        (stabilizedCubicFieldCode n k F K) =
      HGAS.conjugateField (cubicLiftReindexEquiv n k)
        (fun y : RealVeroneseSpace n k =>
          evalCoordinateField
            (stabilizedCubicField (k := k)
              (HGAS.PolynomialFieldCode.decode F)
              (HGAS.RationalCode.decode K)) y) := by
  funext x j
  rw [HGAS.PolynomialFieldCode.realize_apply,
    decode_stabilizedCubicFieldCode,
    MvPolynomial.eval₂Hom_rename]
  simp only [HGAS.conjugateField, cubicLiftReindexEquiv_apply,
    evalCoordinateField_apply]
  congr 1

theorem globallyAsymptoticallyStable_realize_stabilizedCode_iff
    (n k : ℕ) (F : HGAS.PolynomialFieldCode n)
    (K : HGAS.RationalCode) :
    HGAS.GloballyAsymptoticallyStable
        (HGAS.PolynomialFieldCode.realize
          (stabilizedCubicFieldCode n k F K)) 0 ↔
      HGAS.GloballyAsymptoticallyStable
        (fun y : RealVeroneseSpace n k =>
          evalCoordinateField
            (stabilizedCubicField (k := k)
              (HGAS.PolynomialFieldCode.decode F)
              (HGAS.RationalCode.decode K)) y) 0 := by
  rw [realize_stabilizedCubicFieldCode]
  exact HGAS.globallyAsymptoticallyStable_conjugateField_iff
    (cubicLiftReindexEquiv n k) _

end

end HGAS.Veronese
