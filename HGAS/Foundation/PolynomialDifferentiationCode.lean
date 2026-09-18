import HGAS.Foundation.FinitePolynomialCode
import HGAS.Lyapunov.RationalCertificateAlgebra
import Mathlib.Tactic

/-!
# Executable differentiation of sparse polynomial codes

`FinitePolynomialCode` supplies exact addition, multiplication, powers, and
equality.  This module adds the one missing operation needed by the
Lyapunov-certificate checker: formal partial differentiation.

The implementation works directly on the raw sparse list.  A monomial
whose selected exponent is zero disappears; otherwise that exponent is
decremented and the coefficient is multiplied by the old exponent.  The
main theorems show that decoding commutes exactly with `MvPolynomial.pderiv`
and with the complete rational Lyapunov numerator

```
q = -ρ (∇p · F) + 2r p (x · F).
```

All definitions in this file are executable.  The semantic statements are
kept separate, so later certificate enumerators can reuse the syntax
without importing any ODE theory.
-/

namespace HGAS

open MvPolynomial
open scoped BigOperators

namespace RationalCode

/-- Canonical denominator-one code of a natural number. -/
def ofNat (m : ℕ) : RationalCode :=
  ((false, m), 0)

@[simp]
theorem decode_ofNat (m : ℕ) :
    decode (ofNat m) = (m : ℚ) := by
  simp [ofNat, decode, SignedMagnitudeCode.decode]

end RationalCode

namespace ExponentCode

variable {n : ℕ}

/-- Decrement the `i`-th exponent, leaving all other exponents unchanged. -/
def predAt (i : Fin n) (e : ExponentCode n) : ExponentCode n :=
  fun j ↦ if j = i then e j - 1 else e j

/-- When the selected exponent is positive, decoding `predAt` is
subtraction of the corresponding singleton exponent. -/
theorem decode_predAt
    (i : Fin n) (e : ExponentCode n) :
    decode (predAt i e) =
      decode e - Finsupp.single i 1 := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [predAt, decode]
  · simp [predAt, decode, hji]

/-- Exponent vector of the variable `X i`. -/
def singleVariable (i : Fin n) : ExponentCode n :=
  fun j ↦ if j = i then 1 else 0

@[simp]
theorem decode_singleVariable (i : Fin n) :
    decode (singleVariable i) = Finsupp.single i 1 := by
  ext j
  simp [singleVariable, decode, Finsupp.single_apply, eq_comm]

/-- Exponent vector of the monomial `X i ^ 2`. -/
def squareVariable (i : Fin n) : ExponentCode n :=
  fun j ↦ if j = i then 2 else 0

@[simp]
theorem decode_squareVariable (i : Fin n) :
    decode (squareVariable i) = Finsupp.single i 2 := by
  ext j
  simp [squareVariable, decode, Finsupp.single_apply, eq_comm]

end ExponentCode

namespace PolynomialCode

variable {n : ℕ}

/-- Sparse one-term code of the variable `X i`. -/
def varCode (i : Fin n) : PolynomialCode n :=
  [(ExponentCode.singleVariable i, RationalCode.one)]

@[simp]
theorem decode_varCode (i : Fin n) :
    decode (varCode i) = X i := by
  rw [varCode, decode_cons, decode_nil, add_zero, decodeTerm,
    ExponentCode.decode_singleVariable, RationalCode.decode_one]
  simpa using
    (X_pow_eq_monomial (R := ℚ) (n := i) (e := 1)).symm

/-- Sparse code for `ρ = ∑ i, X i ^ 2`. -/
def rhoCode (n : ℕ) : PolynomialCode n :=
  List.ofFn fun i : Fin n ↦
    (ExponentCode.squareVariable i, RationalCode.one)

@[simp]
theorem decode_rhoCode (n : ℕ) :
    decode (rhoCode n) = rhoPolynomial (n := n) := by
  rw [rhoCode, decode, rhoPolynomial]
  simp only [List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Function.comp_apply, decodeTerm, ← X_pow_eq_monomial]

/-- Differentiate one raw monomial term. -/
def pderivTerm
    (i : Fin n) (t : ExponentCode n × RationalCode) :
    PolynomialCode n :=
  if t.1 i = 0 then
    []
  else
    [(ExponentCode.predAt i t.1,
      RationalCode.mul t.2 (RationalCode.ofNat (t.1 i)))]

/-- Decoding a differentiated term gives its formal partial derivative. -/
@[simp]
theorem decode_pderivTerm
    (i : Fin n) (t : ExponentCode n × RationalCode) :
    decode (pderivTerm i t) = pderiv i (decodeTerm t) := by
  by_cases h : t.1 i = 0
  · rw [pderivTerm, if_pos h]
    change 0 = pderiv i
      (monomial (ExponentCode.decode t.1)
        (RationalCode.decode t.2))
    rw [pderiv_monomial]
    simp [ExponentCode.decode, h]
  · rw [pderivTerm, if_neg h, decode_cons, decode_nil, add_zero]
    change
      monomial (ExponentCode.decode (ExponentCode.predAt i t.1))
          (RationalCode.decode
            (RationalCode.mul t.2
              (RationalCode.ofNat (t.1 i)))) =
        pderiv i
          (monomial (ExponentCode.decode t.1)
            (RationalCode.decode t.2))
    rw [pderiv_monomial, ExponentCode.decode_predAt,
      RationalCode.decode_mul, RationalCode.decode_ofNat]
    norm_cast

/-- Executable formal partial derivative of a raw sparse polynomial code. -/
def pderiv (i : Fin n) (p : PolynomialCode n) : PolynomialCode n :=
  p.flatMap (pderivTerm i)

/-- Sparse differentiation is exactly sound under semantic decoding. -/
@[simp]
theorem decode_pderiv (i : Fin n) (p : PolynomialCode n) :
    decode (pderiv i p) = MvPolynomial.pderiv i (decode p) := by
  induction p with
  | nil => simp [pderiv]
  | cons t p ih =>
      change
        decode (pderivTerm i t ++ pderiv i p) =
          MvPolynomial.pderiv i (decodeTerm t + decode p)
      rw [decode_append, decode_pderivTerm, ih, map_add]

/-- Sum a finite list of sparse polynomial codes. -/
def sumCodes (p : List (PolynomialCode n)) : PolynomialCode n :=
  p.foldr add zero

@[simp]
theorem decode_sumCodes (p : List (PolynomialCode n)) :
    decode (sumCodes p) = (p.map decode).sum := by
  induction p with
  | nil => simp [sumCodes]
  | cons q p ih =>
      change
        decode (add q (sumCodes p)) =
          decode q + (p.map decode).sum
      rw [decode_add_code, ih]

end PolynomialCode

/-! ## Coded polynomial vector fields and the Lyapunov numerator -/

/-- A completely finite sparse code for every coordinate of a polynomial
vector field. -/
abbrev PolynomialFieldCode (n : ℕ) :=
  Fin n → PolynomialCode n

namespace PolynomialFieldCode

variable {n : ℕ}

/-- Semantic polynomial vector field represented by a sparse field code. -/
noncomputable def decode (F : PolynomialFieldCode n) : PolynomialField n :=
  fun i ↦ PolynomialCode.decode (F i)

/-- Real vector field denoted by a completely finite sparse field code. -/
noncomputable def realize (F : PolynomialFieldCode n) :
    (Fin n → ℝ) → (Fin n → ℝ) :=
  evalPolynomialField (decode F)

@[simp]
theorem realize_apply (F : PolynomialFieldCode n)
    (x : Fin n → ℝ) (i : Fin n) :
    realize F x i =
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (F i)) :=
  rfl

end PolynomialFieldCode

namespace PolynomialCode

variable {n : ℕ}

/-- Coded directional derivative `∇p · F`. -/
def gradientDotField
    (p : PolynomialCode n) (F : PolynomialFieldCode n) :
    PolynomialCode n :=
  sumCodes (List.ofFn fun i : Fin n ↦
    mul (pderiv i p) (F i))

@[simp]
theorem decode_gradientDotField
    (p : PolynomialCode n) (F : PolynomialFieldCode n) :
    decode (gradientDotField p F) =
      HGAS.gradientDotField (decode p) (PolynomialFieldCode.decode F) := by
  rw [gradientDotField, decode_sumCodes, List.map_ofFn, List.sum_ofFn]
  simp [HGAS.gradientDotField, PolynomialFieldCode.decode]

/-- Coded radial dot product `x · F(x)`. -/
def radialDotField (F : PolynomialFieldCode n) :
    PolynomialCode n :=
  sumCodes (List.ofFn fun i : Fin n ↦
    mul (varCode i) (F i))

@[simp]
theorem decode_radialDotField
    (F : PolynomialFieldCode n) :
    decode (radialDotField F) =
      radialDotPolynomial (PolynomialFieldCode.decode F) := by
  rw [radialDotField, decode_sumCodes, List.map_ofFn, List.sum_ofFn]
  simp [radialDotPolynomial, PolynomialFieldCode.decode]

/-- Exact sparse code for the rational Lyapunov decay numerator. -/
def rationalLyapunovNumerator
    (F : PolynomialFieldCode n) (p : PolynomialCode n) (r : ℕ) :
    PolynomialCode n :=
  add
    (neg (mul (rhoCode n) (gradientDotField p F)))
    (mul
      (mul (constant (RationalCode.ofNat (2 * r))) p)
      (radialDotField F))

/-- Decoding the executable numerator compiler gives exactly the semantic
`rationalLyapunovNumerator`. -/
@[simp]
theorem decode_rationalLyapunovNumerator
    (F : PolynomialFieldCode n) (p : PolynomialCode n) (r : ℕ) :
    decode (rationalLyapunovNumerator F p r) =
      HGAS.rationalLyapunovNumerator
        (PolynomialFieldCode.decode F) (decode p) r := by
  simp [rationalLyapunovNumerator,
    HGAS.rationalLyapunovNumerator]

end PolynomialCode

/-! ## Primitive-recursiveness

These declarations make the differentiated numerator available to genuine
`REPred` certificate enumerators. -/

namespace RationalCode

theorem ofNat_primrec :
    Primrec ofNat := by
  exact Primrec.pair
    (Primrec.pair (Primrec.const false) Primrec.id)
    (Primrec.const 0)

end RationalCode

namespace ExponentCode

theorem predAt_primrec {n : ℕ} :
    Primrec₂ (predAt : Fin n → ExponentCode n → ExponentCode n) := by
  change Primrec
    (fun p : Fin n × ExponentCode n ↦ predAt p.1 p.2)
  rw [Primrec.fin_curry]
  have heq :
      PrimrecPred
        (fun q : (Fin n × ExponentCode n) × Fin n ↦
          q.2 = q.1.1) :=
    Primrec.eq.comp
      Primrec.snd
      (Primrec.fst.comp Primrec.fst)
  have hpred :
      Primrec
        (fun q : (Fin n × ExponentCode n) × Fin n ↦
          q.1.2 q.2 - 1) :=
    Primrec.nat_sub.comp
      (Primrec.fin_app.comp
        (Primrec.snd.comp Primrec.fst)
        Primrec.snd)
      (Primrec.const 1)
  have hkeep :
      Primrec
        (fun q : (Fin n × ExponentCode n) × Fin n ↦
          q.1.2 q.2) :=
    Primrec.fin_app.comp
      (Primrec.snd.comp Primrec.fst)
      Primrec.snd
  exact (Primrec.ite heq hpred hkeep).of_eq fun q ↦ by
    simp [predAt]

end ExponentCode

namespace PolynomialCode

theorem pderivTerm_primrec {n : ℕ} :
    Primrec₂ (pderivTerm :
      Fin n → (ExponentCode n × RationalCode) → PolynomialCode n) := by
  have hzero :
      PrimrecPred
        (fun p : Fin n × (ExponentCode n × RationalCode) ↦
          p.2.1 p.1 = 0) :=
    Primrec.eq.comp
      (Primrec.fin_app.comp
        (Primrec.fst.comp Primrec.snd)
        Primrec.fst)
      (Primrec.const 0)
  have hexponent :
      Primrec
        (fun p : Fin n × (ExponentCode n × RationalCode) ↦
          p.2.1 p.1) :=
    Primrec.fin_app.comp
      (Primrec.fst.comp Primrec.snd)
      Primrec.fst
  have hterm :
      Primrec
        (fun p : Fin n × (ExponentCode n × RationalCode) ↦
          (ExponentCode.predAt p.1 p.2.1,
            RationalCode.mul p.2.2
              (RationalCode.ofNat (p.2.1 p.1)))) :=
    Primrec.pair
      (ExponentCode.predAt_primrec.comp
        Primrec.fst
        (Primrec.fst.comp Primrec.snd))
      (RationalCode.mul_primrec.comp
        (Primrec.snd.comp Primrec.snd)
        (RationalCode.ofNat_primrec.comp hexponent))
  have hone :
      Primrec
        (fun p : Fin n × (ExponentCode n × RationalCode) ↦
          [(ExponentCode.predAt p.1 p.2.1,
            RationalCode.mul p.2.2
              (RationalCode.ofNat (p.2.1 p.1)))]) :=
    Primrec.list_cons.comp hterm (Primrec.const [])
  exact
    (Primrec.ite hzero (Primrec.const []) hone).to₂.of_eq
      fun _ _ ↦ rfl

theorem pderiv_primrec {n : ℕ} :
    Primrec₂ (pderiv :
      Fin n → PolynomialCode n → PolynomialCode n) := by
  have hterm :
      Primrec₂
        (fun (p : Fin n × PolynomialCode n)
          (t : ExponentCode n × RationalCode) ↦
            pderivTerm p.1 t) :=
    pderivTerm_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.left)
      Primrec₂.right
  exact
    (Primrec.list_flatMap Primrec.snd hterm).to₂.of_eq
      fun _ _ ↦ rfl

theorem sumCodes_primrec {n : ℕ} :
    Primrec (sumCodes : List (PolynomialCode n) → PolynomialCode n) := by
  have hstep :
      Primrec₂
        (fun (_ : List (PolynomialCode n))
          (p : PolynomialCode n × PolynomialCode n) ↦
            add p.1 p.2) :=
    PolynomialCode.add_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.list_foldr Primrec.id
      (Primrec.const (zero : PolynomialCode n)) hstep).of_eq
      fun _ ↦ rfl

theorem gradientDotField_primrec {n : ℕ} :
    Primrec₂ (gradientDotField :
      PolynomialCode n → PolynomialFieldCode n → PolynomialCode n) := by
  have hlist :
      Primrec
        (fun p : PolynomialCode n × PolynomialFieldCode n ↦
          List.ofFn fun i : Fin n ↦
            mul (pderiv i p.1) (p.2 i)) :=
    Primrec.list_ofFn fun i ↦
      PolynomialCode.mul_primrec.comp
        (pderiv_primrec.comp
          (Primrec.const i) Primrec.fst)
        (Primrec.fin_app.comp
          Primrec.snd (Primrec.const i))
  exact
    (sumCodes_primrec.comp hlist).to₂.of_eq
      fun _ _ ↦ rfl

theorem radialDotField_primrec {n : ℕ} :
    Primrec (radialDotField : PolynomialFieldCode n → PolynomialCode n) := by
  have hlist :
      Primrec
        (fun F : PolynomialFieldCode n ↦
          List.ofFn fun i : Fin n ↦
            mul (varCode i) (F i)) :=
    Primrec.list_ofFn fun i ↦
      PolynomialCode.mul_primrec.comp
        (Primrec.const (varCode i))
        (Primrec.fin_app.comp Primrec.id (Primrec.const i))
  exact sumCodes_primrec.comp hlist

/-- Primitive-recursive compiler for the complete numerator.  The nested
input is `((F,p),r)`. -/
theorem rationalLyapunovNumerator_primrec {n : ℕ} :
    Primrec
      (fun q : (PolynomialFieldCode n × PolynomialCode n) × ℕ ↦
        rationalLyapunovNumerator q.1.1 q.1.2 q.2) := by
  have hgradient :
      Primrec
        (fun q : (PolynomialFieldCode n × PolynomialCode n) × ℕ ↦
          gradientDotField q.1.2 q.1.1) :=
    gradientDotField_primrec.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp Primrec.fst)
  have hfirst :
      Primrec
        (fun q : (PolynomialFieldCode n × PolynomialCode n) × ℕ ↦
          neg (mul (rhoCode n)
            (gradientDotField q.1.2 q.1.1))) :=
    PolynomialCode.neg_primrec.comp
      (PolynomialCode.mul_primrec.comp
        (Primrec.const (rhoCode n)) hgradient)
  have hscalar :
      Primrec
        (fun q : (PolynomialFieldCode n × PolynomialCode n) × ℕ ↦
          (constant (RationalCode.ofNat (2 * q.2)) :
            PolynomialCode n)) :=
    PolynomialCode.constant_primrec.comp
      (RationalCode.ofNat_primrec.comp
        (Primrec.nat_mul.comp
          (Primrec.const 2) Primrec.snd))
  have hsecond :
      Primrec
        (fun q : (PolynomialFieldCode n × PolynomialCode n) × ℕ ↦
          mul
            (mul
              (constant (RationalCode.ofNat (2 * q.2)))
              q.1.2)
            (radialDotField q.1.1)) :=
    PolynomialCode.mul_primrec.comp
      (PolynomialCode.mul_primrec.comp
        hscalar (Primrec.snd.comp Primrec.fst))
      (radialDotField_primrec.comp
        (Primrec.fst.comp Primrec.fst))
  exact
    (PolynomialCode.add_primrec.comp hfirst hsecond).of_eq
      fun _ ↦ rfl

end PolynomialCode

end HGAS
