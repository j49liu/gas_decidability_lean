import Mathlib.Computability.Primrec.List
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Rat.Encodable
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

/-!
# Finite codes for rational multivariate polynomials

This file gives a deliberately elementary code for a polynomial in the
fixed variables `Fin n`.

* A signed integer is coded by `(s, a) : Bool × ℕ`, where `s` is the
  sign bit and `a` the absolute value.
* A rational number is coded by a signed numerator together with a natural
  `b`, and denotes the numerator divided by `b + 1`.  Thus every code has
  a nonzero denominator.
* A monomial exponent is the finite vector `Fin n → ℕ`.
* A polynomial is a list of exponent/coefficient pairs.  Repeated
  exponents and zero coefficients are allowed; decoding simply adds the
  represented monomials.

The raw list representation is useful for enumeration: it is
`Primcodable` without hiding finite support behind a quotient or a choice
of ordering.  A (noncomputable) semantic encoder is also supplied and is
proved to be a right inverse of decoding.  Consequently the raw codes
enumerate every rational polynomial.  The normalization operation
`PolynomialCode.normalize` removes zero coefficients and combines repeated
monomials.

Finally, exact equality and homogeneity are exposed as decidable predicates
on codes and related to the usual `MvPolynomial` notions.
-/

namespace HGAS

open MvPolynomial
open scoped BigOperators

/-! ## Signed integers and rational codes -/

/-- A signed-magnitude integer.  `false` is the nonnegative sign and `true`
is the nonpositive sign.  Both signs are permitted for zero. -/
abbrev SignedMagnitudeCode := Bool × ℕ

namespace SignedMagnitudeCode

/-- Interpret a signed-magnitude integer. -/
def decode (z : SignedMagnitudeCode) : ℤ :=
  if z.1 then -(z.2 : ℤ) else (z.2 : ℤ)

/-- Canonical signed-magnitude code of an integer. -/
def encode : ℤ → SignedMagnitudeCode
  | .ofNat n => (false, n)
  | .negSucc n => (true, n + 1)

@[simp]
theorem decode_encode (z : ℤ) : decode (encode z) = z := by
  cases z <;> simp [decode, encode, Int.negSucc_eq]

/-- Negation of a signed-magnitude code.  Toggling the sign is sound even
for either representation of zero. -/
def neg (z : SignedMagnitudeCode) : SignedMagnitudeCode :=
  (!z.1, z.2)

@[simp]
theorem decode_neg (z : SignedMagnitudeCode) : decode (neg z) = -decode z := by
  rcases z with ⟨s, a⟩
  cases s <;> simp [decode, neg]

/-- Multiplication of signed-magnitude integers. -/
def mul (a b : SignedMagnitudeCode) : SignedMagnitudeCode :=
  (xor a.1 b.1, a.2 * b.2)

@[simp]
theorem decode_mul (a b : SignedMagnitudeCode) :
    decode (mul a b) = decode a * decode b := by
  rcases a with ⟨sa, a⟩
  rcases b with ⟨sb, b⟩
  cases sa <;> cases sb <;> simp [decode, mul]

/-- Addition of signed-magnitude integers, using only Boolean tests and
natural-number arithmetic. -/
def add (a b : SignedMagnitudeCode) : SignedMagnitudeCode :=
  if a.1 = b.1 then
    (a.1, a.2 + b.2)
  else if a.2 ≤ b.2 then
    (b.1, b.2 - a.2)
  else
    (a.1, a.2 - b.2)

@[simp]
theorem decode_add (a b : SignedMagnitudeCode) :
    decode (add a b) = decode a + decode b := by
  rcases a with ⟨sa, a⟩
  rcases b with ⟨sb, b⟩
  cases sa <;> cases sb <;> simp only [add, Bool.false_eq_true,
    Bool.true_eq_false, ↓reduceIte, decode]
  all_goals try omega
  all_goals split_ifs with h <;> simp_all <;> omega

/-- Semantic equality of signed-magnitude integers.  The extra zero case
identifies positive and negative zero. -/
def equal (a b : SignedMagnitudeCode) : Bool :=
  (a.2 == b.2) && ((a.2 == 0) || (a.1 == b.1))

@[simp]
theorem equal_eq_true_iff (a b : SignedMagnitudeCode) :
    equal a b = true ↔ decode a = decode b := by
  rcases a with ⟨sa, a⟩
  rcases b with ⟨sb, b⟩
  cases sa <;> cases sb <;> simp [equal, decode] <;> omega

/-- Strict positivity of the represented integer. -/
def positive (a : SignedMagnitudeCode) : Bool :=
  (!a.1) && (a.2 != 0)

@[simp]
theorem positive_eq_true_iff (a : SignedMagnitudeCode) :
    positive a = true ↔ 0 < decode a := by
  rcases a with ⟨s, a⟩
  cases s <;> simp [positive, decode]

end SignedMagnitudeCode

/-- A rational code consists of a signed numerator and a denominator minus
one. -/
abbrev RationalCode := SignedMagnitudeCode × ℕ

namespace RationalCode

/-- `((s, a), b)` represents the rational number represented by `(s, a)`
divided by `b + 1`.

The shifted denominator makes every pair a valid code and is particularly
convenient for exhaustive enumeration. -/
def decode (q : RationalCode) : ℚ :=
  Rat.divInt (SignedMagnitudeCode.decode q.1) ((q.2 + 1 : ℕ) : ℤ)

/-- The canonical numerator/denominator code of a rational number. -/
def encode (q : ℚ) : RationalCode :=
  (SignedMagnitudeCode.encode q.num, q.den - 1)

/-- Encoding followed by decoding recovers the original rational number. -/
@[simp]
theorem decode_encode (q : ℚ) : decode (encode q) = q := by
  rw [decode, encode, SignedMagnitudeCode.decode_encode,
    Nat.sub_add_cancel q.den_pos]
  exact q.num_divInt_den

/-- Decoding is onto; this is the only fact needed to enumerate rational
coefficients by enumerating `RationalCode`. -/
theorem decode_surjective : Function.Surjective decode :=
  fun q ↦ ⟨encode q, decode_encode q⟩

/-- The code of zero. -/
def zero : RationalCode :=
  ((false, 0), 0)

@[simp]
theorem decode_zero : decode zero = 0 := by
  simp [decode, zero, SignedMagnitudeCode.decode]

/-- The code of one. -/
def one : RationalCode :=
  ((false, 1), 0)

@[simp]
theorem decode_one : decode one = 1 := by
  simp [decode, one, SignedMagnitudeCode.decode]

/-- Negate a rational code without changing its positive denominator. -/
def neg (q : RationalCode) : RationalCode :=
  (SignedMagnitudeCode.neg q.1, q.2)

@[simp]
theorem decode_neg (q : RationalCode) :
    decode (neg q) = -decode q := by
  rw [decode, neg, SignedMagnitudeCode.decode_neg]
  exact
    (Rat.neg_divInt (SignedMagnitudeCode.decode q.1)
      (((q.2 + 1 : ℕ) : ℤ))).symm

/-- If `a` and `b` are denominator-minus-one values, then this is the
denominator-minus-one value for their product. -/
def denominatorProductMinusOne (a b : ℕ) : ℕ :=
  a + b + a * b

@[simp]
theorem denominatorProductMinusOne_add_one (a b : ℕ) :
    denominatorProductMinusOne a b + 1 = (a + 1) * (b + 1) := by
  simp [denominatorProductMinusOne]
  ring

/-- Multiply rational codes by multiplying signed numerators and positive
denominators. -/
def mul (a b : RationalCode) : RationalCode :=
  (SignedMagnitudeCode.mul a.1 b.1,
    denominatorProductMinusOne a.2 b.2)

@[simp]
theorem decode_mul (a b : RationalCode) :
    decode (mul a b) = decode a * decode b := by
  simpa [decode, mul, denominatorProductMinusOne_add_one,
    Int.natCast_mul] using
    (Rat.divInt_mul_divInt
      (SignedMagnitudeCode.decode a.1)
      (SignedMagnitudeCode.decode b.1)
      (d₁ := ((a.2 + 1 : ℕ) : ℤ))
      (d₂ := ((b.2 + 1 : ℕ) : ℤ))).symm

/-- Add rational codes by the usual common-denominator formula. -/
def add (a b : RationalCode) : RationalCode :=
  (SignedMagnitudeCode.add
      (SignedMagnitudeCode.mul a.1 (false, b.2 + 1))
      (SignedMagnitudeCode.mul b.1 (false, a.2 + 1)),
    denominatorProductMinusOne a.2 b.2)

@[simp]
theorem decode_add (a b : RationalCode) :
    decode (add a b) = decode a + decode b := by
  have ha : (((a.2 + 1 : ℕ) : ℤ)) ≠ 0 := by omega
  have hb : (((b.2 + 1 : ℕ) : ℤ)) ≠ 0 := by omega
  rw [decode, add, SignedMagnitudeCode.decode_add,
    SignedMagnitudeCode.decode_mul, SignedMagnitudeCode.decode_mul,
    denominatorProductMinusOne_add_one]
  simpa only [SignedMagnitudeCode.decode, Bool.false_eq_true,
    ↓reduceIte, Int.natCast_mul] using
    (Rat.divInt_add_divInt
      (SignedMagnitudeCode.decode a.1)
      (SignedMagnitudeCode.decode b.1) ha hb).symm

/-- Exact semantic equality of rational codes, checked by cross
multiplication of signed numerators. -/
def equal (a b : RationalCode) : Bool :=
  SignedMagnitudeCode.equal
    (SignedMagnitudeCode.mul a.1 (false, b.2 + 1))
    (SignedMagnitudeCode.mul b.1 (false, a.2 + 1))

@[simp]
theorem equal_eq_true_iff (a b : RationalCode) :
    equal a b = true ↔ decode a = decode b := by
  have ha : (((a.2 + 1 : ℕ) : ℤ)) ≠ 0 := by omega
  have hb : (((b.2 + 1 : ℕ) : ℤ)) ≠ 0 := by omega
  rw [equal, SignedMagnitudeCode.equal_eq_true_iff,
    SignedMagnitudeCode.decode_mul, SignedMagnitudeCode.decode_mul]
  simp only [SignedMagnitudeCode.decode, Bool.false_eq_true,
    ↓reduceIte, decode]
  exact (Rat.divInt_eq_divInt_iff ha hb).symm

/-- Strict positivity of a rational code.  The denominator is always
positive, so only the signed numerator must be inspected. -/
def positive (q : RationalCode) : Bool :=
  SignedMagnitudeCode.positive q.1

@[simp]
theorem positive_eq_true_iff (q : RationalCode) :
    positive q = true ↔ 0 < decode q := by
  have hd : (0 : ℤ) < ((q.2 + 1 : ℕ) : ℤ) := by omega
  rw [positive, SignedMagnitudeCode.positive_eq_true_iff]
  calc
    0 < SignedMagnitudeCode.decode q.1 ↔
        0 ≤ SignedMagnitudeCode.decode q.1 ∧
          SignedMagnitudeCode.decode q.1 ≠ 0 := by
      simpa only [ne_comm] using
        (lt_iff_le_and_ne :
          (0 : ℤ) < SignedMagnitudeCode.decode q.1 ↔
            0 ≤ SignedMagnitudeCode.decode q.1 ∧
              0 ≠ SignedMagnitudeCode.decode q.1)
    _ ↔ 0 ≤ decode q ∧ decode q ≠ 0 := by
      simp only [decode, Rat.divInt_nonneg_iff_of_pos_right hd,
        Rat.divInt_ne_zero hd.ne']
    _ ↔ 0 < decode q := by
      simpa only [ne_comm] using
        (lt_iff_le_and_ne :
          (0 : ℚ) < decode q ↔
            0 ≤ decode q ∧ 0 ≠ decode q).symm

end RationalCode

/-! ## Exponent vectors -/

/-- A finite exponent vector for the variables `Fin n`. -/
abbrev ExponentCode (n : ℕ) := Fin n → ℕ

namespace ExponentCode

/-- Turn a finite exponent vector into the finitely supported exponent used
by `MvPolynomial`. -/
def decode {n : ℕ} (e : ExponentCode n) : Fin n →₀ ℕ :=
  { support := Finset.univ.filter fun i ↦ e i ≠ 0
    toFun := e
    mem_support_toFun := by simp }

/-- Read a finitely supported exponent as a finite vector. -/
def encode {n : ℕ} (e : Fin n →₀ ℕ) : ExponentCode n :=
  fun i ↦ e i

@[simp]
theorem decode_encode {n : ℕ} (e : Fin n →₀ ℕ) :
    decode (encode e) = e := by
  ext i
  simp [decode, encode]

@[simp]
theorem encode_decode {n : ℕ} (e : ExponentCode n) :
    encode (decode e) = e := by
  funext i
  simp [decode, encode]

/-- Decoding exponent vectors is injective. -/
theorem decode_injective {n : ℕ} :
    Function.Injective (decode : ExponentCode n → Fin n →₀ ℕ) := by
  intro a b h
  rw [← encode_decode a, ← encode_decode b, h]

/-- Pointwise addition of exponent vectors. -/
def add {n : ℕ} (a b : ExponentCode n) : ExponentCode n :=
  fun i ↦ a i + b i

@[simp]
theorem decode_add {n : ℕ} (a b : ExponentCode n) :
    decode (add a b) = decode a + decode b := by
  ext i
  simp [decode, add]

/-- The zero exponent vector. -/
def zero {n : ℕ} : ExponentCode n :=
  fun _ ↦ 0

@[simp]
theorem decode_zero {n : ℕ} :
    decode (zero : ExponentCode n) = 0 := by
  ext i
  simp [decode, zero]

/-- Total degree of a finite exponent vector. -/
def totalDegree {n : ℕ} (e : ExponentCode n) : ℕ :=
  (List.ofFn e).sum

@[simp]
theorem degree_decode {n : ℕ} (e : ExponentCode n) :
    (decode e).degree = totalDegree e := by
  rw [Finsupp.degree_eq_sum]
  rw [totalDegree, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

end ExponentCode

/-! ## Sparse polynomial codes -/

/-- A raw sparse code is a list of monomials.  It need not be normalized:
repeated exponents and zero coefficients are harmless and are combined by
decoding. -/
abbrev PolynomialCode (n : ℕ) :=
  List (ExponentCode n × RationalCode)

namespace PolynomialCode

variable {n : ℕ}

/-- Decode one exponent/coefficient pair as a monomial. -/
noncomputable def decodeTerm (t : ExponentCode n × RationalCode) :
    MvPolynomial (Fin n) ℚ :=
  monomial (ExponentCode.decode t.1) (RationalCode.decode t.2)

/-- Decode a raw sparse list by summing its monomials. -/
noncomputable def decode (c : PolynomialCode n) : MvPolynomial (Fin n) ℚ :=
  (c.map decodeTerm).sum

@[simp]
theorem decode_nil : decode ([] : PolynomialCode n) = 0 := rfl

@[simp]
theorem decode_cons (t : ExponentCode n × RationalCode)
    (c : PolynomialCode n) :
    decode (t :: c) = decodeTerm t + decode c := rfl

noncomputable section

/-- A normalized sparse code obtained from the actual support of a
polynomial.  `Finset.toList` only chooses an order; decoding is independent
of that order. -/
def encode (p : MvPolynomial (Fin n) ℚ) : PolynomialCode n :=
  p.support.toList.map fun e ↦
    (ExponentCode.encode e, RationalCode.encode (coeff e p))

/-- The list sum underlying `encode` is the standard support sum. -/
private theorem sum_encode_terms (p : MvPolynomial (Fin n) ℚ) :
    ((p.support.toList.map fun e ↦ monomial e (coeff e p))).sum =
      ∑ e ∈ p.support, monomial e (coeff e p) := by
  change
    ((p.support.toList : Multiset (Fin n →₀ ℕ)).map
      fun e ↦ monomial e (coeff e p)).sum =
      ∑ e ∈ p.support, monomial e (coeff e p)
  rw [Finset.coe_toList]
  rfl

/-- Every rational polynomial has a finite code. -/
@[simp]
theorem decode_encode (p : MvPolynomial (Fin n) ℚ) :
    decode (encode p) = p := by
  rw [decode, encode, List.map_map]
  change
    ((p.support.toList.map fun e ↦
      monomial (ExponentCode.decode (ExponentCode.encode e))
        (RationalCode.decode (RationalCode.encode (coeff e p))))).sum = p
  simp_rw [ExponentCode.decode_encode, RationalCode.decode_encode]
  rw [sum_encode_terms, support_sum_monomial_coeff]

/-- Decoding raw sparse polynomial codes is onto. -/
theorem decode_surjective :
    Function.Surjective (decode : PolynomialCode n → MvPolynomial (Fin n) ℚ) :=
  fun p ↦ ⟨encode p, decode_encode p⟩

/-- Canonicalize a raw code semantically: combine equal exponents, remove
zero coefficients, canonically encode rational coefficients, and choose the
fixed support-list order. -/
def normalize (c : PolynomialCode n) : PolynomialCode n :=
  encode (decode c)

@[simp]
theorem decode_normalize (c : PolynomialCode n) :
    decode (normalize c) = decode c :=
  decode_encode _

@[simp]
theorem normalize_idempotent (c : PolynomialCode n) :
    normalize (normalize c) = normalize c := by
  unfold normalize
  rw [decode_encode]

/-- A normalized code has no repeated exponent vectors. -/
theorem normalize_exponents_nodup (c : PolynomialCode n) :
    ((normalize c).map Prod.fst).Nodup := by
  unfold normalize encode
  rw [List.map_map]
  simpa only [Function.comp_apply] using
    (decode c).support.nodup_toList.map
      (Finsupp.equivFunOnFinite.injective)

/-- A normalized code contains no zero coefficient. -/
theorem normalize_coefficients_ne_zero (c : PolynomialCode n)
    (t : ExponentCode n × RationalCode) (ht : t ∈ normalize c) :
    RationalCode.decode t.2 ≠ 0 := by
  unfold normalize encode at ht
  simp only [List.mem_map] at ht
  obtain ⟨e, he, rfl⟩ := ht
  simpa only [RationalCode.decode_encode] using
    (MvPolynomial.mem_support_iff.mp
      (Finset.mem_toList.mp he))

end

/-! ## Effective coefficient extraction -/

/-- Add all coefficients attached to a given exponent vector.  This is a
total executable operation on the raw list and therefore automatically
handles duplicates and cancellation. -/
def coefficient (e : ExponentCode n) (c : PolynomialCode n) :
    RationalCode :=
  c.foldr
    (fun t acc ↦
      if t.1 = e then RationalCode.add t.2 acc else acc)
    RationalCode.zero

@[simp]
theorem coefficient_nil (e : ExponentCode n) :
    coefficient e ([] : PolynomialCode n) = RationalCode.zero := rfl

@[simp]
theorem coefficient_cons (e : ExponentCode n)
    (t : ExponentCode n × RationalCode) (c : PolynomialCode n) :
    coefficient e (t :: c) =
      if t.1 = e then RationalCode.add t.2 (coefficient e c)
      else coefficient e c := rfl

/-- The executable coefficient accumulator agrees with semantic
`MvPolynomial.coeff`. -/
@[simp]
theorem decode_coefficient (e : ExponentCode n)
    (c : PolynomialCode n) :
    RationalCode.decode (coefficient e c) =
      coeff (ExponentCode.decode e) (decode c) := by
  induction c with
  | nil =>
      simp [coefficient]
  | cons t c ih =>
      rw [coefficient_cons, decode_cons, coeff_add]
      by_cases h : t.1 = e
      · subst h
        simp [decodeTerm, ih]
      · have hdecode :
            ExponentCode.decode t.1 ≠ ExponentCode.decode e :=
          fun h' ↦ h (ExponentCode.decode_injective h')
        simp [h, decodeTerm, hdecode, ih]

/-- The exponent vectors occurring syntactically in a raw code. -/
def exponents (c : PolynomialCode n) : List (ExponentCode n) :=
  c.map Prod.fst

theorem coefficient_eq_zero_of_not_mem (e : ExponentCode n)
    (c : PolynomialCode n) (h : e ∉ exponents c) :
    coefficient e c = RationalCode.zero := by
  induction c with
  | nil => rfl
  | cons t c ih =>
      simp only [exponents, List.map_cons, List.mem_cons, not_or] at h
      have hne : t.1 ≠ e := fun h' ↦ h.1 h'.symm
      rw [coefficient_cons, if_neg hne, ih h.2]

/-! ## Executable polynomial arithmetic -/

/-- The zero polynomial code. -/
def zero : PolynomialCode n :=
  []

/-- The constant-one polynomial code. -/
def one : PolynomialCode n :=
  [(ExponentCode.zero, RationalCode.one)]

/-- A one-term code for a constant rational. -/
def constant (q : RationalCode) : PolynomialCode n :=
  [(ExponentCode.zero, q)]

@[simp]
theorem decode_zero_code :
    decode (zero : PolynomialCode n) = 0 := rfl

@[simp]
theorem decode_one_code :
    decode (one : PolynomialCode n) = 1 := by
  simp [one, decodeTerm]

@[simp]
theorem decode_constant (q : RationalCode) :
    decode (constant q : PolynomialCode n) =
      C (RationalCode.decode q) := by
  rw [constant, decode_cons, decode_nil, add_zero]
  change
    monomial (ExponentCode.decode ExponentCode.zero)
      (RationalCode.decode q) =
      C (RationalCode.decode q)
  rw [ExponentCode.decode_zero]
  exact (C_apply (σ := Fin n) (a := RationalCode.decode q)).symm

/-- Addition is concatenation of raw monomial lists. -/
def add (a b : PolynomialCode n) : PolynomialCode n :=
  a ++ b

@[simp]
theorem decode_append (a b : PolynomialCode n) :
    decode (a ++ b) = decode a + decode b := by
  induction a with
  | nil => simp
  | cons t a ih =>
      simp only [List.cons_append, decode_cons, ih]
      ac_rfl

@[simp]
theorem decode_add_code (a b : PolynomialCode n) :
    decode (add a b) = decode a + decode b := by
  exact decode_append a b

/-- Negate every coefficient in a polynomial code. -/
def neg (a : PolynomialCode n) : PolynomialCode n :=
  a.map fun t ↦ (t.1, RationalCode.neg t.2)

@[simp]
theorem decode_neg_code (a : PolynomialCode n) :
    decode (neg a) = -decode a := by
  unfold neg
  induction a with
  | nil => simp
  | cons t a ih =>
      simp only [List.map_cons, decode_cons, decodeTerm,
        RationalCode.decode_neg, ih, neg_add_rev]
      have hmonomial :
          (monomial (ExponentCode.decode t.1)
              (-RationalCode.decode t.2) :
            MvPolynomial (Fin n) ℚ) =
            -monomial (ExponentCode.decode t.1)
              (RationalCode.decode t.2) :=
        (monomial (R := ℚ) (ExponentCode.decode t.1)).map_neg _
      rw [hmonomial]
      ac_rfl

/-- Subtraction of polynomial codes. -/
def sub (a b : PolynomialCode n) : PolynomialCode n :=
  add a (neg b)

@[simp]
theorem decode_sub_code (a b : PolynomialCode n) :
    decode (sub a b) = decode a - decode b := by
  simp [sub, sub_eq_add_neg]

/-- Multiply two coded monomials. -/
def mulTerm (a b : ExponentCode n × RationalCode) :
    ExponentCode n × RationalCode :=
  (ExponentCode.add a.1 b.1, RationalCode.mul a.2 b.2)

@[simp]
theorem decodeTerm_mulTerm
    (a b : ExponentCode n × RationalCode) :
    decodeTerm (mulTerm a b) = decodeTerm a * decodeTerm b := by
  simp [decodeTerm, mulTerm, monomial_mul]

/-- Multiply every monomial in a code by one fixed monomial. -/
def mulByTerm (a : ExponentCode n × RationalCode)
    (b : PolynomialCode n) : PolynomialCode n :=
  b.map (mulTerm a)

@[simp]
theorem decode_mulByTerm
    (a : ExponentCode n × RationalCode) (b : PolynomialCode n) :
    decode (mulByTerm a b) = decodeTerm a * decode b := by
  unfold mulByTerm
  induction b with
  | nil => simp
  | cons t b ih =>
      simp [ih, mul_add]

/-- Distributive product of raw sparse polynomial codes. -/
def mul : PolynomialCode n → PolynomialCode n → PolynomialCode n
  | [], _ => []
  | a :: as, b => mulByTerm a b ++ mul as b

@[simp]
theorem decode_mul_code (a b : PolynomialCode n) :
    decode (mul a b) = decode a * decode b := by
  induction a with
  | nil => simp [mul]
  | cons t a ih =>
      simp [mul, ih, add_mul]

/-- Natural powers in the raw polynomial-code algebra. -/
def pow (a : PolynomialCode n) : ℕ → PolynomialCode n
  | 0 => one
  | k + 1 => mul a (pow a k)

@[simp]
theorem decode_pow_code (a : PolynomialCode n) (k : ℕ) :
    decode (pow a k) = decode a ^ k := by
  induction k with
  | zero => simp [pow]
  | succ k ih => simp [pow, ih, pow_succ, mul_comm]

/-! ## Executable exact equality -/

/-- Two raw codes are semantically equal when they decode to the same
polynomial.  This relation correctly accounts for repeated exponents and
cancellation of coefficients. -/
def SemanticallyEqual (a b : PolynomialCode n) : Prop :=
  decode a = decode b

noncomputable instance (a b : PolynomialCode n) :
    Decidable (SemanticallyEqual a b) :=
  inferInstanceAs (Decidable (decode a = decode b))

/-- Executable Boolean checker for exact polynomial equality.

Only exponents actually occurring in one of the two lists need to be
checked.  At each such exponent, the rational accumulator combines all
duplicates before comparing by exact cross multiplication. -/
def equal (a b : PolynomialCode n) : Bool :=
  (exponents a ++ exponents b).all fun e ↦
    RationalCode.equal (coefficient e a) (coefficient e b)

private theorem equal_eq_true_iff_coefficients
    (a b : PolynomialCode n) :
    equal a b = true ↔
      ∀ e ∈ exponents a ++ exponents b,
        RationalCode.decode (coefficient e a) =
          RationalCode.decode (coefficient e b) := by
  simp only [equal, List.all_eq_true, RationalCode.equal_eq_true_iff,
    List.mem_append]

@[simp]
theorem equal_eq_true_iff (a b : PolynomialCode n) :
    equal a b = true ↔ decode a = decode b := by
  rw [equal_eq_true_iff_coefficients]
  constructor
  · intro h
    ext m
    let e := ExponentCode.encode m
    have hea :
        RationalCode.decode (coefficient e a) =
          coeff m (decode a) := by
      exact (decode_coefficient e a).trans (by simp [e])
    have heb :
        RationalCode.decode (coefficient e b) =
          coeff m (decode b) := by
      exact (decode_coefficient e b).trans (by simp [e])
    by_cases he : e ∈ exponents a ++ exponents b
    · exact hea.symm.trans ((h e he).trans heb)
    · have hpair : e ∉ exponents a ∧ e ∉ exponents b := by
        simpa only [List.mem_append, not_or] using he
      have hena : e ∉ exponents a := hpair.1
      have henb : e ∉ exponents b := by
        exact hpair.2
      rw [coefficient_eq_zero_of_not_mem e a hena,
        RationalCode.decode_zero] at hea
      rw [coefficient_eq_zero_of_not_mem e b henb,
        RationalCode.decode_zero] at heb
      exact hea.symm.trans heb
  · intro h e he
    rw [decode_coefficient, decode_coefficient, h]

@[simp]
theorem equal_eq_false_iff (a b : PolynomialCode n) :
    equal a b = false ↔ decode a ≠ decode b := by
  simp only [Bool.eq_false_iff, ne_eq, equal_eq_true_iff]

/-! ## Executable homogeneity -/

/-- The support-based predicate saying that every nonzero monomial in the
decoded polynomial has total degree `d`. -/
def IsHomogeneousOfDegree (d : ℕ) (c : PolynomialCode n) : Prop :=
  ∀ e ∈ (decode c).support, e.degree = d

noncomputable instance (d : ℕ) (c : PolynomialCode n) :
    Decidable (IsHomogeneousOfDegree d c) :=
  inferInstanceAs
    (Decidable (∀ e ∈ (decode c).support, e.degree = d))

/-- The finite support checker is exactly Mathlib's semantic notion of a
homogeneous multivariate polynomial. -/
theorem isHomogeneousOfDegree_iff (d : ℕ) (c : PolynomialCode n) :
    IsHomogeneousOfDegree d c ↔ (decode c).IsHomogeneous d := by
  constructor
  · intro h e he
    simpa only [Finsupp.degree_apply, Finsupp.weight_apply, Pi.one_apply,
      smul_eq_mul, mul_one] using
      h e (MvPolynomial.mem_support_iff.mpr he)
  · intro h e he
    simpa only [Finsupp.degree_apply, Finsupp.weight_apply, Pi.one_apply,
      smul_eq_mul, mul_one] using
      h (MvPolynomial.mem_support_iff.mp he)

/-- Executable homogeneity checker.

For every syntactically occurring exponent, the accumulated coefficient is
either zero (because duplicate terms cancelled) or the total degree is
exactly `d`. -/
def homogeneous (d : ℕ) (c : PolynomialCode n) : Bool :=
  (exponents c).all fun e ↦
    RationalCode.equal (coefficient e c) RationalCode.zero ||
      decide (ExponentCode.totalDegree e = d)

private theorem homogeneous_eq_true_iff_coefficients
    (d : ℕ) (c : PolynomialCode n) :
    homogeneous d c = true ↔
      ∀ e ∈ exponents c,
        RationalCode.decode (coefficient e c) = 0 ∨
          ExponentCode.totalDegree e = d := by
  simp [homogeneous]

@[simp]
theorem homogeneous_eq_true_iff (d : ℕ) (c : PolynomialCode n) :
    homogeneous d c = true ↔ (decode c).IsHomogeneous d := by
  rw [homogeneous_eq_true_iff_coefficients]
  constructor
  · intro h m hm
    let e := ExponentCode.encode m
    have hecoeff :
        RationalCode.decode (coefficient e c) =
          coeff m (decode c) := by
      exact (decode_coefficient e c).trans (by simp [e])
    have he_mem : e ∈ exponents c := by
      by_contra hnot
      rw [coefficient_eq_zero_of_not_mem e c hnot,
        RationalCode.decode_zero] at hecoeff
      exact hm hecoeff.symm
    rcases h e he_mem with hzero | hdegree
    · exact (hm (hecoeff ▸ hzero)).elim
    · have hmdegree : m.degree = d := by
        rw [← ExponentCode.decode_encode m,
          ExponentCode.degree_decode]
        exact hdegree
      simpa only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul,
        mul_one, Finsupp.degree_apply] using hmdegree
  · intro h e he
    by_cases hzero : RationalCode.decode (coefficient e c) = 0
    · exact Or.inl hzero
    · right
      have hcoeff :
          coeff (ExponentCode.decode e) (decode c) ≠ 0 := by
        simpa only [decode_coefficient] using hzero
      have hweight := h hcoeff
      have hdegree : (ExponentCode.decode e).degree = d := by
        simpa only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul,
          mul_one, Finsupp.degree_apply] using hweight
      simpa only [ExponentCode.degree_decode] using hdegree

@[simp]
theorem homogeneous_eq_false_iff (d : ℕ) (c : PolynomialCode n) :
    homogeneous d c = false ↔ ¬(decode c).IsHomogeneous d := by
  simp only [Bool.eq_false_iff, ne_eq, homogeneous_eq_true_iff]

end PolynomialCode

/-! The code types are built only from standard primitive-codable
constructors.  These declarations are compile-time checks that exhaustive
enumeration is available for fixed `n`. -/

example : Primcodable RationalCode := inferInstance
example (n : ℕ) : Primcodable (ExponentCode n) := inferInstance
example (n : ℕ) : Primcodable (PolynomialCode n) := inferInstance

/-! ## Primitive-recursiveness of coefficient arithmetic -/

namespace SignedMagnitudeCode

theorem neg_primrec : Primrec neg :=
  Primrec.pair
    (Primrec.not.comp Primrec.fst)
    Primrec.snd

theorem mul_primrec : Primrec₂ mul := by
  exact Primrec.pair
    ((Primrec.dom_bool₂ xor).comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd))
    (Primrec.nat_mul.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd))

theorem add_primrec : Primrec₂ add := by
  have hsame :
      PrimrecPred
        (fun p : SignedMagnitudeCode × SignedMagnitudeCode ↦
          p.1.1 = p.2.1) :=
    Primrec.eq.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
  have hle :
      PrimrecPred
        (fun p : SignedMagnitudeCode × SignedMagnitudeCode ↦
          p.1.2 ≤ p.2.2) :=
    Primrec.nat_le.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  have hsameValue :
      Primrec
        (fun p : SignedMagnitudeCode × SignedMagnitudeCode ↦
          (p.1.1, p.1.2 + p.2.2)) :=
    Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.nat_add.comp
        (Primrec.snd.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd))
  have hleValue :
      Primrec
        (fun p : SignedMagnitudeCode × SignedMagnitudeCode ↦
          (p.2.1, p.2.2 - p.1.2)) :=
    Primrec.pair
      (Primrec.fst.comp Primrec.snd)
      (Primrec.nat_sub.comp
        (Primrec.snd.comp Primrec.snd)
        (Primrec.snd.comp Primrec.fst))
  have hgtValue :
      Primrec
        (fun p : SignedMagnitudeCode × SignedMagnitudeCode ↦
          (p.1.1, p.1.2 - p.2.2)) :=
    Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.nat_sub.comp
        (Primrec.snd.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd))
  exact
    (Primrec.ite hsame hsameValue
      (Primrec.ite hle hleValue hgtValue)).of_eq fun p ↦ by
        simp only [add]

theorem equal_primrec : Primrec₂ equal := by
  have hmag :
      Primrec
        (fun p : SignedMagnitudeCode × SignedMagnitudeCode ↦
          p.1.2 == p.2.2) :=
    Primrec.beq.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  have hzero :
      Primrec
        (fun p : SignedMagnitudeCode × SignedMagnitudeCode ↦
          p.1.2 == 0) :=
    Primrec.beq.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.const 0)
  have hsign :
      Primrec
        (fun p : SignedMagnitudeCode × SignedMagnitudeCode ↦
          p.1.1 == p.2.1) :=
    Primrec.beq.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
  exact
    (Primrec.and.comp hmag (Primrec.or.comp hzero hsign)).of_eq
      fun _ ↦ rfl

theorem positive_primrec : Primrec positive := by
  exact
    (Primrec.and.comp
      (Primrec.not.comp Primrec.fst)
      (Primrec.not.comp
        (Primrec.beq.comp Primrec.snd (Primrec.const 0)))).of_eq
      fun _ ↦ rfl

end SignedMagnitudeCode

namespace RationalCode

theorem denominatorProductMinusOne_primrec :
    Primrec₂ denominatorProductMinusOne := by
  exact
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp Primrec.fst Primrec.snd)
      (Primrec.nat_mul.comp Primrec.fst Primrec.snd)).of_eq
      fun _ ↦ rfl

theorem neg_primrec : Primrec neg :=
  Primrec.pair
    (SignedMagnitudeCode.neg_primrec.comp Primrec.fst)
    Primrec.snd

theorem mul_primrec : Primrec₂ mul := by
  exact Primrec.pair
    (SignedMagnitudeCode.mul_primrec.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd))
    (denominatorProductMinusOne_primrec.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd))

theorem add_primrec : Primrec₂ add := by
  have hdenA :
      Primrec
        (fun p : RationalCode × RationalCode ↦
          ((false, p.2.2 + 1) : SignedMagnitudeCode)) :=
    Primrec.pair (Primrec.const false)
      (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
  have hdenB :
      Primrec
        (fun p : RationalCode × RationalCode ↦
          ((false, p.1.2 + 1) : SignedMagnitudeCode)) :=
    Primrec.pair (Primrec.const false)
      (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))
  have hcrossA :
      Primrec
        (fun p : RationalCode × RationalCode ↦
          SignedMagnitudeCode.mul p.1.1 (false, p.2.2 + 1)) :=
    SignedMagnitudeCode.mul_primrec.comp
      (Primrec.fst.comp Primrec.fst) hdenA
  have hcrossB :
      Primrec
        (fun p : RationalCode × RationalCode ↦
          SignedMagnitudeCode.mul p.2.1 (false, p.1.2 + 1)) :=
    SignedMagnitudeCode.mul_primrec.comp
      (Primrec.fst.comp Primrec.snd) hdenB
  exact Primrec.pair
    (SignedMagnitudeCode.add_primrec.comp hcrossA hcrossB)
    (denominatorProductMinusOne_primrec.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd))

theorem equal_primrec : Primrec₂ equal := by
  have hdenA :
      Primrec
        (fun p : RationalCode × RationalCode ↦
          ((false, p.2.2 + 1) : SignedMagnitudeCode)) :=
    Primrec.pair (Primrec.const false)
      (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
  have hdenB :
      Primrec
        (fun p : RationalCode × RationalCode ↦
          ((false, p.1.2 + 1) : SignedMagnitudeCode)) :=
    Primrec.pair (Primrec.const false)
      (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))
  exact SignedMagnitudeCode.equal_primrec.comp
    (SignedMagnitudeCode.mul_primrec.comp
      (Primrec.fst.comp Primrec.fst) hdenA)
    (SignedMagnitudeCode.mul_primrec.comp
      (Primrec.fst.comp Primrec.snd) hdenB)

theorem positive_primrec : Primrec positive :=
  SignedMagnitudeCode.positive_primrec.comp Primrec.fst

end RationalCode

namespace ExponentCode

theorem add_primrec {n : ℕ} :
    Primrec₂ (add : ExponentCode n → ExponentCode n → ExponentCode n) := by
  change
    Primrec
      (fun p : ExponentCode n × ExponentCode n ↦ add p.1 p.2)
  rw [Primrec.fin_curry]
  exact Primrec.nat_add.comp
    (Primrec.fin_app.comp
      (Primrec.fst.comp Primrec.fst)
      Primrec.snd)
    (Primrec.fin_app.comp
      (Primrec.snd.comp Primrec.fst)
      Primrec.snd)

private theorem natListSum_primrec :
    Primrec (fun l : List ℕ ↦ l.sum) := by
  have hstep :
      Primrec₂
        (fun (_ : List ℕ) (p : ℕ × ℕ) ↦ p.1 + p.2) :=
    Primrec.nat_add.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.list_foldr Primrec.id (Primrec.const 0) hstep).of_eq
      fun _ ↦ rfl

theorem totalDegree_primrec {n : ℕ} :
    Primrec (totalDegree : ExponentCode n → ℕ) := by
  have hlist :
      Primrec
        (fun e : ExponentCode n ↦ List.ofFn fun i ↦ e i) :=
    Primrec.list_ofFn fun i ↦
      Primrec.fin_app.comp Primrec.id (Primrec.const i)
  exact natListSum_primrec.comp hlist

end ExponentCode

namespace PolynomialCode

private theorem boolListAll_primrec :
    Primrec (fun l : List Bool ↦ l.all id) := by
  have hstep :
      Primrec₂
        (fun (_ : List Bool) (p : Bool × Bool) ↦ p.1 && p.2) :=
    Primrec.and.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  refine
    (Primrec.list_foldr Primrec.id (Primrec.const true) hstep).of_eq ?_
  intro l
  induction l with
  | nil => rfl
  | cons b l ih =>
      change
        List.foldr (fun b s ↦ b && s) true l = l.all id at ih
      change
        (b && List.foldr (fun b s ↦ b && s) true l) =
          (b && l.all id)
      rw [ih]

theorem exponents_primrec {n : ℕ} :
    Primrec (exponents : PolynomialCode n → List (ExponentCode n)) := by
  exact
    (Primrec.list_map Primrec.id
      ((Primrec.fst.comp Primrec.snd).to₂)).of_eq
      fun _ ↦ rfl

theorem constant_primrec {n : ℕ} :
    Primrec (constant : RationalCode → PolynomialCode n) := by
  exact Primrec.list_cons.comp
    (Primrec.pair
      (Primrec.const (ExponentCode.zero : ExponentCode n))
      Primrec.id)
    (Primrec.const [])

theorem add_primrec {n : ℕ} :
    Primrec₂ (add : PolynomialCode n → PolynomialCode n →
      PolynomialCode n) :=
  Primrec.list_append

theorem neg_primrec {n : ℕ} :
    Primrec (neg : PolynomialCode n → PolynomialCode n) := by
  have hterm :
      Primrec₂
        (fun (_ : PolynomialCode n)
          (t : ExponentCode n × RationalCode) ↦
            (t.1, RationalCode.neg t.2)) :=
    Primrec.pair
      (Primrec.fst.comp₂ Primrec₂.right)
      (RationalCode.neg_primrec.comp
        (Primrec.snd.comp₂ Primrec₂.right))
  exact
    (Primrec.list_map Primrec.id hterm).of_eq
      fun _ ↦ rfl

theorem mulTerm_primrec {n : ℕ} :
    Primrec₂ (mulTerm :
      (ExponentCode n × RationalCode) →
      (ExponentCode n × RationalCode) →
      (ExponentCode n × RationalCode)) := by
  exact Primrec.pair
    (ExponentCode.add_primrec.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd))
    (RationalCode.mul_primrec.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd))

theorem mulByTerm_primrec {n : ℕ} :
    Primrec₂ (mulByTerm :
      (ExponentCode n × RationalCode) →
      PolynomialCode n → PolynomialCode n) := by
  have hterm :
      Primrec₂
        (fun (p :
            (ExponentCode n × RationalCode) × PolynomialCode n)
          (t : ExponentCode n × RationalCode) ↦
            mulTerm p.1 t) :=
    mulTerm_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.left)
      Primrec₂.right
  exact
    (Primrec.list_map Primrec₂.right hterm).of_eq
      fun _ ↦ rfl

theorem mul_primrec {n : ℕ} :
    Primrec₂ (mul : PolynomialCode n → PolynomialCode n →
      PolynomialCode n) := by
  have hstep :
      Primrec₂
        (fun (p : PolynomialCode n × PolynomialCode n)
          (q : (ExponentCode n × RationalCode) × PolynomialCode n) ↦
            mulByTerm q.1 p.2 ++ q.2) :=
    Primrec.list_append.comp₂
      (mulByTerm_primrec.comp₂
        (Primrec.fst.comp₂ Primrec₂.right)
        (Primrec.snd.comp₂ Primrec₂.left))
      (Primrec.snd.comp₂ Primrec₂.right)
  refine
    (Primrec.list_foldr Primrec.fst (Primrec.const []) hstep).of_eq ?_
  intro p
  induction p.1 with
  | nil => rfl
  | cons t a ih =>
      change
        mulByTerm t p.2 ++
          List.foldr
            (fun t acc ↦ mulByTerm t p.2 ++ acc) [] a =
          mul (t :: a) p.2
      rw [ih]
      rfl

theorem pow_primrec {n : ℕ} :
    Primrec₂ (pow : PolynomialCode n → ℕ → PolynomialCode n) := by
  have hstep :
      Primrec₂
        (fun (a : PolynomialCode n)
          (p : ℕ × PolynomialCode n) ↦ mul a p.2) :=
    mul_primrec.comp₂ Primrec₂.left
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.nat_rec
      (Primrec.const (one : PolynomialCode n)) hstep).of_eq
      fun a k ↦ by
        induction k with
        | zero => rfl
        | succ k ih =>
            simp only [pow]
            rw [ih]

theorem sub_primrec {n : ℕ} :
    Primrec₂ (sub : PolynomialCode n → PolynomialCode n →
      PolynomialCode n) := by
  exact add_primrec.comp Primrec.fst
    (neg_primrec.comp Primrec.snd)

theorem coefficient_primrec {n : ℕ} :
    Primrec₂ (coefficient :
      ExponentCode n → PolynomialCode n → RationalCode) := by
  have hcondition :
      PrimrecPred
        (fun r :
            (ExponentCode n × PolynomialCode n) ×
              ((ExponentCode n × RationalCode) × RationalCode) ↦
          r.2.1.1 = r.1.1) :=
    Primrec.eq.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp Primrec.fst)
  have hadd :
      Primrec
        (fun r :
            (ExponentCode n × PolynomialCode n) ×
              ((ExponentCode n × RationalCode) × RationalCode) ↦
          RationalCode.add r.2.1.2 r.2.2) :=
    RationalCode.add_primrec.comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have hkeep :
      Primrec
        (fun r :
            (ExponentCode n × PolynomialCode n) ×
              ((ExponentCode n × RationalCode) × RationalCode) ↦
          r.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hstep :
      Primrec₂
        (fun (p : ExponentCode n × PolynomialCode n)
          (q : (ExponentCode n × RationalCode) × RationalCode) ↦
            if q.1.1 = p.1 then
              RationalCode.add q.1.2 q.2
            else q.2) :=
    (Primrec.ite hcondition hadd hkeep).to₂
  exact
    (Primrec.list_foldr Primrec.snd
      (Primrec.const RationalCode.zero) hstep).to₂.of_eq
      fun _ _ ↦ rfl

theorem equal_primrec {n : ℕ} :
    Primrec₂ (equal : PolynomialCode n → PolynomialCode n → Bool) := by
  have hexponents :
      Primrec
        (fun p : PolynomialCode n × PolynomialCode n ↦
          exponents p.1 ++ exponents p.2) :=
    Primrec.list_append.comp
      (exponents_primrec.comp Primrec.fst)
      (exponents_primrec.comp Primrec.snd)
  have hcompare :
      Primrec₂
        (fun (p : PolynomialCode n × PolynomialCode n)
          (e : ExponentCode n) ↦
            RationalCode.equal
              (coefficient e p.1) (coefficient e p.2)) :=
    RationalCode.equal_primrec.comp₂
      (coefficient_primrec.comp₂ Primrec₂.right
        (Primrec.fst.comp₂ Primrec₂.left))
      (coefficient_primrec.comp₂ Primrec₂.right
        (Primrec.snd.comp₂ Primrec₂.left))
  have hchecks :
      Primrec
        (fun p : PolynomialCode n × PolynomialCode n ↦
          (exponents p.1 ++ exponents p.2).map
            (fun e ↦ RationalCode.equal
              (coefficient e p.1) (coefficient e p.2))) :=
    Primrec.list_map hexponents hcompare
  exact
    (boolListAll_primrec.comp hchecks).to₂.of_eq
      fun a b ↦ by
        simp [equal]

theorem homogeneous_primrec {n : ℕ} :
    Primrec₂ (homogeneous : ℕ → PolynomialCode n → Bool) := by
  have hexponents :
      Primrec
        (fun p : ℕ × PolynomialCode n ↦ exponents p.2) :=
    exponents_primrec.comp Primrec.snd
  have hcoefficient :
      Primrec₂
        (fun (p : ℕ × PolynomialCode n) (e : ExponentCode n) ↦
          coefficient e p.2) :=
    coefficient_primrec.comp₂ Primrec₂.right
      (Primrec.snd.comp₂ Primrec₂.left)
  have hzero :
      Primrec₂
        (fun (p : ℕ × PolynomialCode n) (e : ExponentCode n) ↦
          RationalCode.equal (coefficient e p.2)
            RationalCode.zero) :=
    RationalCode.equal_primrec.comp₂ hcoefficient
      (Primrec.const RationalCode.zero)
  have hdegree :
      Primrec₂
        (fun (p : ℕ × PolynomialCode n) (e : ExponentCode n) ↦
          ExponentCode.totalDegree e == p.1) :=
    Primrec.beq.comp₂
      (ExponentCode.totalDegree_primrec.comp₂ Primrec₂.right)
      (Primrec.fst.comp₂ Primrec₂.left)
  have hcheck :
      Primrec₂
        (fun (p : ℕ × PolynomialCode n) (e : ExponentCode n) ↦
          RationalCode.equal (coefficient e p.2)
              RationalCode.zero ||
            decide (ExponentCode.totalDegree e = p.1)) := by
    exact
      (Primrec.or.comp₂ hzero hdegree).of_eq fun _ _ ↦ by
        simp only [Bool.beq_eq_decide_eq]
  have hchecks :
      Primrec
        (fun p : ℕ × PolynomialCode n ↦
          (exponents p.2).map fun e ↦
            RationalCode.equal (coefficient e p.2)
                RationalCode.zero ||
              decide (ExponentCode.totalDegree e = p.1)) :=
    Primrec.list_map hexponents hcheck
  exact
    (boolListAll_primrec.comp hchecks).to₂.of_eq
      fun d c ↦ by
        simp [homogeneous]

end PolynomialCode

end HGAS
