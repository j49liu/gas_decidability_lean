import HGAS.Clocks.ControllerPhaseProductCharacterCode
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Effectivity of the controller-product character compiler

For fixed `q`, this file proves primitive-recursiveness of the complete
maps

```
  exponents                 ↦ characterCode exponents
  (parameters, exponents)   ↦ derivativeCode parameters exponents.
```

The only subtle point is the integral exponent type.  Mathlib equips
`ℤ` with its canonical zig-zag encoding

```
  0 ↦ 0,  -1 ↦ 1,  1 ↦ 2,  -2 ↦ 3,  2 ↦ 4, ...
```

so negativity is parity of the code and `natAbs` is half of one plus the
code.  We prove those two operations primitive recursive explicitly.
This permits a uniform compiler theorem in the exponent tuple; no
fixed-exponent fallback is needed.

All remaining operations are finite sparse-syntax operations: tuple
projection, complex-pair multiplication, natural recursion for powers,
finite-list products, and the existing rational linear-frequency
compiler.
-/

namespace HGAS.Clocks.ControllerPhaseProductCharacterCode

open HGAS

variable {n q : ℕ}

/-! ## Primitive-recursive complex-pair syntax -/

theorem neg_primrec :
    Primrec (neg : ComplexPairCode n → ComplexPairCode n) :=
  Primrec.pair
    (PolynomialCode.neg_primrec.comp Primrec.fst)
    (PolynomialCode.neg_primrec.comp Primrec.snd)

theorem conj_primrec :
    Primrec (conj : ComplexPairCode n → ComplexPairCode n) :=
  Primrec.pair Primrec.fst
    (PolynomialCode.neg_primrec.comp Primrec.snd)

/-- Literal multiplication of complex-pair sparse codes is primitive
recursive. -/
theorem mul_primrec :
    Primrec₂ (mul :
      ComplexPairCode n → ComplexPairCode n →
        ComplexPairCode n) := by
  have hac :
      Primrec
        (fun input :
            ComplexPairCode n × ComplexPairCode n ↦
          PolynomialCode.mul input.1.1 input.2.1) :=
    PolynomialCode.mul_primrec.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
  have hbd :
      Primrec
        (fun input :
            ComplexPairCode n × ComplexPairCode n ↦
          PolynomialCode.mul input.1.2 input.2.2) :=
    PolynomialCode.mul_primrec.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  have had :
      Primrec
        (fun input :
            ComplexPairCode n × ComplexPairCode n ↦
          PolynomialCode.mul input.1.1 input.2.2) :=
    PolynomialCode.mul_primrec.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  have hbc :
      Primrec
        (fun input :
            ComplexPairCode n × ComplexPairCode n ↦
          PolynomialCode.mul input.1.2 input.2.1) :=
    PolynomialCode.mul_primrec.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
  exact
    Primrec.pair
      (PolynomialCode.sub_primrec.comp hac hbd)
      (PolynomialCode.add_primrec.comp had hbc)

/-- Natural powers are primitive recursive jointly in the complex-pair
code and the exponent. -/
theorem pow_primrec :
    Primrec₂ (pow :
      ComplexPairCode n → ℕ → ComplexPairCode n) := by
  have hstep :
      Primrec₂
        (fun (p : ComplexPairCode n)
          (state : ℕ × ComplexPairCode n) ↦
            mul p state.2) :=
    mul_primrec.comp₂ Primrec₂.left
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.nat_rec
      (Primrec.const (one : ComplexPairCode n))
      hstep).of_eq fun p k ↦ by
        induction k with
        | zero => rfl
        | succ k ih =>
            simp only [pow]
            rw [ih]

/-- Folding a finite list by complex-pair multiplication is primitive
recursive. -/
theorem product_primrec :
    Primrec
      (product :
        List (ComplexPairCode n) → ComplexPairCode n) := by
  have hstep :
      Primrec₂
        (fun (_ : List (ComplexPairCode n))
          (state :
            ComplexPairCode n × ComplexPairCode n) ↦
              mul state.1 state.2) :=
    mul_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.list_foldr Primrec.id
      (Primrec.const (one : ComplexPairCode n))
      hstep).of_eq fun ps ↦ by
        induction ps with
        | nil => rfl
        | cons p ps ih =>
            have ih' :
                List.foldr (fun b s ↦ mul b s)
                    (one : ComplexPairCode n) ps =
                  product ps := by
              simpa using ih
            simpa [product] using congrArg (mul p) ih'

/-! ## Effective integral exponent operations -/

/-- Absolute value on Mathlib's canonical primitive-codable integers is
primitive recursive.  Its zig-zag code satisfies
`natAbs e = (encode e + 1) / 2`. -/
theorem intNatAbs_primrec :
    Primrec Int.natAbs := by
  exact
    (Primrec.nat_div.comp
      (Primrec.nat_add.comp
        (Primrec.encode :
          Primrec (fun e : ℤ ↦ Encodable.encode e))
        (Primrec.const 1))
      (Primrec.const 2)).of_eq fun e ↦ by
        cases e with
        | ofNat a =>
            change (2 * a + 1) / 2 = a
            omega
        | negSucc a =>
            change (2 * a + 1 + 1) / 2 = a + 1
            omega

/-- Strict negativity is primitive recursive on the canonical integer
encoding: precisely the negative integers have odd codes. -/
theorem intNegative_primrec :
    PrimrecPred (fun e : ℤ ↦ e < 0) := by
  have hmod :
      Primrec (fun e : ℤ ↦ Encodable.encode e % 2) :=
    Primrec.nat_mod.comp Primrec.encode (Primrec.const 2)
  exact
    (Primrec.eq.comp hmod (Primrec.const 1)).of_eq fun e ↦ by
      cases e with
      | ofNat a =>
          change 2 * a % 2 = 1 ↔ (a : ℤ) < 0
          simp
      | negSucc a =>
          change (2 * a + 1) % 2 = 1 ↔ Int.negSucc a < 0
          simp

/-- The project's canonical signed-magnitude encoding of an integer is
primitive recursive. -/
theorem signedMagnitudeEncode_primrec :
    Primrec SignedMagnitudeCode.encode := by
  exact
    (Primrec.pair intNegative_primrec.decide
      intNatAbs_primrec).of_eq fun e ↦ by
        cases e <;> simp [SignedMagnitudeCode.encode]

/-- Embedding an integer exponent as a denominator-one rational compiler
coefficient is primitive recursive. -/
theorem exponentWeightCode_primrec :
    Primrec exponentWeightCode := by
  exact
    (Primrec.pair signedMagnitudeEncode_primrec
      (Primrec.const 0)).of_eq fun e ↦ by
        simp [exponentWeightCode, RationalCode.encode,
          Rat.num_intCast, Rat.den_intCast]

/-! ## Complete character and derivative compilers -/

/-- For a fixed phase coordinate, compiling its signed integral power is
primitive recursive in the exponent. -/
theorem signedPowerCode_primrec
    (i : Fin q) :
    Primrec
      (signedPowerCode i :
        ℤ → ComplexPairCode
          (ControllerPhaseProductPolynomialCode.dimension q)) := by
  have hnegative :
      Primrec
        (fun e : ℤ ↦
          pow (conj (phaseCode i)) e.natAbs) :=
    pow_primrec.comp
      (Primrec.const (conj (phaseCode i)))
      intNatAbs_primrec
  have hnonnegative :
      Primrec
        (fun e : ℤ ↦
          pow (phaseCode i) e.natAbs) :=
    pow_primrec.comp
      (Primrec.const (phaseCode i))
      intNatAbs_primrec
  exact
    (Primrec.ite intNegative_primrec
      hnegative hnonnegative).of_eq fun e ↦ by
        rfl

/-- **Effective Laurent-character compiler.**

For fixed `q`, the complete real/imaginary sparse polynomial character
is primitive recursive in the entire integral exponent tuple. -/
theorem characterCode_primrec :
    Primrec
      (characterCode :
        (Fin q → ℤ) →
          ComplexPairCode
            (ControllerPhaseProductPolynomialCode.dimension q)) := by
  apply product_primrec.comp
  apply Primrec.list_ofFn
  intro i
  exact
    (signedPowerCode_primrec i).comp
      (Primrec.fin_app.comp Primrec.id
        (Primrec.const i))

theorem characterCode_computable :
    Computable
      (characterCode :
        (Fin q → ℤ) →
          ComplexPairCode
            (ControllerPhaseProductPolynomialCode.dimension q)) :=
  characterCode_primrec.to_comp

/-- Convert the complete exponent tuple to the rational weight tuple
used by the linear-frequency compiler. -/
theorem exponentWeights_primrec :
    Primrec
      (fun exponents : Fin q → ℤ ↦
        fun i ↦ exponentWeightCode (exponents i)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro i
  exact
    exponentWeightCode_primrec.comp
      (Primrec.fin_app.comp Primrec.id
        (Primrec.const i))

/-- Runtime input for the character-derivative compiler. -/
abbrev DerivativeCompilerInput (q : ℕ) :=
  (Fin q → RationalCode) × (Fin q → ℤ)

set_option maxHeartbeats 800000 in
-- Nested finite-function encodings make this composition costly to elaborate.
/-- The character-frequency polynomial is primitive recursive jointly in
the rational controller parameters and the integral exponent tuple. -/
theorem frequencyCode_primrec :
    Primrec
      (fun input : DerivativeCompilerInput q ↦
        frequencyCode input.1 input.2) := by
  exact
    ControllerPhaseProductLinearFrequencyCode.code_primrec.comp
      (Primrec.pair
        (exponentWeights_primrec.comp Primrec.snd)
        Primrec.fst)

set_option maxHeartbeats 800000 in
-- The output pair composes two nested finite-function compiler graphs.
/-- **Effective character-derivative compiler.**

The pair of sparse codes for
`i * frequency(parameters, exponents) * character(exponents)` is
primitive recursive jointly in both finite tuples. -/
theorem derivativeCode_primrec :
    Primrec
      (fun input : DerivativeCompilerInput q ↦
        derivativeCode input.1 input.2) := by
  have hfrequency :
      Primrec
        (fun input : DerivativeCompilerInput q ↦
          frequencyCode input.1 input.2) :=
    frequencyCode_primrec
  have hcharacter :
      Primrec
        (fun input : DerivativeCompilerInput q ↦
          characterCode input.2) :=
    characterCode_primrec.comp Primrec.snd
  exact
    Primrec.pair
      (PolynomialCode.neg_primrec.comp
        (PolynomialCode.mul_primrec.comp
          hfrequency
          (Primrec.snd.comp hcharacter)))
      (PolynomialCode.mul_primrec.comp
        hfrequency
        (Primrec.fst.comp hcharacter))

theorem derivativeCode_computable :
    Computable
      (fun input : DerivativeCompilerInput q ↦
        derivativeCode input.1 input.2) :=
  derivativeCode_primrec.to_comp

end HGAS.Clocks.ControllerPhaseProductCharacterCode
