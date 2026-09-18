import HGAS.Clocks.ControllerPhaseProductLinearFrequencyCode
import Mathlib.Tactic

/-!
# Laurent characters of a finite controller--phase product

The arithmetic source repeatedly uses integral characters of the phase
circles.  For an exponent vector `a : Fin q → ℤ` and phase coordinates

```
                         ζᵢ = cᵢ + i dᵢ,
```

the intended observable is

```
                         ∏ i, ζᵢ ^ aᵢ.
```

Negative powers are represented polynomially by conjugates.  This agrees
with the Laurent character on the unit circles because
`conj ζ = ζ⁻¹` there.  The present module stays algebraic and compiles the
real and imaginary parts as rational sparse polynomials in the full `4q`
controller--phase coordinates.

It also compiles the intended velocity.  If
`ζᵢ' = i (pᵢ rᵢ) ζᵢ`, then the character has velocity

```
            χ' = i (∑ i, aᵢ pᵢ rᵢ) χ.
```

The frequency in parentheses is supplied by the reusable rational linear
readout compiler.  Exact code-evaluation theorems hold at every structured
ambient state; no circle or controller-lock hypothesis is used in those
identities.
-/

namespace HGAS.Clocks.ControllerPhaseProductCharacterCode

open HGAS
open ControllerPhaseProductPolynomialCode

variable {n q : ℕ}

/-- A pair of real polynomial codes representing one complex polynomial
observable. -/
abbrev ComplexPairCode (n : ℕ) :=
  PolynomialCode n × PolynomialCode n

/-- Evaluate a pair of real polynomial codes as one complex number. -/
noncomputable def evalPair
    (p : ComplexPairCode n) (x : Fin n → ℝ) : ℂ :=
  ⟨MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
      (PolynomialCode.decode p.1),
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
      (PolynomialCode.decode p.2)⟩

def zero : ComplexPairCode n :=
  (PolynomialCode.zero, PolynomialCode.zero)

def one : ComplexPairCode n :=
  (PolynomialCode.one, PolynomialCode.zero)

def neg (p : ComplexPairCode n) : ComplexPairCode n :=
  (PolynomialCode.neg p.1, PolynomialCode.neg p.2)

def conj (p : ComplexPairCode n) : ComplexPairCode n :=
  (p.1, PolynomialCode.neg p.2)

/-- Literal complex multiplication in real coordinates. -/
def mul (p r : ComplexPairCode n) : ComplexPairCode n :=
  (PolynomialCode.sub
      (PolynomialCode.mul p.1 r.1)
      (PolynomialCode.mul p.2 r.2),
    PolynomialCode.add
      (PolynomialCode.mul p.1 r.2)
      (PolynomialCode.mul p.2 r.1))

/-- Natural powers in the complex-pair code ring. -/
def pow (p : ComplexPairCode n) : ℕ → ComplexPairCode n
  | 0 => one
  | k + 1 => mul p (pow p k)

/-- Product of a finite list of complex-pair codes. -/
def product : List (ComplexPairCode n) → ComplexPairCode n
  | [] => one
  | p :: ps => mul p (product ps)

@[simp]
theorem evalPair_zero (x : Fin n → ℝ) :
    evalPair zero x = 0 := by
  apply Complex.ext <;> simp [evalPair, zero]

@[simp]
theorem evalPair_one (x : Fin n → ℝ) :
    evalPair one x = 1 := by
  apply Complex.ext <;> simp [evalPair, one]

@[simp]
theorem evalPair_neg
    (p : ComplexPairCode n) (x : Fin n → ℝ) :
    evalPair (neg p) x = -evalPair p x := by
  apply Complex.ext <;> simp [evalPair, neg]

@[simp]
theorem evalPair_conj
    (p : ComplexPairCode n) (x : Fin n → ℝ) :
    evalPair (conj p) x = star (evalPair p x) := by
  apply Complex.ext <;> simp [evalPair, conj]

@[simp]
theorem evalPair_mul
    (p r : ComplexPairCode n) (x : Fin n → ℝ) :
    evalPair (mul p r) x = evalPair p x * evalPair r x := by
  apply Complex.ext <;>
    simp [evalPair, mul, Complex.mul_re, Complex.mul_im]

@[simp]
theorem evalPair_pow
    (p : ComplexPairCode n) (k : ℕ) (x : Fin n → ℝ) :
    evalPair (pow p k) x = evalPair p x ^ k := by
  induction k with
  | zero => simp [pow]
  | succ k ih =>
      simp [pow, ih, pow_succ, mul_comm]

@[simp]
theorem evalPair_product
    (ps : List (ComplexPairCode n)) (x : Fin n → ℝ) :
    evalPair (product ps) x =
      (ps.map fun p ↦ evalPair p x).prod := by
  induction ps with
  | nil => simp [product]
  | cons p ps ih => simp [product, ih]

/-! ## Phase characters in the controller product -/

def phaseReCode (a : Fin q) :
    PolynomialCode (dimension q) :=
  PolynomialCode.varCode
    (blockEmbedding a ControllerPolynomialCode.cIndex)

def phaseImCode (a : Fin q) :
    PolynomialCode (dimension q) :=
  PolynomialCode.varCode
    (blockEmbedding a ControllerPolynomialCode.dIndex)

def phaseCode (a : Fin q) :
    ComplexPairCode (dimension q) :=
  (phaseReCode a, phaseImCode a)

noncomputable def phaseValue
    (z : StateFamily q ℝ) (a : Fin q) : ℂ :=
  ⟨(z a).phase.c, (z a).phase.d⟩

@[simp]
theorem evalPair_phaseCode
    (z : StateFamily q ℝ) (a : Fin q) :
    evalPair (phaseCode a) (point z) = phaseValue z a := by
  apply Complex.ext <;>
    simp [evalPair, phaseCode, phaseReCode, phaseImCode,
      phaseValue, point, blockEmbedding,
      ControllerPolynomialCode.point,
      ControllerPolynomialCode.cIndex,
      ControllerPolynomialCode.dIndex]

/-- Polynomial representative of one signed integral phase power.
Negative exponents use the conjugate polynomial. -/
def signedPowerCode
    (a : Fin q) (e : ℤ) :
    ComplexPairCode (dimension q) :=
  if e < 0 then
    pow (conj (phaseCode a)) e.natAbs
  else
    pow (phaseCode a) e.natAbs

noncomputable def signedPowerValue
    (z : StateFamily q ℝ) (a : Fin q) (e : ℤ) : ℂ :=
  if e < 0 then
    star (phaseValue z a) ^ e.natAbs
  else
    phaseValue z a ^ e.natAbs

@[simp]
theorem evalPair_signedPowerCode
    (z : StateFamily q ℝ) (a : Fin q) (e : ℤ) :
    evalPair (signedPowerCode a e) (point z) =
      signedPowerValue z a e := by
  by_cases h : e < 0
  · simp [signedPowerCode, signedPowerValue, h]
  · simp [signedPowerCode, signedPowerValue, h]

/-- Literal polynomial representative of an integral character. -/
def characterCode
    (exponents : Fin q → ℤ) :
    ComplexPairCode (dimension q) :=
  product
    (List.ofFn fun a : Fin q ↦
      signedPowerCode a (exponents a))

/-- The corresponding signed-power product at a structured phase state. -/
noncomputable def characterValue
    (exponents : Fin q → ℤ)
    (z : StateFamily q ℝ) : ℂ :=
  (List.ofFn fun a : Fin q ↦
    signedPowerValue z a (exponents a)).prod

@[simp]
theorem evalPair_characterCode
    (exponents : Fin q → ℤ)
    (z : StateFamily q ℝ) :
    evalPair (characterCode exponents) (point z) =
      characterValue exponents z := by
  rw [characterCode, evalPair_product]
  unfold characterValue
  rw [List.map_ofFn]
  congr 1
  rw [List.ofFn_inj]
  funext a
  exact evalPair_signedPowerCode z a (exponents a)

@[simp]
theorem eval₂Hom_characterCode_re
    (exponents : Fin q → ℤ)
    (z : StateFamily q ℝ) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode (characterCode exponents).1) =
      (characterValue exponents z).re := by
  have h := congrArg Complex.re
    (evalPair_characterCode exponents z)
  simpa only [evalPair] using h

@[simp]
theorem eval₂Hom_characterCode_im
    (exponents : Fin q → ℤ)
    (z : StateFamily q ℝ) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode (characterCode exponents).2) =
      (characterValue exponents z).im := by
  have h := congrArg Complex.im
    (evalPair_characterCode exponents z)
  simpa only [evalPair] using h

/-! ## The character frequency and velocity code -/

/-- Regard an integer exponent as a rational compiler coefficient. -/
def exponentWeightCode (e : ℤ) : RationalCode :=
  RationalCode.encode (e : ℚ)

def frequencyCode
    (parameters : Fin q → RationalCode)
    (exponents : Fin q → ℤ) :
    PolynomialCode (dimension q) :=
  ControllerPhaseProductLinearFrequencyCode.code
    (fun i ↦ exponentWeightCode (exponents i))
    parameters

noncomputable def frequencyValue
    (parameters : Fin q → RationalCode)
    (exponents : Fin q → ℤ)
    (z : StateFamily q ℝ) : ℝ :=
  ∑ i,
    (exponents i : ℝ) *
      (RationalCode.decode (parameters i) : ℝ) *
      (z i).controller.r

@[simp]
theorem eval₂Hom_frequencyCode
    (parameters : Fin q → RationalCode)
    (exponents : Fin q → ℤ)
    (z : StateFamily q ℝ) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode
          (frequencyCode parameters exponents)) =
      frequencyValue parameters exponents z := by
  rw [frequencyCode,
    ControllerPhaseProductLinearFrequencyCode.eval₂Hom_code]
  simp [ControllerPhaseProductLinearFrequencyCode.value,
    exponentWeightCode, frequencyValue]

/-- Real and imaginary codes for `i * frequency * character`. -/
def derivativeCode
    (parameters : Fin q → RationalCode)
    (exponents : Fin q → ℤ) :
    ComplexPairCode (dimension q) :=
  (PolynomialCode.neg
      (PolynomialCode.mul
        (frequencyCode parameters exponents)
        (characterCode exponents).2),
    PolynomialCode.mul
      (frequencyCode parameters exponents)
      (characterCode exponents).1)

@[simp]
theorem evalPair_derivativeCode
    (parameters : Fin q → RationalCode)
    (exponents : Fin q → ℤ)
    (z : StateFamily q ℝ) :
    evalPair (derivativeCode parameters exponents) (point z) =
      Complex.I *
        (frequencyValue parameters exponents z : ℂ) *
          characterValue exponents z := by
  apply Complex.ext
  · simp only [evalPair, derivativeCode,
      PolynomialCode.decode_neg_code,
      PolynomialCode.decode_mul_code, map_neg, map_mul,
      eval₂Hom_frequencyCode, eval₂Hom_characterCode_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  · simp only [evalPair, derivativeCode,
      PolynomialCode.decode_mul_code, map_mul,
      eval₂Hom_frequencyCode, eval₂Hom_characterCode_re,
      Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring

end HGAS.Clocks.ControllerPhaseProductCharacterCode
