import HGAS.Foundation.PolynomialDifferentiationCode
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Finite syntax for complex-valued polynomials

This file provides a small, reusable syntax layer for the complex
polynomials used in the modular source construction.

A point of `ℂ^n` is written in real coordinates as

```
Fin (n + n) → ℝ.
```

The first copy of `Fin n` contains the real parts and the second copy
contains the imaginary parts.  A complex-valued polynomial is consequently
represented by a pair of rational sparse polynomials in these `2n` real
variables.  This representation is intentionally slightly more general
than a holomorphic polynomial: an arbitrary pair represents a
complex-valued *real* polynomial.  The constructors `variable`,
`gaussianConstant`, `add`, and `mul` generate the usual holomorphic
rational-Gaussian polynomial algebra.

Everything on the syntax side is finite and executable.  Semantic
evaluation is separated from syntax and is proved to commute exactly with
all algebraic constructors.  At the end of the file, a complex polynomial
vector field on `ℂ^n` is realified to the existing
`PolynomialFieldCode (n + n)` language.
-/

namespace HGAS

open MvPolynomial

namespace ComplexCoordinates

variable {n : ℕ}

/-- Index of the real part of the `i`-th complex coordinate. -/
def realIndex (i : Fin n) : Fin (n + n) :=
  finSumFinEquiv (Sum.inl i)

/-- Index of the imaginary part of the `i`-th complex coordinate. -/
def imagIndex (i : Fin n) : Fin (n + n) :=
  finSumFinEquiv (Sum.inr i)

@[simp]
theorem finSumFinEquiv_symm_realIndex (i : Fin n) :
    finSumFinEquiv.symm (realIndex i) = Sum.inl i := by
  exact finSumFinEquiv.symm_apply_apply (Sum.inl i)

@[simp]
theorem finSumFinEquiv_symm_imagIndex (i : Fin n) :
    finSumFinEquiv.symm (imagIndex i) = Sum.inr i := by
  exact finSumFinEquiv.symm_apply_apply (Sum.inr i)

/-- Split a complex point into its real coordinate vector. -/
def realifyPoint (z : Fin n → ℂ) : Fin (n + n) → ℝ :=
  fun q ↦
    match finSumFinEquiv.symm q with
    | Sum.inl i => (z i).re
    | Sum.inr i => (z i).im

/-- Reassemble a complex point from a real coordinate vector. -/
def complexifyPoint (x : Fin (n + n) → ℝ) : Fin n → ℂ :=
  fun i ↦ ⟨x (realIndex i), x (imagIndex i)⟩

@[simp]
theorem realifyPoint_realIndex (z : Fin n → ℂ) (i : Fin n) :
    realifyPoint z (realIndex i) = (z i).re := by
  simp [realifyPoint]

@[simp]
theorem realifyPoint_imagIndex (z : Fin n → ℂ) (i : Fin n) :
    realifyPoint z (imagIndex i) = (z i).im := by
  simp [realifyPoint]

@[simp]
theorem complexifyPoint_re (x : Fin (n + n) → ℝ) (i : Fin n) :
    (complexifyPoint x i).re = x (realIndex i) :=
  rfl

@[simp]
theorem complexifyPoint_im (x : Fin (n + n) → ℝ) (i : Fin n) :
    (complexifyPoint x i).im = x (imagIndex i) :=
  rfl

@[simp]
theorem complexifyPoint_realifyPoint (z : Fin n → ℂ) :
    complexifyPoint (realifyPoint z) = z := by
  funext i
  apply Complex.ext <;> simp

@[simp]
theorem realifyPoint_complexifyPoint (x : Fin (n + n) → ℝ) :
    realifyPoint (complexifyPoint x) = x := by
  funext q
  cases hq : finSumFinEquiv.symm q with
  | inl i =>
      have hqi : q = realIndex i := by
        apply finSumFinEquiv.symm.injective
        simpa using hq
      subst q
      simp
  | inr i =>
      have hqi : q = imagIndex i := by
        apply finSumFinEquiv.symm.injective
        simpa using hq
      subst q
      simp

theorem realIndex_ne_imagIndex (i j : Fin n) :
    realIndex i ≠ imagIndex j := by
  intro h
  have := congrArg finSumFinEquiv.symm h
  simp at this

end ComplexCoordinates

/-! ## Rational Gaussian constants -/

/-- A Gaussian rational is coded by its rational real and imaginary
parts. -/
abbrev GaussianRationalCode :=
  RationalCode × RationalCode

namespace GaussianRationalCode

/-- Semantic complex number represented by a Gaussian-rational code. -/
def decode (q : GaussianRationalCode) : ℂ :=
  ⟨(RationalCode.decode q.1 : ℝ),
    (RationalCode.decode q.2 : ℝ)⟩

/-- Code of `0 : ℚ(i)`. -/
def zero : GaussianRationalCode :=
  (RationalCode.zero, RationalCode.zero)

/-- Code of `1 : ℚ(i)`. -/
def one : GaussianRationalCode :=
  (RationalCode.one, RationalCode.zero)

/-- Code of the imaginary unit. -/
def I : GaussianRationalCode :=
  (RationalCode.zero, RationalCode.one)

@[simp] theorem decode_zero : decode zero = 0 := by
  apply Complex.ext <;> simp [decode, zero]

@[simp] theorem decode_one : decode one = 1 := by
  apply Complex.ext <;> simp [decode, one]

@[simp] theorem decode_I : decode I = Complex.I := by
  apply Complex.ext <;> simp [decode, I]

end GaussianRationalCode

/-! ## Complex polynomial codes and their semantics -/

/-- A complex-valued polynomial in `n` complex variables, represented by
its real and imaginary parts as rational polynomials in `2n` real
variables. -/
abbrev ComplexPolynomialCode (n : ℕ) :=
  PolynomialCode (n + n) × PolynomialCode (n + n)

namespace ComplexPolynomialCode

variable {n : ℕ}

/-- Evaluate a rational real polynomial at the realification of a complex
point. -/
noncomputable def evalReal
    (p : PolynomialCode (n + n)) (z : Fin n → ℂ) : ℝ :=
  MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
    (ComplexCoordinates.realifyPoint z) (PolynomialCode.decode p)

/-- Evaluate a complex polynomial code at a complex point. -/
noncomputable def eval
    (p : ComplexPolynomialCode n) (z : Fin n → ℂ) : ℂ :=
  ⟨evalReal p.1 z, evalReal p.2 z⟩

/-- The zero complex polynomial. -/
def zero : ComplexPolynomialCode n :=
  (PolynomialCode.zero, PolynomialCode.zero)

/-- The constant-one complex polynomial. -/
def one : ComplexPolynomialCode n :=
  (PolynomialCode.one, PolynomialCode.zero)

/-- Embed a rational constant into the complex polynomial algebra. -/
def rationalConstant (q : RationalCode) : ComplexPolynomialCode n :=
  (PolynomialCode.constant q, PolynomialCode.zero)

/-- Embed a Gaussian-rational constant into the complex polynomial
algebra. -/
def gaussianConstant
    (q : GaussianRationalCode) : ComplexPolynomialCode n :=
  (PolynomialCode.constant q.1, PolynomialCode.constant q.2)

/-- The complex coordinate function `z ↦ z i`. -/
def var (i : Fin n) : ComplexPolynomialCode n :=
  (PolynomialCode.varCode (ComplexCoordinates.realIndex i),
    PolynomialCode.varCode (ComplexCoordinates.imagIndex i))

/-- Addition in the complex polynomial algebra. -/
def add (p q : ComplexPolynomialCode n) : ComplexPolynomialCode n :=
  (PolynomialCode.add p.1 q.1,
    PolynomialCode.add p.2 q.2)

/-- Additive inverse in the complex polynomial algebra. -/
def neg (p : ComplexPolynomialCode n) : ComplexPolynomialCode n :=
  (PolynomialCode.neg p.1, PolynomialCode.neg p.2)

/-- Subtraction in the complex polynomial algebra. -/
def sub (p q : ComplexPolynomialCode n) : ComplexPolynomialCode n :=
  (PolynomialCode.sub p.1 q.1,
    PolynomialCode.sub p.2 q.2)

/-- Complex multiplication:
`(a+ib)(c+id) = (ac-bd) + i(ad+bc)`. -/
def mul (p q : ComplexPolynomialCode n) : ComplexPolynomialCode n :=
  (PolynomialCode.sub
      (PolynomialCode.mul p.1 q.1)
      (PolynomialCode.mul p.2 q.2),
    PolynomialCode.add
      (PolynomialCode.mul p.1 q.2)
      (PolynomialCode.mul p.2 q.1))

/-- Natural powers in the complex polynomial algebra. -/
def pow (p : ComplexPolynomialCode n) : ℕ → ComplexPolynomialCode n
  | 0 => one
  | k + 1 => mul p (pow p k)

/-- Multiplication by the imaginary unit, implemented without introducing
any extra monomials: `i(a+ib) = -b+ia`. -/
def mulI (p : ComplexPolynomialCode n) : ComplexPolynomialCode n :=
  (PolynomialCode.neg p.2, p.1)

/-- Multiplication by a rational Gaussian constant. -/
def mulGaussian
    (q : GaussianRationalCode)
    (p : ComplexPolynomialCode n) : ComplexPolynomialCode n :=
  mul (gaussianConstant q) p

@[simp]
theorem evalReal_zero (z : Fin n → ℂ) :
    evalReal PolynomialCode.zero z = 0 := by
  simp [evalReal]

@[simp]
theorem evalReal_one (z : Fin n → ℂ) :
    evalReal PolynomialCode.one z = 1 := by
  simp [evalReal]

@[simp]
theorem evalReal_constant (q : RationalCode) (z : Fin n → ℂ) :
    evalReal (PolynomialCode.constant q) z =
      (RationalCode.decode q : ℝ) := by
  simp [evalReal]

@[simp]
theorem evalReal_varCode (i : Fin (n + n)) (z : Fin n → ℂ) :
    evalReal (PolynomialCode.varCode i) z =
      ComplexCoordinates.realifyPoint z i := by
  simp [evalReal]

@[simp]
theorem evalReal_add
    (p q : PolynomialCode (n + n)) (z : Fin n → ℂ) :
    evalReal (PolynomialCode.add p q) z =
      evalReal p z + evalReal q z := by
  simp [evalReal]

@[simp]
theorem evalReal_neg
    (p : PolynomialCode (n + n)) (z : Fin n → ℂ) :
    evalReal (PolynomialCode.neg p) z = -evalReal p z := by
  simp [evalReal]

@[simp]
theorem evalReal_sub
    (p q : PolynomialCode (n + n)) (z : Fin n → ℂ) :
    evalReal (PolynomialCode.sub p q) z =
      evalReal p z - evalReal q z := by
  simp [evalReal]

@[simp]
theorem evalReal_mul
    (p q : PolynomialCode (n + n)) (z : Fin n → ℂ) :
    evalReal (PolynomialCode.mul p q) z =
      evalReal p z * evalReal q z := by
  simp [evalReal]

@[simp]
theorem evalReal_pow
    (p : PolynomialCode (n + n)) (k : ℕ) (z : Fin n → ℂ) :
    evalReal (PolynomialCode.pow p k) z = evalReal p z ^ k := by
  simp [evalReal]

@[simp]
theorem eval_zero (z : Fin n → ℂ) :
    eval zero z = 0 := by
  apply Complex.ext <;> simp [eval, zero]

@[simp]
theorem eval_one (z : Fin n → ℂ) :
    eval one z = 1 := by
  apply Complex.ext <;> simp [eval, one]

@[simp]
theorem eval_rationalConstant
    (q : RationalCode) (z : Fin n → ℂ) :
    eval (rationalConstant q) z =
      (RationalCode.decode q : ℂ) := by
  apply Complex.ext <;> simp [eval, rationalConstant]

@[simp]
theorem eval_gaussianConstant
    (q : GaussianRationalCode) (z : Fin n → ℂ) :
    eval (gaussianConstant q) z =
      GaussianRationalCode.decode q := by
  apply Complex.ext <;>
    simp [eval, gaussianConstant, GaussianRationalCode.decode]

@[simp]
theorem eval_var (i : Fin n) (z : Fin n → ℂ) :
    eval (var i) z = z i := by
  apply Complex.ext <;>
    simp [eval, var]

@[simp]
theorem eval_add
    (p q : ComplexPolynomialCode n) (z : Fin n → ℂ) :
    eval (add p q) z = eval p z + eval q z := by
  apply Complex.ext <;>
    simp [eval, add]

@[simp]
theorem eval_neg
    (p : ComplexPolynomialCode n) (z : Fin n → ℂ) :
    eval (neg p) z = -eval p z := by
  apply Complex.ext <;>
    simp [eval, neg]

@[simp]
theorem eval_sub
    (p q : ComplexPolynomialCode n) (z : Fin n → ℂ) :
    eval (sub p q) z = eval p z - eval q z := by
  apply Complex.ext <;>
    simp [eval, sub]

@[simp]
theorem eval_mul
    (p q : ComplexPolynomialCode n) (z : Fin n → ℂ) :
    eval (mul p q) z = eval p z * eval q z := by
  apply Complex.ext <;>
    simp [eval, mul]

@[simp]
theorem eval_pow
    (p : ComplexPolynomialCode n) (k : ℕ) (z : Fin n → ℂ) :
    eval (pow p k) z = eval p z ^ k := by
  induction k with
  | zero => simp [pow]
  | succ k ih =>
      simp only [pow, eval_mul, ih, pow_succ]
      rw [mul_comm]

@[simp]
theorem eval_mulI
    (p : ComplexPolynomialCode n) (z : Fin n → ℂ) :
    eval (mulI p) z = Complex.I * eval p z := by
  apply Complex.ext <;>
    simp [eval, mulI]

@[simp]
theorem eval_mulGaussian
    (q : GaussianRationalCode)
    (p : ComplexPolynomialCode n) (z : Fin n → ℂ) :
    eval (mulGaussian q p) z =
      GaussianRationalCode.decode q * eval p z := by
  simp [mulGaussian]

end ComplexPolynomialCode

/-! ## Realification of complex polynomial vector fields -/

/-- A polynomial vector field on `ℂ^n`, with one complex polynomial code
for each complex coordinate. -/
abbrev ComplexPolynomialFieldCode (n : ℕ) :=
  Fin n → ComplexPolynomialCode n

namespace ComplexPolynomialFieldCode

variable {n : ℕ}

/-- Realify a complex polynomial field into the ordinary rational
polynomial-field language on `2n` real coordinates. -/
def realify
    (F : ComplexPolynomialFieldCode n) : PolynomialFieldCode (n + n) :=
  fun q ↦
    match finSumFinEquiv.symm q with
    | Sum.inl i => (F i).1
    | Sum.inr i => (F i).2

@[simp]
theorem realify_realIndex
    (F : ComplexPolynomialFieldCode n) (i : Fin n) :
    realify F (ComplexCoordinates.realIndex i) = (F i).1 := by
  simp [realify]

@[simp]
theorem realify_imagIndex
    (F : ComplexPolynomialFieldCode n) (i : Fin n) :
    realify F (ComplexCoordinates.imagIndex i) = (F i).2 := by
  simp [realify]

@[simp]
theorem realize_realIndex
    (F : ComplexPolynomialFieldCode n)
    (z : Fin n → ℂ) (i : Fin n) :
    PolynomialFieldCode.realize (realify F)
        (ComplexCoordinates.realifyPoint z)
        (ComplexCoordinates.realIndex i) =
      (ComplexPolynomialCode.eval (F i) z).re := by
  simp [PolynomialFieldCode.realize_apply,
    ComplexPolynomialCode.eval,
    ComplexPolynomialCode.evalReal]

@[simp]
theorem realize_imagIndex
    (F : ComplexPolynomialFieldCode n)
    (z : Fin n → ℂ) (i : Fin n) :
    PolynomialFieldCode.realize (realify F)
        (ComplexCoordinates.realifyPoint z)
        (ComplexCoordinates.imagIndex i) =
      (ComplexPolynomialCode.eval (F i) z).im := by
  simp [PolynomialFieldCode.realize_apply,
    ComplexPolynomialCode.eval,
    ComplexPolynomialCode.evalReal]

/-- Realification followed by reassembly agrees pointwise with complex
evaluation of the original field. -/
@[simp]
theorem complexifyPoint_realize_realify
    (F : ComplexPolynomialFieldCode n) (z : Fin n → ℂ) :
    ComplexCoordinates.complexifyPoint
        (PolynomialFieldCode.realize (realify F)
          (ComplexCoordinates.realifyPoint z)) =
      fun i ↦ ComplexPolynomialCode.eval (F i) z := by
  funext i
  apply Complex.ext
  · simpa using realize_realIndex F z i
  · simpa using realize_imagIndex F z i

end ComplexPolynomialFieldCode

end HGAS
