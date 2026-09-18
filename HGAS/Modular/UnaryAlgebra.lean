import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic

/-!
# Algebra of the unary modular differential block

This module contains the exact polynomial identities used at the beginning
of the modular selector.  It is intentionally independent of theta
functions, recurrence, and invariant measures.

For the logarithmic nome derivation `D = q d/dq`, the four complex state
coordinates satisfy

```
D A = A (E + A + 2 C) / 3
D C = C (E - 2 A - C) / 3
D E = (E² - A² - A C - C²) / 6
D Y = (E + A - C) Y / 12.
```

The identities below are polynomial identities over every field containing
the rationals.  Consequently they remain valid after splitting complex
coordinates into real and imaginary parts, where they become identities of
rational real polynomial vector fields.
-/

namespace HGAS.Modular

/-- State of the basic unary Ramanujan--theta polynomial system. -/
@[ext]
structure UnaryModularState (R : Type*) where
  A : R
  C : R
  E : R
  Y : R

namespace UnaryModularState

/-! The coordinate state is used as the codomain of polynomial vector
fields, so its zero is defined coordinatewise.  Keeping this instance here,
next to the structure, makes it reusable by every later dynamics module. -/

instance {R : Type*} [Zero R] : Zero (UnaryModularState R) where
  zero := ⟨0, 0, 0, 0⟩

@[simp] theorem zero_A {R : Type*} [Zero R] :
    (0 : UnaryModularState R).A = 0 := rfl

@[simp] theorem zero_C {R : Type*} [Zero R] :
    (0 : UnaryModularState R).C = 0 := rfl

@[simp] theorem zero_E {R : Type*} [Zero R] :
    (0 : UnaryModularState R).E = 0 := rfl

@[simp] theorem zero_Y {R : Type*} [Zero R] :
    (0 : UnaryModularState R).Y = 0 := rfl

variable {R : Type*} [Field R] [CharZero R]

/-- The rational polynomial vector field of the unary modular block. -/
def vectorField (z : UnaryModularState R) : UnaryModularState R where
  A := (1 / 3 : R) * z.A * (z.E + z.A + 2 * z.C)
  C := (1 / 3 : R) * z.C * (z.E - 2 * z.A - z.C)
  E := (1 / 6 : R) *
    (z.E ^ 2 - z.A ^ 2 - z.A * z.C - z.C ^ 2)
  Y := (1 / 12 : R) * (z.E + z.A - z.C) * z.Y

/-- Jacobi's algebraic residual `Y⁴-A-C`. -/
def jacobiResidual (z : UnaryModularState R) : R :=
  z.Y ^ 4 - z.A - z.C

/-- Formal Lie derivative of the Jacobi residual along `vectorField`. -/
def jacobiResidualLie (z : UnaryModularState R) : R :=
  4 * z.Y ^ 3 * (vectorField z).Y -
    (vectorField z).A - (vectorField z).C

/-- The Jacobi residual evolves by scalar multiplication.  In particular,
its zero set is invariant under every differentiable solution of the
polynomial system. -/
theorem jacobiResidualLie_eq (z : UnaryModularState R) :
    jacobiResidualLie z =
      (1 / 3 : R) * (z.E + z.A - z.C) *
        jacobiResidual z := by
  simp only [jacobiResidualLie, vectorField, jacobiResidual]
  norm_num
  ring

/-- The sum `B=A+C`, equal to `θ₃⁴` on the canonical branch. -/
def B (z : UnaryModularState R) : R :=
  z.A + z.C

/-- Formal derivative of `B`. -/
def BLie (z : UnaryModularState R) : R :=
  (vectorField z).A + (vectorField z).C

/-- The exact logarithmic derivative identity
`D B = B(E+A-C)/3`. -/
theorem BLie_eq (z : UnaryModularState R) :
    BLie z =
      (1 / 3 : R) * B z * (z.E + z.A - z.C) := by
  simp only [BLie, vectorField, B]
  norm_num
  ring

/-- Numerator of the quotient derivative of `A/(A+C)`. -/
def lambdaQuotientNumeratorLie (z : UnaryModularState R) : R :=
  (vectorField z).A * B z - z.A * BLie z

/-- Polynomial form of the modular-lambda differential equation:

`(D A) B - A (D B) = A C B`.

After division by `B²`, this is
`D(A/B)=B(A/B)(1-A/B)`. -/
theorem lambdaQuotientNumeratorLie_eq
    (z : UnaryModularState R) :
    lambdaQuotientNumeratorLie z = z.A * z.C * B z := by
  simp only [lambdaQuotientNumeratorLie, vectorField, B, BLie]
  norm_num
  ring

omit [CharZero R] in
/-- The coordinate divisor `A=0` is algebraically invariant. -/
theorem vectorField_A_eq_zero_of_A_eq_zero
    (z : UnaryModularState R) (hA : z.A = 0) :
    (vectorField z).A = 0 := by
  simp [vectorField, hA]

omit [CharZero R] in
/-- The coordinate divisor `C=0` is algebraically invariant. -/
theorem vectorField_C_eq_zero_of_C_eq_zero
    (z : UnaryModularState R) (hC : z.C = 0) :
    (vectorField z).C = 0 := by
  simp [vectorField, hC]

/-- On `A=0`, the remaining Riccati coordinate is `q₀=E-C`. -/
theorem riccati_E_sub_C_of_A_eq_zero
    (z : UnaryModularState R) (hA : z.A = 0) :
    (vectorField z).E - (vectorField z).C =
      (1 / 6 : R) * (z.E - z.C) ^ 2 := by
  simp only [vectorField]
  rw [hA]
  norm_num
  ring

/-- On `C=0`, the remaining Riccati coordinate is `p₀=E+A`. -/
theorem riccati_E_add_A_of_C_eq_zero
    (z : UnaryModularState R) (hC : z.C = 0) :
    (vectorField z).E + (vectorField z).A =
      (1 / 6 : R) * (z.E + z.A) ^ 2 := by
  simp only [vectorField]
  rw [hC]
  norm_num
  ring

end UnaryModularState

/-! ## Square-root and signed-link extension -/

/-- Independent square-root states used by the Jacobi chart.  The base
coordinates are retained rather than definitionally identified, so every
link has an explicit polynomial residual. -/
@[ext]
structure UnaryRootState (R : Type*) extends UnaryModularState R where
  p2 : R
  p3 : R
  p4 : R
  H : R

namespace UnaryRootState

variable {R : Type*} [Field R] [CharZero R]

/-- Polynomial extension of the modular vector field by the half
logarithmic derivatives of the theta square roots. -/
def vectorField (z : UnaryRootState R) : UnaryRootState R where
  toUnaryModularState := z.toUnaryModularState.vectorField
  p2 := (1 / 6 : R) *
    (12 * z.H + z.p2 ^ 2 + 2 * z.p4 ^ 2) * z.p2
  p3 := (1 / 6 : R) *
    (12 * z.H + z.p2 ^ 2 - z.p4 ^ 2) * z.p3
  p4 := (1 / 6 : R) *
    (12 * z.H - 2 * z.p2 ^ 2 - z.p4 ^ 2) * z.p4
  H := (1 / 72 : R) *
    ((12 * z.H) ^ 2 - z.p2 ^ 4 -
      z.p2 ^ 2 * z.p4 ^ 2 - z.p4 ^ 4)

/-- Residuals for `p2²=A`, `p4²=C`, and `12H=E`. -/
def link2 (z : UnaryRootState R) : R := z.p2 ^ 2 - z.A
def link4 (z : UnaryRootState R) : R := z.p4 ^ 2 - z.C
def linkH (z : UnaryRootState R) : R := 12 * z.H - z.E

/-- Formal Lie derivatives of the three unsigned link residuals. -/
def link2Lie (z : UnaryRootState R) : R :=
  2 * z.p2 * (vectorField z).p2 - (vectorField z).A

def link4Lie (z : UnaryRootState R) : R :=
  2 * z.p4 * (vectorField z).p4 - (vectorField z).C

def linkHLie (z : UnaryRootState R) : R :=
  12 * (vectorField z).H - (vectorField z).E

/-- The `p2²=A` residual evolves in the ideal generated by the three
unsigned links. -/
theorem link2Lie_eq (z : UnaryRootState R) :
    link2Lie z =
      (1 / 3 : R) *
          (12 * z.H + z.p2 ^ 2 + 2 * z.p4 ^ 2) * link2 z +
        (1 / 3 : R) * z.A *
          (linkH z + link2 z + 2 * link4 z) := by
  simp only [link2Lie, vectorField, link2, link4, linkH,
    UnaryModularState.vectorField]
  norm_num
  ring

/-- The `p4²=C` residual evolves in the same link ideal. -/
theorem link4Lie_eq (z : UnaryRootState R) :
    link4Lie z =
      (1 / 3 : R) *
          (12 * z.H - 2 * z.p2 ^ 2 - z.p4 ^ 2) * link4 z +
        (1 / 3 : R) * z.C *
          (linkH z - 2 * link2 z - link4 z) := by
  simp only [link4Lie, vectorField, link2, link4, linkH,
    UnaryModularState.vectorField]
  norm_num
  ring

/-- The `12H=E` residual also evolves in the link ideal. -/
theorem linkHLie_eq (z : UnaryRootState R) :
    linkHLie z =
      (1 / 6 : R) * (12 * z.H + z.E) * linkH z -
        (1 / 6 : R) * (z.p2 ^ 2 + z.A + z.C) * link2 z -
        (1 / 6 : R) * (z.p2 ^ 2 + z.p4 ^ 2 + z.C) *
          link4 z := by
  simp only [linkHLie, vectorField, link2, link4, linkH,
    UnaryModularState.vectorField]
  norm_num
  ring

/-- The signed link fixing `p3=Y²`. -/
def signedLink3 (z : UnaryRootState R) : R :=
  z.p3 - z.Y ^ 2

/-- Formal Lie derivative of the signed `p3-Y²` link. -/
def signedLink3Lie (z : UnaryRootState R) : R :=
  (vectorField z).p3 -
    2 * z.Y * (vectorField z).Y

/-- Exact ideal-membership identity for the signed root link:

```
D(p3-Y²)
 = (12H+p2²-p4²)/6 · (p3-Y²)
   + (LH+L2-L4)/6 · Y².
```

Hence all four link equations cut out an invariant algebraic set. -/
theorem signedLink3Lie_eq (z : UnaryRootState R) :
    signedLink3Lie z =
      (1 / 6 : R) *
          (12 * z.H + z.p2 ^ 2 - z.p4 ^ 2) *
            signedLink3 z +
        (1 / 6 : R) *
          (linkH z + link2 z - link4 z) * z.Y ^ 2 := by
  simp only [signedLink3Lie, vectorField, signedLink3,
    linkH, link2, link4, UnaryModularState.vectorField]
  norm_num
  ring

end UnaryRootState

end HGAS.Modular
