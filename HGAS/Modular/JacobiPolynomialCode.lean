import HGAS.Algebra.ComplexPolynomialCode
import HGAS.Modular.JacobiAlgebra
import HGAS.Modular.UnaryPolynomialCode
import Mathlib.Tactic

/-!
# Finite polynomial syntax for the reciprocal Jacobi chart

`JacobiAlgebra` records the two commuting rational derivations used by the
Jacobi selector as formulas on the structured state

```
  (p₂,p₃,p₄,H,T₁,T₂,T₃,T₄,Δ,U).
```

This file gives those formulas an executable finite representation by
Gaussian-rational complex polynomial codes.  It provides:

* coordinate vectors and their inverse structured-state map;
* separate codes for the elliptic and modular derivations;
* a compiler for an arbitrary Gaussian-rational linear combination;
* rational realification on twenty real coordinates;
* exact pointwise semantic theorems, including one stated on every real
  ambient point; and
* finite codes for the four intrinsic Jacobi-chart residuals.

The construction is purely algebraic.  In particular, it does not use theta
functions, recurrence, a selector theorem, or invariant measures.
-/

namespace HGAS.Modular

open HGAS

namespace JacobiPolynomialCode

open ComplexPolynomialCode

/-! ## Coordinates and reusable syntax -/

/-- Number of complex coordinates in the reciprocal Jacobi chart. -/
abbrev dimension : ℕ := 10

def p2Index : Fin dimension := 0
def p3Index : Fin dimension := 1
def p4Index : Fin dimension := 2
def HIndex : Fin dimension := 3
def T1Index : Fin dimension := 4
def T2Index : Fin dimension := 5
def T3Index : Fin dimension := 6
def T4Index : Fin dimension := 7
def DeltaIndex : Fin dimension := 8
def UIndex : Fin dimension := 9

/-- Coordinate vector associated with a structured Jacobi state. -/
def point (z : JacobiState ℂ) : Fin dimension → ℂ :=
  ![z.p2, z.p3, z.p4, z.H, z.T1, z.T2, z.T3, z.T4, z.Delta, z.U]

/-- Reassemble a structured Jacobi state from its ten coordinates. -/
def state (z : Fin dimension → ℂ) : JacobiState ℂ where
  p2 := z p2Index
  p3 := z p3Index
  p4 := z p4Index
  H := z HIndex
  T1 := z T1Index
  T2 := z T2Index
  T3 := z T3Index
  T4 := z T4Index
  Delta := z DeltaIndex
  U := z UIndex

@[simp]
theorem state_point (z : JacobiState ℂ) :
    state (point z) = z := by
  ext <;>
    simp [state, point, p2Index, p3Index, p4Index, HIndex,
      T1Index, T2Index, T3Index, T4Index, DeltaIndex, UIndex]

@[simp]
theorem point_state (z : Fin dimension → ℂ) :
    point (state z) = z := by
  funext i
  fin_cases i <;> change z _ = z _ <;>
    apply congrArg z <;> rfl

/-- Canonical finite code for a rational constant. -/
def rational (q : ℚ) : ComplexPolynomialCode dimension :=
  UnaryPolynomialCode.rational q

@[simp]
theorem eval_rational (q : ℚ) (z : Fin dimension → ℂ) :
    eval (rational q) z = (q : ℂ) := by
  simp [rational]

def p2Code : ComplexPolynomialCode dimension := var p2Index
def p3Code : ComplexPolynomialCode dimension := var p3Index
def p4Code : ComplexPolynomialCode dimension := var p4Index
def HCode : ComplexPolynomialCode dimension := var HIndex
def T1Code : ComplexPolynomialCode dimension := var T1Index
def T2Code : ComplexPolynomialCode dimension := var T2Index
def T3Code : ComplexPolynomialCode dimension := var T3Index
def T4Code : ComplexPolynomialCode dimension := var T4Index
def DeltaCode : ComplexPolynomialCode dimension := var DeltaIndex
def UCode : ComplexPolynomialCode dimension := var UIndex

/-- Code of the common weight-two coefficient
`K=H+(p₃²+p₄²)/12`. -/
def KCode : ComplexPolynomialCode dimension :=
  add HCode
    (mul (rational (1 / 12))
      (add (pow p3Code 2) (pow p4Code 2)))

@[simp]
theorem eval_KCode (z : JacobiState ℂ) :
    eval KCode (point z) = JacobiState.K z := by
  simp [KCode, point, p3Code, p4Code, HCode, p3Index, p4Index,
    HIndex, JacobiState.K]
  ring

/-! ## The elliptic derivation -/

def ellipticP2Code : ComplexPolynomialCode dimension := zero
def ellipticP3Code : ComplexPolynomialCode dimension := zero
def ellipticP4Code : ComplexPolynomialCode dimension := zero
def ellipticHCode : ComplexPolynomialCode dimension := zero
def ellipticT1Code : ComplexPolynomialCode dimension := DeltaCode

def ellipticT2Code : ComplexPolynomialCode dimension :=
  mul UCode
    (sub (mul DeltaCode T2Code)
      (mul (mul p2Code T3Code) T4Code))

def ellipticT3Code : ComplexPolynomialCode dimension :=
  mul UCode
    (sub (mul DeltaCode T3Code)
      (mul (mul p3Code T4Code) T2Code))

def ellipticT4Code : ComplexPolynomialCode dimension :=
  mul UCode
    (sub (mul DeltaCode T4Code)
      (mul (mul p4Code T2Code) T3Code))

def ellipticDeltaCode : ComplexPolynomialCode dimension :=
  sub
    (mul UCode
      (sub (pow DeltaCode 2)
        (mul (mul p3Code p4Code) (pow T2Code 2))))
    (mul (mul (rational 4) KCode) T1Code)

def ellipticUCode : ComplexPolynomialCode dimension :=
  neg (mul (pow UCode 2) DeltaCode)

/-- Executable complex polynomial field for the elliptic derivation. -/
def ellipticFieldCode :
    ComplexPolynomialFieldCode dimension :=
  ![ellipticP2Code, ellipticP3Code, ellipticP4Code, ellipticHCode,
    ellipticT1Code, ellipticT2Code, ellipticT3Code, ellipticT4Code,
    ellipticDeltaCode, ellipticUCode]

set_option linter.flexible false in
@[simp]
theorem eval_ellipticFieldCode
    (z : JacobiState ℂ) (i : Fin dimension) :
    eval (ellipticFieldCode i) (point z) =
      point (JacobiState.ellipticVectorField z) i := by
  fin_cases i <;>
    simp [ellipticFieldCode, ellipticP2Code, ellipticP3Code,
      ellipticP4Code, ellipticHCode, ellipticT1Code, ellipticT2Code,
      ellipticT3Code, ellipticT4Code, ellipticDeltaCode,
      ellipticUCode, point, p2Code, p3Code, p4Code, HCode, T1Code,
      T2Code, T3Code, T4Code, DeltaCode, UCode, KCode, rational,
      p2Index, p3Index, p4Index, HIndex, T1Index, T2Index, T3Index,
      T4Index, DeltaIndex, UIndex, JacobiState.ellipticVectorField,
      JacobiState.K]
  all_goals
    left
    ring

/-! ## The modular derivation -/

def modularP2Code : ComplexPolynomialCode dimension :=
  mul
    (mul (rational 2)
      (add HCode
        (mul (rational (1 / 12))
          (add (pow p3Code 2) (pow p4Code 2)))))
    p2Code

def modularP3Code : ComplexPolynomialCode dimension :=
  mul
    (mul (rational 2)
      (add HCode
        (mul (rational (1 / 12))
          (sub (pow p2Code 2) (pow p4Code 2)))))
    p3Code

def modularP4Code : ComplexPolynomialCode dimension :=
  mul
    (mul (rational 2)
      (sub HCode
        (mul (rational (1 / 12))
          (add (pow p2Code 2) (pow p3Code 2)))))
    p4Code

def modularHCode : ComplexPolynomialCode dimension :=
  sub
    (mul (rational 2) (pow HCode 2))
    (mul (rational (1 / 144))
      (add (add (pow p2Code 4) (pow p3Code 4))
        (pow p4Code 4)))

def modularT1Code : ComplexPolynomialCode dimension :=
  add
    (add
      (neg
        (mul (mul (rational (1 / 4)) (pow DeltaCode 2)) UCode))
      (mul
        (mul
          (mul
            (mul (rational (1 / 4)) p3Code) p4Code)
          (pow T2Code 2))
        UCode))
    (mul KCode T1Code)

def modularT2Code : ComplexPolynomialCode dimension :=
  add
    (add
      (add
        (neg
          (mul
            (mul
              (mul (rational (1 / 4)) (pow DeltaCode 2))
              (pow UCode 2))
            T2Code))
        (mul
          (mul
            (mul
              (mul
                (mul (rational (1 / 2)) p2Code)
                DeltaCode)
              T3Code)
            T4Code)
          (pow UCode 2)))
      (mul
        (mul
          (mul (rational (1 / 4))
            (sub
              (sub
                (mul (mul p3Code p4Code) (pow T2Code 2))
                (mul (mul p2Code p4Code) (pow T3Code 2)))
              (mul (mul p2Code p3Code) (pow T4Code 2))))
          (pow UCode 2))
        T2Code))
    (mul KCode T2Code)

def modularT3Code : ComplexPolynomialCode dimension :=
  add
    (add
      (add
        (neg
          (mul
            (mul
              (mul (rational (1 / 4)) (pow DeltaCode 2))
              (pow UCode 2))
            T3Code))
        (mul
          (mul
            (mul
              (mul
                (mul (rational (1 / 2)) p3Code)
                DeltaCode)
              T4Code)
            T2Code)
          (pow UCode 2)))
      (mul
        (mul
          (mul (rational (1 / 4))
            (sub
              (sub
                (mul (mul p3Code p4Code) (pow T2Code 2))
                (mul (mul p3Code p2Code) (pow T4Code 2)))
              (mul (mul p3Code p4Code) (pow T2Code 2))))
          (pow UCode 2))
        T3Code))
    (mul KCode T3Code)

def modularT4Code : ComplexPolynomialCode dimension :=
  add
    (add
      (add
        (neg
          (mul
            (mul
              (mul (rational (1 / 4)) (pow DeltaCode 2))
              (pow UCode 2))
            T4Code))
        (mul
          (mul
            (mul
              (mul
                (mul (rational (1 / 2)) p4Code)
                DeltaCode)
              T2Code)
            T3Code)
          (pow UCode 2)))
      (mul
        (mul
          (mul (rational (1 / 4))
            (sub
              (sub
                (mul (mul p3Code p4Code) (pow T2Code 2))
                (mul (mul p4Code p3Code) (pow T2Code 2)))
              (mul (mul p4Code p2Code) (pow T3Code 2))))
          (pow UCode 2))
        T4Code))
    (mul KCode T4Code)

def modularDeltaCode : ComplexPolynomialCode dimension :=
  sub
    (add
      (neg
        (mul
          (mul (rational (1 / 4)) (pow DeltaCode 3))
          (pow UCode 2)))
      (mul
        (mul (rational 3)
          (add
            (mul
              (mul
                (mul
                  (mul (rational (1 / 4)) p3Code)
                  p4Code)
                (pow T2Code 2))
              (pow UCode 2))
            KCode))
        DeltaCode))
    (mul
      (mul
        (mul
          (mul
            (mul
              (mul (rational (1 / 2)) p2Code)
              p3Code)
            p4Code)
          T2Code)
        T3Code)
      (mul T4Code (pow UCode 2)))

def modularUCode : ComplexPolynomialCode dimension :=
  neg
    (mul (pow UCode 2)
      (add
        (add
          (neg
            (mul
              (mul (rational (1 / 4)) (pow DeltaCode 2))
              UCode))
          (mul
            (mul
              (mul
                (mul (rational (1 / 4)) p3Code)
                p4Code)
              (pow T2Code 2))
            UCode))
        (mul KCode T1Code)))

/-- Executable complex polynomial field for the modular derivation. -/
def modularFieldCode :
    ComplexPolynomialFieldCode dimension :=
  ![modularP2Code, modularP3Code, modularP4Code, modularHCode,
    modularT1Code, modularT2Code, modularT3Code, modularT4Code,
    modularDeltaCode, modularUCode]

set_option linter.flexible false in
@[simp]
theorem eval_modularFieldCode
    (z : JacobiState ℂ) (i : Fin dimension) :
    eval (modularFieldCode i) (point z) =
      point (JacobiState.modularVectorField z) i := by
  fin_cases i <;>
    simp [modularFieldCode, modularP2Code, modularP3Code,
      modularP4Code, modularHCode, modularT1Code, modularT2Code,
      modularT3Code, modularT4Code, modularDeltaCode, modularUCode,
      point, p2Code, p3Code, p4Code, HCode, T1Code, T2Code, T3Code,
      T4Code, DeltaCode, UCode, KCode, rational, p2Index, p3Index,
      p4Index, HIndex, T1Index, T2Index, T3Index, T4Index, DeltaIndex,
      UIndex, JacobiState.modularVectorField, JacobiState.K]
  all_goals ring_nf
  all_goals simp

/-! ## Two-clock compilation and realification -/

/-- Complex finite code of the linear combination
`κZ 𝒵 + κPhi Φ`. -/
def combinedFieldCode
    (κZ κPhi : GaussianRationalCode) :
    ComplexPolynomialFieldCode dimension :=
  fun i ↦
    add
      (mulGaussian κZ (ellipticFieldCode i))
      (mulGaussian κPhi (modularFieldCode i))

/-- Rational realification of the two-clock Jacobi field. -/
def compileFieldCode
    (κZ κPhi : GaussianRationalCode) :
    PolynomialFieldCode (dimension + dimension) :=
  ComplexPolynomialFieldCode.realify
    (combinedFieldCode κZ κPhi)

@[simp]
theorem eval_combinedFieldCode
    (κZ κPhi : GaussianRationalCode)
    (z : JacobiState ℂ) (i : Fin dimension) :
    eval (combinedFieldCode κZ κPhi i) (point z) =
      point
        (JacobiState.combinedVectorField
          (GaussianRationalCode.decode κZ)
          (GaussianRationalCode.decode κPhi) z) i := by
  simp only [combinedFieldCode, eval_add, eval_mulGaussian,
    eval_ellipticFieldCode, eval_modularFieldCode]
  fin_cases i <;>
    simp [point, JacobiState.combinedVectorField]

/-- Reassembling the realization of the realified code recovers exactly
the structured combined vector field. -/
@[simp]
theorem complexify_realize_compileFieldCode
    (κZ κPhi : GaussianRationalCode)
    (z : JacobiState ℂ) :
    ComplexCoordinates.complexifyPoint
        (PolynomialFieldCode.realize
          (compileFieldCode κZ κPhi)
          (ComplexCoordinates.realifyPoint (point z))) =
      point
        (JacobiState.combinedVectorField
          (GaussianRationalCode.decode κZ)
          (GaussianRationalCode.decode κPhi) z) := by
  unfold compileFieldCode
  rw [ComplexPolynomialFieldCode.complexifyPoint_realize_realify]
  funext i
  exact eval_combinedFieldCode κZ κPhi z i

/-- Global semantics on every point of the twenty-dimensional real
ambient space. -/
@[simp]
theorem complexify_realize_compileFieldCode_arbitrary
    (κZ κPhi : GaussianRationalCode)
    (x : Fin (dimension + dimension) → ℝ) :
    ComplexCoordinates.complexifyPoint
        (PolynomialFieldCode.realize
          (compileFieldCode κZ κPhi) x) =
      point
        (JacobiState.combinedVectorField
          (GaussianRationalCode.decode κZ)
          (GaussianRationalCode.decode κPhi)
          (state (ComplexCoordinates.complexifyPoint x))) := by
  have h :=
    complexify_realize_compileFieldCode κZ κPhi
      (state (ComplexCoordinates.complexifyPoint x))
  simpa using h

/-! ## Intrinsic validity residuals -/

def residualR0Code : ComplexPolynomialCode dimension :=
  sub (sub (pow p3Code 2) (pow p2Code 2)) (pow p4Code 2)

def residualR1Code : ComplexPolynomialCode dimension :=
  sub
    (sub
      (mul p2Code (pow T4Code 2))
      (mul p4Code (pow T2Code 2)))
    (mul p3Code (pow T1Code 2))

def residualR2Code : ComplexPolynomialCode dimension :=
  sub
    (sub
      (mul p2Code (pow T3Code 2))
      (mul p3Code (pow T2Code 2)))
    (mul p4Code (pow T1Code 2))

def residualRUCode : ComplexPolynomialCode dimension :=
  sub (mul UCode T1Code) (rational 1)

/-- The four residual codes in the order `(R₀,R₁,R₂,Rᵁ)`. -/
def residualCode (i : Fin 4) :
    ComplexPolynomialCode dimension :=
  ![residualR0Code, residualR1Code, residualR2Code, residualRUCode] i

@[simp]
theorem eval_residualR0Code (z : JacobiState ℂ) :
    eval residualR0Code (point z) =
      JacobiState.residualR0 z := by
  simp [residualR0Code, point, p2Code, p3Code, p4Code,
    p2Index, p3Index, p4Index, JacobiState.residualR0]

@[simp]
theorem eval_residualR1Code (z : JacobiState ℂ) :
    eval residualR1Code (point z) =
      JacobiState.residualR1 z := by
  simp [residualR1Code, point, p2Code, p3Code, p4Code, T1Code,
    T2Code, T4Code, p2Index, p3Index, p4Index, T1Index, T2Index,
    T4Index, JacobiState.residualR1]

@[simp]
theorem eval_residualR2Code (z : JacobiState ℂ) :
    eval residualR2Code (point z) =
      JacobiState.residualR2 z := by
  simp [residualR2Code, point, p2Code, p3Code, p4Code, T1Code,
    T2Code, T3Code, p2Index, p3Index, p4Index, T1Index, T2Index,
    T3Index, JacobiState.residualR2]

@[simp]
theorem eval_residualRUCode (z : JacobiState ℂ) :
    eval residualRUCode (point z) =
      JacobiState.residualRU z := by
  simp [residualRUCode, point, UCode, T1Code, UIndex, T1Index,
    rational, JacobiState.residualRU]

@[simp]
theorem eval_residualCode
    (z : JacobiState ℂ) (i : Fin 4) :
    eval (residualCode i) (point z) =
      ![JacobiState.residualR0 z, JacobiState.residualR1 z,
        JacobiState.residualR2 z, JacobiState.residualRU z] i := by
  fin_cases i <;> simp [residualCode]

end JacobiPolynomialCode

end HGAS.Modular
