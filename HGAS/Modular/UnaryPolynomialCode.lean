import HGAS.Algebra.ComplexPolynomialCode
import HGAS.Modular.UnaryAlgebra
import HGAS.Modular.GaugeFourthRootDynamics
import Mathlib.Tactic

/-!
# Finite polynomial syntax for the unary modular source

The analytic modular construction starts from the four complex equations

```
D A = A (E + A + 2 C) / 3,
D C = C (E - 2 A - C) / 3,
D E = (E² - A² - A C - C²) / 6,
D Y = (E + A - C) Y / 12.
```

`UnaryModularState.vectorField` already records these equations as
ordinary algebra.  This file gives them an executable finite
rational-polynomial representation.  A complex field on `ℂ⁴` is first
represented by four `ComplexPolynomialCode`s and is then realified to a
rational field on `ℝ⁸`.

The square-root extension

```
p₂² = A,   p₄² = C,   12 H = E,   p₃ = Y²
```

is treated in the same way, now on `ℂ⁸`.  Its vector field has raw degree
at most four.  We also record finite codes for all five residuals used to
cut out the intended invariant variety.

Finally, a small independent two-coordinate compiler packages the
fourth-root gauge equation `G⁴ = C`.  This is useful beyond the modular
source: for an arbitrary Gaussian-rational logarithmic coefficient `a`,
it produces

```
G' = a G,    C' = 4 a C.
```

All semantic theorems in this file are exact.  No theta-function identity,
recurrence theorem, or invariant-measure classification is used.
-/

namespace HGAS.Modular

open HGAS

namespace UnaryPolynomialCode

open ComplexPolynomialCode

/-! ## Shared syntax helpers -/

/-- Canonical finite code for a rational complex constant. -/
def rational {n : ℕ} (q : ℚ) : ComplexPolynomialCode n :=
  rationalConstant (RationalCode.encode q)

@[simp]
theorem eval_rational {n : ℕ} (q : ℚ) (z : Fin n → ℂ) :
    eval (rational q) z = (q : ℂ) := by
  simp [rational]

/-- Multiply every component of a complex polynomial vector field by one
Gaussian-rational scalar.  This is the syntax-level operation used to
attach a rational complex clock rate. -/
def scaleFieldCode {n : ℕ}
    (κ : GaussianRationalCode)
    (F : ComplexPolynomialFieldCode n) :
    ComplexPolynomialFieldCode n :=
  fun i ↦ mulGaussian κ (F i)

@[simp]
theorem eval_scaleFieldCode {n : ℕ}
    (κ : GaussianRationalCode)
    (F : ComplexPolynomialFieldCode n)
    (z : Fin n → ℂ) (i : Fin n) :
    eval (scaleFieldCode κ F i) z =
      GaussianRationalCode.decode κ * eval (F i) z := by
  simp [scaleFieldCode]

/-! ## The four-coordinate unary modular field -/

/-- Number of complex coordinates in the basic unary modular block. -/
abbrev modularDimension : ℕ := 4

def AIndex : Fin modularDimension := 0
def CIndex : Fin modularDimension := 1
def EIndex : Fin modularDimension := 2
def YIndex : Fin modularDimension := 3

/-- Coordinate vector corresponding to a structured unary modular state. -/
def modularPoint
    (z : UnaryModularState ℂ) : Fin modularDimension → ℂ :=
  ![z.A, z.C, z.E, z.Y]

/-- Reassemble a structured unary modular state from its coordinate
vector. -/
def modularState
    (z : Fin modularDimension → ℂ) : UnaryModularState ℂ where
  A := z AIndex
  C := z CIndex
  E := z EIndex
  Y := z YIndex

@[simp]
theorem modularState_modularPoint (z : UnaryModularState ℂ) :
    modularState (modularPoint z) = z := by
  ext <;> simp [modularState, modularPoint, AIndex, CIndex, EIndex, YIndex]

@[simp]
theorem modularPoint_modularState
    (z : Fin modularDimension → ℂ) :
    modularPoint (modularState z) = z := by
  funext i
  fin_cases i <;> change z _ = z _ <;>
    apply congrArg z <;> rfl

def ACode : ComplexPolynomialCode modularDimension :=
  var AIndex

def CCode : ComplexPolynomialCode modularDimension :=
  var CIndex

def ECode : ComplexPolynomialCode modularDimension :=
  var EIndex

def YCode : ComplexPolynomialCode modularDimension :=
  var YIndex

/-- Code for `A(E+A+2C)/3`. -/
def modularAFieldCode : ComplexPolynomialCode modularDimension :=
  mul (mul (rational (1 / 3)) ACode)
    (add (add ECode ACode) (mul (rational 2) CCode))

/-- Code for `C(E-2A-C)/3`. -/
def modularCFieldCode : ComplexPolynomialCode modularDimension :=
  mul (mul (rational (1 / 3)) CCode)
    (sub (sub ECode (mul (rational 2) ACode)) CCode)

/-- Code for `(E²-A²-AC-C²)/6`. -/
def modularEFieldCode : ComplexPolynomialCode modularDimension :=
  mul (rational (1 / 6))
    (sub
      (sub
        (sub (pow ECode 2) (pow ACode 2))
        (mul ACode CCode))
      (pow CCode 2))

/-- Code for `(E+A-C)Y/12`. -/
def modularYFieldCode : ComplexPolynomialCode modularDimension :=
  mul (mul (rational (1 / 12))
      (sub (add ECode ACode) CCode))
    YCode

/-- Executable complex polynomial field for the unary modular system. -/
def modularFieldCode :
    ComplexPolynomialFieldCode modularDimension :=
  ![modularAFieldCode, modularCFieldCode,
    modularEFieldCode, modularYFieldCode]

/-- Its ordinary real rational polynomial code on eight coordinates. -/
def realModularFieldCode :
    PolynomialFieldCode (modularDimension + modularDimension) :=
  ComplexPolynomialFieldCode.realify modularFieldCode

/-- Unary field at a coded Gaussian-rational clock rate. -/
def scaledModularFieldCode (κ : GaussianRationalCode) :
    ComplexPolynomialFieldCode modularDimension :=
  scaleFieldCode κ modularFieldCode

/-- Executable real compiler for a coded clock rate. -/
def compileModularFieldCode (κ : GaussianRationalCode) :
    PolynomialFieldCode (modularDimension + modularDimension) :=
  ComplexPolynomialFieldCode.realify (scaledModularFieldCode κ)

/-- Exact pointwise semantics of every complex field component. -/
@[simp]
theorem eval_modularFieldCode
    (z : UnaryModularState ℂ) (i : Fin modularDimension) :
    eval (modularFieldCode i) (modularPoint z) =
      modularPoint (UnaryModularState.vectorField z) i := by
  fin_cases i <;>
    simp [modularFieldCode, modularAFieldCode, modularCFieldCode,
      modularEFieldCode, modularYFieldCode, modularPoint,
      ACode, CCode, ECode, YCode, AIndex, CIndex, EIndex, YIndex,
      UnaryModularState.vectorField]

/-- Reassembling the realization of the realified code recovers precisely
the complex vector field from `UnaryAlgebra`. -/
@[simp]
theorem complexify_realize_realModularFieldCode
    (z : UnaryModularState ℂ) :
    ComplexCoordinates.complexifyPoint
        (PolynomialFieldCode.realize realModularFieldCode
          (ComplexCoordinates.realifyPoint (modularPoint z))) =
      modularPoint (UnaryModularState.vectorField z) := by
  unfold realModularFieldCode
  rw [ComplexPolynomialFieldCode.complexifyPoint_realize_realify]
  funext i
  exact eval_modularFieldCode z i

@[simp]
theorem eval_scaledModularFieldCode
    (κ : GaussianRationalCode)
    (z : UnaryModularState ℂ) (i : Fin modularDimension) :
    eval (scaledModularFieldCode κ i) (modularPoint z) =
      GaussianRationalCode.decode κ *
        modularPoint (UnaryModularState.vectorField z) i := by
  simp [scaledModularFieldCode]

@[simp]
theorem complexify_realize_compileModularFieldCode
    (κ : GaussianRationalCode) (z : UnaryModularState ℂ) :
    ComplexCoordinates.complexifyPoint
        (PolynomialFieldCode.realize (compileModularFieldCode κ)
          (ComplexCoordinates.realifyPoint (modularPoint z))) =
      fun i ↦ GaussianRationalCode.decode κ *
        modularPoint (UnaryModularState.vectorField z) i := by
  unfold compileModularFieldCode
  rw [ComplexPolynomialFieldCode.complexifyPoint_realize_realify]
  funext i
  exact eval_scaledModularFieldCode κ z i

/-- The preceding theorem is genuinely global on the realified ambient
space: every real point is the realification of a unique complex state. -/
@[simp]
theorem complexify_realize_compileModularFieldCode_arbitrary
    (κ : GaussianRationalCode)
    (x : Fin (modularDimension + modularDimension) → ℝ) :
    ComplexCoordinates.complexifyPoint
        (PolynomialFieldCode.realize (compileModularFieldCode κ) x) =
      fun i ↦ GaussianRationalCode.decode κ *
        modularPoint
          (UnaryModularState.vectorField
            (modularState
              (ComplexCoordinates.complexifyPoint x))) i := by
  have h :=
    complexify_realize_compileModularFieldCode κ
      (modularState (ComplexCoordinates.complexifyPoint x))
  simpa using h

/-! ### Algebraic validity residual -/

/-- Finite code of Jacobi's residual `Y⁴-A-C`. -/
def jacobiResidualCode :
    ComplexPolynomialCode modularDimension :=
  sub (sub (pow YCode 4) ACode) CCode

@[simp]
theorem eval_jacobiResidualCode (z : UnaryModularState ℂ) :
    eval jacobiResidualCode (modularPoint z) =
      UnaryModularState.jacobiResidual z := by
  simp [jacobiResidualCode, modularPoint, ACode, CCode, YCode,
    AIndex, CIndex, YIndex, UnaryModularState.jacobiResidual]

/-! ## The eight-coordinate square-root extension -/

/-- Number of complex coordinates in the unary root block.  The ordering
is `A,C,E,Y,p₂,p₃,p₄,H`. -/
abbrev rootDimension : ℕ := 8

def rootAIndex : Fin rootDimension := 0
def rootCIndex : Fin rootDimension := 1
def rootEIndex : Fin rootDimension := 2
def rootYIndex : Fin rootDimension := 3
def p2Index : Fin rootDimension := 4
def p3Index : Fin rootDimension := 5
def p4Index : Fin rootDimension := 6
def HIndex : Fin rootDimension := 7

/-- Coordinate vector corresponding to a structured root state. -/
def rootPoint (z : UnaryRootState ℂ) : Fin rootDimension → ℂ :=
  ![z.A, z.C, z.E, z.Y, z.p2, z.p3, z.p4, z.H]

/-- Reassemble a root state from its eight complex coordinates. -/
def rootState
    (z : Fin rootDimension → ℂ) : UnaryRootState ℂ where
  A := z rootAIndex
  C := z rootCIndex
  E := z rootEIndex
  Y := z rootYIndex
  p2 := z p2Index
  p3 := z p3Index
  p4 := z p4Index
  H := z HIndex

@[simp]
theorem rootState_rootPoint (z : UnaryRootState ℂ) :
    rootState (rootPoint z) = z := by
  ext <;>
    simp [rootState, rootPoint, rootAIndex, rootCIndex, rootEIndex,
      rootYIndex, p2Index, p3Index, p4Index, HIndex]

@[simp]
theorem rootPoint_rootState (z : Fin rootDimension → ℂ) :
    rootPoint (rootState z) = z := by
  funext i
  fin_cases i <;> change z _ = z _ <;>
    apply congrArg z <;> rfl

def rA : ComplexPolynomialCode rootDimension := var rootAIndex
def rC : ComplexPolynomialCode rootDimension := var rootCIndex
def rE : ComplexPolynomialCode rootDimension := var rootEIndex
def rY : ComplexPolynomialCode rootDimension := var rootYIndex
def rp2 : ComplexPolynomialCode rootDimension := var p2Index
def rp3 : ComplexPolynomialCode rootDimension := var p3Index
def rp4 : ComplexPolynomialCode rootDimension := var p4Index
def rH : ComplexPolynomialCode rootDimension := var HIndex

def rootAFieldCode : ComplexPolynomialCode rootDimension :=
  mul (mul (rational (1 / 3)) rA)
    (add (add rE rA) (mul (rational 2) rC))

def rootCFieldCode : ComplexPolynomialCode rootDimension :=
  mul (mul (rational (1 / 3)) rC)
    (sub (sub rE (mul (rational 2) rA)) rC)

def rootEFieldCode : ComplexPolynomialCode rootDimension :=
  mul (rational (1 / 6))
    (sub (sub (sub (pow rE 2) (pow rA 2)) (mul rA rC))
      (pow rC 2))

def rootYFieldCode : ComplexPolynomialCode rootDimension :=
  mul (mul (rational (1 / 12)) (sub (add rE rA) rC)) rY

def p2FieldCode : ComplexPolynomialCode rootDimension :=
  mul
    (mul (rational (1 / 6))
      (add (add (mul (rational 12) rH) (pow rp2 2))
        (mul (rational 2) (pow rp4 2))))
    rp2

def p3FieldCode : ComplexPolynomialCode rootDimension :=
  mul
    (mul (rational (1 / 6))
      (sub (add (mul (rational 12) rH) (pow rp2 2))
        (pow rp4 2)))
    rp3

def p4FieldCode : ComplexPolynomialCode rootDimension :=
  mul
    (mul (rational (1 / 6))
      (sub
        (sub (mul (rational 12) rH)
          (mul (rational 2) (pow rp2 2)))
        (pow rp4 2)))
    rp4

def HFieldCode : ComplexPolynomialCode rootDimension :=
  mul (rational (1 / 72))
    (sub
      (sub
        (sub (pow (mul (rational 12) rH) 2) (pow rp2 4))
        (mul (pow rp2 2) (pow rp4 2)))
      (pow rp4 4))

/-- Executable complex field for the square-root extension. -/
def rootFieldCode :
    ComplexPolynomialFieldCode rootDimension :=
  ![rootAFieldCode, rootCFieldCode, rootEFieldCode, rootYFieldCode,
    p2FieldCode, p3FieldCode, p4FieldCode, HFieldCode]

/-- Ordinary rational realification of the root field on sixteen real
coordinates. -/
def realRootFieldCode :
    PolynomialFieldCode (rootDimension + rootDimension) :=
  ComplexPolynomialFieldCode.realify rootFieldCode

/-- Root field at a coded Gaussian-rational clock rate. -/
def scaledRootFieldCode (κ : GaussianRationalCode) :
    ComplexPolynomialFieldCode rootDimension :=
  scaleFieldCode κ rootFieldCode

/-- Executable real compiler for the scaled root field. -/
def compileRootFieldCode (κ : GaussianRationalCode) :
    PolynomialFieldCode (rootDimension + rootDimension) :=
  ComplexPolynomialFieldCode.realify (scaledRootFieldCode κ)

@[simp]
theorem eval_rootFieldCode
    (z : UnaryRootState ℂ) (i : Fin rootDimension) :
    eval (rootFieldCode i) (rootPoint z) =
      rootPoint (UnaryRootState.vectorField z) i := by
  fin_cases i <;>
    simp [rootFieldCode, rootAFieldCode, rootCFieldCode,
      rootEFieldCode, rootYFieldCode, p2FieldCode, p3FieldCode,
      p4FieldCode, HFieldCode, rootPoint, rA, rC, rE, rY, rp2,
      rp3, rp4, rH, rootAIndex, rootCIndex, rootEIndex, rootYIndex,
      p2Index, p3Index, p4Index, HIndex,
      UnaryRootState.vectorField, UnaryModularState.vectorField]

@[simp]
theorem complexify_realize_realRootFieldCode
    (z : UnaryRootState ℂ) :
    ComplexCoordinates.complexifyPoint
        (PolynomialFieldCode.realize realRootFieldCode
          (ComplexCoordinates.realifyPoint (rootPoint z))) =
      rootPoint (UnaryRootState.vectorField z) := by
  unfold realRootFieldCode
  rw [ComplexPolynomialFieldCode.complexifyPoint_realize_realify]
  funext i
  exact eval_rootFieldCode z i

@[simp]
theorem eval_scaledRootFieldCode
    (κ : GaussianRationalCode)
    (z : UnaryRootState ℂ) (i : Fin rootDimension) :
    eval (scaledRootFieldCode κ i) (rootPoint z) =
      GaussianRationalCode.decode κ *
        rootPoint (UnaryRootState.vectorField z) i := by
  simp [scaledRootFieldCode]

@[simp]
theorem complexify_realize_compileRootFieldCode
    (κ : GaussianRationalCode) (z : UnaryRootState ℂ) :
    ComplexCoordinates.complexifyPoint
        (PolynomialFieldCode.realize (compileRootFieldCode κ)
          (ComplexCoordinates.realifyPoint (rootPoint z))) =
      fun i ↦ GaussianRationalCode.decode κ *
        rootPoint (UnaryRootState.vectorField z) i := by
  unfold compileRootFieldCode
  rw [ComplexPolynomialFieldCode.complexifyPoint_realize_realify]
  funext i
  exact eval_scaledRootFieldCode κ z i

/-- Global real-coordinate semantics of the compiled root field. -/
@[simp]
theorem complexify_realize_compileRootFieldCode_arbitrary
    (κ : GaussianRationalCode)
    (x : Fin (rootDimension + rootDimension) → ℝ) :
    ComplexCoordinates.complexifyPoint
        (PolynomialFieldCode.realize (compileRootFieldCode κ) x) =
      fun i ↦ GaussianRationalCode.decode κ *
        rootPoint
          (UnaryRootState.vectorField
            (rootState
              (ComplexCoordinates.complexifyPoint x))) i := by
  have h :=
    complexify_realize_compileRootFieldCode κ
      (rootState (ComplexCoordinates.complexifyPoint x))
  simpa using h

/-! ### Root-link residual codes -/

/-- Unary Jacobi residual in the eight-coordinate root ambient space. -/
def rootJacobiResidualCode : ComplexPolynomialCode rootDimension :=
  sub (sub (pow rY 4) rA) rC

/-- Residual for `p₂²=A`. -/
def link2Code : ComplexPolynomialCode rootDimension :=
  sub (pow rp2 2) rA

/-- Residual for `p₄²=C`. -/
def link4Code : ComplexPolynomialCode rootDimension :=
  sub (pow rp4 2) rC

/-- Residual for `12H=E`. -/
def linkHCode : ComplexPolynomialCode rootDimension :=
  sub (mul (rational 12) rH) rE

/-- Signed residual selecting `p₃=Y²`. -/
def signedLink3Code : ComplexPolynomialCode rootDimension :=
  sub rp3 (pow rY 2)

/-- The five validity residuals, ordered as
`R_J,L₂,L₄,L_H,S₃`. -/
def rootResidualCode (i : Fin 5) :
    ComplexPolynomialCode rootDimension :=
  ![rootJacobiResidualCode, link2Code, link4Code,
    linkHCode, signedLink3Code] i

@[simp]
theorem eval_rootJacobiResidualCode (z : UnaryRootState ℂ) :
    eval rootJacobiResidualCode (rootPoint z) =
      UnaryModularState.jacobiResidual z.toUnaryModularState := by
  simp [rootJacobiResidualCode, rootPoint, rA, rC, rY,
    rootAIndex, rootCIndex, rootYIndex,
    UnaryModularState.jacobiResidual]

@[simp]
theorem eval_link2Code (z : UnaryRootState ℂ) :
    eval link2Code (rootPoint z) = UnaryRootState.link2 z := by
  simp [link2Code, rootPoint, rp2, rA, p2Index, rootAIndex,
    UnaryRootState.link2]

@[simp]
theorem eval_link4Code (z : UnaryRootState ℂ) :
    eval link4Code (rootPoint z) = UnaryRootState.link4 z := by
  simp [link4Code, rootPoint, rp4, rC, p4Index, rootCIndex,
    UnaryRootState.link4]

@[simp]
theorem eval_linkHCode (z : UnaryRootState ℂ) :
    eval linkHCode (rootPoint z) = UnaryRootState.linkH z := by
  simp [linkHCode, rootPoint, rH, rE, HIndex, rootEIndex,
    UnaryRootState.linkH]

@[simp]
theorem eval_signedLink3Code (z : UnaryRootState ℂ) :
    eval signedLink3Code (rootPoint z) =
      UnaryRootState.signedLink3 z := by
  simp [signedLink3Code, rootPoint, rp3, rY, p3Index, rootYIndex,
    UnaryRootState.signedLink3]

@[simp]
theorem eval_rootResidualCode
    (z : UnaryRootState ℂ) (i : Fin 5) :
    eval (rootResidualCode i) (rootPoint z) =
      ![UnaryModularState.jacobiResidual z.toUnaryModularState,
        UnaryRootState.link2 z, UnaryRootState.link4 z,
        UnaryRootState.linkH z, UnaryRootState.signedLink3 z] i := by
  fin_cases i <;> simp [rootResidualCode]

end UnaryPolynomialCode

/-! ## Reusable fourth-root gauge compiler -/

namespace GaugePolynomialCode

open ComplexPolynomialCode

/-- The gauge ambient space has coordinates `(G,C)`. -/
abbrev dimension : ℕ := 2

def GIndex : Fin dimension := 0
def clockIndex : Fin dimension := 1

def point (G C : ℂ) : Fin dimension → ℂ :=
  ![G, C]

def GCode : ComplexPolynomialCode dimension := var GIndex
def clockCode : ComplexPolynomialCode dimension := var clockIndex

/-- Gauge field with logarithmic coefficient `a`:
`G'=aG`, `C'=4aC`. -/
def fieldCode (a : GaussianRationalCode) :
    ComplexPolynomialFieldCode dimension :=
  ![mulGaussian a GCode,
    mul (UnaryPolynomialCode.rational 4)
      (mulGaussian a clockCode)]

/-- Rational realification of `fieldCode a`. -/
def realFieldCode (a : GaussianRationalCode) :
    PolynomialFieldCode (dimension + dimension) :=
  ComplexPolynomialFieldCode.realify (fieldCode a)

/-- Finite code of the link residual `G⁴-C`. -/
def residualCode : ComplexPolynomialCode dimension :=
  sub (pow GCode 4) clockCode

@[simp]
theorem eval_fieldCode
    (a : GaussianRationalCode) (G C : ℂ) :
    (fun i ↦ eval (fieldCode a i) (point G C)) =
      ![GaussianRationalCode.decode a * G,
        4 * GaussianRationalCode.decode a * C] := by
  funext i
  fin_cases i
  · simp [fieldCode, point, GCode, clockCode,
      GIndex, clockIndex, UnaryPolynomialCode.rational]
  · simp [fieldCode, point, GCode, clockCode,
      GIndex, clockIndex, UnaryPolynomialCode.rational]
    ring

@[simp]
theorem eval_residualCode (G C : ℂ) :
    eval residualCode (point G C) =
      gaugeFourthRootResidual G C := by
  simp [residualCode, point, GCode, clockCode, GIndex, clockIndex,
    gaugeFourthRootResidual]

/-- Code of the modular gauge coefficient `i/4`. -/
def modularCoefficient : GaussianRationalCode :=
  (RationalCode.zero, RationalCode.encode (1 / 4))

/-- Code of the elliptic gauge coefficient `i/2`. -/
def ellipticCoefficient : GaussianRationalCode :=
  (RationalCode.zero, RationalCode.encode (1 / 2))

@[simp]
theorem decode_modularCoefficient :
    GaussianRationalCode.decode modularCoefficient =
      Complex.I / 4 := by
  apply Complex.ext <;>
    simp [modularCoefficient, GaussianRationalCode.decode]

@[simp]
theorem decode_ellipticCoefficient :
    GaussianRationalCode.decode ellipticCoefficient =
      Complex.I / 2 := by
  apply Complex.ext <;>
    simp [ellipticCoefficient, GaussianRationalCode.decode]

end GaugePolynomialCode

end HGAS.Modular
