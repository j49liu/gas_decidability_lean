import HGAS.Arithmetic.CorrectedJacobiSelectorCentering
import HGAS.Arithmetic.FixedDetectorMomentCode
import Mathlib.Tactic

/-!
# Corrected finite selector-moment compiler

This is a conservative replacement for `FixedDetectorMomentCode` which
changes only the constants subtracted from the last two Jacobi moments.
The first five moment codes are reused verbatim.  For DQL variable `j`,
the two corrected moments are

```text
  F_j (Q_j V_j)⁻¹ - c_j,
  F_j Q_j⁻¹ V_j - c_j,
```

where

```text
  c_j = 1/128   if the complete linear column of `j` is zero,
        1/256   otherwise.
```

`CorrectedJacobiSelectorCentering` proves that this is exactly the
aggregate zero-frequency coefficient in both cases.  All definitions are
placed in a new namespace and file, preserving the previously saved
compiler for comparison and audit.
-/

namespace HGAS

open Clocks.ControllerPhaseProductCharacterCode

namespace CorrectedFixedDetectorMomentCode

variable {eqs vars : ℕ}

abbrev dimension (eqs vars : ℕ) : ℕ :=
  FixedDetectorMomentCode.dimension eqs vars

abbrev localMomentCount : ℕ :=
  FixedDetectorMomentCode.localMomentCount

abbrev momentCount (vars : ℕ) : ℕ :=
  FixedDetectorMomentCode.momentCount vars

abbrev scalarMomentCount (vars : ℕ) : ℕ :=
  FixedDetectorMomentCode.scalarMomentCount vars

/-- Corrected `(1,1)` Jacobi selector polynomial. -/
def jacobiPlusMeanCode
    (I : DQLSystem eqs vars) (j : Fin vars) :
    ComplexPairCode (dimension eqs vars) :=
  FixedDetectorMomentCode.subPair
    (mul (FixedDetectorMomentCode.thetaOutputPair j)
      (FixedDetectorMomentCode.controllerCharacterPair
        (FixedDetectorMomentCode.jacobiPlusExponent I j)))
    (FixedDetectorMomentCode.rationalPair
      (CorrectedJacobiSelectorCentering.selectorCenter I j))

/-- Corrected `(1,-1)` Jacobi selector polynomial. -/
def jacobiMinusMeanCode
    (I : DQLSystem eqs vars) (j : Fin vars) :
    ComplexPairCode (dimension eqs vars) :=
  FixedDetectorMomentCode.subPair
    (mul (FixedDetectorMomentCode.thetaOutputPair j)
      (FixedDetectorMomentCode.controllerCharacterPair
        (FixedDetectorMomentCode.jacobiMinusExponent I j)))
    (FixedDetectorMomentCode.rationalPair
      (CorrectedJacobiSelectorCentering.selectorCenter I j))

/-- Seven corrected local moments.  Entries `0` through `4` are literally
the original definitions; only entries `5` and `6` use conditional
centering. -/
def localMomentCode
    (I : DQLSystem eqs vars) (j : Fin vars) :
    Fin localMomentCount →
      ComplexPairCode (dimension eqs vars) :=
  ![
    FixedDetectorMomentCode.unaryMeanCode j,
    FixedDetectorMomentCode.unaryFirstHarmonicCode j,
    FixedDetectorMomentCode.rootP4MeanCode j,
    FixedDetectorMomentCode.rootP2MeanCode j,
    FixedDetectorMomentCode.jacobiMeanCode j,
    jacobiPlusMeanCode I j,
    jacobiMinusMeanCode I j
  ]

/-- All corrected complex moments, flattened by variable and moment
kind. -/
def momentCode
    (I : DQLSystem eqs vars) :
    Fin (momentCount vars) →
      ComplexPairCode (dimension eqs vars) :=
  fun k ↦
    let jm := finProdFinEquiv.symm k
    localMomentCode I jm.1 jm.2

/-- Corrected realified moment coordinates. -/
def scalarMomentCode
    (I : DQLSystem eqs vars) :
    Fin (scalarMomentCount vars) →
      PolynomialCode (dimension eqs vars) :=
  fun k ↦
    let mc := finProdFinEquiv.symm k
    ![(momentCode I mc.1).1,
      (momentCode I mc.1).2] mc.2

/-- Human-facing semantics of the corrected local selector. -/
noncomputable def localMomentValue
    (I : DQLSystem eqs vars) (j : Fin vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    Fin localMomentCount → ℂ :=
  ![
    (z.base.base.source.linked j).unary.Y - 1,
    (z.base.base.source.linked j).unary.Y *
        characterValue
          (FixedDetectorMomentCode.unaryFirstHarmonicExponent j)
          z.base.base.source.controllers -
      (1 / 128 : ℚ),
    (z.base.base.source.linked j).jacobi.p4 - 1,
    (z.base.base.source.linked j).jacobi.p2 *
        characterValue
          (FixedDetectorMomentCode.rootHalfExponent j)
          z.base.base.source.controllers -
      (1 / 4 : ℚ),
    z.base.base.gauge j *
        (z.base.base.source.linked j).jacobi.T1 -
      1,
    (z.base.base.gauge j *
        (z.base.base.source.linked j).jacobi.T1) *
        characterValue
          (FixedDetectorMomentCode.jacobiPlusExponent I j)
          z.base.base.source.controllers -
      CorrectedJacobiSelectorCentering.selectorCenter I j,
    (z.base.base.gauge j *
        (z.base.base.source.linked j).jacobi.T1) *
        characterValue
          (FixedDetectorMomentCode.jacobiMinusExponent I j)
          z.base.base.source.controllers -
      CorrectedJacobiSelectorCentering.selectorCenter I j
  ]

@[simp]
theorem evalPair_jacobiPlusMeanCode
    (I : DQLSystem eqs vars) (j : Fin vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    evalPair (jacobiPlusMeanCode I j)
        (FixedDetectorPolynomialCode.point z) =
      (z.base.base.gauge j *
          (z.base.base.source.linked j).jacobi.T1) *
          characterValue
            (FixedDetectorMomentCode.jacobiPlusExponent I j)
            z.base.base.source.controllers -
        CorrectedJacobiSelectorCentering.selectorCenter I j := by
  simp [jacobiPlusMeanCode,
    FixedDetectorMomentCode.evalPair_thetaOutputPair,
    FixedDetectorMomentCode.evalPair_controllerCharacterPair]

@[simp]
theorem evalPair_jacobiMinusMeanCode
    (I : DQLSystem eqs vars) (j : Fin vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    evalPair (jacobiMinusMeanCode I j)
        (FixedDetectorPolynomialCode.point z) =
      (z.base.base.gauge j *
          (z.base.base.source.linked j).jacobi.T1) *
          characterValue
            (FixedDetectorMomentCode.jacobiMinusExponent I j)
            z.base.base.source.controllers -
        CorrectedJacobiSelectorCentering.selectorCenter I j := by
  simp [jacobiMinusMeanCode,
    FixedDetectorMomentCode.evalPair_thetaOutputPair,
    FixedDetectorMomentCode.evalPair_controllerCharacterPair]

@[simp]
theorem evalPair_localMomentCode
    (I : DQLSystem eqs vars) (j : Fin vars)
    (r : Fin localMomentCount)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    evalPair (localMomentCode I j r)
        (FixedDetectorPolynomialCode.point z) =
      localMomentValue I j z r := by
  fin_cases r <;>
    simp [localMomentCode, localMomentValue]

end CorrectedFixedDetectorMomentCode

end HGAS
