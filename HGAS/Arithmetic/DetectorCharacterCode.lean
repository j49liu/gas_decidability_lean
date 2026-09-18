import HGAS.Arithmetic.DetectorFourier
import HGAS.Clocks.ControllerPhaseProductCharacterDynamics
import Mathlib.Tactic

/-!
# Finite character data for the DQL detector

The analytic detector is written on a torus indexed by

```
                 DetectorPhase eqs vars
                   = Fin vars ⊕ Fin eqs.
```

The polynomial clock compiler uses the equivalent flat type
`Fin (vars + eqs)`.  Its phase coordinates are the fundamental circles
`ζ`, whereas every arithmetic character in the detector is the fourth
power `ζ⁴`.  Thus flattening includes the common factor four.  This file
records that conversion once and compiles all Laurent characters appearing
in one detector:

* the private character `Q_j`;
* the quadratic equation character `S_j`;
* the linear equation character `V_j`;
* the Poisson argument `W_j = Q_j⁻¹ S_j`; and
* the right-hand-side character `exp(-i c · u)`.

It also proves, before any analytic realization is considered, that
multiplying a theta term and a Poisson term produces exactly the Fourier
exponent `detectorExponent`.  This makes the eventual polynomial-observable
proof a finite character calculation rather than a second derivation of
the arithmetic constant-term identity.
-/

namespace HGAS.DetectorCharacterCode

open HGAS.Clocks.ControllerPhaseProductCharacterCode
open scoped BigOperators

variable {eqs vars : ℕ}

/-- Flatten the sum-indexed arithmetic detector torus into the product
compiler's canonical fundamental-clock indexing.  The factor four is the
manuscript's fourth-power convention `Q,V,S = ζ⁴`; it preserves Haar
orthogonality while making the theta gauge roots Laurent monomials. -/
def flattenCharacter
    (a : DetectorPhase eqs vars → ℤ) :
    Fin (vars + eqs) → ℤ :=
  fun i ↦ 4 * a (finSumFinEquiv.symm i)

/-- The private character `Q_j`. -/
def privateCharacter
    (j : Fin vars) : DetectorPhase eqs vars → ℤ
  | Sum.inl k => if k = j then 1 else 0
  | Sum.inr _ => 0

/-- The equation character whose exponent vector is the `j`th quadratic
column of the DQL system. -/
def quadraticCharacter
    (I : DQLSystem eqs vars) (j : Fin vars) :
    DetectorPhase eqs vars → ℤ
  | Sum.inl _ => 0
  | Sum.inr row => I.quadratic row j

/-- The equation character whose exponent vector is the `j`th linear
column of the DQL system. -/
def linearCharacter
    (I : DQLSystem eqs vars) (j : Fin vars) :
    DetectorPhase eqs vars → ℤ
  | Sum.inl _ => 0
  | Sum.inr row => I.linear row j

/-- The global right-hand-side character `exp(-i c · u)`. -/
def rhsCharacter
    (I : DQLSystem eqs vars) :
    DetectorPhase eqs vars → ℤ
  | Sum.inl _ => 0
  | Sum.inr row => -I.rhs row

/-- Exponent vector of `W_j = Q_j⁻¹ S_j`. -/
def poissonArgumentCharacter
    (I : DQLSystem eqs vars) (j : Fin vars)
    (phase : DetectorPhase eqs vars) : ℤ :=
  -privateCharacter j phase +
    quadraticCharacter I j phase

/-- Character contributed by index `x_j` in the `j`th theta series:
`Q_j^(x_j²) V_j^(x_j)`. -/
def thetaTermCharacter
    (I : DQLSystem eqs vars)
    (x : Fin vars → ℤ) (j : Fin vars)
    (phase : DetectorPhase eqs vars) : ℤ :=
  x j ^ 2 * privateCharacter j phase +
    x j * linearCharacter I j phase

/-- Character of one fully expanded detector term indexed by `(x,s)`. -/
def expandedTermCharacter
    (I : DQLSystem eqs vars)
    (x s : Fin vars → ℤ)
    (phase : DetectorPhase eqs vars) : ℤ :=
  rhsCharacter I phase +
    ∑ j : Fin vars,
      (thetaTermCharacter I x j phase +
        s j * poissonArgumentCharacter I j phase)

/-- The finite character bookkeeping agrees exactly with the exponent used
in the already proved detector Fourier expansion. -/
theorem expandedTermCharacter_eq_detectorExponent
    (I : DQLSystem eqs vars)
    (x s : Fin vars → ℤ) :
    expandedTermCharacter I x s =
      detectorExponent I (x, s) := by
  funext phase
  cases phase with
  | inl k =>
      simp only [expandedTermCharacter, rhsCharacter,
        thetaTermCharacter, poissonArgumentCharacter,
        privateCharacter, quadraticCharacter, linearCharacter,
        detectorExponent, privatePhaseExponent]
      rw [Finset.sum_eq_single k]
      · simp
        ring
      · intro j _ hj
        simp [show k ≠ j from Ne.symm hj]
      · simp
  | inr row =>
      simp only [expandedTermCharacter, rhsCharacter,
        thetaTermCharacter, poissonArgumentCharacter,
        privateCharacter, quadraticCharacter, linearCharacter,
        detectorExponent, equationPhaseExponent]
      simp only [mul_zero, neg_zero, zero_add]
      have hsum :
          (∑ j : Fin vars,
              (x j * I.linear row j +
                s j * I.quadratic row j)) =
            ∑ j : Fin vars,
              (I.quadratic row j * s j +
                I.linear row j * x j) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hsum]
      ring

/-! ## Literal sparse-polynomial character codes -/

abbrev clockCount (eqs vars : ℕ) : ℕ :=
  vars + eqs

def privateCode
    (j : Fin vars) :
    ComplexPairCode
      (HGAS.Clocks.ControllerPhaseProductPolynomialCode.dimension
        (clockCount eqs vars)) :=
  characterCode
    (flattenCharacter (privateCharacter (eqs := eqs) j))

def quadraticCode
    (I : DQLSystem eqs vars) (j : Fin vars) :
    ComplexPairCode
      (HGAS.Clocks.ControllerPhaseProductPolynomialCode.dimension
        (clockCount eqs vars)) :=
  characterCode
    (flattenCharacter (quadraticCharacter I j))

def linearCode
    (I : DQLSystem eqs vars) (j : Fin vars) :
    ComplexPairCode
      (HGAS.Clocks.ControllerPhaseProductPolynomialCode.dimension
        (clockCount eqs vars)) :=
  characterCode
    (flattenCharacter (linearCharacter I j))

def poissonArgumentCode
    (I : DQLSystem eqs vars) (j : Fin vars) :
    ComplexPairCode
      (HGAS.Clocks.ControllerPhaseProductPolynomialCode.dimension
        (clockCount eqs vars)) :=
  characterCode
    (flattenCharacter (poissonArgumentCharacter I j))

def rhsCode
    (I : DQLSystem eqs vars) :
    ComplexPairCode
      (HGAS.Clocks.ControllerPhaseProductPolynomialCode.dimension
        (clockCount eqs vars)) :=
  characterCode (flattenCharacter (rhsCharacter I))

/-- Controller-frequency weights for the private modular clock of block
`j`. -/
def omegaWeights
    (j : Fin vars) :
    Fin (clockCount eqs vars) → RationalCode :=
  fun i ↦
    exponentWeightCode
      (flattenCharacter
        (privateCharacter (eqs := eqs) j) i)

/-- Controller-frequency weights for the linear equation character
`V_j`. -/
def numberWeights
    (I : DQLSystem eqs vars) (j : Fin vars) :
    Fin (clockCount eqs vars) → RationalCode :=
  fun i ↦
    exponentWeightCode
      (flattenCharacter (linearCharacter I j) i)

/-- The private character frequency code is definitionally the frequency
readout used to drive the corresponding linked Jacobi block. -/
theorem privateFrequencyCode_eq
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (j : Fin vars) :
    frequencyCode parameters
        (flattenCharacter
          (privateCharacter (eqs := eqs) j)) =
      HGAS.Clocks.ControllerPhaseProductLinearFrequencyCode.code
        (omegaWeights (eqs := eqs) j) parameters :=
  rfl

/-- Likewise, the linear equation character frequency is the block's
`N_j` readout. -/
theorem linearFrequencyCode_eq
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars) (j : Fin vars) :
    frequencyCode parameters
        (flattenCharacter (linearCharacter I j)) =
      HGAS.Clocks.ControllerPhaseProductLinearFrequencyCode.code
        (numberWeights I j) parameters :=
  rfl

end HGAS.DetectorCharacterCode
