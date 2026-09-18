import HGAS.Compiler.ComplexReciprocalPolynomialCode
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Effectivity of the complex reciprocal polynomial compiler

This file isolates the purely finite compilation algorithm behind the
complex reciprocal extension.  For a fixed base dimension `n`, its input
is bundled as

```
  (F, (η, wdot))
```

where `F` is a finite vector of rational sparse polynomial codes, `η` is
a coded rational number, and `wdot` is a pair of rational sparse codes.
The output is the complete extended vector field.  The graph-residual
compiler is similarly bundled as `(η, w)` and returns its real and
imaginary residual codes together.

Every construction below is primitive recursive, hence computable.
Compilation consists only of finite tuple projections, variable
renaming, and sparse-list addition, negation, and multiplication.  It
does not decode a rational into a real number, normalize a polynomial,
solve an equation, or inspect a trajectory.
-/

namespace HGAS.ComplexReciprocalPolynomialCode

variable {n : ℕ}

/-- Bundled finite syntax accepted by the complete field compiler. -/
abbrev CompilerInput (n : ℕ) :=
  PolynomialFieldCode n ×
    (RationalCode × ComplexObservableCode n)

/-- Bundled finite syntax accepted by the residual compiler. -/
abbrev ResidualInput (n : ℕ) :=
  RationalCode × ComplexObservableCode n

/-- The two reciprocal-velocity output coordinates, bundled as finite
syntax before they are inserted into the extended field. -/
def velocityCodes
    (input : ResidualInput n) :
    PolynomialCode (dimension n) ×
      PolynomialCode (dimension n) :=
  (reciprocalVelocityReCode input.1 input.2,
    reciprocalVelocityImCode input.1 input.2)

/-- The real and imaginary reciprocal graph residuals, bundled together. -/
def residualCodes
    (input : ResidualInput n) :
    PolynomialCode (dimension n) ×
      PolynomialCode (dimension n) :=
  (residualReCode input.1 input.2,
    residualImCode input.1 input.2)

/-- Variable insertion from the base block into the extended block is
primitive recursive. -/
theorem liftBase_primrec :
    Primrec
      (liftBase :
        PolynomialCode n →
          PolynomialCode (dimension n)) :=
  PolynomialBlockCode.left_primrec

/-- Forming the degree-zero code of the rational parameter is primitive
recursive. -/
theorem etaCode_primrec :
    Primrec
      (etaCode :
        RationalCode → PolynomialCode (dimension n)) :=
  PolynomialCode.constant_primrec

/-- The real reciprocal-velocity coordinate is primitive recursive in
the bundled pair `(η, wdot)`. -/
theorem reciprocalVelocityReCode_primrec :
    Primrec
      (fun input : ResidualInput n ↦
        reciprocalVelocityReCode input.1 input.2) := by
  have heta :
      Primrec
        (fun input : ResidualInput n ↦
          etaCode (n := n) input.1) :=
    (etaCode_primrec (n := n)).comp Primrec.fst
  have hwdotRe :
      Primrec
        (fun input : ResidualInput n ↦
          liftBase input.2.1) :=
    liftBase_primrec.comp
      (Primrec.fst.comp Primrec.snd)
  have hwdotIm :
      Primrec
        (fun input : ResidualInput n ↦
          liftBase input.2.2) :=
    liftBase_primrec.comp
      (Primrec.snd.comp Primrec.snd)
  have hinner :
      Primrec
        (fun input : ResidualInput n ↦
          PolynomialCode.sub
            (PolynomialCode.mul (liftBase input.2.1)
              (reciprocalSquareReCode :
                PolynomialCode (dimension n)))
            (PolynomialCode.mul (liftBase input.2.2)
              (reciprocalSquareImCode :
                PolynomialCode (dimension n)))) :=
    PolynomialCode.sub_primrec.comp
      (PolynomialCode.mul_primrec.comp hwdotRe
        (Primrec.const reciprocalSquareReCode))
      (PolynomialCode.mul_primrec.comp hwdotIm
        (Primrec.const reciprocalSquareImCode))
  exact
    (PolynomialCode.mul_primrec.comp heta hinner).of_eq
      fun input ↦ rfl

/-- The imaginary reciprocal-velocity coordinate is primitive recursive
in the bundled pair `(η, wdot)`. -/
theorem reciprocalVelocityImCode_primrec :
    Primrec
      (fun input : ResidualInput n ↦
        reciprocalVelocityImCode input.1 input.2) := by
  have heta :
      Primrec
        (fun input : ResidualInput n ↦
          etaCode (n := n) input.1) :=
    (etaCode_primrec (n := n)).comp Primrec.fst
  have hwdotRe :
      Primrec
        (fun input : ResidualInput n ↦
          liftBase input.2.1) :=
    liftBase_primrec.comp
      (Primrec.fst.comp Primrec.snd)
  have hwdotIm :
      Primrec
        (fun input : ResidualInput n ↦
          liftBase input.2.2) :=
    liftBase_primrec.comp
      (Primrec.snd.comp Primrec.snd)
  have hinner :
      Primrec
        (fun input : ResidualInput n ↦
          PolynomialCode.add
            (PolynomialCode.mul (liftBase input.2.1)
              (reciprocalSquareImCode :
                PolynomialCode (dimension n)))
            (PolynomialCode.mul (liftBase input.2.2)
              (reciprocalSquareReCode :
                PolynomialCode (dimension n)))) :=
    PolynomialCode.add_primrec.comp
      (PolynomialCode.mul_primrec.comp hwdotRe
        (Primrec.const reciprocalSquareImCode))
      (PolynomialCode.mul_primrec.comp hwdotIm
        (Primrec.const reciprocalSquareReCode))
  exact
    (PolynomialCode.mul_primrec.comp heta hinner).of_eq
      fun input ↦ rfl

/-- The bundled pair of reciprocal-velocity equations is primitive
recursive. -/
theorem velocityCodes_primrec :
    Primrec (velocityCodes : ResidualInput n →
      PolynomialCode (dimension n) ×
        PolynomialCode (dimension n)) := by
  exact
    Primrec.pair reciprocalVelocityReCode_primrec
      reciprocalVelocityImCode_primrec

theorem velocityCodes_computable :
    Computable (velocityCodes : ResidualInput n →
      PolynomialCode (dimension n) ×
        PolynomialCode (dimension n)) :=
  velocityCodes_primrec.to_comp

/-- **Effective reciprocal field compiler.**

For every fixed base dimension, assembling the complete extended field
from the bundled finite syntax `(F, (η, wdot))` is primitive recursive. -/
theorem fieldCode_primrec :
    Primrec
      (fun input : CompilerInput n ↦
        fieldCode input.1 input.2.1 input.2.2) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro k
  cases hk : finSumFinEquiv.symm k with
  | inl i =>
      exact
        (liftBase_primrec.comp
          (Primrec.fin_app.comp Primrec.fst
            (Primrec.const i))).of_eq fun input ↦ by
              simp [fieldCode, hk]
  | inr j =>
      fin_cases j
      · exact
          (reciprocalVelocityReCode_primrec.comp
            Primrec.snd).of_eq fun input ↦ by
              simp [fieldCode, hk]
      · exact
          (reciprocalVelocityImCode_primrec.comp
            Primrec.snd).of_eq fun input ↦ by
              simp [fieldCode, hk]

theorem fieldCode_computable :
    Computable
      (fun input : CompilerInput n ↦
        fieldCode input.1 input.2.1 input.2.2) :=
  fieldCode_primrec.to_comp

/-- The real denominator coordinate is primitive recursive in `(η, w)`. -/
theorem denominatorReCode_primrec :
    Primrec
      (fun input : ResidualInput n ↦
        denominatorReCode input.1 input.2) := by
  have heta :
      Primrec
        (fun input : ResidualInput n ↦
          etaCode (n := n) input.1) :=
    (etaCode_primrec (n := n)).comp Primrec.fst
  have hwRe :
      Primrec
        (fun input : ResidualInput n ↦
          liftBase input.2.1) :=
    liftBase_primrec.comp
      (Primrec.fst.comp Primrec.snd)
  exact
    (PolynomialCode.sub_primrec.comp
      (Primrec.const (oneCode :
        PolynomialCode (dimension n)))
      (PolynomialCode.mul_primrec.comp heta hwRe)).of_eq
        fun input ↦ rfl

/-- The imaginary denominator coordinate is primitive recursive in
`(η, w)`. -/
theorem denominatorImCode_primrec :
    Primrec
      (fun input : ResidualInput n ↦
        denominatorImCode input.1 input.2) := by
  have heta :
      Primrec
        (fun input : ResidualInput n ↦
          etaCode (n := n) input.1) :=
    (etaCode_primrec (n := n)).comp Primrec.fst
  have hwIm :
      Primrec
        (fun input : ResidualInput n ↦
          liftBase input.2.2) :=
    liftBase_primrec.comp
      (Primrec.snd.comp Primrec.snd)
  exact
    (PolynomialCode.neg_primrec.comp
      (PolynomialCode.mul_primrec.comp heta hwIm)).of_eq
        fun input ↦ rfl

/-- The real reciprocal graph residual is primitive recursive in
the bundled pair `(η, w)`. -/
theorem residualReCode_primrec :
    Primrec
      (fun input : ResidualInput n ↦
        residualReCode input.1 input.2) := by
  have hreProduct :
      Primrec
        (fun input : ResidualInput n ↦
          PolynomialCode.mul
            (denominatorReCode input.1 input.2)
            (reciprocalReCode :
              PolynomialCode (dimension n))) :=
    PolynomialCode.mul_primrec.comp
      denominatorReCode_primrec
      (Primrec.const reciprocalReCode)
  have himProduct :
      Primrec
        (fun input : ResidualInput n ↦
          PolynomialCode.mul
            (denominatorImCode input.1 input.2)
            (reciprocalImCode :
              PolynomialCode (dimension n))) :=
    PolynomialCode.mul_primrec.comp
      denominatorImCode_primrec
      (Primrec.const reciprocalImCode)
  exact
    (PolynomialCode.sub_primrec.comp
      (PolynomialCode.sub_primrec.comp hreProduct himProduct)
      (Primrec.const (oneCode :
        PolynomialCode (dimension n)))).of_eq
          fun input ↦ rfl

/-- The imaginary reciprocal graph residual is primitive recursive in
the bundled pair `(η, w)`. -/
theorem residualImCode_primrec :
    Primrec
      (fun input : ResidualInput n ↦
        residualImCode input.1 input.2) := by
  exact
    (PolynomialCode.add_primrec.comp
      (PolynomialCode.mul_primrec.comp
        denominatorReCode_primrec
        (Primrec.const (reciprocalImCode :
          PolynomialCode (dimension n))))
      (PolynomialCode.mul_primrec.comp
        denominatorImCode_primrec
        (Primrec.const (reciprocalReCode :
          PolynomialCode (dimension n))))).of_eq
            fun input ↦ rfl

/-- **Effective reciprocal residual compiler.**

The bundled map `(η, w) ↦ (Re R, Im R)` is primitive recursive. -/
theorem residualCodes_primrec :
    Primrec (residualCodes : ResidualInput n →
      PolynomialCode (dimension n) ×
        PolynomialCode (dimension n)) := by
  exact
    Primrec.pair residualReCode_primrec
      residualImCode_primrec

theorem residualCodes_computable :
    Computable (residualCodes : ResidualInput n →
      PolynomialCode (dimension n) ×
        PolynomialCode (dimension n)) :=
  residualCodes_primrec.to_comp

end HGAS.ComplexReciprocalPolynomialCode
