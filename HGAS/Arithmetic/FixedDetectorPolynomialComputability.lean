import HGAS.Arithmetic.DetectorPoissonReciprocalComputability
import HGAS.Arithmetic.FixedDetectorPolynomialCode
import HGAS.Clocks.RHSOscillatorPolynomialComputability
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Effectivity of the complete fixed-degree DQL detector

For fixed finite numbers of equations and variables, the full affine
detector is compiled from

```text
  (controller parameters, DQL coefficient table).
```

The Poisson-reciprocal source is already effective.  The remaining
right-hand-side oscillator uses each DQL right-hand side only as a rational
coefficient and uses a fixed unit exponent for each fundamental equation
clock.  Composing those compiler maps proves primitive-recursiveness of the
complete field.

The final observable is a fixed sparse-polynomial expression in the state:
the input-dependent right-hand-side exponents occur only in oscillator
coefficients, never in the observable syntax.  We therefore also expose a
single primitive-recursive compiler returning the field and detector code
together.
-/

namespace HGAS.FixedDetectorPolynomialCode

open HGAS.Clocks
open HGAS.Clocks.ControllerPhaseProductCharacterCode
open HGAS.Modular

variable {eqs vars : ℕ}

/-- Runtime input for the complete fixed-degree detector compiler. -/
abbrev CompilerInput (eqs vars : ℕ) :=
  DetectorPoissonReciprocalCode.CompilerInput eqs vars

/-! ## Effective equation-clock frequency family -/

/-- Lifting a scalar controller polynomial through the linked-Jacobi,
gauge, and reciprocal blocks is primitive recursive. -/
theorem liftControllerScalar_primrec :
    Primrec
      (liftControllerScalar (eqs := eqs) (vars := vars) :
        PolynomialCode
            (ControllerProductLinkedJacobiFamilyPolynomialCode.controllerDimension
              (clockCount eqs vars)) →
          PolynomialCode (baseDimension eqs vars)) := by
  exact
    (ComplexReciprocalFamilyPolynomialCode.liftBase_primrec.comp
      (ComplexGaugeFamilyPolynomialCode.liftBase_primrec.comp
        ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.liftController_primrec)).of_eq
      (fun _ ↦ rfl)

private theorem equationFrequencyInput_primrec (row : Fin eqs) :
    Primrec
      (fun parameters : Fin (clockCount eqs vars) → RationalCode ↦
        (parameters, equationBasisExponent (vars := vars) row)) :=
  Primrec.pair Primrec.id
    (Primrec.const (equationBasisExponent (vars := vars) row))

set_option maxHeartbeats 1200000 in
-- The common frequency compiler traverses the fixed finite parameter tuple.
/-- The polynomial frequency of one fundamental equation clock is
primitive recursive in the controller parameter tuple. -/
theorem equationFrequencyCode_primrec (row : Fin eqs) :
    Primrec
      (fun parameters : Fin (clockCount eqs vars) → RationalCode ↦
        equationFrequencyCode parameters row) := by
  exact
    (liftControllerScalar_primrec.comp
      (frequencyCode_primrec.comp
        (equationFrequencyInput_primrec row))).of_eq
      (fun _ ↦ rfl)

/-- Compile all fundamental equation-clock frequencies simultaneously. -/
theorem equationFrequencyCodeFamily_primrec :
    Primrec
      (fun parameters : Fin (clockCount eqs vars) → RationalCode ↦
        fun row ↦ equationFrequencyCode parameters row) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro row
  exact equationFrequencyCode_primrec row

/-! ## Effective right-hand-side coefficient family -/

/-- A fixed DQL right-hand-side entry, embedded as a denominator-one
rational code, is primitive recursive. -/
theorem rhsWeightCode_primrec (row : Fin eqs) :
    Primrec
      (fun I : DQLSystem eqs vars ↦ rhsWeightCode I row) := by
  exact
    (exponentWeightCode_primrec.comp
      (DetectorCharacterCode.rhsEntry_primrec row)).of_eq
      (fun _ ↦ rfl)

/-- Compile the complete rational RHS coefficient tuple. -/
theorem rhsWeightCodeFamily_primrec :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        fun row ↦ rhsWeightCode I row) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro row
  exact rhsWeightCode_primrec row

/-! ## Complete field and fixed-degree observable -/

private theorem genericFieldInput_primrec :
    Primrec
      (fun input : CompilerInput eqs vars ↦
        (DetectorPoissonReciprocalCode.fieldCode input.1 input.2,
          (rhsWeightCode input.2,
            fun row ↦ equationFrequencyCode input.1 row))) :=
  Primrec.pair
    DetectorPoissonReciprocalCode.fieldCode_primrec
    (Primrec.pair
      (rhsWeightCodeFamily_primrec.comp Primrec.snd)
      (equationFrequencyCodeFamily_primrec.comp Primrec.fst))

set_option maxHeartbeats 1600000 in
-- This final composition joins the already compiled reciprocal source to
-- one two-coordinate RHS oscillator.
/-- The complete fixed-detector vector-field compiler is primitive
recursive in `(parameters, I)`. -/
theorem fieldCode_primrec :
    Primrec
      (fun input : CompilerInput eqs vars ↦
        fieldCode input.1 input.2) := by
  exact
    (RHSOscillatorPolynomialCode.fieldCode_primrec.comp
      genericFieldInput_primrec).of_eq
      (fun _ ↦ rfl)

theorem fieldCode_computable :
    Computable
      (fun input : CompilerInput eqs vars ↦
        fieldCode input.1 input.2) :=
  fieldCode_primrec.to_comp

/-- The complete detector observable has no runtime coefficient: all DQL
dependence is carried by the vector field and the resulting oscillator
trajectory. -/
theorem detectorCode_primrec :
    Primrec
      (fun _ : CompilerInput eqs vars ↦
        detectorCode (eqs := eqs) (vars := vars)) :=
  Primrec.const _

theorem detectorCode_computable :
    Computable
      (fun _ : CompilerInput eqs vars ↦
        detectorCode (eqs := eqs) (vars := vars)) :=
  detectorCode_primrec.to_comp

/-- The executable end-to-end compiler returns the full rational
polynomial field and its fixed-degree complex detector code. -/
theorem fieldAndDetectorCode_primrec :
    Primrec
      (fun input : CompilerInput eqs vars ↦
        (fieldCode input.1 input.2,
          detectorCode (eqs := eqs) (vars := vars))) :=
  Primrec.pair fieldCode_primrec detectorCode_primrec

theorem fieldAndDetectorCode_computable :
    Computable
      (fun input : CompilerInput eqs vars ↦
        (fieldCode input.1 input.2,
          detectorCode (eqs := eqs) (vars := vars))) :=
  fieldAndDetectorCode_primrec.to_comp

end HGAS.FixedDetectorPolynomialCode
