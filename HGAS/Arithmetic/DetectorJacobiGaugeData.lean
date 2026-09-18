import HGAS.Arithmetic.DetectorCharacterCode
import HGAS.Modular.ControllerProductLinkedJacobiGaugeFamilyPolynomialCode
import Mathlib.Tactic

/-!
# DQL detector data for the gauge-completed Jacobi compiler

For detector variable `j`, the Jacobi block is driven by the two torus
characters

```text
                         Qⱼ,  Vⱼ.
```

The fourth-root gauge must therefore be linked to

```text
                         Qⱼ Vⱼ².
```

This file records its integral exponent vector and proves the crucial
frequency identity

```text
              freq(QⱼVⱼ²) = freq(Qⱼ) + 2 freq(Vⱼ).
```

Consequently the generic gauge equation uses exactly the logarithmic
derivative required by the manuscript:

```text
             Gⱼ' = (i/4)(ωⱼ + 2Nⱼ)Gⱼ.
```

The final definitions instantiate the complete common-controller,
linked-Jacobi, and gauge compiler directly from a DQL system.
-/

namespace HGAS.DetectorJacobiGaugeData

open HGAS.Clocks
open HGAS.Clocks.ControllerPhaseProductCharacterCode
open HGAS.Modular

variable {eqs vars : ℕ}

/-- Character of the fourth power of the `j`th theta gauge. -/
def gaugeCharacter
    (I : DQLSystem eqs vars) (j : Fin vars) :
    DetectorPhase eqs vars → ℤ :=
  fun phase ↦
    DetectorCharacterCode.privateCharacter j phase +
      2 * DetectorCharacterCode.linearCharacter I j phase

/-- Flattened exponent vector accepted by the common clock compiler. -/
def gaugeExponents
    (I : DQLSystem eqs vars) (j : Fin vars) :
    Fin (DetectorCharacterCode.clockCount eqs vars) → ℤ :=
  DetectorCharacterCode.flattenCharacter
    (gaugeCharacter I j)

@[simp]
theorem gaugeExponents_apply
    (I : DQLSystem eqs vars) (j : Fin vars)
    (i : Fin (DetectorCharacterCode.clockCount eqs vars)) :
    gaugeExponents I j i =
      DetectorCharacterCode.flattenCharacter
          (DetectorCharacterCode.privateCharacter j) i +
        2 *
          DetectorCharacterCode.flattenCharacter
            (DetectorCharacterCode.linearCharacter I j) i :=
  by
    simp [gaugeExponents, gaugeCharacter,
      DetectorCharacterCode.flattenCharacter]
    ring

/-- The exact frequency identity behind the gauge coefficient. -/
theorem gaugeFrequencyValue_eq_private_add_two_linear
    (parameters :
      Fin (DetectorCharacterCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (j : Fin vars)
    (z :
      ControllerPhaseProductPolynomialCode.StateFamily
        (DetectorCharacterCode.clockCount eqs vars) ℝ) :
    frequencyValue parameters (gaugeExponents I j) z =
      ControllerPhaseProductLinearFrequencyCode.value
          (fun i ↦
            (RationalCode.decode
              (DetectorCharacterCode.omegaWeights
                (eqs := eqs) j i) : ℝ))
          (fun i ↦
            (RationalCode.decode (parameters i) : ℝ)) z +
        2 *
          ControllerPhaseProductLinearFrequencyCode.value
            (fun i ↦
              (RationalCode.decode
                (DetectorCharacterCode.numberWeights I j i) : ℝ))
            (fun i ↦
              (RationalCode.decode (parameters i) : ℝ)) z := by
  simp only [frequencyValue,
    ControllerPhaseProductLinearFrequencyCode.value,
    gaugeExponents_apply,
    DetectorCharacterCode.omegaWeights,
    DetectorCharacterCode.numberWeights,
    exponentWeightCode]
  simp only [RationalCode.decode_encode, Rat.cast_intCast]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

/-- Version phrased in the semantic vocabulary of the linked-Jacobi
family compiler. -/
theorem gaugeFrequencyValue_eq_omega_add_two_number
    (parameters :
      Fin (DetectorCharacterCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (j : Fin vars)
    (z :
      ControllerProductLinkedJacobiFamilyState
        (DetectorCharacterCode.clockCount eqs vars) vars) :
    frequencyValue parameters (gaugeExponents I j)
        z.controllers =
      ControllerProductLinkedJacobiFamilyPolynomialCode.omega
          (fun a i ↦
            (RationalCode.decode
              (DetectorCharacterCode.omegaWeights
                (eqs := eqs) a i) : ℝ))
          (fun i ↦
            (RationalCode.decode (parameters i) : ℝ))
          z j +
        2 *
          ControllerProductLinkedJacobiFamilyPolynomialCode.number
            (fun a i ↦
              (RationalCode.decode
                (DetectorCharacterCode.numberWeights I a i) : ℝ))
            (fun i ↦
              (RationalCode.decode (parameters i) : ℝ))
            z j := by
  exact
    gaugeFrequencyValue_eq_private_add_two_linear
      parameters I j z.controllers

/-! ## Complete detector specialization -/

abbrev clockCount (eqs vars : ℕ) : ℕ :=
  DetectorCharacterCode.clockCount eqs vars

abbrev dimension (eqs vars : ℕ) : ℕ :=
  ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.dimension
    (clockCount eqs vars) vars

/-- Complete polynomial field for the controller, linked Jacobi, and
fourth-root gauge blocks of a DQL detector. -/
def fieldCode
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars) :
    PolynomialFieldCode (dimension eqs vars) :=
  ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.fieldCode
    parameters
    (DetectorCharacterCode.omegaWeights (eqs := eqs))
    (DetectorCharacterCode.numberWeights I)
    (gaugeExponents I)

/-- The `2*vars` real gauge residual coordinates. -/
def residualCode
    (scale : Fin vars → RationalCode)
    (I : DQLSystem eqs vars) :
    Fin (ComplexGaugeFamilyPolynomialCode.gaugeDimension vars) →
      PolynomialCode (dimension eqs vars) :=
  ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.gaugeResidualCode
    scale (gaugeExponents I)

/-- Complex pair code of the `j`th theta factor
`GⱼT₁,ⱼ = Θλ(Qⱼ,Vⱼ)`. -/
def thetaOutputCode
    (j : Fin vars) :
    ComplexPairCode (dimension eqs vars) :=
  ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.thetaOutputCode
    (q := clockCount eqs vars) j

/-- On every structured state, the detector specialization has the exact
gauge logarithmic velocity `(i/4)(ωⱼ+2Nⱼ)Gⱼ`. -/
theorem detectorGaugeVelocity_eq
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (z :
      ControllerProductLinkedJacobiGaugeFamilyState
        (clockCount eqs vars) vars)
    (j : Fin vars) :
    (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.vectorField
        parameters
        (DetectorCharacterCode.omegaWeights (eqs := eqs))
        (DetectorCharacterCode.numberWeights I)
        (gaugeExponents I) z).gauge j =
      Complex.I *
        ((ControllerProductLinkedJacobiFamilyPolynomialCode.omega
              (fun a i ↦
                (RationalCode.decode
                  (DetectorCharacterCode.omegaWeights
                    (eqs := eqs) a i) : ℝ))
              (fun i ↦
                (RationalCode.decode (parameters i) : ℝ))
              z.source j +
            2 *
              ControllerProductLinkedJacobiFamilyPolynomialCode.number
                (fun a i ↦
                  (RationalCode.decode
                    (DetectorCharacterCode.numberWeights I a i) : ℝ))
                (fun i ↦
                  (RationalCode.decode (parameters i) : ℝ))
                z.source j) / 4 : ℝ) *
          z.gauge j := by
  change
    Complex.I *
        ((frequencyValue parameters (gaugeExponents I j)
              z.source.controllers / 4 : ℝ) : ℂ) *
          z.gauge j =
      _
  rw [gaugeFrequencyValue_eq_omega_add_two_number]

end HGAS.DetectorJacobiGaugeData
