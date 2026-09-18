import HGAS.Arithmetic.FixedDetectorPolynomialCode
import HGAS.Compiler.ComplexGaugeFamilyPolynomialDegrees
import HGAS.Compiler.ComplexReciprocalFamilyPolynomialDegrees
import HGAS.Clocks.RHSOscillatorPolynomialDegrees
import HGAS.Modular.ControllerProductLinkedJacobiFamilyPolynomialDegrees
import Mathlib.Tactic

/-!
# Resource ledger for the complete fixed detector

For `eqs` DQL equations and `vars` arithmetic variables, the complete
affine detector source has exactly

```text
                     4*eqs + 38*vars + 2
```

real coordinates.  More importantly, the final observable

```text
        R * ∏ j (theta-output j) (Poisson-output j)
```

has degree at most `4*vars+1`, independently of every DQL coefficient.
The vector-field degree depends only on the exponent energy of the
quadratic Poisson characters; the right-hand side affects coefficients but
does not affect degree.
-/

namespace HGAS

open Clocks.ControllerPhaseProductCharacterCode

namespace FixedDetectorPolynomialCode

variable {eqs vars : ℕ}

/-- Exact real ambient dimension of the complete affine detector source. -/
theorem dimension_eq :
    dimension eqs vars = 4 * eqs + 38 * vars + 2 := by
  change
    ((vars + eqs) * 4 + vars * ((4 + 10) + (4 + 10)) +
          vars * 2 + vars * 2 * 2) +
        2 =
      4 * eqs + 38 * vars + 2
  omega

/-! ## Degree of the fixed observable -/

private theorem T1BaseCode_termsDegreeLE
    (a : Fin vars) :
    TermsDegreeLE 1
      (Modular.ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.T1BaseCode
        (q := DetectorCharacterCode.clockCount eqs vars) a) :=
  ⟨PolynomialCode.termsDegreeLE_varCode _,
    PolynomialCode.termsDegreeLE_varCode _⟩

theorem thetaOutputCode_termsDegreeLE
    (j : Fin vars) :
    TermsDegreeLE 2
      (DetectorJacobiGaugeData.thetaOutputCode
        (eqs := eqs) j) := by
  apply
    ComplexGaugeFamilyPolynomialCode.outputCode_termsDegreeLE
      (T := 1)
  intro a
  exact T1BaseCode_termsDegreeLE (eqs := eqs) a

theorem reciprocalPairCode_termsDegreeLE
    (k : Fin (DetectorPoissonReciprocalCode.reciprocalCount vars)) :
    TermsDegreeLE 1
      (DetectorPoissonReciprocalCode.reciprocalPairCode
        (eqs := eqs) k) :=
  ⟨PolynomialCode.termsDegreeLE_varCode _,
    PolynomialCode.termsDegreeLE_varCode _⟩

theorem poissonScaleCode_termsDegreeLE :
    TermsDegreeLE 0
      (DetectorPoissonReciprocalCode.poissonScaleCode
        (eqs := eqs) (vars := vars)) :=
  ⟨PolynomialCode.termsDegreeLE_constant _,
    PolynomialCode.termsDegreeLE_zero 0⟩

theorem poissonFactorCode_termsDegreeLE
    (j : Fin vars) :
    TermsDegreeLE 2
      (DetectorPoissonReciprocalCode.poissonFactorCode
        (eqs := eqs) j) := by
  have hproduct :
      TermsDegreeLE 2
        (mul
          (DetectorPoissonReciprocalCode.reciprocalPairCode
            (eqs := eqs)
            (DetectorPoissonReciprocalCode.positiveIndex j))
          (DetectorPoissonReciprocalCode.reciprocalPairCode
            (eqs := eqs)
            (DetectorPoissonReciprocalCode.negativeIndex j))) :=
    termsDegreeLE_mul
      (reciprocalPairCode_termsDegreeLE
        (eqs := eqs)
        (DetectorPoissonReciprocalCode.positiveIndex j))
      (reciprocalPairCode_termsDegreeLE
        (eqs := eqs)
        (DetectorPoissonReciprocalCode.negativeIndex j))
  simpa [DetectorPoissonReciprocalCode.poissonFactorCode] using
    termsDegreeLE_mul
      (poissonScaleCode_termsDegreeLE
        (eqs := eqs) (vars := vars))
      hproduct

private theorem liftGaugeBasePair_termsDegreeLE
    {D : ℕ}
    {p :
      ComplexPairCode
        (DetectorPoissonReciprocalCode.baseDimension eqs vars)}
    (hp : TermsDegreeLE D p) :
    TermsDegreeLE D
      (DetectorPoissonReciprocalCode.liftGaugeBasePair p) :=
  ⟨ComplexReciprocalFamilyPolynomialCode.liftBase_termsDegreeLE hp.1,
    ComplexReciprocalFamilyPolynomialCode.liftBase_termsDegreeLE hp.2⟩

theorem thetaFactorCode_termsDegreeLE
    (j : Fin vars) :
    TermsDegreeLE 2
      (DetectorPoissonReciprocalCode.thetaFactorCode
        (eqs := eqs) j) :=
  liftGaugeBasePair_termsDegreeLE
    (thetaOutputCode_termsDegreeLE (eqs := eqs) j)

theorem detectorFactorCode_termsDegreeLE
    (j : Fin vars) :
    TermsDegreeLE 4
      (DetectorPoissonReciprocalCode.detectorFactorCode
        (eqs := eqs) j) :=
  termsDegreeLE_mul
    (thetaFactorCode_termsDegreeLE (eqs := eqs) j)
    (poissonFactorCode_termsDegreeLE (eqs := eqs) j)

theorem detectorProductCode_termsDegreeLE :
    TermsDegreeLE (4 * vars)
      (DetectorPoissonReciprocalCode.detectorProductCode
        (eqs := eqs) (vars := vars)) := by
  let indices : List (Fin vars) :=
    List.ofFn fun j : Fin vars ↦ j
  have h :=
    product_map_termsDegreeLE indices
      (fun j ↦
        DetectorPoissonReciprocalCode.detectorFactorCode
          (eqs := eqs) j)
      (fun _ ↦ 4)
      (fun j _ ↦
        detectorFactorCode_termsDegreeLE (eqs := eqs) j)
  simpa [DetectorPoissonReciprocalCode.detectorProductCode,
    indices, List.map_ofFn, List.sum_ofFn,
    Finset.sum_const, Nat.mul_comm] using h

private theorem liftBasePair_termsDegreeLE
    {D : ℕ}
    {p :
      ComplexPairCode
        (baseDimension eqs vars)}
    (hp : TermsDegreeLE D p) :
    TermsDegreeLE D (liftBasePair p) :=
  ⟨Clocks.RHSOscillatorPolynomialCode.liftBase_termsDegreeLE hp.1,
    Clocks.RHSOscillatorPolynomialCode.liftBase_termsDegreeLE hp.2⟩

theorem rhsOscillatorCode_termsDegreeLE :
    TermsDegreeLE 1
      (rhsOscillatorCode (eqs := eqs) (vars := vars)) :=
  ⟨PolynomialCode.termsDegreeLE_varCode _,
    PolynomialCode.termsDegreeLE_varCode _⟩

/-- The complete detector observable has a coefficient-independent degree
bound `4*vars+1`. -/
theorem detectorCode_termsDegreeLE :
    TermsDegreeLE (4 * vars + 1)
      (detectorCode (eqs := eqs) (vars := vars)) := by
  simpa [detectorCode, Nat.add_comm] using
    termsDegreeLE_mul
      (rhsOscillatorCode_termsDegreeLE
        (eqs := eqs) (vars := vars))
      (liftBasePair_termsDegreeLE
        (detectorProductCode_termsDegreeLE
          (eqs := eqs) (vars := vars)))

/-! ## Degree of the graph residual families -/

/-- Sum of all Laurent exponent energies used by the fourth-root gauge
constraints.  It is an executable common bound for every individual gauge
character. -/
def gaugeExponentEnergySum
    (I : DQLSystem eqs vars) : ℕ :=
  ∑ j : Fin vars,
    exponentEnergy (DetectorJacobiGaugeData.gaugeExponents I j)

private theorem gaugeExponentEnergy_le_sum
    (I : DQLSystem eqs vars) (j : Fin vars) :
    exponentEnergy (DetectorJacobiGaugeData.gaugeExponents I j) ≤
      gaugeExponentEnergySum I := by
  unfold gaugeExponentEnergySum
  exact
    Finset.single_le_sum
      (fun i _ ↦ Nat.zero_le
        (exponentEnergy
          (DetectorJacobiGaugeData.gaugeExponents I i)))
      (Finset.mem_univ j)

private theorem gaugeCharacterBaseCode_termsDegreeLE
    (I : DQLSystem eqs vars) (j : Fin vars) :
    TermsDegreeLE (gaugeExponentEnergySum I)
      (Modular.ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.gaugeCharacterBaseCode
        (DetectorJacobiGaugeData.gaugeExponents I) j) := by
  have h :=
    characterCode_termsDegreeLE
      (DetectorJacobiGaugeData.gaugeExponents I j)
  have hp :
      TermsDegreeLE (gaugeExponentEnergySum I)
        (characterCode
          (DetectorJacobiGaugeData.gaugeExponents I j)) :=
    ⟨h.1.promote (gaugeExponentEnergy_le_sum I j),
      h.2.promote (gaugeExponentEnergy_le_sum I j)⟩
  exact
    ⟨PolynomialCode.termsDegreeLE_injectVariables _ hp.1,
      PolynomialCode.termsDegreeLE_injectVariables _ hp.2⟩

/-- Every real coordinate of the specialized fourth-root gauge residual
family has degree at most
`max 4 (gaugeExponentEnergySum I)`. -/
theorem gaugeResidualCode_termsDegreeLE
    (scale : Fin vars → RationalCode)
    (I : DQLSystem eqs vars) :
    ∀ k,
      PolynomialCode.TermsDegreeLE
        (max 4 (gaugeExponentEnergySum I))
        (DetectorJacobiGaugeData.residualCode scale I k) := by
  exact
    ComplexGaugeFamilyPolynomialCode.residualCode_termsDegreeLE
      scale
      (Modular.ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.gaugeCharacterBaseCode
        (DetectorJacobiGaugeData.gaugeExponents I))
      (gaugeCharacterBaseCode_termsDegreeLE I)

/-! ## Data-dependent field degree -/

/-- Sum of the Laurent exponent energies of all `W` and `W⁻¹`
characters.  Every individual reciprocal character energy is bounded by
this one executable number. -/
def reciprocalExponentEnergySum
    (I : DQLSystem eqs vars) : ℕ :=
  ∑ k : Fin (DetectorPoissonReciprocalCode.reciprocalCount vars),
    exponentEnergy
      (DetectorPoissonReciprocalCode.reciprocalExponent I k)

def fieldDegree (I : DQLSystem eqs vars) : ℕ :=
  max 9 (reciprocalExponentEnergySum I + 3)

private theorem reciprocalExponentEnergy_le_sum
    (I : DQLSystem eqs vars)
    (k : Fin (DetectorPoissonReciprocalCode.reciprocalCount vars)) :
    exponentEnergy
        (DetectorPoissonReciprocalCode.reciprocalExponent I k) ≤
      reciprocalExponentEnergySum I := by
  unfold reciprocalExponentEnergySum
  exact
    Finset.single_le_sum
      (fun i _ ↦ Nat.zero_le
        (exponentEnergy
          (DetectorPoissonReciprocalCode.reciprocalExponent I i)))
      (Finset.mem_univ k)

private theorem reciprocalCharacterBaseCode_termsDegreeLE
    (I : DQLSystem eqs vars)
    (k : Fin (DetectorPoissonReciprocalCode.reciprocalCount vars)) :
    TermsDegreeLE (reciprocalExponentEnergySum I)
      (DetectorPoissonReciprocalCode.characterBaseCode I k) := by
  have h :=
    characterCode_termsDegreeLE
      (DetectorPoissonReciprocalCode.reciprocalExponent I k)
  have hp :
      TermsDegreeLE (reciprocalExponentEnergySum I)
        (characterCode
          (DetectorPoissonReciprocalCode.reciprocalExponent I k)) :=
    ⟨h.1.promote (reciprocalExponentEnergy_le_sum I k),
      h.2.promote (reciprocalExponentEnergy_le_sum I k)⟩
  exact
    ComplexGaugeFamilyPolynomialCode.liftBasePair_termsDegreeLE
      ⟨PolynomialCode.termsDegreeLE_injectVariables _ hp.1,
        PolynomialCode.termsDegreeLE_injectVariables _ hp.2⟩

/-- Every real coordinate of the specialized Poisson reciprocal residual
family has degree at most `reciprocalExponentEnergySum I + 1`. -/
theorem reciprocalResidualCode_termsDegreeLE
    (I : DQLSystem eqs vars) :
    ∀ k,
      PolynomialCode.TermsDegreeLE
        (reciprocalExponentEnergySum I + 1)
        (DetectorPoissonReciprocalCode.residualCode I k) := by
  exact
    ComplexReciprocalFamilyPolynomialCode.residualCode_termsDegreeLE
      DetectorPoissonReciprocalCode.etaCode
      (DetectorPoissonReciprocalCode.characterBaseCode I)
      (reciprocalCharacterBaseCode_termsDegreeLE I)

private theorem gaugeFrequencyBaseCode_termsDegreeLE
    (parameters : Fin (DetectorCharacterCode.clockCount eqs vars) →
      RationalCode)
    (gaugeExponents :
      Fin vars →
        Fin (DetectorCharacterCode.clockCount eqs vars) → ℤ)
    (a : Fin vars) :
    PolynomialCode.TermsDegreeLE 1
      (Modular.ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.gaugeFrequencyBaseCode
        parameters gaugeExponents a) := by
  exact
    PolynomialCode.termsDegreeLE_injectVariables _
      (frequencyCode_termsDegreeLE parameters (gaugeExponents a))

theorem gaugeBaseFieldCode_termsDegreeLE
    (parameters : Fin (DetectorCharacterCode.clockCount eqs vars) →
      RationalCode)
    (I : DQLSystem eqs vars) :
    ∀ i, PolynomialCode.TermsDegreeLE 9
      (DetectorJacobiGaugeData.fieldCode parameters I i) := by
  have h :=
    ComplexGaugeFamilyPolynomialCode.fieldCode_termsDegreeLE
      (D := 9) (E := 1)
      (Modular.ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode
        parameters
        (DetectorCharacterCode.omegaWeights (eqs := eqs))
        (DetectorCharacterCode.numberWeights I))
      (Modular.ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.gaugeFrequencyBaseCode
        parameters (DetectorJacobiGaugeData.gaugeExponents I))
      (Modular.ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode_termsDegreeLE
        _ _ _)
      (gaugeFrequencyBaseCode_termsDegreeLE
        parameters (DetectorJacobiGaugeData.gaugeExponents I))
  simpa [DetectorJacobiGaugeData.fieldCode,
    Modular.ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.fieldCode]
    using h

private theorem derivativeBaseCode_termsDegreeLE
    (parameters : Fin (DetectorCharacterCode.clockCount eqs vars) →
      RationalCode)
    (I : DQLSystem eqs vars)
    (k : Fin (DetectorPoissonReciprocalCode.reciprocalCount vars)) :
    TermsDegreeLE (reciprocalExponentEnergySum I + 1)
      (DetectorPoissonReciprocalCode.derivativeBaseCode
        parameters I k) := by
  have h :=
    derivativeCode_termsDegreeLE parameters
      (DetectorPoissonReciprocalCode.reciprocalExponent I k)
  have hpromoted :
      TermsDegreeLE (reciprocalExponentEnergySum I + 1)
        (derivativeCode parameters
          (DetectorPoissonReciprocalCode.reciprocalExponent I k)) :=
    ⟨h.1.promote
        (Nat.add_le_add_right
          (reciprocalExponentEnergy_le_sum I k) 1),
      h.2.promote
        (Nat.add_le_add_right
          (reciprocalExponentEnergy_le_sum I k) 1)⟩
  exact
    ComplexGaugeFamilyPolynomialCode.liftBasePair_termsDegreeLE
      (D := reciprocalExponentEnergySum I + 1)
      (p :=
        Modular.ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.liftControllerPair
          (derivativeCode parameters
            (DetectorPoissonReciprocalCode.reciprocalExponent I k)))
      ⟨PolynomialCode.termsDegreeLE_injectVariables _ hpromoted.1,
        PolynomialCode.termsDegreeLE_injectVariables _ hpromoted.2⟩

theorem poissonBaseFieldCode_termsDegreeLE
    (parameters : Fin (DetectorCharacterCode.clockCount eqs vars) →
      RationalCode)
    (I : DQLSystem eqs vars) :
    ∀ i,
      PolynomialCode.TermsDegreeLE (fieldDegree I)
        (DetectorPoissonReciprocalCode.fieldCode parameters I i) := by
  simpa [fieldDegree, Nat.add_assoc] using
    (ComplexReciprocalFamilyPolynomialCode.fieldCode_termsDegreeLE
      (D := 9)
      (E := reciprocalExponentEnergySum I + 1)
      (DetectorJacobiGaugeData.fieldCode parameters I)
      DetectorPoissonReciprocalCode.etaCode
      (DetectorPoissonReciprocalCode.derivativeBaseCode parameters I)
      (gaugeBaseFieldCode_termsDegreeLE parameters I)
      (fun k ↦ derivativeBaseCode_termsDegreeLE parameters I k))

private theorem equationFrequencyCode_termsDegreeLE
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (row : Fin eqs) :
    PolynomialCode.TermsDegreeLE 1
      (equationFrequencyCode parameters row) := by
  exact
    ComplexReciprocalFamilyPolynomialCode.liftBase_termsDegreeLE
      (ComplexGaugeFamilyPolynomialCode.liftBase_termsDegreeLE
        (PolynomialCode.termsDegreeLE_injectVariables _
          (frequencyCode_termsDegreeLE parameters
            (equationBasisExponent row))))

/-- Complete field degree bound.  The right-hand side changes oscillator
coefficients only, so it does not enter `fieldDegree`. -/
theorem fieldCode_termsDegreeLE
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars) :
    ∀ i, PolynomialCode.TermsDegreeLE (fieldDegree I)
      (fieldCode parameters I i) := by
  apply Clocks.RHSOscillatorPolynomialCode.fieldCode_termsDegreeLE
  · exact poissonBaseFieldCode_termsDegreeLE parameters I
  · exact equationFrequencyCode_termsDegreeLE parameters
  · unfold fieldDegree
    omega

end FixedDetectorPolynomialCode

end HGAS
