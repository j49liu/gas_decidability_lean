import HGAS.Arithmetic.FixedDetectorMomentCode
import Mathlib.Tactic

/-!
# Degree bounds for the fixed-detector selector moments

The selector compiler exposes seven complex polynomial observables for
each arithmetic variable.  Four of them contain Laurent characters, so
their raw sparse degree depends on the input DQL table.  This file records
one executable common bound for all seven codes.

The ledger is intentionally syntactic.  It counts the unsigned exponent
energy of every character that can occur and then adds two, the degree of
the gauge-corrected theta output.  Variable transport through the linked,
gauge, reciprocal, and RHS blocks preserves total degree exactly.
-/

namespace HGAS.FixedDetectorMomentCode

open HGAS
open Modular
open Clocks.ControllerPhaseProductCharacterCode

variable {eqs vars : ℕ}

/-! ## Degree-preserving compiler operations -/

theorem rationalPair_termsDegreeLE
    (D : ℕ) (c : ℚ) :
    TermsDegreeLE D
      (rationalPair (eqs := eqs) (vars := vars) c) :=
  ⟨(PolynomialCode.termsDegreeLE_constant _).promote
      (Nat.zero_le D),
    PolynomialCode.termsDegreeLE_zero D⟩

theorem termsDegreeLE_promote
    {D E : ℕ} {p : ComplexPairCode (dimension eqs vars)}
    (hp : TermsDegreeLE D p) (hDE : D ≤ E) :
    TermsDegreeLE E p :=
  ⟨hp.1.promote hDE, hp.2.promote hDE⟩

theorem subPair_termsDegreeLE
    {D : ℕ}
    {p r : ComplexPairCode (dimension eqs vars)}
    (hp : TermsDegreeLE D p)
    (hr : TermsDegreeLE D r) :
    TermsDegreeLE D (subPair p r) :=
  ⟨PolynomialCode.termsDegreeLE_sub hp.1 hr.1,
    PolynomialCode.termsDegreeLE_sub hp.2 hr.2⟩

theorem liftLocalLinkedScalar_termsDegreeLE
    {D : ℕ} (j : Fin vars)
    {p : PolynomialCode
      (LinkedJacobiPolynomialCode.dimension +
        LinkedJacobiPolynomialCode.dimension)}
    (hp : PolynomialCode.TermsDegreeLE D p) :
    PolynomialCode.TermsDegreeLE D
      (liftLocalLinkedScalar
        (eqs := eqs) j p) := by
  unfold liftLocalLinkedScalar PolynomialBlockCode.right
  exact
    PolynomialCode.termsDegreeLE_injectVariables _
      (PolynomialFiniteProductCode.termsDegreeLE_lift hp)

theorem liftLocalLinkedPair_termsDegreeLE
    {D : ℕ} (j : Fin vars)
    {p : ComplexPolynomialCode
      LinkedJacobiPolynomialCode.dimension}
    (hp : ComplexPolynomialCode.TermsDegreeLE D p) :
    TermsDegreeLE D
      (liftLocalLinkedPair (eqs := eqs) j p) :=
  ⟨liftLocalLinkedScalar_termsDegreeLE j hp.1,
    liftLocalLinkedScalar_termsDegreeLE j hp.2⟩

theorem liftLinkedPair_termsDegreeLE
    {D : ℕ}
    {p : ComplexPairCode
      (ControllerProductLinkedJacobiFamilyPolynomialCode.dimension
        (clockCount eqs vars) vars)}
    (hp : TermsDegreeLE D p) :
    TermsDegreeLE D (liftLinkedPair p) :=
  ⟨FixedDetectorValidityEnergyCode.liftLinkedScalar_termsDegreeLE hp.1,
    FixedDetectorValidityEnergyCode.liftLinkedScalar_termsDegreeLE hp.2⟩

theorem linkedCoordinatePair_termsDegreeLE
    {D : ℕ} (j : Fin vars)
    {p : ComplexPolynomialCode
      LinkedJacobiPolynomialCode.dimension}
    (hp : ComplexPolynomialCode.TermsDegreeLE D p) :
    TermsDegreeLE D
      (linkedCoordinatePair (eqs := eqs) j p) :=
  liftLinkedPair_termsDegreeLE
    (liftLocalLinkedPair_termsDegreeLE j hp)

theorem controllerCharacterPair_termsDegreeLE
    (exponents : Fin (clockCount eqs vars) → ℤ) :
    TermsDegreeLE (exponentEnergy exponents)
      (controllerCharacterPair
        (eqs := eqs) (vars := vars) exponents) := by
  have h := characterCode_termsDegreeLE exponents
  unfold controllerCharacterPair
    FixedDetectorPolynomialCode.liftBasePair
    DetectorPoissonReciprocalCode.liftGaugeBasePair
    DetectorPoissonReciprocalCode.liftControllerPair
    Modular.ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.liftControllerPair
  constructor
  · exact
      Clocks.RHSOscillatorPolynomialCode.liftBase_termsDegreeLE
        (ComplexReciprocalFamilyPolynomialCode.liftBase_termsDegreeLE
          (ComplexGaugeFamilyPolynomialCode.liftBase_termsDegreeLE
            (PolynomialCode.termsDegreeLE_injectVariables _ h.1)))
  · exact
      Clocks.RHSOscillatorPolynomialCode.liftBase_termsDegreeLE
        (ComplexReciprocalFamilyPolynomialCode.liftBase_termsDegreeLE
          (ComplexGaugeFamilyPolynomialCode.liftBase_termsDegreeLE
            (PolynomialCode.termsDegreeLE_injectVariables _ h.2)))

theorem thetaOutputPair_termsDegreeLE
    (j : Fin vars) :
    TermsDegreeLE 2
      (thetaOutputPair (eqs := eqs) j) := by
  have h :=
    FixedDetectorPolynomialCode.thetaOutputCode_termsDegreeLE
      (eqs := eqs) j
  unfold thetaOutputPair
    FixedDetectorPolynomialCode.liftBasePair
    DetectorPoissonReciprocalCode.liftGaugeBasePair
  exact
    ⟨Clocks.RHSOscillatorPolynomialCode.liftBase_termsDegreeLE
        (ComplexReciprocalFamilyPolynomialCode.liftBase_termsDegreeLE h.1),
      Clocks.RHSOscillatorPolynomialCode.liftBase_termsDegreeLE
        (ComplexReciprocalFamilyPolynomialCode.liftBase_termsDegreeLE h.2)⟩

theorem YPair_termsDegreeLE
    (j : Fin vars) :
    TermsDegreeLE 1 (YPair (eqs := eqs) j) := by
  exact
    linkedCoordinatePair_termsDegreeLE j
      (ComplexPolynomialCode.termsDegreeLE_var _)

theorem p2Pair_termsDegreeLE
    (j : Fin vars) :
    TermsDegreeLE 1 (p2Pair (eqs := eqs) j) := by
  exact
    linkedCoordinatePair_termsDegreeLE j
      (ComplexPolynomialCode.termsDegreeLE_var _)

theorem p4Pair_termsDegreeLE
    (j : Fin vars) :
    TermsDegreeLE 1 (p4Pair (eqs := eqs) j) := by
  exact
    linkedCoordinatePair_termsDegreeLE j
      (ComplexPolynomialCode.termsDegreeLE_var _)

/-! ## One executable common ledger -/

/-- Sum, over all variables, of the exponent energies of the four
characters that occur in selector moments. -/
def momentCharacterEnergySum
    (I : DQLSystem eqs vars) : ℕ :=
  ∑ j : Fin vars,
    (exponentEnergy (unaryFirstHarmonicExponent (eqs := eqs) j) +
      exponentEnergy (rootHalfExponent (eqs := eqs) j) +
      exponentEnergy (jacobiPlusExponent I j) +
      exponentEnergy (jacobiMinusExponent I j))

/-- A common raw total-degree bound for every real coordinate of every
selector moment. -/
def momentDegree
    (I : DQLSystem eqs vars) : ℕ :=
  momentCharacterEnergySum I + 2

private theorem unaryFirst_energy_le_sum
    (I : DQLSystem eqs vars) (j : Fin vars) :
    exponentEnergy (unaryFirstHarmonicExponent (eqs := eqs) j) ≤
      momentCharacterEnergySum I := by
  unfold momentCharacterEnergySum
  apply le_trans
    (show
      exponentEnergy (unaryFirstHarmonicExponent (eqs := eqs) j) ≤
        exponentEnergy (unaryFirstHarmonicExponent (eqs := eqs) j) +
        exponentEnergy (rootHalfExponent (eqs := eqs) j) +
        exponentEnergy (jacobiPlusExponent I j) +
        exponentEnergy (jacobiMinusExponent I j) by omega)
  exact
    Finset.single_le_sum
      (fun i _ => Nat.zero_le
        (exponentEnergy
            (unaryFirstHarmonicExponent (eqs := eqs) i) +
          exponentEnergy (rootHalfExponent (eqs := eqs) i) +
          exponentEnergy (jacobiPlusExponent I i) +
          exponentEnergy (jacobiMinusExponent I i)))
      (Finset.mem_univ j)

private theorem rootHalf_energy_le_sum
    (I : DQLSystem eqs vars) (j : Fin vars) :
    exponentEnergy (rootHalfExponent (eqs := eqs) j) ≤
      momentCharacterEnergySum I := by
  unfold momentCharacterEnergySum
  apply le_trans
    (show
      exponentEnergy (rootHalfExponent (eqs := eqs) j) ≤
        exponentEnergy (unaryFirstHarmonicExponent (eqs := eqs) j) +
        exponentEnergy (rootHalfExponent (eqs := eqs) j) +
        exponentEnergy (jacobiPlusExponent I j) +
        exponentEnergy (jacobiMinusExponent I j) by omega)
  exact
    Finset.single_le_sum
      (fun i _ => Nat.zero_le
        (exponentEnergy
            (unaryFirstHarmonicExponent (eqs := eqs) i) +
          exponentEnergy (rootHalfExponent (eqs := eqs) i) +
          exponentEnergy (jacobiPlusExponent I i) +
          exponentEnergy (jacobiMinusExponent I i)))
      (Finset.mem_univ j)

private theorem jacobiPlus_energy_le_sum
    (I : DQLSystem eqs vars) (j : Fin vars) :
    exponentEnergy (jacobiPlusExponent I j) ≤
      momentCharacterEnergySum I := by
  unfold momentCharacterEnergySum
  apply le_trans
    (show
      exponentEnergy (jacobiPlusExponent I j) ≤
        exponentEnergy (unaryFirstHarmonicExponent (eqs := eqs) j) +
        exponentEnergy (rootHalfExponent (eqs := eqs) j) +
        exponentEnergy (jacobiPlusExponent I j) +
        exponentEnergy (jacobiMinusExponent I j) by omega)
  exact
    Finset.single_le_sum
      (fun i _ => Nat.zero_le
        (exponentEnergy
            (unaryFirstHarmonicExponent (eqs := eqs) i) +
          exponentEnergy (rootHalfExponent (eqs := eqs) i) +
          exponentEnergy (jacobiPlusExponent I i) +
          exponentEnergy (jacobiMinusExponent I i)))
      (Finset.mem_univ j)

private theorem jacobiMinus_energy_le_sum
    (I : DQLSystem eqs vars) (j : Fin vars) :
    exponentEnergy (jacobiMinusExponent I j) ≤
      momentCharacterEnergySum I := by
  unfold momentCharacterEnergySum
  apply le_trans
    (show
      exponentEnergy (jacobiMinusExponent I j) ≤
        exponentEnergy (unaryFirstHarmonicExponent (eqs := eqs) j) +
        exponentEnergy (rootHalfExponent (eqs := eqs) j) +
        exponentEnergy (jacobiPlusExponent I j) +
        exponentEnergy (jacobiMinusExponent I j) by omega)
  exact
    Finset.single_le_sum
      (fun i _ => Nat.zero_le
        (exponentEnergy
            (unaryFirstHarmonicExponent (eqs := eqs) i) +
          exponentEnergy (rootHalfExponent (eqs := eqs) i) +
          exponentEnergy (jacobiPlusExponent I i) +
          exponentEnergy (jacobiMinusExponent I i)))
      (Finset.mem_univ j)

/-! ## The seven named moment bounds -/

theorem unaryMeanCode_termsDegreeLE
    (I : DQLSystem eqs vars) (j : Fin vars) :
    TermsDegreeLE (momentDegree I)
      (unaryMeanCode (eqs := eqs) j) := by
  have h :=
    subPair_termsDegreeLE
      (YPair_termsDegreeLE (eqs := eqs) j)
      (rationalPair_termsDegreeLE (eqs := eqs) (vars := vars) 1 1)
  exact termsDegreeLE_promote h (by unfold momentDegree; omega)

theorem unaryFirstHarmonicCode_termsDegreeLE
    (I : DQLSystem eqs vars) (j : Fin vars) :
    TermsDegreeLE (momentDegree I)
      (unaryFirstHarmonicCode (eqs := eqs) j) := by
  have hproduct :=
    termsDegreeLE_mul
      (YPair_termsDegreeLE (eqs := eqs) j)
      (controllerCharacterPair_termsDegreeLE
        (unaryFirstHarmonicExponent (eqs := eqs) j))
  have h :=
    subPair_termsDegreeLE hproduct
      (rationalPair_termsDegreeLE
        (eqs := eqs) (vars := vars)
        (1 + exponentEnergy
          (unaryFirstHarmonicExponent (eqs := eqs) j))
        (1 / 128))
  exact termsDegreeLE_promote h (by
    unfold momentDegree
    have := unaryFirst_energy_le_sum I j
    omega)

theorem rootP4MeanCode_termsDegreeLE
    (I : DQLSystem eqs vars) (j : Fin vars) :
    TermsDegreeLE (momentDegree I)
      (rootP4MeanCode (eqs := eqs) j) := by
  have h :=
    subPair_termsDegreeLE
      (p4Pair_termsDegreeLE (eqs := eqs) j)
      (rationalPair_termsDegreeLE (eqs := eqs) (vars := vars) 1 1)
  exact termsDegreeLE_promote h (by unfold momentDegree; omega)

theorem rootP2MeanCode_termsDegreeLE
    (I : DQLSystem eqs vars) (j : Fin vars) :
    TermsDegreeLE (momentDegree I)
      (rootP2MeanCode (eqs := eqs) j) := by
  have hproduct :=
    termsDegreeLE_mul
      (p2Pair_termsDegreeLE (eqs := eqs) j)
      (controllerCharacterPair_termsDegreeLE
        (rootHalfExponent (eqs := eqs) j))
  have h :=
    subPair_termsDegreeLE hproduct
      (rationalPair_termsDegreeLE
        (eqs := eqs) (vars := vars)
        (1 + exponentEnergy (rootHalfExponent (eqs := eqs) j))
        (1 / 4))
  exact termsDegreeLE_promote h (by
    unfold momentDegree
    have := rootHalf_energy_le_sum I j
    omega)

theorem jacobiMeanCode_termsDegreeLE
    (I : DQLSystem eqs vars) (j : Fin vars) :
    TermsDegreeLE (momentDegree I)
      (jacobiMeanCode (eqs := eqs) j) := by
  have h :=
    subPair_termsDegreeLE
      (thetaOutputPair_termsDegreeLE (eqs := eqs) j)
      (rationalPair_termsDegreeLE (eqs := eqs) (vars := vars) 2 1)
  exact termsDegreeLE_promote h (by unfold momentDegree; omega)

theorem jacobiPlusMeanCode_termsDegreeLE
    (I : DQLSystem eqs vars) (j : Fin vars) :
    TermsDegreeLE (momentDegree I)
      (jacobiPlusMeanCode I j) := by
  have hproduct :=
    termsDegreeLE_mul
      (thetaOutputPair_termsDegreeLE (eqs := eqs) j)
      (controllerCharacterPair_termsDegreeLE
        (jacobiPlusExponent I j))
  have h :=
    subPair_termsDegreeLE hproduct
      (rationalPair_termsDegreeLE
        (eqs := eqs) (vars := vars)
        (2 + exponentEnergy (jacobiPlusExponent I j))
        (1 / 256))
  exact termsDegreeLE_promote h (by
    unfold momentDegree
    have := jacobiPlus_energy_le_sum I j
    omega)

theorem jacobiMinusMeanCode_termsDegreeLE
    (I : DQLSystem eqs vars) (j : Fin vars) :
    TermsDegreeLE (momentDegree I)
      (jacobiMinusMeanCode I j) := by
  have hproduct :=
    termsDegreeLE_mul
      (thetaOutputPair_termsDegreeLE (eqs := eqs) j)
      (controllerCharacterPair_termsDegreeLE
        (jacobiMinusExponent I j))
  have h :=
    subPair_termsDegreeLE hproduct
      (rationalPair_termsDegreeLE
        (eqs := eqs) (vars := vars)
        (2 + exponentEnergy (jacobiMinusExponent I j))
        (1 / 256))
  exact termsDegreeLE_promote h (by
    unfold momentDegree
    have := jacobiMinus_energy_le_sum I j
    omega)

/-- The common bound holds for all seven moments of one variable. -/
theorem localMomentCode_termsDegreeLE
    (I : DQLSystem eqs vars) (j : Fin vars)
    (m : Fin localMomentCount) :
    TermsDegreeLE (momentDegree I)
      (localMomentCode I j m) := by
  fin_cases m
  · exact unaryMeanCode_termsDegreeLE I j
  · exact unaryFirstHarmonicCode_termsDegreeLE I j
  · exact rootP4MeanCode_termsDegreeLE I j
  · exact rootP2MeanCode_termsDegreeLE I j
  · exact jacobiMeanCode_termsDegreeLE I j
  · exact jacobiPlusMeanCode_termsDegreeLE I j
  · exact jacobiMinusMeanCode_termsDegreeLE I j

/-- Uniform complex-pair bound for the flattened moment family. -/
theorem momentCode_termsDegreeLE
    (I : DQLSystem eqs vars)
    (k : Fin (momentCount vars)) :
    TermsDegreeLE (momentDegree I)
      (momentCode I k) := by
  exact
    localMomentCode_termsDegreeLE I
      (finProdFinEquiv.symm k).1
      (finProdFinEquiv.symm k).2

/-- Uniform real-coordinate bound after flattening real and imaginary
parts in adjacent coordinates. -/
theorem scalarMomentCode_termsDegreeLE
    (I : DQLSystem eqs vars)
    (k : Fin (scalarMomentCount vars)) :
    PolynomialCode.TermsDegreeLE (momentDegree I)
      (scalarMomentCode I k) := by
  let mc := finProdFinEquiv.symm k
  have h := momentCode_termsDegreeLE I mc.1
  change
    PolynomialCode.TermsDegreeLE (momentDegree I)
      (![(momentCode I mc.1).1,
        (momentCode I mc.1).2] mc.2)
  have hk : mc.2 = 0 ∨ mc.2 = 1 := by omega
  rcases hk with hzero | hone
  · rw [hzero]
    exact h.1
  · rw [hone]
    exact h.2

end HGAS.FixedDetectorMomentCode
