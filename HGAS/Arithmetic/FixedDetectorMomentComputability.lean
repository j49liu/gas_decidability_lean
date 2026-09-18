import HGAS.Arithmetic.FixedDetectorMomentCode
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Effective compilation of fixed-detector selector moments

For fixed finite numbers of equations and variables, the seven selector
moments are literal finite sparse-polynomial syntax.  Five are independent
of the DQL table.  The remaining two use only pointwise integer addition
and negation applied to the already effective flattened linear character.

This file proves that the complete complex moment family and its adjacent
real/imaginary flattening are primitive recursive in the finite DQL table.
The intermediate lifting and pair-operation lemmas are exposed for reuse
by later selector and compactification compilers.
-/

namespace HGAS.FixedDetectorMomentCode

open HGAS
open Modular
open Clocks.ControllerPhaseProductCharacterCode

variable {eqs vars : ℕ}

/-! ## Reusable primitive-recursive pair operations and lifts -/

theorem subPair_primrec :
    Primrec₂
      (subPair (eqs := eqs) (vars := vars) :
        ComplexPairCode (dimension eqs vars) →
          ComplexPairCode (dimension eqs vars) →
            ComplexPairCode (dimension eqs vars)) :=
  Primrec.pair
    (PolynomialCode.sub_primrec.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd))
    (PolynomialCode.sub_primrec.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd))

theorem liftLocalLinkedScalar_primrec
    (j : Fin vars) :
    Primrec
      (liftLocalLinkedScalar (eqs := eqs) j :
        PolynomialCode
            (LinkedJacobiPolynomialCode.dimension +
              LinkedJacobiPolynomialCode.dimension) →
          PolynomialCode
            (ControllerProductLinkedJacobiFamilyPolynomialCode.dimension
              (clockCount eqs vars) vars)) := by
  exact
    (PolynomialBlockCode.right_primrec.comp
      (PolynomialFiniteProductCode.lift_primrec j)).of_eq
      (fun _ => rfl)

theorem liftLocalLinkedPair_primrec
    (j : Fin vars) :
    Primrec
      (liftLocalLinkedPair (eqs := eqs) j :
        ComplexPolynomialCode LinkedJacobiPolynomialCode.dimension →
          ComplexPairCode
            (ControllerProductLinkedJacobiFamilyPolynomialCode.dimension
              (clockCount eqs vars) vars)) :=
  Primrec.pair
    (liftLocalLinkedScalar_primrec j |>.comp Primrec.fst)
    (liftLocalLinkedScalar_primrec j |>.comp Primrec.snd)

theorem liftLinkedPair_primrec :
    Primrec
      (liftLinkedPair (eqs := eqs) (vars := vars) :
        ComplexPairCode
            (ControllerProductLinkedJacobiFamilyPolynomialCode.dimension
              (clockCount eqs vars) vars) →
          ComplexPairCode (dimension eqs vars)) :=
  Primrec.pair
    (FixedDetectorValidityEnergyCode.liftLinkedScalar_primrec.comp
      Primrec.fst)
    (FixedDetectorValidityEnergyCode.liftLinkedScalar_primrec.comp
      Primrec.snd)

theorem linkedCoordinatePair_primrec
    (j : Fin vars) :
    Primrec
      (linkedCoordinatePair (eqs := eqs) j :
        ComplexPolynomialCode LinkedJacobiPolynomialCode.dimension →
          ComplexPairCode (dimension eqs vars)) :=
  liftLinkedPair_primrec.comp
    (liftLocalLinkedPair_primrec j)

/-- Lift a gauge-base pair through the reciprocal family. -/
theorem liftGaugeBasePair_primrec :
    Primrec
      (DetectorPoissonReciprocalCode.liftGaugeBasePair
        (eqs := eqs) (vars := vars) :
        ComplexPairCode
            (DetectorPoissonReciprocalCode.baseDimension eqs vars) →
          ComplexPairCode
            (DetectorPoissonReciprocalCode.dimension eqs vars)) :=
  Primrec.pair
    (ComplexReciprocalFamilyPolynomialCode.liftBase_primrec.comp
      Primrec.fst)
    (ComplexReciprocalFamilyPolynomialCode.liftBase_primrec.comp
      Primrec.snd)

/-- Lift a reciprocal-base pair through the final RHS oscillator. -/
theorem finalLiftBasePair_primrec :
    Primrec
      (FixedDetectorPolynomialCode.liftBasePair
        (eqs := eqs) (vars := vars) :
        ComplexPairCode
            (FixedDetectorPolynomialCode.baseDimension eqs vars) →
          ComplexPairCode
            (FixedDetectorPolynomialCode.dimension eqs vars)) :=
  Primrec.pair
    (Clocks.RHSOscillatorPolynomialCode.liftBase_primrec.comp
      Primrec.fst)
    (Clocks.RHSOscillatorPolynomialCode.liftBase_primrec.comp
      Primrec.snd)

/-- Compile and lift an arbitrary controller Laurent character through
all detector extensions. -/
theorem controllerCharacterPair_primrec :
    Primrec
      (controllerCharacterPair (eqs := eqs) (vars := vars) :
        (Fin (clockCount eqs vars) → ℤ) →
          ComplexPairCode (dimension eqs vars)) := by
  exact
    (finalLiftBasePair_primrec.comp
      (liftGaugeBasePair_primrec.comp
        (DetectorPoissonReciprocalCode.liftControllerPair_primrec.comp
          characterCode_primrec))).of_eq
      (fun _ => rfl)

/-- The final-layout theta-output family is primitive recursive in its
finite variable index. -/
theorem thetaOutputPair_primrec :
    Primrec
      (thetaOutputPair (eqs := eqs) :
        Fin vars →
          ComplexPairCode (dimension eqs vars)) := by
  exact
    (finalLiftBasePair_primrec.comp
      (liftGaugeBasePair_primrec.comp
        DetectorJacobiGaugeData.thetaOutputCode_primrec)).of_eq
      (fun _ => rfl)

/-! ## Effective input-dependent exponent tuples -/

theorem jacobiPlusExponent_primrec
    (j : Fin vars) :
    Primrec
      (fun I : DQLSystem eqs vars =>
        jacobiPlusExponent I j) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro i
  have hlinear :
      Primrec
        (fun I : DQLSystem eqs vars =>
          linearExponent I j i) :=
    Primrec.fin_app.comp
      (DetectorCharacterCode.flattenLinearCharacter_primrec j)
      (Primrec.const i)
  exact
    (DetectorCharacterCode.integerNeg_primrec.comp
      (DetectorCharacterCode.integerAdd_primrec.comp
        (Primrec.const
          (privateExponent (eqs := eqs) j i))
        hlinear)).of_eq
      (by
        intro I
        rfl)

theorem jacobiMinusExponent_primrec
    (j : Fin vars) :
    Primrec
      (fun I : DQLSystem eqs vars =>
        jacobiMinusExponent I j) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro i
  have hlinear :
      Primrec
        (fun I : DQLSystem eqs vars =>
          linearExponent I j i) :=
    Primrec.fin_app.comp
      (DetectorCharacterCode.flattenLinearCharacter_primrec j)
      (Primrec.const i)
  exact
    (DetectorCharacterCode.integerAdd_primrec.comp
      (Primrec.const
        (-privateExponent (eqs := eqs) j i))
      hlinear).of_eq
      (by
        intro I
        rfl)

/-! ## The two input-dependent moments -/

theorem jacobiPlusMeanCode_primrec
    (j : Fin vars) :
    Primrec
      (fun I : DQLSystem eqs vars =>
        jacobiPlusMeanCode I j) := by
  have hcharacter :
      Primrec
        (fun I : DQLSystem eqs vars =>
          controllerCharacterPair
            (eqs := eqs) (vars := vars)
            (jacobiPlusExponent I j)) :=
    (controllerCharacterPair_primrec
      (eqs := eqs) (vars := vars)).comp
      (jacobiPlusExponent_primrec (eqs := eqs) j)
  have hproduct :=
    mul_primrec.comp
      (Primrec.const (thetaOutputPair (eqs := eqs) j))
      hcharacter
  exact
    (subPair_primrec.comp hproduct
      (Primrec.const
        (rationalPair (eqs := eqs) (vars := vars)
          (1 / 256)))).of_eq
      (fun _ => rfl)

theorem jacobiMinusMeanCode_primrec
    (j : Fin vars) :
    Primrec
      (fun I : DQLSystem eqs vars =>
        jacobiMinusMeanCode I j) := by
  have hcharacter :
      Primrec
        (fun I : DQLSystem eqs vars =>
          controllerCharacterPair
            (eqs := eqs) (vars := vars)
            (jacobiMinusExponent I j)) :=
    (controllerCharacterPair_primrec
      (eqs := eqs) (vars := vars)).comp
      (jacobiMinusExponent_primrec (eqs := eqs) j)
  have hproduct :=
    mul_primrec.comp
      (Primrec.const (thetaOutputPair (eqs := eqs) j))
      hcharacter
  exact
    (subPair_primrec.comp hproduct
      (Primrec.const
        (rationalPair (eqs := eqs) (vars := vars)
          (1 / 256)))).of_eq
      (fun _ => rfl)

/-! ## Complete finite families -/

private theorem localMomentCode_at_primrec
    (j : Fin vars) (m : Fin localMomentCount) :
    Primrec
      (fun I : DQLSystem eqs vars =>
        localMomentCode I j m) := by
  fin_cases m
  · exact Primrec.const (unaryMeanCode (eqs := eqs) j)
  · exact
      Primrec.const
        (unaryFirstHarmonicCode (eqs := eqs) j)
  · exact Primrec.const (rootP4MeanCode (eqs := eqs) j)
  · exact Primrec.const (rootP2MeanCode (eqs := eqs) j)
  · exact Primrec.const (jacobiMeanCode (eqs := eqs) j)
  · exact jacobiPlusMeanCode_primrec j
  · exact jacobiMinusMeanCode_primrec j

/-- Compile the seven moments of one fixed arithmetic variable. -/
theorem localMomentCode_primrec
    (j : Fin vars) :
    Primrec
      (fun I : DQLSystem eqs vars =>
        localMomentCode I j) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro m
  exact localMomentCode_at_primrec j m

private theorem momentCode_at_primrec
    (k : Fin (momentCount vars)) :
    Primrec
      (fun I : DQLSystem eqs vars =>
        momentCode I k) := by
  let jm := finProdFinEquiv.symm k
  exact
    (localMomentCode_at_primrec jm.1 jm.2).of_eq
      (fun _ => rfl)

/-- The complete flattened complex moment compiler is primitive recursive
in the finite DQL table. -/
theorem momentCode_primrec :
    Primrec
      (momentCode :
        DQLSystem eqs vars →
          Fin (momentCount vars) →
            ComplexPairCode (dimension eqs vars)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro k
  exact momentCode_at_primrec k

theorem momentCode_computable :
    Computable
      (momentCode :
        DQLSystem eqs vars →
          Fin (momentCount vars) →
            ComplexPairCode (dimension eqs vars)) :=
  momentCode_primrec.to_comp

private theorem pairCoordinate_primrec
    {n : ℕ} (c : Fin 2) :
    Primrec
      (fun p : ComplexPairCode n =>
        ![p.1, p.2] c) := by
  fin_cases c
  · exact Primrec.fst
  · exact Primrec.snd

private theorem scalarMomentCode_at_primrec
    (k : Fin (scalarMomentCount vars)) :
    Primrec
      (fun I : DQLSystem eqs vars =>
        scalarMomentCode I k) := by
  let mc := finProdFinEquiv.symm k
  have hmoment :
      Primrec
        (fun I : DQLSystem eqs vars =>
          momentCode I mc.1) :=
    Primrec.fin_app.comp momentCode_primrec
      (Primrec.const mc.1)
  exact
    ((pairCoordinate_primrec mc.2).comp hmoment).of_eq
      (fun _ => rfl)

/-- The adjacent real/imaginary scalar moment compiler is primitive
recursive in the finite DQL table. -/
theorem scalarMomentCode_primrec :
    Primrec
      (scalarMomentCode :
        DQLSystem eqs vars →
          Fin (scalarMomentCount vars) →
            PolynomialCode (dimension eqs vars)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro k
  exact scalarMomentCode_at_primrec k

theorem scalarMomentCode_computable :
    Computable
      (scalarMomentCode :
        DQLSystem eqs vars →
          Fin (scalarMomentCount vars) →
            PolynomialCode (dimension eqs vars)) :=
  scalarMomentCode_primrec.to_comp

end HGAS.FixedDetectorMomentCode
