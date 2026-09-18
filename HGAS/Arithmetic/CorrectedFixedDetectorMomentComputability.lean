import HGAS.Arithmetic.CorrectedFixedDetectorMomentCode
import HGAS.Arithmetic.FixedDetectorMomentComputability
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Effective compilation of the corrected selector moments

The only new computation is the conditional center.  Equality of the
finite linear-character tuple with zero is primitive recursive, so
choosing between the two fixed rationals `1/128` and `1/256` is primitive
recursive.  The remaining syntax is assembled using the already audited
pair, character, and multiplication compilers.
-/

namespace HGAS.CorrectedFixedDetectorMomentCode

open HGAS
open HGAS.Clocks.ControllerPhaseProductCharacterCode

variable {eqs vars : ℕ}

/-- The test deciding which of the two corrected constants is required is
primitive recursive.  We state the result as a predicate because Mathlib
does not equip `ℚ` itself with the primitive-coding instance used here;
the sparse rational codes selected below do have such an instance. -/
theorem linearCharacterZero_primrec
    (j : Fin vars) :
    PrimrecPred
      (fun I : DQLSystem eqs vars ↦
        DetectorCharacterCode.linearCharacter I j = 0) :=
  Primrec.eq.comp
    (DetectorCharacterCode.linearCharacter_primrec j)
    (Primrec.const 0)

/-- The corrected positive Jacobi moment compiler is primitive recursive. -/
theorem jacobiPlusMeanCode_primrec
    (j : Fin vars) :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        jacobiPlusMeanCode I j) := by
  have hcharacter :
      Primrec
        (fun I : DQLSystem eqs vars ↦
          FixedDetectorMomentCode.controllerCharacterPair
            (eqs := eqs) (vars := vars)
            (FixedDetectorMomentCode.jacobiPlusExponent I j)) :=
    (FixedDetectorMomentCode.controllerCharacterPair_primrec
      (eqs := eqs) (vars := vars)).comp
      (FixedDetectorMomentCode.jacobiPlusExponent_primrec
        (eqs := eqs) j)
  have hproduct :=
    mul_primrec.comp
      (Primrec.const
        (FixedDetectorMomentCode.thetaOutputPair (eqs := eqs) j))
      hcharacter
  have hcenter :
      Primrec
        (fun I : DQLSystem eqs vars ↦
          FixedDetectorMomentCode.rationalPair
            (eqs := eqs) (vars := vars)
            (CorrectedJacobiSelectorCentering.selectorCenter I j)) :=
    (Primrec.ite
      (linearCharacterZero_primrec (eqs := eqs) j)
      (Primrec.const
        (FixedDetectorMomentCode.rationalPair
          (eqs := eqs) (vars := vars) (1 / 128)))
      (Primrec.const
        (FixedDetectorMomentCode.rationalPair
          (eqs := eqs) (vars := vars) (1 / 256)))).of_eq
      (by
        intro I
        by_cases h :
            DetectorCharacterCode.linearCharacter I j = 0
        · simp [CorrectedJacobiSelectorCentering.selectorCenter, h]
        · simp [CorrectedJacobiSelectorCentering.selectorCenter, h])
  exact
    (FixedDetectorMomentCode.subPair_primrec.comp
      hproduct hcenter).of_eq
      (fun _ ↦ rfl)

/-- The corrected negative Jacobi moment compiler is primitive recursive. -/
theorem jacobiMinusMeanCode_primrec
    (j : Fin vars) :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        jacobiMinusMeanCode I j) := by
  have hcharacter :
      Primrec
        (fun I : DQLSystem eqs vars ↦
          FixedDetectorMomentCode.controllerCharacterPair
            (eqs := eqs) (vars := vars)
            (FixedDetectorMomentCode.jacobiMinusExponent I j)) :=
    (FixedDetectorMomentCode.controllerCharacterPair_primrec
      (eqs := eqs) (vars := vars)).comp
      (FixedDetectorMomentCode.jacobiMinusExponent_primrec
        (eqs := eqs) j)
  have hproduct :=
    mul_primrec.comp
      (Primrec.const
        (FixedDetectorMomentCode.thetaOutputPair (eqs := eqs) j))
      hcharacter
  have hcenter :
      Primrec
        (fun I : DQLSystem eqs vars ↦
          FixedDetectorMomentCode.rationalPair
            (eqs := eqs) (vars := vars)
            (CorrectedJacobiSelectorCentering.selectorCenter I j)) :=
    (Primrec.ite
      (linearCharacterZero_primrec (eqs := eqs) j)
      (Primrec.const
        (FixedDetectorMomentCode.rationalPair
          (eqs := eqs) (vars := vars) (1 / 128)))
      (Primrec.const
        (FixedDetectorMomentCode.rationalPair
          (eqs := eqs) (vars := vars) (1 / 256)))).of_eq
      (by
        intro I
        by_cases h :
            DetectorCharacterCode.linearCharacter I j = 0
        · simp [CorrectedJacobiSelectorCentering.selectorCenter, h]
        · simp [CorrectedJacobiSelectorCentering.selectorCenter, h])
  exact
    (FixedDetectorMomentCode.subPair_primrec.comp
      hproduct hcenter).of_eq
      (fun _ ↦ rfl)

private theorem localMomentCode_at_primrec
    (j : Fin vars) (m : Fin localMomentCount) :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        localMomentCode I j m) := by
  fin_cases m
  · exact
      Primrec.const
        (FixedDetectorMomentCode.unaryMeanCode (eqs := eqs) j)
  · exact
      Primrec.const
        (FixedDetectorMomentCode.unaryFirstHarmonicCode
          (eqs := eqs) j)
  · exact
      Primrec.const
        (FixedDetectorMomentCode.rootP4MeanCode (eqs := eqs) j)
  · exact
      Primrec.const
        (FixedDetectorMomentCode.rootP2MeanCode (eqs := eqs) j)
  · exact
      Primrec.const
        (FixedDetectorMomentCode.jacobiMeanCode (eqs := eqs) j)
  · exact jacobiPlusMeanCode_primrec j
  · exact jacobiMinusMeanCode_primrec j

/-- Compile the seven corrected moments of one variable. -/
theorem localMomentCode_primrec
    (j : Fin vars) :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        localMomentCode I j) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro m
  exact localMomentCode_at_primrec j m

private theorem momentCode_at_primrec
    (k : Fin (momentCount vars)) :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        momentCode I k) := by
  let jm := finProdFinEquiv.symm k
  exact
    (localMomentCode_at_primrec jm.1 jm.2).of_eq
      (fun _ ↦ rfl)

/-- The complete corrected complex moment family is primitive recursive. -/
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
      (fun p : ComplexPairCode n ↦
        ![p.1, p.2] c) := by
  fin_cases c
  · exact Primrec.fst
  · exact Primrec.snd

private theorem scalarMomentCode_at_primrec
    (k : Fin (scalarMomentCount vars)) :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        scalarMomentCode I k) := by
  let mc := finProdFinEquiv.symm k
  have hmoment :
      Primrec
        (fun I : DQLSystem eqs vars ↦
          momentCode I mc.1) :=
    Primrec.fin_app.comp momentCode_primrec
      (Primrec.const mc.1)
  exact
    ((pairCoordinate_primrec mc.2).comp hmoment).of_eq
      (fun _ ↦ rfl)

/-- Every real or imaginary corrected moment code is primitive recursive. -/
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

end HGAS.CorrectedFixedDetectorMomentCode
