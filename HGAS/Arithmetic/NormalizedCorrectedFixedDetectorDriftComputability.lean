import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorDriftCode
import HGAS.Arithmetic.CorrectedFixedDetectorMomentComputability
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Effectivity of the radius-normalized corrected drift

The added normalization polynomial is independent of the arithmetic
instance, and its sum with the old validity code is primitive recursive.
Therefore the repaired complete drift and the field-and-drift compiler
remain primitive recursive and computable.
-/

namespace HGAS.NormalizedCorrectedFixedDetectorDriftCode

open HGAS
open HGAS.NormalizedCorrectedFixedDetectorValidityCode

variable {eqs vars : ℕ}

theorem driftCode_at_primrec
    (q : Fin (driftCount vars)) :
    Primrec
      (fun I : DQLSystem eqs vars ↦ driftCode I q) := by
  obtain ⟨i | r, rfl⟩ := finSumFinEquiv.surjective q
  · fin_cases i
    simpa [driftCode] using
      (totalNormalizedValidityEnergyCode_primrec
        (eqs := eqs) (vars := vars))
  · obtain ⟨k | b, rfl⟩ := finSumFinEquiv.surjective r
    · simpa [driftCode] using
        (Primrec.fin_app.comp
          (CorrectedFixedDetectorMomentCode.scalarMomentCode_primrec
            (eqs := eqs) (vars := vars))
          (Primrec.const k))
    · fin_cases b
      · simpa [driftCode] using
          (Primrec.const
            (FixedDetectorPolynomialCode.detectorCode
              (eqs := eqs) (vars := vars)).1 :
            Primrec
              (fun _ : DQLSystem eqs vars ↦
                (FixedDetectorPolynomialCode.detectorCode
                  (eqs := eqs) (vars := vars)).1))
      · simpa [driftCode] using
          (Primrec.const
            (FixedDetectorPolynomialCode.detectorCode
              (eqs := eqs) (vars := vars)).2 :
            Primrec
              (fun _ : DQLSystem eqs vars ↦
                (FixedDetectorPolynomialCode.detectorCode
                  (eqs := eqs) (vars := vars)).2))

theorem driftCode_primrec :
    Primrec
      (driftCode :
        DQLSystem eqs vars →
          Fin (driftCount vars) →
            PolynomialCode (dimension eqs vars)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro q
  exact driftCode_at_primrec q

theorem driftCode_computable :
    Computable
      (driftCode :
        DQLSystem eqs vars →
          Fin (driftCount vars) →
            PolynomialCode (dimension eqs vars)) :=
  driftCode_primrec.to_comp

def fieldAndDriftCode
    (input : FixedDetectorPolynomialCode.CompilerInput eqs vars) :
    PolynomialFieldCode (dimension eqs vars) ×
      (Fin (driftCount vars) → PolynomialCode (dimension eqs vars)) :=
  (FixedDetectorPolynomialCode.fieldCode input.1 input.2,
    driftCode input.2)

theorem fieldAndDriftCode_primrec :
    Primrec
      (fieldAndDriftCode :
        FixedDetectorPolynomialCode.CompilerInput eqs vars →
          PolynomialFieldCode (dimension eqs vars) ×
            (Fin (driftCount vars) →
              PolynomialCode (dimension eqs vars))) := by
  exact
    (Primrec.pair
      FixedDetectorPolynomialCode.fieldCode_primrec
      (driftCode_primrec.comp Primrec.snd)).of_eq
      (fun _ ↦ rfl)

theorem fieldAndDriftCode_computable :
    Computable
      (fieldAndDriftCode :
        FixedDetectorPolynomialCode.CompilerInput eqs vars →
          PolynomialFieldCode (dimension eqs vars) ×
            (Fin (driftCount vars) →
              PolynomialCode (dimension eqs vars))) :=
  fieldAndDriftCode_primrec.to_comp

end HGAS.NormalizedCorrectedFixedDetectorDriftCode
