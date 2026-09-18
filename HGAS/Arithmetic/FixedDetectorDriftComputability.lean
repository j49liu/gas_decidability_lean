import HGAS.Arithmetic.FixedDetectorDriftCode
import HGAS.Arithmetic.FixedDetectorMomentComputability
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Effective compilation of the complete fixed-detector drift

For fixed finite arities, the complete drift vector is primitive recursive
in the finite DQL coefficient table.  The proof follows the same three
blocks as the syntax:

* the validity coordinate uses the effective sum-of-squares compiler;
* the moment coordinates use the effective selector compiler; and
* the two detector coordinates are constant sparse codes.

The final section combines this drift compiler with the already verified
fixed-detector vector-field compiler.  This paired theorem is the
effectivity interface needed by later accumulator and compactification
modules.
-/

namespace HGAS.FixedDetectorDriftCode

open HGAS

variable {eqs vars : ℕ}

/-- For a fixed output coordinate, its sparse polynomial is primitive
recursive in the DQL table. -/
theorem driftCode_at_primrec
    (q : Fin (driftCount vars)) :
    Primrec
      (fun I : DQLSystem eqs vars ↦ driftCode I q) := by
  obtain ⟨i | r, rfl⟩ := finSumFinEquiv.surjective q
  · fin_cases i
    simpa [driftCode] using
      (FixedDetectorValidityEnergyCode.totalValidityEnergyCode_primrec
        (eqs := eqs) (vars := vars))
  · obtain ⟨k | b, rfl⟩ := finSumFinEquiv.surjective r
    · simpa [driftCode] using
        (Primrec.fin_app.comp
          (FixedDetectorMomentCode.scalarMomentCode_primrec
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

/-- The whole finite drift family is primitive recursive in the DQL
table. -/
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

/-- Computable form of `driftCode_primrec`. -/
theorem driftCode_computable :
    Computable
      (driftCode :
        DQLSystem eqs vars →
          Fin (driftCount vars) →
            PolynomialCode (dimension eqs vars)) :=
  driftCode_primrec.to_comp

/-- Compile the fixed-detector vector field and its complete drift vector
simultaneously from controller parameters and a DQL table. -/
def fieldAndDriftCode
    (input : FixedDetectorPolynomialCode.CompilerInput eqs vars) :
    PolynomialFieldCode (dimension eqs vars) ×
      (Fin (driftCount vars) → PolynomialCode (dimension eqs vars)) :=
  (FixedDetectorPolynomialCode.fieldCode input.1 input.2,
    driftCode input.2)

/-- The paired field-and-drift compiler is primitive recursive. -/
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

/-- Computable form of `fieldAndDriftCode_primrec`. -/
theorem fieldAndDriftCode_computable :
    Computable
      (fieldAndDriftCode :
        FixedDetectorPolynomialCode.CompilerInput eqs vars →
          PolynomialFieldCode (dimension eqs vars) ×
            (Fin (driftCount vars) →
              PolynomialCode (dimension eqs vars))) :=
  fieldAndDriftCode_primrec.to_comp

end HGAS.FixedDetectorDriftCode
