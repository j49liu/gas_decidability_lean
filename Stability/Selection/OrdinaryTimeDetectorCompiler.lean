import Stability.Selection.OrdinaryTimeDetectorSign
import HGAS.Wrapper.UnitSphereWrapperComputability

/-!
# Effective compilation of the detector with fixed matrices

For fixed quadratic and linear matrices and a fixed prime tuple, the
right-hand side determines the literal compact source and homogeneous
wrapper computably. The emitted codes use the least-integer gain and do
not depend on a proof of the semantic sign theorem.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.CompactAccumulatorPipelineCode
open HGAS.NormalizedCorrectedFixedDetectorCompactSourceCode
open HGAS.Clocks.ObservedTimeChangedControllerPhaseHaar

variable {eqs vars : ℕ}

private theorem signedIntegerCode_primrec : Primrec intSignedCodeEquiv := by
  rw [← Primrec.encode_iff]
  exact (Primrec.encode : Primrec (fun z : ℤ ↦ Encodable.encode z)).of_eq
    (fun z ↦ by cases z <;> rfl)

/-- Replacing only the right-hand side is primitive recursive in its
finite integer tuple. -/
theorem detectorReplaceRhs_primrec (I : DQLSystem eqs vars) :
    Primrec (fun rhs : Fin eqs → ℤ ↦ { I with rhs := rhs }) := by
  have hrhs : Primrec (fun rhs : Fin eqs → ℤ ↦ fun row ↦ intSignedCodeEquiv (rhs row)) := by
    rw [Primrec.fin_curry]
    apply Primrec₂.swap
    rw [Primrec.fin_curry₁]
    intro row
    exact signedIntegerCode_primrec.comp
      (Primrec.fin_app.comp Primrec.id (Primrec.const row))
  have hcode : Primrec (fun rhs : Fin eqs → ℤ ↦
      dqlSystemCodeEquiv eqs vars { I with rhs := rhs }) :=
    Primrec.pair
      (Primrec.const ((fun r j ↦ intSignedCodeEquiv (I.quadratic r j)),
        (fun r j ↦ intSignedCodeEquiv (I.linear r j)))) hrhs
  exact (Primrec.of_equiv_symm.comp hcode).of_eq (fun _ ↦ by simp)

/-- The actual compiler input, including the raw least-denominator gain,
is computable as the right-hand side varies. -/
theorem detectorCompilerInput_rhs_computable (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) :
    Computable (fun rhs : Fin eqs → ℤ ↦ detectorCompilerInput { I with rhs := rhs } p) := by
  exact (Computable.pair
    (Computable.pair
      (Computable.pair (Computable.const _) (detectorReplaceRhs_primrec I).to_comp)
      (rhsGraphGainCode_computable I p))
    (Computable.const _)).of_eq (fun _ ↦ rfl)

/-- The literal compact field/reward pair is computable with fixed
matrices and prime tuple. -/
theorem detectorCompiledSourceCode_rhs_computable (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) :
    Computable (fun rhs : Fin eqs → ℤ ↦
      NormalizedCorrectedFixedDetectorCompactSourceCode.compile
        (detectorCompilerInput { I with rhs := rhs } p)) :=
  compile_computable.comp (detectorCompilerInput_rhs_computable I p)

/-- A proof-independent sparse polynomial code for the final wrapper. -/
def detectorWrappedFieldCode (I : DQLSystem eqs vars) (p : Fin (vars + eqs) → ℕ) :
    PolynomialFieldCode (finalDimension eqs vars + 1) :=
  let source := NormalizedCorrectedFixedDetectorCompactSourceCode.compile
    (detectorCompilerInput I p)
  UnitSpherePolynomialWrapper.finalFieldCode
    (sourceBlock (m := driftDimension vars) (layout (eqs := eqs) (vars := vars)))
    (wrapperDegree (sourceDegreeBound I) 1 (clearingExponent I)) source.1 source.2

/-- The wrapper's degree remains fixed when only the right-hand side
changes. -/
theorem detectorWrapperDegree_replace_rhs (I : DQLSystem eqs vars)
    (rhs : Fin eqs → ℤ) :
    wrapperDegree (sourceDegreeBound { I with rhs := rhs }) 1
        (clearingExponent { I with rhs := rhs }) =
      wrapperDegree (sourceDegreeBound I) 1 (clearingExponent I) := rfl

/-- The actual final homogeneous code is computable in the right-hand
side, at the same fixed dimension and wrapper degree. -/
theorem detectorWrappedFieldCode_rhs_computable (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) :
    Computable (fun rhs : Fin eqs → ℤ ↦ detectorWrappedFieldCode { I with rhs := rhs } p) := by
  exact ((UnitSpherePolynomialWrapper.finalFieldCode_computable
    (sourceBlock (m := driftDimension vars) (layout (eqs := eqs) (vars := vars)))
    (wrapperDegree (sourceDegreeBound I) 1 (clearingExponent I))).comp
      (detectorCompiledSourceCode_rhs_computable I p)).of_eq (fun _ ↦ rfl)

local instance : Nonempty (DetectorCompactSpace eqs vars) := by
  simpa [NormalizedCorrectedFixedDetectorCompactSourceCode.layout] using
    nonempty_sourceProductSphere_oneBlockAllAffine
      (sourceDimension eqs vars) (driftDimension vars)

/-- The executable output is literally the field in the semantic
certificate, not only a dynamically equivalent polynomial field. -/
theorem detectorWrappedFieldCode_eq_certificate
    (I : DQLSystem eqs vars) (hcolumns : DQLNonzeroLinearAugmentation.HasNonzeroLinearColumn I)
    (p : Fin (vars + eqs) → ℕ) (hp : ∀ i, (p i).Prime) (hinjective : Function.Injective p) :
    detectorWrappedFieldCode I p =
      (detectorSignCertificate I hcolumns p hp hinjective).finalFieldCode := rfl

theorem detectorWrappedFieldCode_gas_iff_solvable
    (I : DQLSystem eqs vars) (hcolumns : DQLNonzeroLinearAugmentation.HasNonzeroLinearColumn I)
    (p : Fin (vars + eqs) → ℕ) (hp : ∀ i, (p i).Prime) (hinjective : Function.Injective p) :
    GloballyAsymptoticallyStable (PolynomialFieldCode.realize
      (detectorWrappedFieldCode I p)) 0 ↔ I.Solvable :=
  detectorFinalField_gas_iff_solvable I hcolumns p hp hinjective

end Stability.Selection
