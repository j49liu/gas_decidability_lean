import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorDriftComputability
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorDriftDegrees
import HGAS.Arithmetic.CorrectedFixedDetectorCompactSourceCode
import Mathlib.Tactic

/-!
# Radius-normalized corrected detector as a compact polynomial source

This module reruns the existing one-block all-affine compactification with
the repaired drift.  State and drift dimensions are unchanged.  The new
radius terms have degree four, below the pre-existing validity bound, so
all source, clearing, compact-field, and reward degree ledgers are
literally unchanged.
-/

namespace HGAS.NormalizedCorrectedFixedDetectorCompactSourceCode

open HGAS

variable {eqs vars : ℕ}

abbrev sourceDimension (eqs vars : ℕ) : ℕ :=
  CorrectedFixedDetectorCompactSourceCode.sourceDimension eqs vars

abbrev driftDimension (vars : ℕ) : ℕ :=
  NormalizedCorrectedFixedDetectorDriftCode.driftCount vars

abbrev affineBlockCount : ℕ := 1
abbrev compactBlockCount : ℕ := 0

abbrev finalDimension (eqs vars : ℕ) : ℕ :=
  (sourceDimension eqs vars + affineBlockCount) +
    (driftDimension vars + 1)

def layout :
    Fin (sourceDimension eqs vars) →
      Fin affineBlockCount ⊕ Fin compactBlockCount :=
  MixedCentralPolynomialCode.oneBlockAllAffineLayout
    (sourceDimension eqs vars)

theorem driftDimension_eq :
    driftDimension vars = 14 * vars + 3 :=
  CorrectedFixedDetectorCompactSourceCode.driftDimension_eq

theorem finalDimension_eq :
    finalDimension eqs vars = 4 * eqs + 52 * vars + 7 :=
  CorrectedFixedDetectorCompactSourceCode.finalDimension_eq

def sourceDegreeBound (I : DQLSystem eqs vars) : ℕ :=
  CorrectedFixedDetectorCompactSourceCode.sourceDegreeBound I

def clearingExponent (I : DQLSystem eqs vars) : ℕ :=
  2 * sourceDegreeBound I

def compactFieldDegree (I : DQLSystem eqs vars) : ℕ :=
  sourceDegreeBound I + clearingExponent I + 3

abbrev compactRewardDegree : ℕ := 2

def compilerDegree (I : DQLSystem eqs vars) : ℕ :=
  max (compactFieldDegree I) compactRewardDegree

theorem fieldDegree_le_sourceDegreeBound
    (I : DQLSystem eqs vars) :
    FixedDetectorPolynomialCode.fieldDegree I ≤ sourceDegreeBound I :=
  CorrectedFixedDetectorCompactSourceCode.fieldDegree_le_sourceDegreeBound I

theorem driftDegree_le_sourceDegreeBound
    (I : DQLSystem eqs vars) :
    NormalizedCorrectedFixedDetectorDriftCode.driftDegree I ≤
      sourceDegreeBound I :=
  Nat.le_max_right _ _

theorem sourceDegreeBound_le_clearingExponent
    (I : DQLSystem eqs vars) :
    sourceDegreeBound I ≤ clearingExponent I := by
  unfold clearingExponent
  omega

theorem clearingExponent_even
    (I : DQLSystem eqs vars) :
    clearingExponent I % 2 = 0 := by
  simp [clearingExponent]

def sourceFieldCode
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars) :
    PolynomialFieldCode (sourceDimension eqs vars) :=
  FixedDetectorPolynomialCode.fieldCode parameters I

def sourceDriftCode
    (I : DQLSystem eqs vars) :
    Fin (driftDimension vars) →
      PolynomialCode (sourceDimension eqs vars) :=
  NormalizedCorrectedFixedDetectorDriftCode.driftCode I

theorem sourceFieldCode_termsDegreeLE
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars) :
    ∀ j,
      PolynomialCode.TermsDegreeLE (sourceDegreeBound I)
        (sourceFieldCode parameters I j) := by
  intro j
  exact
    (FixedDetectorPolynomialCode.fieldCode_termsDegreeLE
      parameters I j).promote
        (fieldDegree_le_sourceDegreeBound I)

theorem sourceDriftCode_termsDegreeLE
    (I : DQLSystem eqs vars) :
    ∀ i,
      PolynomialCode.TermsDegreeLE (sourceDegreeBound I)
        (sourceDriftCode I i) := by
  intro i
  exact
    (NormalizedCorrectedFixedDetectorDriftCode.driftCode_termsDegreeLE
      I i).promote
        (driftDegree_le_sourceDegreeBound I)

theorem sourceFieldCode_termsAffineBlockDegreeLE
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars) :
    ∀ j,
      MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
        layout (clearingExponent I)
        (sourceFieldCode parameters I j) := by
  intro j
  apply
    MixedCentralPolynomialCode.termsAffineBlockDegreeLE_oneBlockAllAffineLayout
  exact
    (sourceFieldCode_termsDegreeLE parameters I j).promote
      (sourceDegreeBound_le_clearingExponent I)

theorem sourceDriftCode_termsAffineBlockDegreeLE
    (I : DQLSystem eqs vars) :
    ∀ i,
      MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
        layout (clearingExponent I) (sourceDriftCode I i) := by
  intro i
  apply
    MixedCentralPolynomialCode.termsAffineBlockDegreeLE_oneBlockAllAffineLayout
  exact
    (sourceDriftCode_termsDegreeLE I i).promote
      (sourceDegreeBound_le_clearingExponent I)

theorem baseCompactTangency
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars) :
    CompactAccumulatorPipelineCode.BaseCompactTangency
      layout (clearingExponent I)
      (sourceFieldCode parameters I) := by
  intro y
  dsimp
  intro c
  exact Fin.elim0 c

abbrev CompilerInput (eqs vars : ℕ) :=
  (((Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode) ×
      DQLSystem eqs vars) × RationalCode) × RationalCode

def parameters
    (u : CompilerInput eqs vars) :
    Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
      RationalCode :=
  u.1.1.1

def system (u : CompilerInput eqs vars) :
    DQLSystem eqs vars :=
  u.1.1.2

def accumulatorScale (u : CompilerInput eqs vars) :
    RationalCode :=
  u.1.2

def rewardMargin (u : CompilerInput eqs vars) :
    RationalCode :=
  u.2

def toPipelineInput
    (u : CompilerInput eqs vars) :
    CompactAccumulatorPipelineCode.CompilerInput
      (sourceDimension eqs vars) (driftDimension vars) :=
  (((accumulatorScale u,
      sourceFieldCode (parameters u) (system u)),
    sourceDriftCode (system u)),
    rewardMargin u)

def compile
    (u : CompilerInput eqs vars) :
    PolynomialFieldCode (finalDimension eqs vars) ×
      PolynomialCode (finalDimension eqs vars) :=
  CompactAccumulatorPipelineCode.compile
    layout (clearingExponent (system u)) (toPipelineInput u)

theorem compile_field_termsDegreeLE
    (u : CompilerInput eqs vars) :
    ∀ q,
      PolynomialCode.TermsDegreeLE
        (compactFieldDegree (system u))
        ((compile u).1 q) := by
  simpa [compile, toPipelineInput, compactFieldDegree,
    affineBlockCount] using
    (CompactAccumulatorPipelineCode.fieldCode_termsDegreeLE
      layout (clearingExponent (system u))
      (accumulatorScale u)
      (sourceFieldCode (parameters u) (system u))
      (sourceFieldCode_termsDegreeLE (parameters u) (system u))
      (sourceDriftCode (system u))
      (sourceDriftCode_termsDegreeLE (system u)))

theorem compile_reward_termsDegreeLE
    (u : CompilerInput eqs vars) :
    PolynomialCode.TermsDegreeLE compactRewardDegree
      (compile u).2 := by
  simpa [compile, toPipelineInput, compactRewardDegree,
    affineBlockCount] using
    (CompactAccumulatorPipelineCode.rewardCode_termsDegreeLE
      (n := sourceDimension eqs vars)
      (k := affineBlockCount)
      (m := driftDimension vars)
      (rewardMargin u))

theorem compile_termsDegreeLE
    (u : CompilerInput eqs vars) :
    (∀ q,
      PolynomialCode.TermsDegreeLE
        (compilerDegree (system u)) ((compile u).1 q)) ∧
      PolynomialCode.TermsDegreeLE
        (compilerDegree (system u)) (compile u).2 := by
  constructor
  · intro q
    exact
      (compile_field_termsDegreeLE u q).promote
        (Nat.le_max_left _ _)
  · exact
      (compile_reward_termsDegreeLE u).promote
        (Nat.le_max_right _ _)

theorem sourceDegreeBound_primrec :
    Primrec
      (sourceDegreeBound :
        DQLSystem eqs vars → ℕ) := by
  simpa [sourceDegreeBound] using
    (CorrectedFixedDetectorCompactSourceCode.sourceDegreeBound_primrec
      (eqs := eqs) (vars := vars))

theorem clearingExponent_primrec :
    Primrec
      (clearingExponent :
        DQLSystem eqs vars → ℕ) :=
  Primrec.nat_mul.comp
    (Primrec.const 2) sourceDegreeBound_primrec

theorem toPipelineInput_primrec :
    Primrec
      (toPipelineInput :
        CompilerInput eqs vars →
          CompactAccumulatorPipelineCode.CompilerInput
            (sourceDimension eqs vars) (driftDimension vars)) := by
  have hfieldDrift :
      Primrec
        (fun u : CompilerInput eqs vars ↦
          NormalizedCorrectedFixedDetectorDriftCode.fieldAndDriftCode
            u.1.1) :=
    NormalizedCorrectedFixedDetectorDriftCode.fieldAndDriftCode_primrec.comp
        (Primrec.fst.comp Primrec.fst)
  exact
    (Primrec.pair
      (Primrec.pair
        (Primrec.pair
          (Primrec.snd.comp Primrec.fst)
          (Primrec.fst.comp hfieldDrift))
        (Primrec.snd.comp hfieldDrift))
      Primrec.snd).of_eq
      (fun _ ↦ rfl)

theorem compile_primrec :
    Primrec
      (compile :
        CompilerInput eqs vars →
          PolynomialFieldCode (finalDimension eqs vars) ×
            PolynomialCode (finalDimension eqs vars)) := by
  have hsystem :
      Primrec
        (fun u : CompilerInput eqs vars ↦ system u) :=
    (Primrec.snd.comp
      (Primrec.fst.comp Primrec.fst)).of_eq
      (fun _ ↦ rfl)
  exact
    ((FixedDetectorCompactSourceCode.pipelineCompile_withExponent_primrec
      layout).comp
      (Primrec.pair
        (clearingExponent_primrec.comp hsystem)
        toPipelineInput_primrec)).of_eq
      (fun _ ↦ rfl)

theorem compile_computable :
    Computable
      (compile :
        CompilerInput eqs vars →
          PolynomialFieldCode (finalDimension eqs vars) ×
            PolynomialCode (finalDimension eqs vars)) :=
  compile_primrec.to_comp

end HGAS.NormalizedCorrectedFixedDetectorCompactSourceCode
