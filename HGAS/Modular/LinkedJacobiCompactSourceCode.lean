import HGAS.Compactification.AllAffinePolynomialCode
import HGAS.Compiler.CompactAccumulatorPipelineComputability
import HGAS.Compiler.CompactAccumulatorPipelineGapCertificate
import HGAS.Modular.LinkedJacobiPolynomialComputability
import HGAS.Modular.LinkedJacobiPolynomialDegrees
import Mathlib.Tactic

/-!
# The linked Jacobi block as a concrete compact-pipeline source

`LinkedJacobiPolynomialCode` produces a rational polynomial field on
twenty-eight real coordinates and twenty scalar validity residuals.  This
file instantiates the mixed-central compactification and accumulator
compiler with those exact finite objects.

All twenty-eight source coordinates are affine.  We therefore use the
one-block layout

```
                  Fin 28 → Fin 1 ⊕ Fin 0.
```

The degree-eight field bound is also a valid denominator-clearing bound in
that block.  Since there are no already compact source blocks, the
source-specific `BaseCompactTangency` premise is vacuous.  Thus this module
removes that premise completely for the linked Jacobi block.

The output is still only one component of the eventual universal source:
arithmetic detectors and dynamic radical clocks must later be adjoined.
The present module makes the linked modular/Jacobi contribution a literal,
primitive-recursive input to the already verified compact pipeline.
-/

namespace HGAS.Modular

open HGAS

namespace LinkedJacobiCompactSourceCode

abbrev sourceDimension : ℕ :=
  LinkedJacobiPolynomialCode.dimension +
    LinkedJacobiPolynomialCode.dimension

abbrev residualDimension : ℕ := 10 + 10
abbrev affineBlockCount : ℕ := 1
abbrev compactBlockCount : ℕ := 0

/-- Both the source field and all residuals have raw degree at most eight. -/
abbrev degreeBound : ℕ := 8

/-- Denominator-clearing exponent for the unique affine block. -/
abbrev clearingExponent : ℕ := 8

def layout :
    Fin sourceDimension →
      Fin affineBlockCount ⊕ Fin compactBlockCount :=
  MixedCentralPolynomialCode.oneBlockAllAffineLayout sourceDimension

/-- The exact twenty-eight-real-coordinate linked Jacobi field. -/
def sourceFieldCode
    (κZ κPhi : GaussianRationalCode) :
    PolynomialFieldCode sourceDimension :=
  LinkedJacobiPolynomialCode.compileFieldCode κZ κPhi

/-- The twenty real and imaginary validity residuals. -/
def residualCode :
    Fin residualDimension → PolynomialCode sourceDimension :=
  LinkedJacobiPolynomialCode.realResidualCode

theorem sourceFieldCode_termsDegreeLE
    (κZ κPhi : GaussianRationalCode) :
    ∀ j, PolynomialCode.TermsDegreeLE degreeBound
      (sourceFieldCode κZ κPhi j) :=
  LinkedJacobiPolynomialCode.compileFieldCode_termsDegreeLE
    κZ κPhi

theorem residualCode_termsDegreeLE :
    ∀ i, PolynomialCode.TermsDegreeLE degreeBound
      (residualCode i) := by
  intro i
  exact
    (LinkedJacobiPolynomialCode.realResidualCode_termsDegreeLE i).promote
      (by norm_num [degreeBound])

/-- The ordinary degree ledger supplies the exact mixed-central clearing
premise for every source-field component. -/
theorem sourceFieldCode_termsAffineBlockDegreeLE
    (κZ κPhi : GaussianRationalCode) :
    ∀ j,
      MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
        layout clearingExponent
        (sourceFieldCode κZ κPhi j) := by
  exact
    MixedCentralPolynomialCode.field_termsAffineBlockDegreeLE_oneBlockAllAffineLayout
      (sourceFieldCode_termsDegreeLE κZ κPhi)

/-- The same clearing premise for all twenty residuals. -/
theorem residualCode_termsAffineBlockDegreeLE :
    ∀ i,
      MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
        layout clearingExponent (residualCode i) := by
  intro i
  exact
    MixedCentralPolynomialCode.termsAffineBlockDegreeLE_oneBlockAllAffineLayout
      (residualCode_termsDegreeLE i)

/-- With zero compact source blocks, base compact tangency is a proposition
over `Fin 0` and is therefore automatic. -/
theorem baseCompactTangency
    (κZ κPhi : GaussianRationalCode) :
    CompactAccumulatorPipelineCode.BaseCompactTangency
      layout clearingExponent
      (sourceFieldCode κZ κPhi) := by
  intro y
  dsimp
  intro c
  exact Fin.elim0 c

/-- Exact semantics of the uncompactified linked source at every real
ambient point. -/
@[simp]
theorem complexify_realize_sourceFieldCode
    (κZ κPhi : GaussianRationalCode)
    (x : Fin sourceDimension → ℝ) :
    ComplexCoordinates.complexifyPoint
        (PolynomialFieldCode.realize
          (sourceFieldCode κZ κPhi) x) =
      LinkedJacobiPolynomialCode.point
        (LinkedJacobiState.combinedVectorField
          (GaussianRationalCode.decode κZ)
          (GaussianRationalCode.decode κPhi)
          (LinkedJacobiPolynomialCode.state
            (ComplexCoordinates.complexifyPoint x))) :=
  LinkedJacobiPolynomialCode.complexify_realize_compileFieldCode_arbitrary
    κZ κPhi x

/-! ## One executable call to the compact accumulator pipeline -/

/-- Runtime input: two linked-source clock coefficients, one rational
accumulator scale, and one rational strict-sign margin. -/
abbrev CompilerInput :=
  ((GaussianRationalCode × GaussianRationalCode) × RationalCode) ×
    RationalCode

/-- Convert the small linked-source input to the generic pipeline input. -/
def toPipelineInput
    (u : CompilerInput) :
    CompactAccumulatorPipelineCode.CompilerInput
      sourceDimension residualDimension :=
  (((u.1.2,
      sourceFieldCode u.1.1.1 u.1.1.2),
    residualCode),
    u.2)

/-- The complete centrally compactified source field and reward code. -/
def compile
    (u : CompilerInput) :
    CompactAccumulatorPipelineCode.CompilerOutput
      sourceDimension affineBlockCount residualDimension :=
  CompactAccumulatorPipelineCode.compile
    layout clearingExponent (toPipelineInput u)

/-- Formation of the generic pipeline input is primitive recursive. -/
theorem toPipelineInput_primrec :
    Primrec toPipelineInput := by
  have hsource :
      Primrec
        (fun u : CompilerInput ↦
          sourceFieldCode u.1.1.1 u.1.1.2) :=
    let hclocks :
        Primrec (fun u : CompilerInput ↦ u.1.1) :=
      Primrec.fst.comp Primrec.fst
    LinkedJacobiPolynomialCode.compileFieldCode_primrec.comp
      (Primrec.fst.comp hclocks)
      (Primrec.snd.comp hclocks)
  have hscale :
      Primrec (fun u : CompilerInput ↦ u.1.2) :=
    Primrec.snd.comp Primrec.fst
  exact
    Primrec.pair
      (Primrec.pair
        (Primrec.pair hscale hsource)
        (Primrec.const residualCode))
      Primrec.snd

/-- The complete linked-source compactification/accumulator compiler is
primitive recursive. -/
theorem compile_primrec :
    Primrec compile :=
  (CompactAccumulatorPipelineCode.compile_primrec
    (m := residualDimension)
    layout clearingExponent).comp
      toPipelineInput_primrec

theorem compile_computable :
    Computable compile :=
  compile_primrec.to_comp

end LinkedJacobiCompactSourceCode

end HGAS.Modular
