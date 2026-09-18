import HGAS.Compiler.ComplexReciprocalFamilyPolynomialCode
import HGAS.Compiler.ComplexReciprocalPolynomialComputability
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Effectivity of the finite complex-reciprocal family compiler

For fixed finite dimensions `n` and `b`, the field compiler accepts

```text
  (F, (eta, wdot))
```

where `F` is the common base field and `eta`, `wdot` are `b`-tuples of
rational parameters and coded complex observables.  The residual compiler
accepts `(eta, w)` and returns all `2b` real residual codes.

Both maps are primitive recursive, hence computable.  The proof selects
finite tuple entries, invokes the effective one-reciprocal compiler, and
performs a fixed injective variable renaming into the selected family
block.  No rational decoding, real arithmetic, polynomial normalization,
or ODE computation occurs.
-/

namespace HGAS.ComplexReciprocalFamilyPolynomialCode

variable {n b : ℕ}

/-- Runtime input for all `2b` reciprocal graph residual coordinates. -/
abbrev ResidualCompilerInput (n b : ℕ) :=
  (Fin b → RationalCode) × ObservableFamily n b

/-- Runtime input for the complete base-plus-reciprocal-family field. -/
abbrev FieldCompilerInput (n b : ℕ) :=
  PolynomialFieldCode n × ResidualCompilerInput n b

/-- Fixed injection into reciprocal block `a` is primitive recursive on
sparse polynomial syntax. -/
theorem liftSingle_primrec (a : Fin b) :
    Primrec
      (liftSingle a :
        PolynomialCode
            (ComplexReciprocalPolynomialCode.dimension n) →
          PolynomialCode (dimension n b)) :=
  PolynomialCode.injectVariables_primrec (singleEmbedding a)

/-- Base-block insertion is primitive recursive. -/
theorem liftBase_primrec :
    Primrec
      (liftBase :
        PolynomialCode n →
          PolynomialCode (dimension n b)) :=
  PolynomialBlockCode.left_primrec

private theorem etaFamily_primrec :
    Primrec
      (fun input : ResidualCompilerInput n b ↦ input.1) :=
  Primrec.fst

private theorem observableFamily_primrec :
    Primrec
      (fun input : ResidualCompilerInput n b ↦ input.2) :=
  Primrec.snd

private theorem etaAt_primrec (a : Fin b) :
    Primrec
      (fun input : ResidualCompilerInput n b ↦ input.1 a) :=
  Primrec.fin_app.comp etaFamily_primrec (Primrec.const a)

private theorem observableAt_primrec (a : Fin b) :
    Primrec
      (fun input : ResidualCompilerInput n b ↦ input.2 a) :=
  Primrec.fin_app.comp observableFamily_primrec (Primrec.const a)

/-- Select block `a` and package the one-reciprocal compiler input. -/
private theorem singleInputAt_primrec (a : Fin b) :
    Primrec
      (fun input : ResidualCompilerInput n b ↦
        (input.1 a, input.2 a)) :=
  Primrec.pair (etaAt_primrec a) (observableAt_primrec a)

/-- Select block `a` and compile its pair of one-reciprocal residual
coordinates before the final variable injection. -/
private theorem singleResidualCodesAt_primrec (a : Fin b) :
    Primrec
      (fun input : ResidualCompilerInput n b ↦
        ComplexReciprocalPolynomialCode.residualCodes
          (input.1 a, input.2 a)) :=
  ComplexReciprocalPolynomialCode.residualCodes_primrec.comp
    (singleInputAt_primrec a)

/-- Real velocity syntax for block `a` is primitive recursive in the
complete parameter/velocity family. -/
theorem reciprocalVelocityReCode_primrec (a : Fin b) :
    Primrec
      (fun input : ResidualCompilerInput n b ↦
        reciprocalVelocityReCode input.1 input.2 a) := by
  exact
    (liftSingle_primrec a).comp
      (ComplexReciprocalPolynomialCode.reciprocalVelocityReCode_primrec.comp
          (singleInputAt_primrec a))

/-- Imaginary velocity syntax for block `a` is primitive recursive. -/
theorem reciprocalVelocityImCode_primrec (a : Fin b) :
    Primrec
      (fun input : ResidualCompilerInput n b ↦
        reciprocalVelocityImCode input.1 input.2 a) := by
  exact
    (liftSingle_primrec a).comp
      (ComplexReciprocalPolynomialCode.reciprocalVelocityImCode_primrec.comp
          (singleInputAt_primrec a))

/-- Real reciprocal residual syntax for block `a` is primitive recursive. -/
theorem residualReCode_primrec (a : Fin b) :
    Primrec
      (fun input : ResidualCompilerInput n b ↦
        residualReCode input.1 input.2 a) := by
  exact
    ((liftSingle_primrec a).comp
      (Primrec.fst.comp
        (singleResidualCodesAt_primrec a))).of_eq
      fun _ ↦ rfl

/-- Imaginary reciprocal residual syntax for block `a` is primitive
recursive. -/
theorem residualImCode_primrec (a : Fin b) :
    Primrec
      (fun input : ResidualCompilerInput n b ↦
        residualImCode input.1 input.2 a) := by
  exact
    ((liftSingle_primrec a).comp
      (Primrec.snd.comp
        (singleResidualCodesAt_primrec a))).of_eq
      fun _ ↦ rfl

/-- **Effective complete field compiler.**

For fixed `n` and `b`, compilation is uniform in the common base field
and in every rational parameter and velocity-observable code. -/
theorem fieldCode_primrec :
    Primrec
      (fun input : FieldCompilerInput n b ↦
        fieldCode input.1 input.2.1 input.2.2) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro k
  obtain ⟨i | r, rfl⟩ := finSumFinEquiv.surjective k
  · exact
      (liftBase_primrec.comp
        (Primrec.fin_app.comp Primrec.fst
          (Primrec.const i))).of_eq fun input ↦
            (fieldCode_baseEmbedding
              input.1 input.2.1 input.2.2 i).symm
  · obtain ⟨⟨a, j⟩, rfl⟩ :=
      finProdFinEquiv.surjective r
    fin_cases j
    · exact
        ((reciprocalVelocityReCode_primrec a).comp
          Primrec.snd).of_eq fun input ↦
            (fieldCode_reciprocalReIndex
              input.1 input.2.1 input.2.2 a).symm
    · exact
        ((reciprocalVelocityImCode_primrec a).comp
          Primrec.snd).of_eq fun input ↦
            (fieldCode_reciprocalImIndex
              input.1 input.2.1 input.2.2 a).symm

theorem fieldCode_computable :
    Computable
      (fun input : FieldCompilerInput n b ↦
        fieldCode input.1 input.2.1 input.2.2) :=
  fieldCode_primrec.to_comp

/-- **Effective complete residual-family compiler.**

For fixed `n` and `b`, the map from all parameters and observable codes to
the flattened `2b` sparse residual coordinates is primitive recursive. -/
theorem residualCode_primrec :
    Primrec
      (fun input : ResidualCompilerInput n b ↦
        residualCode input.1 input.2) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro k
  obtain ⟨⟨a, j⟩, rfl⟩ :=
    finProdFinEquiv.surjective k
  fin_cases j
  · exact
      (residualReCode_primrec a).of_eq fun input ↦
        (residualCode_reciprocalBlockEmbedding
          input.1 input.2 a (0 : Fin 2)).symm
  · exact
      (residualImCode_primrec a).of_eq fun input ↦
        (residualCode_reciprocalBlockEmbedding
          input.1 input.2 a (1 : Fin 2)).symm

theorem residualCode_computable :
    Computable
      (fun input : ResidualCompilerInput n b ↦
        residualCode input.1 input.2) :=
  residualCode_primrec.to_comp

end HGAS.ComplexReciprocalFamilyPolynomialCode
