import HGAS.Clocks.ControllerPhaseProductCharacterComputability
import HGAS.Compiler.ComplexGaugeFamilyPolynomialCode
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Effectivity of finite fourth-root gauge families

For fixed source dimension `n` and family size `b`, all gauge operations
are primitive recursive on the literal sparse syntax:

* extending a base field by `b` gauge equations;
* compiling all `2b` fourth-root residual coordinates; and
* compiling all `b` gauge-corrected outputs `GₐTₐ`.

No polynomial normalization or real/complex evaluation is performed by
these compiler maps.
-/

namespace HGAS.ComplexGaugeFamilyPolynomialCode

open Clocks.ControllerPhaseProductCharacterCode

variable {n b : ℕ}

abbrev FieldCompilerInput (n b : ℕ) :=
  PolynomialFieldCode n × (Fin b → PolynomialCode n)

abbrev ResidualCompilerInput (n b : ℕ) :=
  (Fin b → RationalCode) × ObservableFamily n b

theorem sub_primrec :
    Primrec₂
      (sub :
        ComplexObservableCode (dimension n b) →
          ComplexObservableCode (dimension n b) →
            ComplexObservableCode (dimension n b)) := by
  exact
    Primrec.pair
      (PolynomialCode.sub_primrec.comp
        (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))
      (PolynomialCode.sub_primrec.comp
        (Primrec.snd.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd))

theorem rationalConstant_primrec :
    Primrec
      (rationalConstant (n := n) (b := b) :
        RationalCode →
          ComplexObservableCode (dimension n b)) :=
  Primrec.pair PolynomialCode.constant_primrec
    (Primrec.const PolynomialCode.zero)

theorem liftBase_primrec :
    Primrec
      (liftBase :
        PolynomialCode n →
          PolynomialCode (dimension n b)) :=
  PolynomialBlockCode.left_primrec

theorem liftBasePair_primrec :
    Primrec
      (liftBasePair (b := b) :
        ComplexObservableCode n →
          ComplexObservableCode (dimension n b)) :=
  Primrec.pair
    (liftBase_primrec.comp Primrec.fst)
    (liftBase_primrec.comp Primrec.snd)

private theorem frequencyAt_primrec (a : Fin b) :
    Primrec
      (fun frequency : Fin b → PolynomialCode n ↦
        frequency a) :=
  Primrec.fin_app.comp Primrec.id (Primrec.const a)

theorem logarithmicCoefficientCode_primrec
    (a : Fin b) :
    Primrec
      (fun frequency : Fin b → PolynomialCode n ↦
        logarithmicCoefficientCode frequency a) := by
  exact
    Primrec.pair
      (Primrec.const PolynomialCode.zero)
      (PolynomialCode.mul_primrec.comp
        (Primrec.const
          (PolynomialCode.constant quarterCode))
        (liftBase_primrec.comp
          (frequencyAt_primrec a)))

theorem gaugeVelocityCode_primrec
    (a : Fin b) :
    Primrec
      (fun frequency : Fin b → PolynomialCode n ↦
        gaugeVelocityCode frequency a) :=
  mul_primrec.comp
    (logarithmicCoefficientCode_primrec a)
    (Primrec.const (gaugeCode (n := n) a))

/-- Uniform primitive-recursive compiler for the complete extended field. -/
theorem fieldCode_primrec :
    Primrec
      (fun input : FieldCompilerInput n b ↦
        fieldCode input.1 input.2) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro k
  obtain ⟨i | r, rfl⟩ := finSumFinEquiv.surjective k
  · exact
      (liftBase_primrec.comp
        (Primrec.fin_app.comp Primrec.fst
          (Primrec.const i))).of_eq fun input ↦
            (fieldCode_baseEmbedding input.1 input.2 i).symm
  · obtain ⟨⟨a, j⟩, rfl⟩ :=
      finProdFinEquiv.surjective r
    fin_cases j
    · exact
        ((Primrec.fst.comp
          (gaugeVelocityCode_primrec a)).comp
            Primrec.snd).of_eq fun input ↦
              (fieldCode_gaugeReIndex
                input.1 input.2 a).symm
    · exact
        ((Primrec.snd.comp
          (gaugeVelocityCode_primrec a)).comp
            Primrec.snd).of_eq fun input ↦
              (fieldCode_gaugeImIndex
                input.1 input.2 a).symm

theorem fieldCode_computable :
    Computable
      (fun input : FieldCompilerInput n b ↦
        fieldCode input.1 input.2) :=
  fieldCode_primrec.to_comp

private theorem scaleAt_primrec (a : Fin b) :
    Primrec
      (fun input : ResidualCompilerInput n b ↦
        input.1 a) :=
  Primrec.fin_app.comp Primrec.fst (Primrec.const a)

private theorem characterAt_primrec (a : Fin b) :
    Primrec
      (fun input : ResidualCompilerInput n b ↦
        input.2 a) :=
  Primrec.fin_app.comp Primrec.snd (Primrec.const a)

theorem scaledCharacterCode_primrec
    (a : Fin b) :
    Primrec
      (fun input : ResidualCompilerInput n b ↦
        scaledCharacterCode input.1 input.2 a) :=
  mul_primrec.comp
    (rationalConstant_primrec.comp
      (scaleAt_primrec a))
    (liftBasePair_primrec.comp
      (characterAt_primrec a))

theorem residualPairCode_primrec
    (a : Fin b) :
    Primrec
      (fun input : ResidualCompilerInput n b ↦
        residualPairCode input.1 input.2 a) :=
  sub_primrec.comp
    (Primrec.const
      (pow (gaugeCode (n := n) a) 4))
    (scaledCharacterCode_primrec a)

theorem residualReCode_primrec
    (a : Fin b) :
    Primrec
      (fun input : ResidualCompilerInput n b ↦
        residualReCode input.1 input.2 a) :=
  Primrec.fst.comp (residualPairCode_primrec a)

theorem residualImCode_primrec
    (a : Fin b) :
    Primrec
      (fun input : ResidualCompilerInput n b ↦
        residualImCode input.1 input.2 a) :=
  Primrec.snd.comp (residualPairCode_primrec a)

/-- Uniform primitive-recursive compiler for all fourth-root residuals. -/
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
        (residualCode_gaugeBlockEmbedding
          input.1 input.2 a (0 : Fin 2)).symm
  · exact
      (residualImCode_primrec a).of_eq fun input ↦
        (residualCode_gaugeBlockEmbedding
          input.1 input.2 a (1 : Fin 2)).symm

theorem residualCode_computable :
    Computable
      (fun input : ResidualCompilerInput n b ↦
        residualCode input.1 input.2) :=
  residualCode_primrec.to_comp

theorem outputCode_primrec :
    Primrec
      (fun observable : ObservableFamily n b ↦
        fun a ↦ outputCode observable a) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro a
  exact
    mul_primrec.comp
      (Primrec.const (gaugeCode (n := n) a))
      (liftBasePair_primrec.comp
        (Primrec.fin_app.comp Primrec.id
          (Primrec.const a)))

theorem outputCode_computable :
    Computable
      (fun observable : ObservableFamily n b ↦
        fun a ↦ outputCode observable a) :=
  outputCode_primrec.to_comp

end HGAS.ComplexGaugeFamilyPolynomialCode
