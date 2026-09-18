import HGAS.Clocks.ControllerPhaseProductCharacterDegrees
import HGAS.Compiler.ComplexGaugeFamilyPolynomialCode
import Mathlib.Tactic

/-!
# Degree ledger for finite fourth-root gauge families

If the base field has degree `D` and the gauge frequency codes have degree
`E`, adjoining

```text
                         G' = (i/4)νG
```

raises the field bound only to `max D (E+1)`.

If the linked characters have degree `C`, the fourth-root residuals
`G⁴-λχ` have degree at most `max 4 C`.  Finally, multiplying a base
observable of degree `T` by its gauge has degree at most `T+1`.
All bounds are uniform in the number of gauge blocks.
-/

namespace HGAS.ComplexGaugeFamilyPolynomialCode

open Clocks.ControllerPhaseProductCharacterCode

variable {n b D E C T : ℕ}

def ObservableFamilyTermsDegreeLE
    (d : ℕ) (p : ObservableFamily n b) : Prop :=
  ∀ a, TermsDegreeLE d (p a)

instance observableFamilyTermsDegreeLEDecidable
    (d : ℕ) (p : ObservableFamily n b) :
    Decidable (ObservableFamilyTermsDegreeLE d p) := by
  unfold ObservableFamilyTermsDegreeLE
  infer_instance

theorem termsDegreeLE_sub
    {p r : ComplexObservableCode (dimension n b)}
    (hp : TermsDegreeLE D p)
    (hr : TermsDegreeLE D r) :
    TermsDegreeLE D (sub p r) :=
  ⟨PolynomialCode.termsDegreeLE_sub hp.1 hr.1,
    PolynomialCode.termsDegreeLE_sub hp.2 hr.2⟩

theorem rationalConstant_termsDegreeLE
    (c : RationalCode) :
    TermsDegreeLE 0
      (rationalConstant (n := n) (b := b) c) :=
  ⟨PolynomialCode.termsDegreeLE_constant c,
    PolynomialCode.termsDegreeLE_zero 0⟩

theorem liftBase_termsDegreeLE
    {p : PolynomialCode n}
    (hp : PolynomialCode.TermsDegreeLE D p) :
    PolynomialCode.TermsDegreeLE D
      (liftBase (b := b) p) :=
  PolynomialCode.termsDegreeLE_injectVariables _ hp

theorem liftBasePair_termsDegreeLE
    {p : ComplexObservableCode n}
    (hp : TermsDegreeLE D p) :
    TermsDegreeLE D (liftBasePair (b := b) p) :=
  ⟨liftBase_termsDegreeLE (b := b) hp.1,
    liftBase_termsDegreeLE (b := b) hp.2⟩

theorem gaugeCode_termsDegreeLE
    (a : Fin b) :
    TermsDegreeLE 1 (gaugeCode (n := n) a) :=
  ⟨PolynomialCode.termsDegreeLE_varCode _,
    PolynomialCode.termsDegreeLE_varCode _⟩

theorem logarithmicCoefficientCode_termsDegreeLE
    (frequency : Fin b → PolynomialCode n)
    (hfrequency :
      ∀ a, PolynomialCode.TermsDegreeLE E (frequency a))
    (a : Fin b) :
    TermsDegreeLE E
      (logarithmicCoefficientCode frequency a) := by
  constructor
  · exact PolynomialCode.termsDegreeLE_zero E
  · have hquarter :
        PolynomialCode.TermsDegreeLE 0
          (PolynomialCode.constant quarterCode :
            PolynomialCode (dimension n b)) :=
      PolynomialCode.termsDegreeLE_constant quarterCode
    have hlift :=
      liftBase_termsDegreeLE (b := b) (hfrequency a)
    simpa [logarithmicCoefficientCode] using
      PolynomialCode.termsDegreeLE_mul hquarter hlift

theorem gaugeVelocityCode_termsDegreeLE
    (frequency : Fin b → PolynomialCode n)
    (hfrequency :
      ∀ a, PolynomialCode.TermsDegreeLE E (frequency a))
    (a : Fin b) :
    TermsDegreeLE (E + 1)
      (gaugeVelocityCode frequency a) := by
  exact
    termsDegreeLE_mul
      (logarithmicCoefficientCode_termsDegreeLE
        frequency hfrequency a)
      (gaugeCode_termsDegreeLE a)

theorem fieldCode_termsDegreeLE
    (F : PolynomialFieldCode n)
    (frequency : Fin b → PolynomialCode n)
    (hF : ∀ i, PolynomialCode.TermsDegreeLE D (F i))
    (hfrequency :
      ∀ a, PolynomialCode.TermsDegreeLE E (frequency a)) :
    ∀ k,
      PolynomialCode.TermsDegreeLE (max D (E + 1))
        (fieldCode F frequency k) := by
  intro k
  obtain ⟨i | r, rfl⟩ := finSumFinEquiv.surjective k
  · change
      PolynomialCode.TermsDegreeLE (max D (E + 1))
        (fieldCode F frequency (baseEmbedding i))
    rw [fieldCode_baseEmbedding]
    exact
      (liftBase_termsDegreeLE (b := b) (hF i)).promote
        (Nat.le_max_left D (E + 1))
  · obtain ⟨⟨a, j⟩, rfl⟩ :=
      finProdFinEquiv.surjective r
    fin_cases j
    · change
        PolynomialCode.TermsDegreeLE (max D (E + 1))
          (fieldCode F frequency (gaugeReIndex a))
      rw [fieldCode_gaugeReIndex]
      exact
        (gaugeVelocityCode_termsDegreeLE
          frequency hfrequency a).1.promote
            (Nat.le_max_right D (E + 1))
    · change
        PolynomialCode.TermsDegreeLE (max D (E + 1))
          (fieldCode F frequency (gaugeImIndex a))
      rw [fieldCode_gaugeImIndex]
      exact
        (gaugeVelocityCode_termsDegreeLE
          frequency hfrequency a).2.promote
            (Nat.le_max_right D (E + 1))

theorem scaledCharacterCode_termsDegreeLE
    (scale : Fin b → RationalCode)
    (character : ObservableFamily n b)
    (hcharacter : ObservableFamilyTermsDegreeLE C character)
    (a : Fin b) :
    TermsDegreeLE C
      (scaledCharacterCode scale character a) := by
  simpa [Nat.zero_add] using
    termsDegreeLE_mul
      (rationalConstant_termsDegreeLE
        (n := n) (b := b) (scale a))
      (liftBasePair_termsDegreeLE (b := b) (hcharacter a))

theorem residualPairCode_termsDegreeLE
    (scale : Fin b → RationalCode)
    (character : ObservableFamily n b)
    (hcharacter : ObservableFamilyTermsDegreeLE C character)
    (a : Fin b) :
    TermsDegreeLE (max 4 C)
      (residualPairCode scale character a) := by
  have hg4 :
      TermsDegreeLE 4 (pow (gaugeCode (n := n) a) 4) := by
    simpa using
      termsDegreeLE_pow (gaugeCode_termsDegreeLE (n := n) a) 4
  have hc :=
    scaledCharacterCode_termsDegreeLE
      scale character hcharacter a
  exact
    termsDegreeLE_sub
      ⟨hg4.1.promote (Nat.le_max_left 4 C),
        hg4.2.promote (Nat.le_max_left 4 C)⟩
      ⟨hc.1.promote (Nat.le_max_right 4 C),
        hc.2.promote (Nat.le_max_right 4 C)⟩

theorem residualReCode_termsDegreeLE
    (scale : Fin b → RationalCode)
    (character : ObservableFamily n b)
    (hcharacter : ObservableFamilyTermsDegreeLE C character)
    (a : Fin b) :
    PolynomialCode.TermsDegreeLE (max 4 C)
      (residualReCode scale character a) :=
  (residualPairCode_termsDegreeLE
    scale character hcharacter a).1

theorem residualImCode_termsDegreeLE
    (scale : Fin b → RationalCode)
    (character : ObservableFamily n b)
    (hcharacter : ObservableFamilyTermsDegreeLE C character)
    (a : Fin b) :
    PolynomialCode.TermsDegreeLE (max 4 C)
      (residualImCode scale character a) :=
  (residualPairCode_termsDegreeLE
    scale character hcharacter a).2

theorem residualCode_termsDegreeLE
    (scale : Fin b → RationalCode)
    (character : ObservableFamily n b)
    (hcharacter : ObservableFamilyTermsDegreeLE C character) :
    ∀ k,
      PolynomialCode.TermsDegreeLE (max 4 C)
        (residualCode scale character k) := by
  intro k
  obtain ⟨⟨a, j⟩, rfl⟩ :=
    finProdFinEquiv.surjective k
  change
    PolynomialCode.TermsDegreeLE (max 4 C)
      (residualCode scale character
        (gaugeBlockEmbedding a j))
  rw [residualCode_gaugeBlockEmbedding]
  fin_cases j
  · exact
      residualReCode_termsDegreeLE
        scale character hcharacter a
  · exact
      residualImCode_termsDegreeLE
        scale character hcharacter a

theorem outputCode_termsDegreeLE
    (observable : ObservableFamily n b)
    (hobservable : ObservableFamilyTermsDegreeLE T observable)
    (a : Fin b) :
    TermsDegreeLE (T + 1)
      (outputCode observable a) := by
  simpa [Nat.add_comm] using
    termsDegreeLE_mul
      (gaugeCode_termsDegreeLE (n := n) a)
      (liftBasePair_termsDegreeLE (b := b)
        (hobservable a))

end HGAS.ComplexGaugeFamilyPolynomialCode
