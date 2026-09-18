import HGAS.Accumulator.PolynomialComputability
import HGAS.Clocks.RHSOscillatorPolynomialCode
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Effectivity of the right-hand-side oscillator compiler

For fixed finite base and frequency dimensions, the entire augmentation

```
  (F, (a, ν)) ↦ (F, X' = 4(∑aᵢνᵢ)Y,
                     Y' = -4(∑aᵢνᵢ)X)
```

is primitive recursive on raw rational sparse-polynomial codes.  In
particular, arbitrarily large input integers occur only as ordinary rational
coefficient codes; they do not change the number of variables or the state
degree.
-/

namespace HGAS.Clocks.RHSOscillatorPolynomialCode

open HGAS

variable {n q : ℕ}

theorem liftBase_primrec :
    Primrec (liftBase :
      PolynomialCode n → PolynomialCode (dimension n)) :=
  PolynomialBlockCode.left_primrec

theorem weightedFrequencyCode_primrec :
    Primrec
      (fun input :
          (Fin q → RationalCode) ×
            (Fin q → PolynomialCode n) ↦
        weightedFrequencyCode input.1 input.2) := by
  apply PolynomialCode.sumCodes_primrec.comp
  apply Primrec.list_ofFn
  intro i
  exact
    PolynomialCode.mul_primrec.comp
      (PolynomialCode.constant_primrec.comp
        (Primrec.fin_app.comp Primrec.fst
          (Primrec.const i)))
      (liftBase_primrec.comp
        (Primrec.fin_app.comp Primrec.snd
          (Primrec.const i)))

theorem xFieldCode_primrec :
    Primrec
      (fun input :
          (Fin q → RationalCode) ×
            (Fin q → PolynomialCode n) ↦
        xFieldCode input.1 input.2) := by
  exact
    PolynomialCode.mul_primrec.comp
      (PolynomialCode.mul_primrec.comp
        (Primrec.const fourCode)
        weightedFrequencyCode_primrec)
      (Primrec.const yCode)

theorem yFieldCode_primrec :
    Primrec
      (fun input :
          (Fin q → RationalCode) ×
            (Fin q → PolynomialCode n) ↦
        yFieldCode input.1 input.2) := by
  exact
    PolynomialCode.neg_primrec.comp
      (PolynomialCode.mul_primrec.comp
        (PolynomialCode.mul_primrec.comp
          (Primrec.const fourCode)
          weightedFrequencyCode_primrec)
        (Primrec.const xCode))

/-- Runtime input of the complete oscillator augmentation. -/
abbrev CompilerInput (n q : ℕ) :=
  PolynomialFieldCode n ×
    ((Fin q → RationalCode) ×
      (Fin q → PolynomialCode n))

/-- The complete augmented-field compiler is primitive recursive. -/
theorem fieldCode_primrec :
    Primrec
      (fun input : CompilerInput n q ↦
        fieldCode input.1 input.2.1 input.2.2) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro k
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective k
  · exact
      (liftBase_primrec.comp
          (Primrec.fin_app.comp Primrec.fst
          (Primrec.const i))).of_eq fun input ↦ by
            simp only [fieldCode, Equiv.symm_apply_apply,
              Function.id_def]
  · fin_cases j
    · exact
        (xFieldCode_primrec.comp Primrec.snd).of_eq
          fun input ↦ by
            simp [fieldCode]
    · exact
        (yFieldCode_primrec.comp Primrec.snd).of_eq
          fun input ↦ by
            simp [fieldCode]

theorem fieldCode_computable :
    Computable
      (fun input : CompilerInput n q ↦
        fieldCode input.1 input.2.1 input.2.2) :=
  fieldCode_primrec.to_comp

end HGAS.Clocks.RHSOscillatorPolynomialCode
