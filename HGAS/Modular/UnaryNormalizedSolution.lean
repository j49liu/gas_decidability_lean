import HGAS.Modular.UnaryAlgebra
import Mathlib.NumberTheory.ModularForms.Derivative

/-!
# Normalization bridge for the unary modular system

The polynomial vector field in `UnaryAlgebra` is written using the
derivation used in the paper,

```
                    Dₚ = q d/dq = (π i)⁻¹ d/dτ.
```

Mathlib's modular-form library instead uses

```
                    Dₘ = (2 π i)⁻¹ d/dτ.
```

Thus `Dₚ = 2 Dₘ`.  This small module records that factor once and for all.
It is deliberately independent of theta identities: any four
upper-half-plane functions satisfying the component equations can use the
same interface.
-/

namespace HGAS.Modular

open UpperHalfPlane Complex

noncomputable section

local notation "Dₘ" => Derivative.normalizedDerivOfComplex

/-- Assemble four scalar functions into a unary modular state. -/
def unaryStateOfFunctions
    (A C E Y : ℍ → ℂ) (τ : ℍ) :
    UnaryModularState ℂ where
  A := A τ
  C := C τ
  E := E τ
  Y := Y τ

@[simp] theorem unaryStateOfFunctions_A
    (A C E Y : ℍ → ℂ) (τ : ℍ) :
    (unaryStateOfFunctions A C E Y τ).A = A τ := rfl

@[simp] theorem unaryStateOfFunctions_C
    (A C E Y : ℍ → ℂ) (τ : ℍ) :
    (unaryStateOfFunctions A C E Y τ).C = C τ := rfl

@[simp] theorem unaryStateOfFunctions_E
    (A C E Y : ℍ → ℂ) (τ : ℍ) :
    (unaryStateOfFunctions A C E Y τ).E = E τ := rfl

@[simp] theorem unaryStateOfFunctions_Y
    (A C E Y : ℍ → ℂ) (τ : ℍ) :
    (unaryStateOfFunctions A C E Y τ).Y = Y τ := rfl

/-- The four equations in Mathlib's normalization
`Dₘ = (2πi)⁻¹ d/dτ`.  Each right-hand side is one half of the paper's
polynomial vector field. -/
structure IsMathlibNormalizedUnarySolution
    (z : ℍ → UnaryModularState ℂ) : Prop where
  A_eq : ∀ τ,
    Dₘ (fun w ↦ (z w).A) τ =
      (1 / 2 : ℂ) * (UnaryModularState.vectorField (z τ)).A
  C_eq : ∀ τ,
    Dₘ (fun w ↦ (z w).C) τ =
      (1 / 2 : ℂ) * (UnaryModularState.vectorField (z τ)).C
  E_eq : ∀ τ,
    Dₘ (fun w ↦ (z w).E) τ =
      (1 / 2 : ℂ) * (UnaryModularState.vectorField (z τ)).E
  Y_eq : ∀ τ,
    Dₘ (fun w ↦ (z w).Y) τ =
      (1 / 2 : ℂ) * (UnaryModularState.vectorField (z τ)).Y

/-- The same four equations in the paper's normalization
`Dₚ = q d/dq = 2Dₘ`. -/
structure IsPaperNormalizedUnarySolution
    (z : ℍ → UnaryModularState ℂ) : Prop where
  A_eq : ∀ τ,
    2 * Dₘ (fun w ↦ (z w).A) τ =
      (UnaryModularState.vectorField (z τ)).A
  C_eq : ∀ τ,
    2 * Dₘ (fun w ↦ (z w).C) τ =
      (UnaryModularState.vectorField (z τ)).C
  E_eq : ∀ τ,
    2 * Dₘ (fun w ↦ (z w).E) τ =
      (UnaryModularState.vectorField (z τ)).E
  Y_eq : ∀ τ,
    2 * Dₘ (fun w ↦ (z w).Y) τ =
      (UnaryModularState.vectorField (z τ)).Y

/-- Multiplying the Mathlib-normalized equations by two gives exactly the
paper-normalized polynomial system. -/
theorem IsMathlibNormalizedUnarySolution.toPaper
    {z : ℍ → UnaryModularState ℂ}
    (hz : IsMathlibNormalizedUnarySolution z) :
    IsPaperNormalizedUnarySolution z where
  A_eq τ := by
    rw [hz.A_eq τ]
    ring
  C_eq τ := by
    rw [hz.C_eq τ]
    ring
  E_eq τ := by
    rw [hz.E_eq τ]
    ring
  Y_eq τ := by
    rw [hz.Y_eq τ]
    ring

/-- Dividing the paper-normalized equations by two recovers Mathlib's
normalization. -/
theorem IsPaperNormalizedUnarySolution.toMathlib
    {z : ℍ → UnaryModularState ℂ}
    (hz : IsPaperNormalizedUnarySolution z) :
    IsMathlibNormalizedUnarySolution z where
  A_eq τ := by
    have h := hz.A_eq τ
    linear_combination (1 / 2 : ℂ) * h
  C_eq τ := by
    have h := hz.C_eq τ
    linear_combination (1 / 2 : ℂ) * h
  E_eq τ := by
    have h := hz.E_eq τ
    linear_combination (1 / 2 : ℂ) * h
  Y_eq τ := by
    have h := hz.Y_eq τ
    linear_combination (1 / 2 : ℂ) * h

/-- The two normalizations define equivalent solution predicates. -/
theorem mathlibNormalized_iff_paperNormalized
    (z : ℍ → UnaryModularState ℂ) :
    IsMathlibNormalizedUnarySolution z ↔
      IsPaperNormalizedUnarySolution z :=
  ⟨IsMathlibNormalizedUnarySolution.toPaper,
    IsPaperNormalizedUnarySolution.toMathlib⟩

end

end HGAS.Modular
