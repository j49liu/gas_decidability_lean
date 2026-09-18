import HGAS.Modular.UnaryNormalizedSolution

/-!
# Normalization bridge for the square-root unary system

This is the square-root analogue of `UnaryNormalizedSolution`.  It exposes
the four base equations together with the `p₂,p₃,p₄,H` equations and
records, once, the factor two between Mathlib's normalized modular
derivative and the derivation used in the paper.
-/

namespace HGAS.Modular

open UpperHalfPlane Complex

noncomputable section

local notation "Dₘ" => Derivative.normalizedDerivOfComplex

/-- Square-root unary equations in Mathlib's normalization. -/
structure IsMathlibNormalizedUnaryRootSolution
    (z : ℍ → UnaryRootState ℂ) : Prop where
  base : IsMathlibNormalizedUnarySolution
    (fun τ ↦ (z τ).toUnaryModularState)
  p2_eq : ∀ τ,
    Dₘ (fun w ↦ (z w).p2) τ =
      (1 / 2 : ℂ) * (UnaryRootState.vectorField (z τ)).p2
  p3_eq : ∀ τ,
    Dₘ (fun w ↦ (z w).p3) τ =
      (1 / 2 : ℂ) * (UnaryRootState.vectorField (z τ)).p3
  p4_eq : ∀ τ,
    Dₘ (fun w ↦ (z w).p4) τ =
      (1 / 2 : ℂ) * (UnaryRootState.vectorField (z τ)).p4
  H_eq : ∀ τ,
    Dₘ (fun w ↦ (z w).H) τ =
      (1 / 2 : ℂ) * (UnaryRootState.vectorField (z τ)).H

/-- Square-root unary equations in the paper's normalization
`Dₚ=2Dₘ`. -/
structure IsPaperNormalizedUnaryRootSolution
    (z : ℍ → UnaryRootState ℂ) : Prop where
  base : IsPaperNormalizedUnarySolution
    (fun τ ↦ (z τ).toUnaryModularState)
  p2_eq : ∀ τ,
    2 * Dₘ (fun w ↦ (z w).p2) τ =
      (UnaryRootState.vectorField (z τ)).p2
  p3_eq : ∀ τ,
    2 * Dₘ (fun w ↦ (z w).p3) τ =
      (UnaryRootState.vectorField (z τ)).p3
  p4_eq : ∀ τ,
    2 * Dₘ (fun w ↦ (z w).p4) τ =
      (UnaryRootState.vectorField (z τ)).p4
  H_eq : ∀ τ,
    2 * Dₘ (fun w ↦ (z w).H) τ =
      (UnaryRootState.vectorField (z τ)).H

/-- Convert all eight Mathlib-normalized equations to the paper
normalization. -/
theorem IsMathlibNormalizedUnaryRootSolution.toPaper
    {z : ℍ → UnaryRootState ℂ}
    (hz : IsMathlibNormalizedUnaryRootSolution z) :
    IsPaperNormalizedUnaryRootSolution z where
  base := hz.base.toPaper
  p2_eq τ := by
    rw [hz.p2_eq τ]
    ring
  p3_eq τ := by
    rw [hz.p3_eq τ]
    ring
  p4_eq τ := by
    rw [hz.p4_eq τ]
    ring
  H_eq τ := by
    rw [hz.H_eq τ]
    ring

/-- Convert all eight paper-normalized equations back to Mathlib
normalization. -/
theorem IsPaperNormalizedUnaryRootSolution.toMathlib
    {z : ℍ → UnaryRootState ℂ}
    (hz : IsPaperNormalizedUnaryRootSolution z) :
    IsMathlibNormalizedUnaryRootSolution z where
  base := hz.base.toMathlib
  p2_eq τ := by
    have h := hz.p2_eq τ
    linear_combination (1 / 2 : ℂ) * h
  p3_eq τ := by
    have h := hz.p3_eq τ
    linear_combination (1 / 2 : ℂ) * h
  p4_eq τ := by
    have h := hz.p4_eq τ
    linear_combination (1 / 2 : ℂ) * h
  H_eq τ := by
    have h := hz.H_eq τ
    linear_combination (1 / 2 : ℂ) * h

/-- Equivalence of the two normalizations for the full root system. -/
theorem mathlibRootNormalized_iff_paperRootNormalized
    (z : ℍ → UnaryRootState ℂ) :
    IsMathlibNormalizedUnaryRootSolution z ↔
      IsPaperNormalizedUnaryRootSolution z :=
  ⟨IsMathlibNormalizedUnaryRootSolution.toPaper,
    IsPaperNormalizedUnaryRootSolution.toMathlib⟩

end

end HGAS.Modular
