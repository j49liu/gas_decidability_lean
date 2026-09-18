import HGAS.Modular.ExplicitGammaTwoHaarProbabilityCusp

/-!
# Bridge from explicit Haar probability to the legacy chosen witness

`gammaTwoFrameHaarProbability` was defined earlier as `Classical.choose`
from the proposition asserting existence of a right-invariant
probability.  In contrast,
`gammaTwoExplicitFrameHaarProbability` is definitionally tied to the
normalized explicit fundamental-domain measure.

Mathematically the two probabilities are equal by uniqueness of
invariant measure on the homogeneous space
`Γ(2) \ SL(2, ℝ)`.  Mathlib currently has the corresponding uniqueness
machinery for Haar measures on groups and for quotients by normal
subgroups, but not for a non-normal lattice quotient.  The proposition
below isolates exactly that final identification.  Every geometric,
measurability, normalization, and cusp-marginal reduction is
unconditional in the imported module.
-/

namespace HGAS.Modular

open _root_.MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-- The weakest exact statement needed to transfer the unconditional
explicit cusp theorem to the legacy `Classical.choose` witness. -/
def GammaTwoChosenHaarIdentification : Prop :=
  gammaTwoFrameHaarProbability =
    gammaTwoExplicitFrameHaarProbability

/-- A standard uniqueness theorem for right-invariant probabilities
would imply the exact chosen-witness identification. -/
def GammaTwoRightInvariantProbabilityUnique : Prop :=
  ∀ ν₁ ν₂ : ProbabilityMeasure GammaTwoFrameQuotient,
    IsRightInvariantFrameProbability ν₁ →
    IsRightInvariantFrameProbability ν₂ →
    ν₁ = ν₂

theorem GammaTwoRightInvariantProbabilityUnique.chosenHaarIdentification
    (hunique : GammaTwoRightInvariantProbabilityUnique) :
    GammaTwoChosenHaarIdentification :=
  hunique gammaTwoFrameHaarProbability
    gammaTwoExplicitFrameHaarProbability
    gammaTwoFrameHaarProbability_rightInvariant
    gammaTwoExplicitFrameHaarProbability_rightInvariant

/-- Under precisely the chosen-witness identification, the legacy
canonical probability inherits the explicit positive cusp marginal. -/
theorem exists_gammaTwoFrameHaarProbability_cuspMarginal
    (hidentify : GammaTwoChosenHaarIdentification)
    (Y : ℝ) (hY : 1 < Y) :
    ∃ c : ℝ≥0, c ≠ 0 ∧
      c • HGAS.Dynamics.cuspHeightMeasure Y ≤
        Measure.map (gammaTwoExplicitCuspHeight Y)
          (gammaTwoFrameHaarProbability :
            Measure GammaTwoFrameQuotient) := by
  rw [hidentify]
  exact
    exists_gammaTwoExplicitFrameHaarProbability_cuspMarginal
      Y hY

/-- The legacy chosen Haar marginal version of the reciprocal-slowdown
divergence theorem, conditional only on the exact identification above. -/
theorem chosenGammaTwoHaar_reciprocalSlowdown_lintegral_eq_top
    (hidentify : GammaTwoChosenHaarIdentification)
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X)
    (proj : X → GammaTwoFrameQuotient)
    (hproj : Measurable proj)
    (reciprocalSlowdown : X → ℝ≥0∞)
    (Y : ℝ) (hY : 1 < Y)
    (Ychart : ℝ)
    (M : ℕ) (hM : 2 ≤ M)
    (hmarginal :
      Measure.map proj μ =
        (gammaTwoFrameHaarProbability :
          Measure GammaTwoFrameQuotient))
    (κ : ℝ≥0) (hκ : κ ≠ 0)
    (hchart :
      ∀ᵐ x ∂μ,
        (κ : ℝ≥0∞) ^ M *
            HGAS.Dynamics.cuspTailHeightPower
              Ychart M
              (gammaTwoExplicitCuspHeight Y (proj x)) ≤
          reciprocalSlowdown x) :
    ∫⁻ x, reciprocalSlowdown x ∂μ = ∞ := by
  change
    gammaTwoFrameHaarProbability =
      gammaTwoExplicitFrameHaarProbability at hidentify
  rw [hidentify] at hmarginal
  exact
    explicitGammaTwoHaar_reciprocalSlowdown_lintegral_eq_top
      μ proj hproj reciprocalSlowdown
      Y hY Ychart M hM hmarginal
      κ hκ hchart

end

end HGAS.Modular
