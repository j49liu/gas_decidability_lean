import HGAS.Clocks.PhaseClockFlow
import HGAS.Clocks.ScaledRadicalClock
import Mathlib.Tactic

/-!
# Finite products of physical phase clocks

This module lifts the one-circle normalization in `PhaseClockFlow` to an
arbitrary finite family.  A physical phase torus is represented by
`d → Circle`, with angular velocities `ω i` in radians.  Coordinatewise
inverse angle maps give a continuous surjective semiconjugacy to the
standard additive torus translation at frequencies

```
                       ω i / (2π).
```

Combining this with the scaled radical-clock theorem yields the literal
Haar-marginal statement for polynomial phase circles.  Thus the common
`2π` normalization is no longer an implicit hypothesis.
-/

noncomputable section

open Function MeasureTheory

namespace HGAS.Clocks.PhaseTorusFlow

local instance : MeasurableSpace Circle :=
  borel Circle

local instance : BorelSpace Circle :=
  ⟨rfl⟩

variable {d : Type*}

/-- Coordinatewise physical rotation flow on a finite product of circles. -/
def phaseTorusFlow (ω : d → ℝ) : Flow ℝ (d → Circle) where
  toFun t z := fun i ↦
    HGAS.Clocks.PhaseClockFlow.phaseRotationFlow (ω i) t (z i)
  cont' := by
    apply continuous_pi
    intro i
    exact
      (HGAS.Clocks.PhaseClockFlow.phaseRotationFlow (ω i)).continuous
        continuous_fst
        ((continuous_apply i).comp continuous_snd)
  map_add' := by
    intro t u z
    funext i
    exact
      (HGAS.Clocks.PhaseClockFlow.phaseRotationFlow (ω i)).map_add
        t u (z i)
  map_zero' := by
    intro z
    funext i
    exact
      (HGAS.Clocks.PhaseClockFlow.phaseRotationFlow (ω i)).map_zero_apply
        (z i)

@[simp]
theorem phaseTorusFlow_apply
    (ω : d → ℝ) (t : ℝ) (z : d → Circle) (i : d) :
    phaseTorusFlow ω t z i =
      HGAS.Clocks.PhaseClockFlow.phaseRotationFlow
        (ω i) t (z i) :=
  rfl

/-- Convert every physical circle coordinate back to turns. -/
def phaseTorusToTurns
    (z : d → Circle) : UnitAddTorus d :=
  fun i ↦
    HGAS.Clocks.PhaseClockFlow.unitAddCircleHomeomorph.symm (z i)

theorem continuous_phaseTorusToTurns :
    Continuous (phaseTorusToTurns :
      (d → Circle) → UnitAddTorus d) := by
  apply continuous_pi
  intro i
  exact
    HGAS.Clocks.PhaseClockFlow.unitAddCircleHomeomorph.symm.continuous.comp
      (continuous_apply i)

theorem surjective_phaseTorusToTurns :
    Function.Surjective
      (phaseTorusToTurns :
        (d → Circle) → UnitAddTorus d) := by
  intro x
  refine ⟨fun i ↦
    HGAS.Clocks.PhaseClockFlow.unitAddCircleHomeomorph (x i), ?_⟩
  funext i
  exact
    HGAS.Clocks.PhaseClockFlow.unitAddCircleHomeomorph.symm_apply_apply
      (x i)

/-- Physical angular velocities expressed in turns. -/
def turnsFrequency (ω : d → ℝ) : d → ℝ :=
  fun i ↦
    HGAS.Clocks.PhaseClockFlow.radiansToTurnsFrequency (ω i)

theorem turnsFrequency_eq_commonScale
    (ω : d → ℝ) :
    turnsFrequency ω =
      fun i ↦ (1 / (2 * Real.pi)) * ω i := by
  funext i
  unfold turnsFrequency
  unfold HGAS.Clocks.PhaseClockFlow.radiansToTurnsFrequency
  ring

/-- The inverse angle map semiconjugates the physical product flow to the
standard additive torus translation. -/
theorem phaseTorusToTurns_semiconj
    (ω : d → ℝ) (t : ℝ) :
    Function.Semiconj phaseTorusToTurns
      (phaseTorusFlow ω t)
      (HGAS.Clocks.RadicalClock.torusTranslationFlow
        (turnsFrequency ω) t) := by
  intro z
  funext i
  apply
    HGAS.Clocks.PhaseClockFlow.unitAddCircleHomeomorph.injective
  simp only [phaseTorusToTurns, phaseTorusFlow_apply,
    HGAS.Clocks.RadicalClock.torusTranslationFlow_apply,
    Pi.add_apply, HGAS.Clocks.RadicalClock.torusDisplacement,
    turnsFrequency]
  rw [
    HGAS.Clocks.PhaseClockFlow.unitAddCircleHomeomorph.apply_symm_apply]
  have hone :=
    HGAS.Clocks.PhaseClockFlow.unitAddCircleHomeomorph_semiconj
      (ω i) t
      (HGAS.Clocks.PhaseClockFlow.unitAddCircleHomeomorph.symm (z i))
  simpa only [HGAS.Clocks.PhaseClockFlow.turnTranslationFlow_apply,
    HGAS.Clocks.PhaseClockFlow.unitAddCircleHomeomorph.apply_symm_apply]
    using hone.symm

theorem phaseTorusToTurns_isSemiconjugacy
    (ω : d → ℝ) :
    Flow.IsSemiconjugacy phaseTorusToTurns
      (phaseTorusFlow ω)
      (HGAS.Clocks.RadicalClock.torusTranslationFlow
        (turnsFrequency ω)) :=
  ⟨continuous_phaseTorusToTurns,
    surjective_phaseTorusToTurns,
    phaseTorusToTurns_semiconj ω⟩

variable [Fintype d]

/-- Haar marginal for the literal physical product of signed radical phase
clocks. -/
theorem physicalSignedRadicalPhase_marginal_eq_haar
    (p : d → ℕ)
    (hp : ∀ i : d, (p i).Prime)
    (hinjective : Function.Injective p)
    (sign : d → ℤ)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (μ : HGAS.Dynamics.InvariantProbabilityMeasure
      (phaseTorusFlow
        (HGAS.Clocks.RadicalIndependence.signedPrimeSqrtFrequency
          p sign))) :
    (μ.mapEquivariant phaseTorusToTurns
      continuous_phaseTorusToTurns
      (phaseTorusToTurns_semiconj _)).measure =
        HGAS.Clocks.RadicalClock.torusHaarProbability := by
  apply
    HGAS.Clocks.RadicalClock.invariantProbability_eq_torusHaar_of_noCharacter
  rw [turnsFrequency_eq_commonScale]
  exact
    HGAS.Clocks.ScaledRadicalClock.scaledSignedPrimeSqrtFrequency_hasNoCharacter
      (1 / (2 * Real.pi))
      HGAS.Clocks.ScaledRadicalClock.one_div_two_pi_ne_zero
      p hp hinjective sign hsign

/-- Ambient-factor form: an arbitrary invariant joining whose physical
phase projection is equivariant has Haar angle marginal. -/
theorem physicalSignedRadicalPhase_equivariantMarginal_eq_haar
    {K : Type*} [TopologicalSpace K]
    [MeasurableSpace K] [BorelSpace K]
    {ϕ : Flow ℝ K}
    (p : d → ℕ)
    (hp : ∀ i : d, (p i).Prime)
    (hinjective : Function.Injective p)
    (sign : d → ℤ)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (μ : HGAS.Dynamics.InvariantProbabilityMeasure ϕ)
    (phaseProjection : K → (d → Circle))
    (hcontinuous : Continuous phaseProjection)
    (hequivariant : ∀ t : ℝ,
      Function.Semiconj phaseProjection (ϕ t)
        (phaseTorusFlow
          (HGAS.Clocks.RadicalIndependence.signedPrimeSqrtFrequency
            p sign) t)) :
    (μ.mapEquivariant
      (phaseTorusToTurns ∘ phaseProjection)
      (continuous_phaseTorusToTurns.comp hcontinuous)
      (fun t ↦
        (phaseTorusToTurns_semiconj _ t).comp_left
          (hequivariant t))).measure =
        HGAS.Clocks.RadicalClock.torusHaarProbability := by
  apply
    HGAS.Clocks.RadicalClock.invariantProbability_eq_torusHaar_of_noCharacter
  rw [turnsFrequency_eq_commonScale]
  exact
    HGAS.Clocks.ScaledRadicalClock.scaledSignedPrimeSqrtFrequency_hasNoCharacter
      (1 / (2 * Real.pi))
      HGAS.Clocks.ScaledRadicalClock.one_div_two_pi_ne_zero
      p hp hinjective sign hsign

end HGAS.Clocks.PhaseTorusFlow
