import HGAS.Clocks.RadicalClock
import Mathlib.Tactic

/-!
# Common rescalings of radical clock frequencies

The algebraic phase equation uses angular velocity in radians, whereas the
standard `UnitAddCircle = ℝ/ℤ` translation coordinate uses turns.  Passing
between them divides every frequency by `2π`.  Rational independence and
unique ergodicity are unchanged by any common nonzero real scale.

This module records that normalization explicitly.  It prevents a hidden
`2π` convention from entering later semiconjugacy arguments.
-/

noncomputable section

open Function MeasureTheory
open scoped BigOperators

namespace HGAS.Clocks.ScaledRadicalClock

variable {d : Type*} [Fintype d]

/-- Multiplying every frequency by one nonzero scalar preserves the absence
of nontrivial integer resonances. -/
theorem hasNoNontrivialIntegerCharacter_smul
    (ω : d → ℝ) (scale : ℝ) (hscale : scale ≠ 0)
    (hω :
      HGAS.Clocks.RadicalIndependence.HasNoNontrivialIntegerCharacter
        ω) :
    HGAS.Clocks.RadicalIndependence.HasNoNontrivialIntegerCharacter
      (fun i ↦ scale * ω i) := by
  intro k hk
  apply hω k
  have hfactor :
      scale * (∑ i : d, (k i : ℝ) * ω i) =
        ∑ i : d, (k i : ℝ) * (scale * ω i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hzero :
      scale * (∑ i : d, (k i : ℝ) * ω i) = 0 := by
    rw [hfactor]
    exact hk
  exact (mul_eq_zero.mp hzero).resolve_left hscale

/-- A commonly scaled signed-prime-root vector. -/
def scaledSignedPrimeSqrtFrequency
    (scale : ℝ) (p : d → ℕ) (sign : d → ℤ) :
    d → ℝ :=
  fun i ↦ scale *
    HGAS.Clocks.RadicalIndependence.signedPrimeSqrtFrequency
      p sign i

theorem scaledSignedPrimeSqrtFrequency_hasNoCharacter
    (scale : ℝ) (hscale : scale ≠ 0)
    (p : d → ℕ)
    (hp : ∀ i : d, (p i).Prime)
    (hinjective : Function.Injective p)
    (sign : d → ℤ)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1) :
    HGAS.Clocks.RadicalIndependence.HasNoNontrivialIntegerCharacter
      (scaledSignedPrimeSqrtFrequency scale p sign) := by
  apply hasNoNontrivialIntegerCharacter_smul _ scale hscale
  exact
    HGAS.Clocks.RadicalIndependence.signedPrimeSqrtFrequency_hasNoNontrivialIntegerCharacter
      p hp hinjective sign hsign

/-- Haar probability remains the unique invariant probability after a
common nonzero rescaling of all signed radical frequencies. -/
theorem scaledSignedPrimeSqrt_uniqueInvariantProbability
    (scale : ℝ) (hscale : scale ≠ 0)
    (p : d → ℕ)
    (hp : ∀ i : d, (p i).Prime)
    (hinjective : Function.Injective p)
    (sign : d → ℤ)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (μ : ProbabilityMeasure (UnitAddTorus d)) :
    HGAS.Dynamics.IsInvariantProbability
          (HGAS.Clocks.RadicalClock.torusTranslationFlow
          (scaledSignedPrimeSqrtFrequency scale p sign)) μ ↔
      μ = HGAS.Clocks.RadicalClock.torusHaarProbability := by
  apply HGAS.Clocks.RadicalClock.isInvariantProbability_iff_eq_torusHaar
  exact scaledSignedPrimeSqrtFrequency_hasNoCharacter
    scale hscale p hp hinjective sign hsign

/-- Equivariant-factor form, suitable for a polynomial ambient flow. -/
theorem scaledSignedPrimeSqrt_equivariantMarginal_eq_haar
    {K : Type*} [TopologicalSpace K]
    [MeasurableSpace K] [BorelSpace K]
    {ϕ : Flow ℝ K}
    (scale : ℝ) (hscale : scale ≠ 0)
    (p : d → ℕ)
    (hp : ∀ i : d, (p i).Prime)
    (hinjective : Function.Injective p)
    (sign : d → ℤ)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (μ : HGAS.Dynamics.InvariantProbabilityMeasure ϕ)
    (π : K → UnitAddTorus d)
    (hπ : Continuous π)
    (hequiv : ∀ t : ℝ,
      Function.Semiconj π (ϕ t)
          (HGAS.Clocks.RadicalClock.torusTranslationFlow
          (scaledSignedPrimeSqrtFrequency scale p sign) t)) :
    (μ.mapEquivariant π hπ hequiv).measure =
      HGAS.Clocks.RadicalClock.torusHaarProbability := by
  apply
    HGAS.Clocks.RadicalClock.invariantProbability_eq_torusHaar_of_noCharacter
  exact scaledSignedPrimeSqrtFrequency_hasNoCharacter
    scale hscale p hp hinjective sign hsign

/-- The turns-per-radian normalization is nonzero. -/
theorem one_div_two_pi_ne_zero :
    (1 / (2 * Real.pi) : ℝ) ≠ 0 := by
  positivity

/-- Concrete no-resonance theorem in the `UnitAddCircle` normalization. -/
theorem turnsNormalizedSignedPrimeSqrt_hasNoCharacter
    (p : d → ℕ)
    (hp : ∀ i : d, (p i).Prime)
    (hinjective : Function.Injective p)
    (sign : d → ℤ)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1) :
    HGAS.Clocks.RadicalIndependence.HasNoNontrivialIntegerCharacter
      (scaledSignedPrimeSqrtFrequency
        (1 / (2 * Real.pi)) p sign) :=
  scaledSignedPrimeSqrtFrequency_hasNoCharacter
    _ one_div_two_pi_ne_zero p hp hinjective sign hsign

end HGAS.Clocks.ScaledRadicalClock
