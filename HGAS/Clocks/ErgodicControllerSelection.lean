import HGAS.Clocks.ControllerFlow
import HGAS.Dynamics.ErgodicFactor
import HGAS.Dynamics.ErgodicFixedSupport

/-!
# Ergodicity selects one polynomial-controller equilibrium

For a controller parameter `p > 1`, every invariant probability of the
circle flow is concentrated on the four controller equilibria.  This is the
wandering-strip conclusion proved in `ControllerFlow`.  Every one of those
equilibria is a fixed point of the flow.

Ergodicity now has a simple but important consequence: an ergodic
probability cannot split its mass between several fixed points.  The general
fixed-support theorem therefore makes it a Dirac probability, and the
support conclusion ensures that the selected atom is one of the actual
polynomial equilibria.  We then record the locking equation and its exact
coordinate-square form.

The final results allow the controller to be observed as a continuous flow
factor of a larger dynamical system.  Ergodicity descends through the factor,
so the same one-equilibrium selection applies to the controller marginal.
-/

noncomputable section

open Filter MeasureTheory Set

namespace HGAS.Clocks.ControllerFlow

local instance : MeasurableSpace Circle :=
  borel Circle

local instance : BorelSpace Circle :=
  ⟨rfl⟩

/-- An ergodic invariant probability of the controller flow is exactly a
Dirac probability at one of the four controller equilibria. -/
theorem exists_eq_diracProba_at_controllerEquilibrium
    (p : ℝ) (hp : 1 < p)
    (μ : ProbabilityMeasure Circle)
    (hμ :
      HGAS.Dynamics.IsErgodicInvariantProbability
        (controllerFlow p hp) μ) :
    ∃ z : Circle,
      z ∈ controllerEquilibria p ∧
        μ = MeasureTheory.diracProba z := by
  let μinv :
      HGAS.Dynamics.InvariantProbabilityMeasure
        (controllerFlow p hp) :=
    ⟨μ, hμ.invariant⟩
  have hsupport :
      (μ : Measure Circle) ((controllerEquilibria p)ᶜ) = 0 := by
    simpa only [μinv] using
      invariantProbability_controllerEquilibria_compl_eq_zero
        p hp μinv
  have hmem :
      ∀ᵐ z ∂(μ : Measure Circle), z ∈ controllerEquilibria p :=
    mem_ae_iff.mpr hsupport
  have hfixed :
      ∀ᵐ z ∂(μ : Measure Circle),
        HGAS.Dynamics.InvariantProbabilityMeasure.IsFlowFixedPoint
          (controllerFlow p hp) z :=
    hmem.mono fun _ hz ↦
      isFlowFixedPoint_of_mem_controllerEquilibria p hp hz
  obtain ⟨z, hdirac⟩ :=
    HGAS.Dynamics.exists_eq_diracProba_of_isErgodicInvariantProbability_ae_fixed
      μ hμ hfixed
  have hz : z ∈ controllerEquilibria p := by
    by_contra hz
    have hsupport' := hsupport
    rw [hdirac] at hsupport'
    change Measure.dirac z ((controllerEquilibria p)ᶜ) = 0 at hsupport'
    rw [Measure.dirac_apply_of_mem hz] at hsupport'
    exact one_ne_zero hsupport'
  exact ⟨z, hz, hdirac⟩

/-- Polynomial-field form of the selected equilibrium: the chosen atom is
an equilibrium of the literal cubic controller vector field. -/
theorem exists_eq_diracProba_at_polynomialControllerEquilibrium
    (p : ℝ) (hp : 1 < p)
    (μ : ProbabilityMeasure Circle)
    (hμ :
      HGAS.Dynamics.IsErgodicInvariantProbability
        (controllerFlow p hp) μ) :
    ∃ z : Circle,
      μ = MeasureTheory.diracProba z ∧
        HGAS.Clocks.Controller.IsControllerEquilibrium p
          (circleControllerState z) := by
  obtain ⟨z, hz, hdirac⟩ :=
    exists_eq_diracProba_at_controllerEquilibrium p hp μ hμ
  exact
    ⟨z, hdirac,
      (mem_controllerEquilibria_iff_polynomialEquilibrium
        p hp z).mp hz⟩

/-- Locking-equation form of ergodic controller selection. -/
theorem exists_eq_diracProba_at_lockedController
    (p : ℝ) (hp : 1 < p)
    (μ : ProbabilityMeasure Circle)
    (hμ :
      HGAS.Dynamics.IsErgodicInvariantProbability
        (controllerFlow p hp) μ) :
    ∃ z : Circle,
      μ = MeasureTheory.diracProba z ∧
        p * (z : ℂ).re ^ 2 = 1 := by
  obtain ⟨z, hz, hdirac⟩ :=
    exists_eq_diracProba_at_controllerEquilibrium p hp μ hμ
  have hsquares :=
    (mem_controllerEquilibria_iff_coordinate_squares
      p hp z).mp hz
  have hpne : p ≠ 0 := ne_of_gt (zero_lt_one.trans hp)
  refine ⟨z, hdirac, ?_⟩
  rw [hsquares.1]
  field_simp

/-- Exact coordinate-square form of ergodic controller selection.  This
exhibits all numerical information used later by the locked phase clocks. -/
theorem exists_eq_diracProba_at_lockedCoordinateSquares
    (p : ℝ) (hp : 1 < p)
    (μ : ProbabilityMeasure Circle)
    (hμ :
      HGAS.Dynamics.IsErgodicInvariantProbability
        (controllerFlow p hp) μ) :
    ∃ z : Circle,
      μ = MeasureTheory.diracProba z ∧
        (z : ℂ).re ^ 2 = 1 / p ∧
        (z : ℂ).im ^ 2 = 1 - 1 / p := by
  obtain ⟨z, hz, hdirac⟩ :=
    exists_eq_diracProba_at_controllerEquilibrium p hp μ hμ
  exact
    ⟨z, hdirac,
      (mem_controllerEquilibria_iff_coordinate_squares
        p hp z).mp hz⟩

/-- Phase-clock form of the selection theorem: at the selected controller
atom, the square of the signed frequency `p r` is exactly `p`. -/
theorem exists_eq_diracProba_with_lockedFrequency_sq
    (p : ℝ) (hp : 1 < p)
    (μ : ProbabilityMeasure Circle)
    (hμ :
      HGAS.Dynamics.IsErgodicInvariantProbability
        (controllerFlow p hp) μ) :
    ∃ z : Circle,
      μ = MeasureTheory.diracProba z ∧
        HGAS.Clocks.Controller.lockedFrequency p
            (circleControllerState z) ^ 2 =
          p := by
  obtain ⟨z, hdirac, hlock⟩ :=
    exists_eq_diracProba_at_lockedController p hp μ hμ
  exact
    ⟨z, hdirac,
      HGAS.Clocks.Controller.lockedFrequency_sq_of_lock
        p (circleControllerState z) hlock⟩

section Factor

variable {X : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  {ϕ : Flow ℝ X}

/-- If a continuous equivariant observation of an ergodic flow is a
controller, then the pushed controller marginal is a Dirac probability at
one controller equilibrium. -/
theorem exists_controllerFactorMap_eq_diracProba_at_equilibrium
    (p : ℝ) (hp : 1 < p)
    (μ : ProbabilityMeasure X)
    (hμ : HGAS.Dynamics.IsErgodicInvariantProbability ϕ μ)
    (π : X → Circle) (hπ : Continuous π)
    (hequiv :
      ∀ t : ℝ,
        Function.Semiconj π (ϕ t) (controllerFlow p hp t)) :
    ∃ z : Circle,
      z ∈ controllerEquilibria p ∧
        μ.map hπ.measurable.aemeasurable =
          MeasureTheory.diracProba z := by
  exact
    exists_eq_diracProba_at_controllerEquilibrium p hp
      (μ.map hπ.measurable.aemeasurable)
      (hμ.mapEquivariant π hπ hequiv)

/-- Coordinate-square form of controller-factor selection. -/
theorem exists_controllerFactorMap_eq_diracProba_at_lockedCoordinateSquares
    (p : ℝ) (hp : 1 < p)
    (μ : ProbabilityMeasure X)
    (hμ : HGAS.Dynamics.IsErgodicInvariantProbability ϕ μ)
    (π : X → Circle) (hπ : Continuous π)
    (hequiv :
      ∀ t : ℝ,
        Function.Semiconj π (ϕ t) (controllerFlow p hp t)) :
    ∃ z : Circle,
      μ.map hπ.measurable.aemeasurable =
          MeasureTheory.diracProba z ∧
        (z : ℂ).re ^ 2 = 1 / p ∧
        (z : ℂ).im ^ 2 = 1 - 1 / p := by
  exact
    exists_eq_diracProba_at_lockedCoordinateSquares p hp
      (μ.map hπ.measurable.aemeasurable)
      (hμ.mapEquivariant π hπ hequiv)

end Factor

end HGAS.Clocks.ControllerFlow
