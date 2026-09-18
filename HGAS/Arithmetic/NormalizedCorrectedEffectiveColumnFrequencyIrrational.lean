import HGAS.Arithmetic.DQLNonzeroLinearAugmentation
import HGAS.Arithmetic.NormalizedCorrectedEffectiveSelectedDetectorPhase
import Mathlib.Tactic

/-!
# Irrationality of every effective detector-column frequency ratio

The three-moment rigidity theorem needs the ratio between the linear
elliptic frequency and the private modular frequency to be irrational.
For the effective compiler this is a finite-character consequence of
prime-radical nonresonance.

The reusable first theorem below contains the whole arithmetic idea.
On a torus with no annihilating integer character, pair the frequency
vector with:

* the private character supported at one variable coordinate, and
* a nonzero linear character supported only at equation coordinates.

If the quotient of those pairings were `a / b`, then
`b • linear - a • private` would annihilate the frequency vector.
Nonresonance makes this character zero.  Its private coordinate gives
`a = 0`, and a nonzero linear coordinate then gives `b = 0`, contrary
to the choice of denominator.

The second half transfers this elementary statement to the literal
frequencies of a selected effective compiler orbit.  The common factor
`2π`, converting detector turns to physical angular frequency, cancels
from the quotient.
-/

noncomputable section

open scoped BigOperators

namespace HGAS.NormalizedCorrectedEffectiveColumnFrequencyIrrational

open HGAS
open HGAS.Clocks
open DQLNonzeroLinearAugmentation
open NormalizedCorrectedEffectiveCompilerInput
open NormalizedCorrectedEffectiveSelectedDetectorPhase
open NormalizedCorrectedFixedDetectorBidirectionalValidityOrbit
open NormalizedCorrectedFixedDetectorSelectedFactorization
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
open
  NormalizedCorrectedEffectiveSelectedDetectorPhase.SelectedBidirectionalValidityOrbit
open
  NormalizedCorrectedFixedDetectorSelectedFactorization.SelectedBidirectionalValidityOrbit

variable {eqs vars : ℕ}

/-- A syntactically nonzero linear column gives a nontrivial detector
character. -/
theorem linearCharacter_ne_zero_of_hasNonzeroLinearColumn
    (I : DQLSystem eqs vars)
    (hcolumns : HasNonzeroLinearColumn I)
    (j : Fin vars) :
    DetectorCharacterCode.linearCharacter I j ≠ 0 := by
  obtain ⟨row, hrow⟩ := hcolumns j
  intro hzero
  have hrowzero := congrFun hzero (Sum.inr row)
  simp only [DetectorCharacterCode.linearCharacter, Pi.zero_apply] at hrowzero
  exact hrow hrowzero

/-- Abstract finite-character form of the private/linear irrationality
argument. -/
theorem linear_div_private_pairing_irrational
    (I : DQLSystem eqs vars)
    (hcolumns : HasNonzeroLinearColumn I)
    (frequency : DetectorPhase eqs vars → ℝ)
    (hfrequency :
      RadicalIndependence.HasNoNontrivialIntegerCharacter frequency)
    (j : Fin vars) :
    Irrational
      ((∑ phase : DetectorPhase eqs vars,
          (DetectorCharacterCode.linearCharacter I j phase : ℝ) *
            frequency phase) /
        ∑ phase : DetectorPhase eqs vars,
          (DetectorCharacterCode.privateCharacter j phase : ℝ) *
            frequency phase) := by
  let privatePairing : ℝ :=
    ∑ phase : DetectorPhase eqs vars,
      (DetectorCharacterCode.privateCharacter j phase : ℝ) *
        frequency phase
  let linearPairing : ℝ :=
    ∑ phase : DetectorPhase eqs vars,
      (DetectorCharacterCode.linearCharacter I j phase : ℝ) *
        frequency phase
  have hprivate : privatePairing ≠ 0 := by
    intro hzero
    have hcharacter :=
      hfrequency (DetectorCharacterCode.privateCharacter j) hzero
    have hj := congrFun hcharacter (Sum.inl j)
    simp [DetectorCharacterCode.privateCharacter] at hj
  rw [irrational_iff_ne_rational]
  intro a b hb heq
  have hbR : (b : ℝ) ≠ 0 := by
    exact_mod_cast hb
  have hcross :
      (b : ℝ) * linearPairing -
          (a : ℝ) * privatePairing = 0 := by
    change linearPairing / privatePairing =
      (a : ℝ) / (b : ℝ) at heq
    have hmul :=
      (div_eq_div_iff hprivate hbR).mp heq
    exact sub_eq_zero.mpr (by simpa [mul_comm] using hmul)
  let annihilator : DetectorPhase eqs vars → ℤ :=
    fun phase ↦
      b * DetectorCharacterCode.linearCharacter I j phase -
        a * DetectorCharacterCode.privateCharacter j phase
  have hannihilates :
      (∑ phase : DetectorPhase eqs vars,
          (annihilator phase : ℝ) * frequency phase) = 0 := by
    calc
      (∑ phase : DetectorPhase eqs vars,
          (annihilator phase : ℝ) * frequency phase) =
          (b : ℝ) * linearPairing -
            (a : ℝ) * privatePairing := by
              dsimp only [annihilator, linearPairing, privatePairing]
              push_cast
              rw [Finset.mul_sum, Finset.mul_sum,
                ← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro phase _
              ring
      _ = 0 := hcross
  have hannihilator : annihilator = 0 :=
    hfrequency annihilator hannihilates
  have ha : a = 0 := by
    have hj := congrFun hannihilator (Sum.inl j)
    simp [annihilator, DetectorCharacterCode.privateCharacter,
      DetectorCharacterCode.linearCharacter] at hj
    omega
  obtain ⟨row, hrow⟩ := hcolumns j
  have hrowzero := congrFun hannihilator (Sum.inr row)
  simp only [annihilator, DetectorCharacterCode.linearCharacter,
    DetectorCharacterCode.privateCharacter, mul_zero, sub_zero,
    Pi.zero_apply] at hrowzero
  have : b = 0 := by
    exact (mul_eq_zero.mp hrowzero).resolve_right hrow
  exact hb this

variable (D : DQLSystem eqs vars)
variable
  (O :
    SelectedBidirectionalValidityOrbit
      (NormalizedCorrectedEffectiveCompilerInput.compilerInput D))

private abbrev B :=
  O.toSelectedTwoSidedValidityOrbit

private abbrev parameters :
    Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → RationalCode :=
  NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
    (NormalizedCorrectedEffectiveCompilerInput.compilerInput D)

private abbrev controller :
    Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
      Controller.ControllerState ℝ :=
  NormalizedCorrectedFixedDetectorColumnTrajectory.SelectedTwoSidedValidityOrbit.initialController
    (B D O)

/-- A flattened compiler-character frequency is `2π` times its pairing
with the actual detector frequency in turns. -/
theorem characterFrequency_eq_two_pi_mul_physicalPairing
    (a : DetectorPhase eqs vars → ℤ) :
    LockedControllerPhaseTrajectory.characterFrequency
        (parameters D) (controller D O)
        (DetectorCharacterCode.flattenCharacter a) =
      2 * Real.pi *
        ∑ phase : DetectorPhase eqs vars,
          (a phase : ℝ) *
            physicalDetectorTurnsFrequency O phase := by
  rw [CanonicalFixedDetectorFourierCrosswalk.flattenedCharacterFrequency_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro phase _
  unfold physicalDetectorTurnsFrequency physicalFundamentalTurnsFrequency
  field_simp [Real.pi_ne_zero]

/-- The effective angular-frequency quotient of every column with a
nonzero linear coefficient is irrational. -/
theorem numberFrequency_div_omegaFrequency_irrational
    (hcolumns : HasNonzeroLinearColumn D)
    (j : Fin vars) :
    Irrational
      (CanonicalFixedDetectorTrajectory.numberFrequency
          (parameters D) D (controller D O) j /
        CanonicalFixedDetectorTrajectory.omegaFrequency
          (parameters D) (controller D O) j) := by
  let privatePairing : ℝ :=
    ∑ phase : DetectorPhase eqs vars,
      (DetectorCharacterCode.privateCharacter j phase : ℝ) *
        physicalDetectorTurnsFrequency O phase
  let linearPairing : ℝ :=
    ∑ phase : DetectorPhase eqs vars,
      (DetectorCharacterCode.linearCharacter D j phase : ℝ) *
        physicalDetectorTurnsFrequency O phase
  have hirrational :
      Irrational (linearPairing / privatePairing) := by
    exact
      linear_div_private_pairing_irrational D hcolumns
        (physicalDetectorTurnsFrequency O)
        (physicalDetectorTurnsFrequency_hasNoCharacter D O) j
  have homega :
      CanonicalFixedDetectorTrajectory.omegaFrequency
          (parameters D) (controller D O) j =
        2 * Real.pi * privatePairing := by
    rw [CanonicalFixedDetectorFourierCrosswalk.omegaFrequency_eq_characterFrequency]
    exact characterFrequency_eq_two_pi_mul_physicalPairing D O _
  have hnumber :
      CanonicalFixedDetectorTrajectory.numberFrequency
          (parameters D) D (controller D O) j =
        2 * Real.pi * linearPairing := by
    rw [CanonicalFixedDetectorFourierCrosswalk.numberFrequency_eq_characterFrequency]
    exact characterFrequency_eq_two_pi_mul_physicalPairing D O _
  have hratio :
      CanonicalFixedDetectorTrajectory.numberFrequency
            (parameters D) D (controller D O) j /
          CanonicalFixedDetectorTrajectory.omegaFrequency
            (parameters D) (controller D O) j =
        linearPairing / privatePairing := by
    rw [hnumber, homega]
    field_simp [Real.pi_ne_zero]
  rw [hratio]
  exact hirrational

end HGAS.NormalizedCorrectedEffectiveColumnFrequencyIrrational
