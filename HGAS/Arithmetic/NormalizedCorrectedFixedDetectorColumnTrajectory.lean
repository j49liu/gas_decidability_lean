import HGAS.Arithmetic.FixedDetectorPrivateFrequency
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorTwoSidedCompleteControllerLocking
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorTwoSidedStructuredOrbit
import HGAS.Modular.RecurrentUnarySelectorReduction
import Mathlib.Tactic

/-!
# A selected detector column as a recurrent linked-Jacobi trajectory

After controller locking, every readout in one detector column is constant
for all physical time.  The complete reverse compiler can therefore turn
that column into an ordinary scaled linked-Jacobi trajectory.

This file names the actual signed real frequencies rather than replacing
them by a normalization:

```
  ω_j = private modular frequency,
  N_j = linear-character frequency,
  κZ  = (ω_j + N_j)/2,
  κΦ  = i ω_j.
```

It also projects the common return sequence of the full detector point to
the fourteen complex linked coordinates.
-/

namespace HGAS.NormalizedCorrectedFixedDetectorColumnTrajectory

open HGAS
open HGAS.Clocks
open HGAS.Modular
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorTwoSidedStructuredOrbit
open NormalizedCorrectedFixedDetectorTwoSidedCompleteStructure
open NormalizedCorrectedFixedDetectorTwoSidedCompleteControllerLocking
open NormalizedCorrectedFixedDetectorTwoSidedControllerLocking.SelectedTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorTwoSidedStructuredOrbit.SelectedTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorTwoSidedCompleteStructure.SelectedTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorTwoSidedCompleteControllerLocking.SelectedTwoSidedValidityOrbit

noncomputable section

variable {eqs vars : ℕ}
variable
  {u :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      eqs vars}

namespace SelectedTwoSidedValidityOrbit

variable (O : SelectedTwoSidedValidityOrbit u)

/-- The complete linked state in detector column `j`. -/
def linkedColumn (j : Fin vars) (t : ℝ) :
    LinkedJacobiState ℂ :=
  (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
    O.physicalPoint t).base.base.source.linked j

/-- Controller family at physical time zero. -/
def initialController
    (i : Fin (FixedDetectorPolynomialCode.clockCount eqs vars)) :
    Controller.ControllerState ℝ :=
  ((FixedDetectorReverseTrajectoryCrosswalk.recoveredState
    O.physicalPoint 0).base.base.source.controllers i).controller

/-- Actual signed private modular frequency of column `j`. -/
def columnOmega (j : Fin vars) : ℝ :=
  CanonicalFixedDetectorTrajectory.omegaFrequency
    (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
    (initialController O) j

/-- Actual signed linear-character frequency of column `j`. -/
def columnNumber (j : Fin vars) : ℝ :=
  CanonicalFixedDetectorTrajectory.numberFrequency
    (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
    (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
    (initialController O) j

/-- Elliptic clock of the recovered linked column. -/
def columnKappaZ (j : Fin vars) : ℂ :=
  ((((columnOmega O j) + columnNumber O j) / 2 : ℝ) : ℂ)

/-- Modular clock of the recovered linked column. -/
def columnKappaPhi (j : Fin vars) : ℂ :=
  Complex.I * columnOmega O j

/-- The private controller readout is constant for all physical time. -/
theorem omega_readout_eq_columnOmega
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (j : Fin vars)
    (t : ℝ) :
    ControllerProductLinkedJacobiFamilyPolynomialCode.omega
        (fun a i ↦
          (RationalCode.decode
            (DetectorCharacterCode.omegaWeights
              (eqs := eqs) a i) : ℝ))
        (fun i ↦
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
        (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
          O.physicalPoint t).base.base.source j =
      columnOmega O j := by
  unfold
    ControllerProductLinkedJacobiFamilyPolynomialCode.omega
    ControllerPhaseProductLinearFrequencyCode.value
    columnOmega CanonicalFixedDetectorTrajectory.omegaFrequency
    initialController
  apply Finset.sum_congr rfl
  intro i _
  rw [controller_state_eq_zero O hscale hp t i]

/-- The linear-character controller readout is constant for all physical
time. -/
theorem number_readout_eq_columnNumber
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (j : Fin vars)
    (t : ℝ) :
    ControllerProductLinkedJacobiFamilyPolynomialCode.number
        (fun a i ↦
          (RationalCode.decode
            (DetectorCharacterCode.numberWeights
              (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
              a i) : ℝ))
        (fun i ↦
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
        (FixedDetectorReverseTrajectoryCrosswalk.recoveredState
          O.physicalPoint t).base.base.source j =
      columnNumber O j := by
  unfold
    ControllerProductLinkedJacobiFamilyPolynomialCode.number
    ControllerPhaseProductLinearFrequencyCode.value
    columnNumber CanonicalFixedDetectorTrajectory.numberFrequency
    initialController
  apply Finset.sum_congr rfl
  intro i _
  rw [controller_state_eq_zero O hscale hp t i]

/-- The recovered column is a complete linked-Jacobi trajectory with its
literal signed detector clocks. -/
theorem linkedColumn_isScaledTrajectory
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (j : Fin vars) :
    IsScaledLinkedJacobiTrajectory
      (columnKappaZ O j) (columnKappaPhi O j)
      (linkedColumn O j) := by
  apply
    FixedDetectorReverseTrajectoryCrosswalk.linked_isScaledTrajectory
      (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters u)
      (NormalizedCorrectedFixedDetectorCompactSourceCode.system u)
      O.physicalPoint
      (physicalPoint_isStructuredTrajectory O)
      j
  · intro t
    unfold columnKappaZ
      ControllerProductLinkedJacobiFamilyPolynomialCode.kappaZ
    rw [omega_readout_eq_columnOmega O hscale hp j t,
      number_readout_eq_columnNumber O hscale hp j t]
  · intro t
    unfold columnKappaPhi
      ControllerProductLinkedJacobiFamilyPolynomialCode.kappaPhi
    rw [omega_readout_eq_columnOmega O hscale hp j t]

/-- Exact square of the signed modular frequency. -/
theorem columnOmega_sq
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (j : Fin vars) :
    (columnOmega O j) ^ 2 =
      16 *
        (RationalCode.decode
          (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
            u (FixedDetectorPrivateFrequency.privateClockIndex j)) :
          ℝ) := by
  apply
    FixedDetectorPrivateFrequency.omegaFrequency_sq_of_unit_equilibrium
  · exact
      (clockRadii_one_physicalTime O hscale 0).1
        (FixedDetectorPrivateFrequency.privateClockIndex j)
  · exact
      controller_equilibrium_at_zero O hscale hp
        (FixedDetectorPrivateFrequency.privateClockIndex j)

/-- The signed modular frequency never vanishes. -/
theorem columnOmega_ne_zero
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (j : Fin vars) :
    columnOmega O j ≠ 0 := by
  apply
    FixedDetectorPrivateFrequency.omegaFrequency_ne_zero_of_unit_equilibrium
  · exact hp _
  · exact
      (clockRadii_one_physicalTime O hscale 0).1
        (FixedDetectorPrivateFrequency.privateClockIndex j)
  · exact
      controller_equilibrium_at_zero O hscale hp
        (FixedDetectorPrivateFrequency.privateClockIndex j)

end SelectedTwoSidedValidityOrbit

end

end HGAS.NormalizedCorrectedFixedDetectorColumnTrajectory
