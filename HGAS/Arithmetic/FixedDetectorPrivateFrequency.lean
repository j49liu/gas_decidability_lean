import HGAS.Arithmetic.CanonicalFixedDetectorFourierCrosswalk
import HGAS.Clocks.Controller
import Mathlib.Tactic

/-!
# Exact signed private frequency of a fixed-detector column

The fourth-power convention in the detector characters makes the private
frequency of column `j` especially simple.  If

```
             i(j) = finSumFinEquiv (Sum.inl j),
```

then

```
             ω_j = 4 p_{i(j)} r_{i(j)}.
```

At a normalized locked controller, `p r² = 1`, so

```
             ω_j² = 16 p_{i(j)}.
```

Thus `ω_j` is nonzero when the compiled controller parameter is greater
than one, but its sign remains the sign of the selected equilibrium
coordinate `r`.  This is the precise sign information needed for the
later time-orientation split.
-/

namespace HGAS.FixedDetectorPrivateFrequency

open HGAS
open HGAS.Clocks

noncomputable section

variable {eqs vars : ℕ}

/-- Clock index supporting the private character of detector column `j`. -/
def privateClockIndex (j : Fin vars) :
    Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) :=
  finSumFinEquiv (Sum.inl j)

/-- The private modular readout is four times its single locked angular
velocity. -/
theorem omegaFrequency_eq_four_mul_privateAngularVelocity
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) :
    CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j =
      4 *
        LockedControllerPhaseTrajectory.angularVelocity
          parameters controller (privateClockIndex j) := by
  rw [CanonicalFixedDetectorFourierCrosswalk.omegaFrequency_eq_characterFrequency]
  unfold LockedControllerPhaseTrajectory.characterFrequency
    DetectorCharacterCode.flattenCharacter privateClockIndex
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp [DetectorCharacterCode.privateCharacter]

/-- Exact squared private frequency on the normalized equilibrium locus. -/
theorem omegaFrequency_sq_of_unit_equilibrium
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars)
    (hunit :
      Controller.controllerRadiusSq
        (controller (privateClockIndex j)) = 1)
    (hequilibrium :
      Controller.IsControllerEquilibrium
        (RationalCode.decode
          (parameters (privateClockIndex j)) : ℝ)
        (controller (privateClockIndex j))) :
    (CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j) ^ 2 =
      16 *
        (RationalCode.decode
          (parameters (privateClockIndex j)) : ℝ) := by
  let p : ℝ :=
    (RationalCode.decode
      (parameters (privateClockIndex j)) : ℝ)
  let r : ℝ := (controller (privateClockIndex j)).r
  have hlock : p * r ^ 2 = 1 := by
    exact
      (Controller.isControllerEquilibrium_iff_lock_of_unit
        p (controller (privateClockIndex j)) hunit).mp
        hequilibrium
  rw [omegaFrequency_eq_four_mul_privateAngularVelocity]
  unfold LockedControllerPhaseTrajectory.angularVelocity
  change (4 * (p * r)) ^ 2 = 16 * p
  calc
    (4 * (p * r)) ^ 2 = 16 * p * (p * r ^ 2) := by ring
    _ = 16 * p := by rw [hlock]; ring

/-- A parameter larger than one makes the signed private frequency
nonzero. -/
theorem omegaFrequency_ne_zero_of_unit_equilibrium
    (parameters :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        RationalCode)
    (controller :
      Fin (CanonicalFixedDetectorTrajectory.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars)
    (hp :
      (1 : ℝ) <
        (RationalCode.decode
          (parameters (privateClockIndex j)) : ℝ))
    (hunit :
      Controller.controllerRadiusSq
        (controller (privateClockIndex j)) = 1)
    (hequilibrium :
      Controller.IsControllerEquilibrium
        (RationalCode.decode
          (parameters (privateClockIndex j)) : ℝ)
        (controller (privateClockIndex j))) :
    CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j ≠ 0 := by
  intro hzero
  have hsquare :=
    omegaFrequency_sq_of_unit_equilibrium
      parameters controller j hunit hequilibrium
  have hp0 :
      0 <
        (RationalCode.decode
          (parameters (privateClockIndex j)) : ℝ) :=
    lt_trans zero_lt_one hp
  have hproduct :
      (16 : ℝ) *
          (RationalCode.decode
            (parameters (privateClockIndex j)) : ℝ) = 0 := by
    calc
      _ =
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j) ^ 2 :=
        hsquare.symm
      _ = 0 := by rw [hzero]; norm_num
  have hparameter :
      (RationalCode.decode
        (parameters (privateClockIndex j)) : ℝ) = 0 :=
    (mul_eq_zero.mp hproduct).resolve_left (by norm_num)
  exact hp0.ne' hparameter

end

end HGAS.FixedDetectorPrivateFrequency
