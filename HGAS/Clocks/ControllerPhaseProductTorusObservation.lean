import HGAS.Clocks.CircleRealCoordinates
import HGAS.Clocks.ControllerPhaseProductCharacterCode
import HGAS.Clocks.PhaseClockFlow
import Mathlib.Tactic

/-!
# Reading unit real phase pairs as an additive torus

The polynomial clock compiler stores a phase as two real coordinates
`(c,d)`.  On the invariant locus `c²+d²=1`, these coordinates determine a
point of the multiplicative unit circle and hence, through the standard
homeomorphism `ℝ/ℤ ≃ Circle`, a point of the additive unit circle.

This file packages that conversion for a continuous family of structured
controller--phase states.  Its main crosswalk says that Mathlib's
multivariate Fourier character is *literally* the compiler's signed-power
character.  In particular, negative exponents agree because conjugation is
inversion on the unit circle.
-/

noncomputable section

open Complex Function

namespace HGAS.Clocks.ControllerPhaseProductTorusObservation

open ControllerPhaseProductPolynomialCode
open ControllerPhaseProductCharacterCode

variable {q : ℕ}
variable {X : Type*}

/-- Package the real phase pair of one clock as a multiplicative circle
point. -/
def phaseCircle
    (z : X → StateFamily q ℝ)
    (hphase :
      ∀ x i, Controller.phaseRadiusSq (z x i).phase = 1)
    (x : X) (i : Fin q) : Circle :=
  CircleRealCoordinates.circle
    ⟨![(z x i).phase.c, (z x i).phase.d], by
      simpa [Controller.phaseRadiusSq] using hphase x i⟩

@[simp]
theorem phaseCircle_coe
    (z : X → StateFamily q ℝ)
    (hphase :
      ∀ x i, Controller.phaseRadiusSq (z x i).phase = 1)
    (x : X) (i : Fin q) :
    (phaseCircle z hphase x i : ℂ) =
      ⟨(z x i).phase.c, (z x i).phase.d⟩ := by
  apply Complex.ext <;>
    simp [phaseCircle, CircleRealCoordinates.circle]

/-- The additive-torus observation determined by the real phase pairs. -/
def phase
    (z : X → StateFamily q ℝ)
    (hphase :
      ∀ x i, Controller.phaseRadiusSq (z x i).phase = 1)
    (x : X) :
    UnitAddTorus (Fin q) :=
  fun i ↦
    PhaseClockFlow.unitAddCircleHomeomorph.symm
      (phaseCircle z hphase x i)

/-- Continuity of the structured real state implies continuity of its
additive phase observation. -/
theorem continuous_phase
    [TopologicalSpace X]
    (z : X → StateFamily q ℝ)
    (hc : ∀ i, Continuous fun x ↦ (z x i).phase.c)
    (hd : ∀ i, Continuous fun x ↦ (z x i).phase.d)
    (hphase :
      ∀ x i, Controller.phaseRadiusSq (z x i).phase = 1) :
    Continuous (phase z hphase) := by
  apply continuous_pi
  intro i
  apply PhaseClockFlow.unitAddCircleHomeomorph.symm.continuous.comp
  apply CircleRealCoordinates.continuous_circle.comp
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  fin_cases j
  · exact hc i
  · exact hd i

/-- A one-dimensional Fourier character of the extracted additive phase
is the signed-power convention used by the polynomial compiler. -/
theorem fourier_phase_apply
    (z : X → StateFamily q ℝ)
    (hphase :
      ∀ x i, Controller.phaseRadiusSq (z x i).phase = 1)
    (x : X) (i : Fin q) (e : ℤ) :
    fourier e (phase z hphase x i) =
      signedPowerValue (z x) i e := by
  rw [fourier_apply, AddCircle.toCircle_zsmul]
  have hbase :
      AddCircle.toCircle (phase z hphase x i) =
        phaseCircle z hphase x i := by
    unfold phase
    rw [← PhaseClockFlow.unitAddCircleHomeomorph_apply]
    exact
      PhaseClockFlow.unitAddCircleHomeomorph.apply_symm_apply
        (phaseCircle z hphase x i)
  rw [hbase]
  have hcoe :
      (phaseCircle z hphase x i : ℂ) =
        phaseValue (z x) i := by
    simpa only [phaseValue] using
      phaseCircle_coe z hphase x i
  have hnorm :
      ‖phaseValue (z x) i‖ = 1 := by
    rw [← hcoe]
    exact Circle.norm_coe _
  cases e with
  | ofNat n =>
      change
        (phaseCircle z hphase x i : ℂ) ^ n =
          signedPowerValue (z x) i (Int.ofNat n)
      rw [hcoe]
      simp [signedPowerValue]
  | negSucc n =>
      rw [Circle.coe_zpow, zpow_negSucc, hcoe, ← inv_pow]
      rw [Complex.inv_eq_conj hnorm]
      rw [signedPowerValue, if_pos (Int.negSucc_lt_zero n)]
      rfl

/-- Exact multivariate character crosswalk. -/
theorem mFourier_phase
    (z : X → StateFamily q ℝ)
    (hphase :
      ∀ x i, Controller.phaseRadiusSq (z x i).phase = 1)
    (x : X) (a : Fin q → ℤ) :
    UnitAddTorus.mFourier a (phase z hphase x) =
      characterValue a (z x) := by
  classical
  unfold UnitAddTorus.mFourier characterValue
  simp only [ContinuousMap.coe_mk, List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro i _
  exact fourier_phase_apply z hphase x i (a i)

end HGAS.Clocks.ControllerPhaseProductTorusObservation
