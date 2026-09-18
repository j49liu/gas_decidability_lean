import HGAS.Clocks.LockedControllerPhaseTrajectory
import Mathlib.Tactic

/-!
# Closed formulas for characters of a locked phase trajectory

`LockedControllerPhaseTrajectory` proves the differential equation for
every integral character.  When every initial phase is `1`, the solution
also has a useful closed form:

```text
 χ_a(t) = exp(i t ∑_j a_j p_j r_j).
```

This module proves that formula directly from the circle exponential,
including negative exponents.  It is independent of the DQL detector and
can be reused whenever an explicitly aligned character phase is needed.
-/

namespace HGAS.Clocks.LockedControllerPhaseTrajectory

open HGAS
open Complex
open ControllerPhaseProductPolynomialCode
open ControllerPhaseProductCharacterCode

noncomputable section

variable {q : ℕ}

/-- Constant family of unit initial phases. -/
def onePhase : Fin q → Circle :=
  fun _ ↦ 1

/-- Each fundamental phase is the expected complex exponential. -/
theorem phaseValue_onePhase
    (parameters : Fin q → RationalCode)
    (controller : Fin q → Controller.ControllerState ℝ)
    (i : Fin q) (t : ℝ) :
    phaseValue
        (stateFamily parameters controller onePhase t) i =
      Complex.exp
        (((angularVelocity parameters controller i * t : ℝ) : ℂ) *
          Complex.I) := by
  rw [phaseValue_stateFamily]
  simp [onePhase, PhaseClockFlow.phaseRotationFlow_apply,
    Circle.coe_exp]

/-- Closed exponential formula for one signed power, valid for every
integer exponent. -/
theorem signedPowerValue_onePhase
    (parameters : Fin q → RationalCode)
    (controller : Fin q → Controller.ControllerState ℝ)
    (i : Fin q) (e : ℤ) (t : ℝ) :
    signedPowerValue
        (stateFamily parameters controller onePhase t) i e =
      Complex.exp
        ((((e : ℝ) *
            angularVelocity parameters controller i * t : ℝ) : ℂ) *
          Complex.I) := by
  have hphase :=
    phaseValue_onePhase parameters controller i t
  cases e with
  | ofNat n =>
      have hn0 : 0 ≤ Int.ofNat n := by
        exact Int.natCast_nonneg n
      have hn : ¬ Int.ofNat n < 0 :=
        not_lt_of_ge hn0
      simp only [signedPowerValue, hn, if_false]
      change
        phaseValue
              (stateFamily parameters controller onePhase t) i ^ n =
          Complex.exp
            ((((n : ℝ) *
                angularVelocity parameters controller i * t : ℝ) : ℂ) *
              Complex.I)
      rw [hphase, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
  | negSucc n =>
      rw [signedPowerValue, if_pos (Int.negSucc_lt_zero n)]
      rw [hphase]
      change
        (starRingEnd ℂ)
            (Complex.exp
              (((angularVelocity parameters controller i * t : ℝ) : ℂ) *
                Complex.I)) ^ (n + 1) =
          _
      simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
      rw [← Complex.exp_conj]
      rw [← Complex.exp_nat_mul]
      congr 1
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring

/-- Closed exponential formula for a finite integral character. -/
theorem characterValue_onePhase
    (parameters : Fin q → RationalCode)
    (controller : Fin q → Controller.ControllerState ℝ)
    (exponents : Fin q → ℤ) (t : ℝ) :
    characterValue exponents
        (stateFamily parameters controller onePhase t) =
      Complex.exp
        (((characterFrequency parameters controller exponents *
              t : ℝ) : ℂ) *
          Complex.I) := by
  unfold characterValue
  rw [List.prod_ofFn]
  simp_rw [show
    ∀ i : Fin q,
      signedPowerValue
          (stateFamily parameters controller onePhase t) i
          (exponents i) =
        Complex.exp
          ((((exponents i : ℝ) *
              angularVelocity parameters controller i * t : ℝ) : ℂ) *
            Complex.I) by
      intro i
      exact
        signedPowerValue_onePhase
          parameters controller i (exponents i) t]
  rw [← Complex.exp_sum]
  congr 1
  unfold characterFrequency
  push_cast
  rw [← Finset.sum_mul]
  have hsum :
      (∑ x : Fin q,
          (exponents x : ℂ) *
            (angularVelocity parameters controller x : ℂ) * (t : ℂ)) =
        (t : ℂ) *
          ∑ x : Fin q,
            (exponents x : ℂ) *
              (angularVelocity parameters controller x : ℂ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  ring

end

end HGAS.Clocks.LockedControllerPhaseTrajectory
