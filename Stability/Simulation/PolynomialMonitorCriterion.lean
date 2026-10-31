import Stability.Simulation.RationalMonitorCriterion
import Stability.Simulation.ClockedMonitorPenaltyResources
import Stability.Simulation.FiniteOutputTimeChange

/-!
# An actual polynomial field/output pair characterizing halting

The previously constructed common denominator is positive everywhere.
Multiplying both field and penalized output by it produces literal
rational polynomials. Positive finite time change preserves every output
integral, so the rational-monitor criterion transfers to this polynomial
pair. Its dimensions and degree bounds are independent of the loaded
input. A raw-code compiler and the homogeneous stability lift are separate.
-/

namespace Stability.Simulation.ClockedMonitor

noncomputable section

open AbsFormula

variable {k s : ℕ}

def clearedVectorField (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) :
    (LiftCoordinate program entry initial ε → ℝ) → LiftCoordinate program entry initial ε → ℝ :=
  fun y i ↦ polynomialValue y (clearedField program entry initial ε i)

/-- The unchanged output denominator lets the existing common multiplier
clear the penalty without adding any new denominator factors. -/
def clearedPenalizedOutput (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) :
    MvPolynomial (LiftCoordinate program entry initial ε) ℚ :=
  clearedOutput program entry initial ε -
    clearingPolynomial program entry initial ε * penaltyPolynomial program entry initial ε

theorem clearedVectorField_value (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (y : LiftCoordinate program entry initial ε → ℝ) :
    clearedVectorField program entry initial ε y =
      polynomialValue y (clearingPolynomial program entry initial ε) •
        liftedField program entry initial ε y := by
  funext i
  exact clearedFamily_value program entry initial hε hεOne y (some i)

theorem clearedPenalizedOutput_value (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (y : LiftCoordinate program entry initial ε → ℝ) :
    polynomialValue y (clearedPenalizedOutput program entry initial ε) =
      polynomialValue y (clearingPolynomial program entry initial ε) *
        PolynomialFraction.value y (penalizedOutput program entry initial ε) := by
  have ho := clearedFamily_value program entry initial hε hεOne y none
  change polynomialValue y (clearedOutput program entry initial ε) = _ at ho
  rw [clearedPenalizedOutput]
  simp only [polynomialValue, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul]
  change polynomialValue y (clearedOutput program entry initial ε) -
    polynomialValue y (clearingPolynomial program entry initial ε) *
      polynomialValue y (penaltyPolynomial program entry initial ε) = _
  rw [ho, penalizedOutput_value program entry initial hε hεOne, mul_sub]
  rfl

theorem bounded_output_iff_cleared (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1) :
    Stability.HasBoundedFiniteOutput (liftedField program entry initial ε)
        (fun y ↦ PolynomialFraction.value y (penalizedOutput program entry initial ε)) ↔
      Stability.HasBoundedFiniteOutput (clearedVectorField program entry initial ε)
        (fun y ↦ polynomialValue y (clearedPenalizedOutput program entry initial ε)) := by
  have hQ : Continuous (fun y ↦ polynomialValue y (clearingPolynomial program entry initial ε)) :=
    (contDiff_polynomialValue (fun i ↦ by fun_prop)
      (clearingPolynomial program entry initial ε)).continuous
  have h := Stability.hasBoundedFiniteOutput_iff_timeScaled
    (F := liftedField program entry initial ε) hQ
    (continuous_penalizedOutput program entry initial hε hεOne)
    (fun y ↦ zero_lt_one.trans_le (clearingPolynomial_one_le program entry initial hε hεOne y))
  simpa only [← clearedVectorField_value program entry initial hε hεOne,
    ← clearedPenalizedOutput_value program entry initial hε hεOne] using h

theorem halts_iff_bounded_polynomialOutput (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ}
    (hε : 0 < ε) (hεSmall : ε ≤ 1 / 1024) :
    RegisterMachine.Halts program ⟨some entry, initial⟩ ↔
      Stability.HasBoundedFiniteOutput (clearedVectorField program entry initial ε)
        (fun y ↦ polynomialValue y (clearedPenalizedOutput program entry initial ε)) :=
  (halts_iff_bounded_penalizedOutput program entry initial hε hεSmall).trans
    (bounded_output_iff_cleared program entry initial hε (by linarith))

def clearedPenalizedDegreeBound (program : RegisterMachine.Program k s) (entry : Fin s) : ℕ :=
  clearedDegreeBound program entry + penaltyDegreeBound program entry

theorem clearedPenalizedOutput_totalDegree_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) (ε : ℚ) :
    (clearedPenalizedOutput program entry initial ε).totalDegree ≤
      clearedPenalizedDegreeBound program entry := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · exact (clearedOutput_totalDegree_le program entry initial ε).trans (Nat.le_add_right _ _)
  · exact (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add (clearingPolynomial_totalDegree_le program entry initial ε)
        (penaltyPolynomial_totalDegree_le program entry initial ε))

end

end Stability.Simulation.ClockedMonitor
