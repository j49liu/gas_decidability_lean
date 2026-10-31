import Stability.Simulation.ClockedMonitorLiftError
import Stability.Simulation.PolynomialFractionSubtraction

/-!
# The monitor's actual polynomial penalty

The penalty is the clock weight times the square of the global weighted
defect. It is a rational polynomial, vanishes on the canonical graph,
and subtracting it leaves the output denominator unchanged. These are
pointwise identities; the integral characterization of halting is a
separate step.
-/

namespace Stability.Simulation.ClockedMonitor

noncomputable section

open AbsFormula

variable {k s : ℕ}

def penaltyPolynomial (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) :
    MvPolynomial (LiftCoordinate program entry initial ε) ℚ :=
  (1 + MvPolynomial.X (Sum.inl MonitorCoordinate.clock) ^ 2) *
    errorWeight program entry initial ε ^ 2 * defectEnergy program entry initial ε

def penalizedOutput (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) : PolynomialFraction (LiftCoordinate program entry initial ε) :=
  PolynomialFraction.subPolynomial (rationalOutput program entry initial ε)
    (penaltyPolynomial program entry initial ε)

theorem defectEnergy_nonneg (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) (y : LiftCoordinate program entry initial ε → ℝ) :
    0 ≤ polynomialValue y (defectEnergy program entry initial ε) :=
  RadicalDefectBounds.defectEnergy_nonneg _ y

theorem penaltyPolynomial_value (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) (y : LiftCoordinate program entry initial ε → ℝ) :
    polynomialValue y (penaltyPolynomial program entry initial ε) =
      (1 + y (Sum.inl .clock) ^ 2) *
        (polynomialValue y (errorWeight program entry initial ε) *
          defectSize program entry initial ε y) ^ 2 := by
  have hsquare := Real.sq_sqrt (defectEnergy_nonneg program entry initial ε y)
  simp only [penaltyPolynomial, polynomialValue, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_add, MvPolynomial.eval₂_one, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_X]
  change (1 + y (Sum.inl .clock) ^ 2) *
      polynomialValue y (errorWeight program entry initial ε) ^ 2 *
        polynomialValue y (defectEnergy program entry initial ε) = _
  rw [mul_pow, defectSize, hsquare]
  dsimp only [polynomialValue]
  ring

theorem penaltyPolynomial_nonneg (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ) (y : LiftCoordinate program entry initial ε → ℝ) :
    0 ≤ polynomialValue y (penaltyPolynomial program entry initial ε) := by
  rw [penaltyPolynomial_value]
  positivity

theorem penalizedOutput_denominator_one_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (y : LiftCoordinate program entry initial ε → ℝ) :
    1 ≤ polynomialValue y (penalizedOutput program entry initial ε).denominator :=
  rationalOutput_denominator_one_le program entry initial hε hεOne y

theorem penalizedOutput_value (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (y : LiftCoordinate program entry initial ε → ℝ) :
    PolynomialFraction.value y (penalizedOutput program entry initial ε) =
      PolynomialFraction.value y (rationalOutput program entry initial ε) -
        polynomialValue y (penaltyPolynomial program entry initial ε) :=
  PolynomialFraction.value_subPolynomial _ _ _
    (ne_of_gt (zero_lt_one.trans_le
      (rationalOutput_denominator_one_le program entry initial hε hεOne y)))

theorem defectEnergy_liftGraph (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (x : MonitorCoordinate k → ℝ) :
    polynomialValue (liftGraph program entry initial ε x)
      (defectEnergy program entry initial ε) = 0 := by
  rw [defectEnergy, RadicalDefectBounds.defectEnergy_value]
  apply Finset.sum_eq_zero
  intro j _
  have hj := finiteLiftRoots_fourth (precision program entry initial ε)
    (formulaList program entry initial) x
    (precision_one_le program entry initial hε hεOne x) j
  rw [liftRadicand_value] at hj
  change polynomialValue (Sum.elim x (finiteLiftRoots (precision program entry initial ε)
    (formulaList program entry initial) x)) _ ^ 2 = 0
  rw [RadicalDefectBounds.defect_value, hj, sub_self, zero_pow (by decide)]

theorem penaltyPolynomial_liftGraph (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (x : MonitorCoordinate k → ℝ) :
    polynomialValue (liftGraph program entry initial ε x)
      (penaltyPolynomial program entry initial ε) = 0 := by
  rw [penaltyPolynomial_value]
  simp [defectSize, defectEnergy_liftGraph program entry initial hε hεOne]

/-- Penalization leaves the intended smoothed output unchanged on the
actual graph, not on a postulated solution of the constraint equations. -/
theorem penalizedOutput_liftGraph (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ} (hε : 0 < ε) (hεOne : ε ≤ 1)
    (x : MonitorCoordinate k → ℝ) :
    PolynomialFraction.value (liftGraph program entry initial ε x)
      (penalizedOutput program entry initial ε) =
      smoothEval (polynomialValue x (precision program entry initial ε)) x outputFormula := by
  rw [penalizedOutput_value program entry initial hε hεOne,
    penaltyPolynomial_liftGraph program entry initial hε hεOne, sub_zero,
    rationalOutput_on_graph program entry initial hε hεOne]

end

end Stability.Simulation.ClockedMonitor
