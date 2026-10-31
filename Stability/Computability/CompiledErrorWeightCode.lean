import Stability.Computability.PolynomialErrorWeightCode
import Stability.Simulation.ClockedMonitorPenalty

/-!
# Decoding error-weight codes for the actual compiled family

The generic sparse-code assembly specializes to the existing formula-family
error weight and to the monitor's polynomial penalty. The hypotheses identify
only the input radicand and numerator codes; no error estimate or penalty
identity is supplied as a hypothesis.
-/

namespace Stability.PolynomialErrorWeightCode

open HGAS Simulation Simulation.AbsFormula

noncomputable section

variable {σ : Type*} [Fintype σ] {n : ℕ}

section Family

variable (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ))
    (e : (σ ⊕ Fin (finiteRadicalFamily L es).rootCount) ≃ Fin n)
    (D : Fin (finiteRadicalFamily L es).rootCount → PolynomialCode n)
    (outputs : Fin es.length → PolynomialCode n)
    (hD : ∀ j, PolynomialCode.decode (D j) =
      MvPolynomial.rename e ((finiteRadicalFamily L es).radicands j))
    (hQ : ∀ i, PolynomialCode.decode (outputs i) =
      MvPolynomial.rename e (CompiledFormulaLift.outputAt L es i).numerator)

include hD hQ

theorem decode_familyWeight_compiled :
    PolynomialCode.decode (familyWeight e D outputs) =
      MvPolynomial.rename e (CompiledFormulaLift.familyErrorWeight L es) :=
  decode_familyWeight e D _ hD outputs _ hQ

theorem decode_penalty_compiled (clock : σ) :
    PolynomialCode.decode (penalty e clock D outputs) =
      MvPolynomial.rename e ((1 + MvPolynomial.X (.inl clock) ^ 2) *
        CompiledFormulaLift.familyErrorWeight L es ^ 2 *
        RadicalDefectBounds.defectEnergy (finiteRadicalFamily L es).radicands) :=
  decode_penalty e clock D _ hD outputs _ hQ

end Family

section Monitor

open ClockedMonitor

variable {k s : ℕ}

theorem decode_penalty_monitor (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) (ε : ℚ)
    (e : LiftCoordinate program entry initial ε ≃ Fin n)
    (D : Fin (finiteRadicalFamily (precision program entry initial ε)
      (formulaList program entry initial)).rootCount → PolynomialCode n)
    (outputs : Fin (formulaList program entry initial).length → PolynomialCode n)
    (hD : ∀ j, PolynomialCode.decode (D j) = MvPolynomial.rename e
      ((finiteRadicalFamily (precision program entry initial ε)
        (formulaList program entry initial)).radicands j))
    (hQ : ∀ i, PolynomialCode.decode (outputs i) = MvPolynomial.rename e
      (CompiledFormulaLift.outputAt (precision program entry initial ε)
        (formulaList program entry initial) i).numerator) :
    PolynomialCode.decode (penalty e MonitorCoordinate.clock D outputs) =
      MvPolynomial.rename e (penaltyPolynomial program entry initial ε) :=
  decode_penalty_compiled (precision program entry initial ε)
    (formulaList program entry initial) e D outputs hD hQ MonitorCoordinate.clock

end Monitor

end

end Stability.PolynomialErrorWeightCode
