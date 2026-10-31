import Stability.Computability.ClockedMonitorRationalCode
import Stability.Computability.ClockedMonitorPenaltyCode
import Stability.Computability.PolynomialClearingCode
import Stability.Simulation.PolynomialMonitorCriterion

/-!
# An effective code for the actual penalized polynomial monitor

The code clears the original rational field and output jointly, then
subtracts the same common multiplier times the polynomial penalty.
It therefore represents the literal polynomial pair used by the halting
criterion. Its input-dependent coefficients are primitive recursive and
both decoded degrees have one input-independent bound.
-/

namespace Stability.ClockedMonitorCode

open HGAS Simulation

noncomputable section

variable {k s n : ℕ}

def rationalFamilyCode (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n) :
    Option (Fin n) → (Fin k → ℕ) → PolynomialFractionCode n
  | none => rationalOutputCode program entry ε e
  | some i => rationalFieldCode program entry ε e i

theorem rationalFamilyCode_primrec (program : RegisterMachine.Program k s)
    (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (i : Option (Fin n)) : Primrec (rationalFamilyCode program entry ε e i) := by
  cases i with
  | none => exact rationalOutputCode_primrec program entry ε e
  | some i => exact rationalFieldCode_primrec program entry ε e i

private def familyEquiv (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (initial : Fin k → ℕ) :
    Option (Fin n) ≃ Option (ClockedMonitor.LiftCoordinate program entry initial ε) :=
  Equiv.optionCongr (coordinateEquiv program entry ε e initial).symm

private theorem decode_rationalFamilyCode (program : RegisterMachine.Program k s)
    (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (initial : Fin k → ℕ) (i : Option (Fin n)) :
    PolynomialFractionCode.decode (rationalFamilyCode program entry ε e i initial) =
      PolynomialFractionCode.rename (coordinateEquiv program entry ε e initial)
        (ClockedMonitor.rationalFamily program entry initial ε
          (familyEquiv program entry ε e initial i)) := by
  cases i with
  | none => exact decode_rationalOutputCode program entry ε e initial
  | some i => exact decode_rationalFieldCode program entry ε e i initial

def clearingCode (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (initial : Fin k → ℕ) : PolynomialCode n :=
  PolynomialClearingCode.denominator (fun i ↦ rationalFamilyCode program entry ε e i initial)

def clearedFamilyCode (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (i : Option (Fin n)) (initial : Fin k → ℕ) : PolynomialCode n :=
  PolynomialClearingCode.numerator (fun j ↦ rationalFamilyCode program entry ε e j initial) i

theorem clearingCode_primrec (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n) :
    Primrec (clearingCode program entry ε e) :=
  PolynomialClearingCode.denominator_primrec _ (rationalFamilyCode_primrec program entry ε e)

theorem clearedFamilyCode_primrec (program : RegisterMachine.Program k s)
    (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (i : Option (Fin n)) : Primrec (clearedFamilyCode program entry ε e i) :=
  PolynomialClearingCode.numerator_primrec _ (rationalFamilyCode_primrec program entry ε e) i

theorem decode_clearingCode (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (initial : Fin k → ℕ) : PolynomialCode.decode (clearingCode program entry ε e initial) =
      MvPolynomial.rename (coordinateEquiv program entry ε e initial)
        (ClockedMonitor.clearingPolynomial program entry initial ε) := by
  rw [clearingCode, PolynomialClearingCode.decode_denominator _ _ _
    (decode_rationalFamilyCode program entry ε e initial)]
  rw [PolynomialClearingCode.commonDenominator_comp_equiv]
  rfl

private theorem decode_clearedFamilyCode (program : RegisterMachine.Program k s)
    (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (initial : Fin k → ℕ) (i : Option (Fin n)) :
    PolynomialCode.decode (clearedFamilyCode program entry ε e i initial) =
      MvPolynomial.rename (coordinateEquiv program entry ε e initial)
        (PolynomialFraction.clearedNumerator (ClockedMonitor.rationalFamily program entry initial ε)
          (familyEquiv program entry ε e initial i)) := by
  rw [clearedFamilyCode, PolynomialClearingCode.decode_numerator _ _ _
    (decode_rationalFamilyCode program entry ε e initial)]
  rw [PolynomialClearingCode.clearedNumerator_comp_equiv]

def clearedFieldCode (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (i : Fin n) : (Fin k → ℕ) → PolynomialCode n := clearedFamilyCode program entry ε e (some i)

def clearedOutputCode (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n) :
    (Fin k → ℕ) → PolynomialCode n := clearedFamilyCode program entry ε e none

def clearedPenalizedOutputCode (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (initial : Fin k → ℕ) : PolynomialCode n :=
  PolynomialCode.sub (clearedOutputCode program entry ε e initial)
    (PolynomialCode.mul (clearingCode program entry ε e initial)
      (penaltyCode program entry ε e initial))

theorem clearedFieldCode_primrec (program : RegisterMachine.Program k s)
    (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (i : Fin n) : Primrec (clearedFieldCode program entry ε e i) :=
  clearedFamilyCode_primrec program entry ε e (some i)

theorem clearedPenalizedOutputCode_primrec (program : RegisterMachine.Program k s)
    (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n) :
    Primrec (clearedPenalizedOutputCode program entry ε e) :=
  PolynomialCode.sub_primrec.comp (clearedFamilyCode_primrec program entry ε e none)
    (PolynomialCode.mul_primrec.comp (clearingCode_primrec program entry ε e)
      (penaltyCode_primrec program entry ε e))

theorem decode_clearedFieldCode (program : RegisterMachine.Program k s)
    (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (i : Fin n) (initial : Fin k → ℕ) :
    PolynomialCode.decode (clearedFieldCode program entry ε e i initial) =
      MvPolynomial.rename (coordinateEquiv program entry ε e initial)
        (ClockedMonitor.clearedField program entry initial ε
          ((coordinateEquiv program entry ε e initial).symm i)) :=
  decode_clearedFamilyCode program entry ε e initial (some i)

theorem decode_clearedOutputCode (program : RegisterMachine.Program k s)
    (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (initial : Fin k → ℕ) : PolynomialCode.decode (clearedOutputCode program entry ε e initial) =
      MvPolynomial.rename (coordinateEquiv program entry ε e initial)
        (ClockedMonitor.clearedOutput program entry initial ε) :=
  decode_clearedFamilyCode program entry ε e initial none

/-- The decoded output is precisely the original cleared output minus
the common denominator times the actual polynomial penalty. -/
theorem decode_clearedPenalizedOutputCode (program : RegisterMachine.Program k s)
    (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (initial : Fin k → ℕ) :
    PolynomialCode.decode (clearedPenalizedOutputCode program entry ε e initial) =
      MvPolynomial.rename (coordinateEquiv program entry ε e initial)
        (ClockedMonitor.clearedPenalizedOutput program entry initial ε) := by
  simp [clearedPenalizedOutputCode, decode_clearedOutputCode, decode_clearingCode,
    decode_penaltyCode, ClockedMonitor.clearedPenalizedOutput]

def pairCode (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (initial : Fin k → ℕ) : PolynomialFieldCode n × PolynomialCode n :=
  (fun i ↦ clearedFieldCode program entry ε e i initial,
    clearedPenalizedOutputCode program entry ε e initial)

theorem pairCode_primrec (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n) :
    Primrec (pairCode program entry ε e) := by
  apply Primrec.pair
  · rw [Primrec.fin_curry]
    apply Primrec₂.swap
    rw [Primrec.fin_curry₁]
    intro i
    exact clearedFieldCode_primrec program entry ε e i
  · exact clearedPenalizedOutputCode_primrec program entry ε e

/-- One degree bound for both decoded components, independent of input,
precision, and the chosen fixed coordinate order. -/
theorem pairCode_totalDegree_le (program : RegisterMachine.Program k s)
    (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (initial : Fin k → ℕ) :
    (∀ i, (PolynomialCode.decode ((pairCode program entry ε e initial).1 i)).totalDegree ≤
      ClockedMonitor.clearedPenalizedDegreeBound program entry) ∧
    (PolynomialCode.decode (pairCode program entry ε e initial).2).totalDegree ≤
      ClockedMonitor.clearedPenalizedDegreeBound program entry := by
  constructor
  · intro i
    change (PolynomialCode.decode (clearedFieldCode program entry ε e i initial)).totalDegree ≤ _
    rw [decode_clearedFieldCode, PolynomialCodeRealization.totalDegree_rename_equiv]
    exact (ClockedMonitor.clearedField_totalDegree_le program entry initial ε _).trans
      (Nat.le_add_right _ _)
  · change (PolynomialCode.decode
      (clearedPenalizedOutputCode program entry ε e initial)).totalDegree ≤ _
    rw [decode_clearedPenalizedOutputCode, PolynomialCodeRealization.totalDegree_rename_equiv]
    exact ClockedMonitor.clearedPenalizedOutput_totalDegree_le program entry initial ε

end

end Stability.ClockedMonitorCode
