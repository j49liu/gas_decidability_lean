import Stability.Computability.ClockedMonitorRadicalCode
import Stability.Computability.TriangularLiftCodeCast

/-!
# Input-effective rational field and output of the monitor

The stored output numerators undergo the actual auxiliary-square substitution.
Their denominators are powers of the shared precision. Squared radicands
and these base fractions feed the literal triangular velocity compiler.
The resulting fixed-coordinate codes decode to the existing rational
monitor, including its numerator and denominator polynomials separately.
-/

namespace Stability.ClockedMonitorCode

open HGAS Simulation

noncomputable section

variable {k s n : ℕ}

private theorem fraction_eq_of_components {σ : Type*} {f g : PolynomialFraction σ}
    (hn : f.numerator = g.numerator) (hd : f.denominator = g.denominator) : f = g := by
  cases f
  cases g
  cases hn
  cases hd
  rfl

private theorem decode_squaredPower_cast {σ : Type*} {J K : ℕ} (h : J = K)
    (e : (σ ⊕ Fin K) ≃ Fin n) (L : PolynomialCode n) (P : MvPolynomial σ ℚ)
    (out : PowerFractionCode n) (f : PowerFraction (σ ⊕ Fin J))
    (hL : PolynomialCode.decode L = MvPolynomial.rename (fun i ↦ e (.inl i)) P)
    (hout : (PolynomialCode.decode out.1, out.2) =
      (MvPolynomial.rename (PolynomialErrorWeightCode.rootCoordinateCast h e) f.numerator,
        f.exponent)) :
    PolynomialFractionCode.decode
      (PolynomialDefectCode.squareCode e out.1, PolynomialCode.pow L out.2) =
      PolynomialFractionCode.rename (PolynomialErrorWeightCode.rootCoordinateCast h e)
        ⟨RadicalProgram.squareRootsPolynomial f.numerator,
          MvPolynomial.rename Sum.inl P ^ f.exponent⟩ := by
  have hn := congrArg Prod.fst hout
  have hd := congrArg Prod.snd hout
  apply fraction_eq_of_components
  · exact PolynomialDefectCode.decode_squareCode_cast h e out.1 f.numerator hn
  · change PolynomialCode.decode (PolynomialCode.pow L out.2) = _
    rw [PolynomialCode.decode_pow_code, hL, hd]
    simp only [PolynomialFractionCode.rename, map_pow, MvPolynomial.rename_rename]
    rfl

def baseFractionCode (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (i : Option (MonitorCoordinate k)) : (Fin k → ℕ) → PolynomialFractionCode n :=
  fun initial ↦
    (PolynomialDefectCode.squareCode e (outputCode program entry ε e i initial).1,
      PolynomialCode.pow (precisionCode program entry ε e initial)
        (outputCode program entry ε e i initial).2)

def squaredRadicandCode (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (j : Fin (ClockedMonitor.fixedRootCount program entry)) : (Fin k → ℕ) → PolynomialCode n :=
  fun initial ↦ PolynomialDefectCode.squareCode e (radicandCode program entry ε e j initial)

def rationalFieldCode (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (j : Fin n) : (Fin k → ℕ) → PolynomialFractionCode n :=
  fun initial ↦ TriangularLiftCode.field e
    (fun i ↦ squaredRadicandCode program entry ε e i initial)
    (fun i ↦ baseFractionCode program entry ε e (some i) initial) (e.symm j)

def rationalOutputCode (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n) :
    (Fin k → ℕ) → PolynomialFractionCode n :=
  baseFractionCode program entry ε e none

theorem baseFractionCode_primrec (program : RegisterMachine.Program k s) (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (i : Option (MonitorCoordinate k)) : Primrec (baseFractionCode program entry ε e i) :=
  Primrec.pair
    ((PolynomialDefectCode.squareCode_primrec e).comp
      (Primrec.fst.comp (outputCode_primrec program entry ε e i)))
    (PolynomialCode.pow_primrec.comp (precisionCode_primrec program entry ε e)
      (Primrec.snd.comp (outputCode_primrec program entry ε e i)))

theorem squaredRadicandCode_primrec (program : RegisterMachine.Program k s)
    (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (j : Fin (ClockedMonitor.fixedRootCount program entry)) :
    Primrec (squaredRadicandCode program entry ε e j) :=
  (PolynomialDefectCode.squareCode_primrec e).comp (radicandCode_primrec program entry ε e j)

theorem rationalFieldCode_primrec (program : RegisterMachine.Program k s)
    (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (j : Fin n) : Primrec (rationalFieldCode program entry ε e j) :=
  TriangularLiftCode.field_primrec e
    (fun initial i ↦ squaredRadicandCode program entry ε e i initial)
    (fun initial i ↦ baseFractionCode program entry ε e (some i) initial)
    (squaredRadicandCode_primrec program entry ε e)
    (fun i ↦ baseFractionCode_primrec program entry ε e (some i)) (e.symm j)

theorem rationalOutputCode_primrec (program : RegisterMachine.Program k s)
    (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n) :
    Primrec (rationalOutputCode program entry ε e) :=
  baseFractionCode_primrec program entry ε e none

set_option maxHeartbeats 800000 in
-- Exact numerator and denominator casts compare the generated dependent root-coordinate types.
theorem decode_baseFractionCode (program : RegisterMachine.Program k s)
    (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (i : Option (MonitorCoordinate k)) (initial : Fin k → ℕ) :
    PolynomialFractionCode.decode (baseFractionCode program entry ε e i initial) =
      PolynomialFractionCode.rename (coordinateEquiv program entry ε e initial)
        (CompiledFormulaLift.baseFraction (ClockedMonitor.precision program entry initial ε)
          (ClockedMonitor.formulaList program entry initial)
          (ClockedMonitor.formulaPosition program entry initial i)) := by
  have hout := decode_outputCode program entry ε e i initial
  dsimp only at hout
  have hcoord : PolynomialErrorWeightCode.rootCoordinateCast
      (ClockedMonitor.rootCount_eq_fixed program entry initial ε) e =
        coordinateEquiv program entry ε e initial := rfl
  rw [← hcoord] at hout
  have h := decode_squaredPower_cast
    (ClockedMonitor.rootCount_eq_fixed program entry initial ε) e
    (precisionCode program entry ε e initial) (ClockedMonitor.precision program entry initial ε)
    (outputCode program entry ε e i initial)
    (CompiledFormulaLift.outputAt (ClockedMonitor.precision program entry initial ε)
      (ClockedMonitor.formulaList program entry initial)
      (ClockedMonitor.formulaPosition program entry initial i))
    (decode_precisionCode program entry ε e initial) hout
  rw [hcoord] at h
  simpa only [baseFractionCode, CompiledFormulaLift.baseFraction] using h

theorem decode_squaredRadicandCode (program : RegisterMachine.Program k s)
    (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (j : Fin (ClockedMonitor.fixedRootCount program entry)) (initial : Fin k → ℕ) :
    PolynomialCode.decode (squaredRadicandCode program entry ε e j initial) =
      MvPolynomial.rename (coordinateEquiv program entry ε e initial)
        (AbsFormula.liftRadicand (ClockedMonitor.precision program entry initial ε)
          (ClockedMonitor.formulaList program entry initial)
          (j.cast (ClockedMonitor.rootCount_eq_fixed program entry initial ε).symm)) :=
  PolynomialDefectCode.decode_squareCode_cast
    (ClockedMonitor.rootCount_eq_fixed program entry initial ε) e _ _
    (decode_radicandCode program entry ε e j initial)

theorem decode_rationalFieldCode (program : RegisterMachine.Program k s)
    (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (j : Fin n) (initial : Fin k → ℕ) :
    PolynomialFractionCode.decode (rationalFieldCode program entry ε e j initial) =
      PolynomialFractionCode.rename (coordinateEquiv program entry ε e initial)
        (ClockedMonitor.rationalField program entry initial ε
          ((coordinateEquiv program entry ε e initial).symm j)) :=
  TriangularLiftCode.decode_field_cast
    (ClockedMonitor.rootCount_eq_fixed program entry initial ε) e
    (fun i ↦ squaredRadicandCode program entry ε e i initial)
    (fun i ↦ baseFractionCode program entry ε e (some i) initial) _ _
    (fun i ↦ decode_squaredRadicandCode program entry ε e i initial)
    (fun i ↦ decode_baseFractionCode program entry ε e (some i) initial) (e.symm j)

theorem decode_rationalOutputCode (program : RegisterMachine.Program k s)
    (entry : Fin s) (ε : ℚ)
    (e : (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃ Fin n)
    (initial : Fin k → ℕ) :
    PolynomialFractionCode.decode (rationalOutputCode program entry ε e initial) =
      PolynomialFractionCode.rename (coordinateEquiv program entry ε e initial)
        (ClockedMonitor.rationalOutput program entry initial ε) :=
  decode_baseFractionCode program entry ε e none initial

end

end Stability.ClockedMonitorCode
