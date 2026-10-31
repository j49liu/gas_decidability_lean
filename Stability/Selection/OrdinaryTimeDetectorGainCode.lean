import Stability.Selection.OrdinaryTimeDetectorGain
import HGAS.Arithmetic.NormalizedCorrectedCanonicalEffectivePrimitiveGainComputability

/-!
# Effective detector gain for a varying right-hand side

The matrices, prime tuple, Fourier radius, and scalar drift family are
fixed. The right-hand side changes only an integer exponent in the
primitive budget. Its raw rational code is primitive recursive; the
least admissible gain denominator is computable. Equal decoded rational
bounds select the same denominator, even for noncanonical codes.
-/

namespace Stability.Selection

open HGAS

theorem gainDenominator_eq_of_decode_eq (M : ℕ) (c c' : RationalCode)
    (h : RationalCode.decode c = RationalCode.decode c') :
    gainDenominator M c = gainDenominator M c' := by
  apply le_antisymm
  · apply gainDenominator_min M c
    apply (gainAdmissible_iff M c _).mpr
    have hc := (gainAdmissible_iff M c' _).mp (gainDenominator_spec M c')
    exact ⟨hc.1, by simpa only [h] using hc.2⟩
  · apply gainDenominator_min M c'
    apply (gainAdmissible_iff M c' _).mpr
    have hc := (gainAdmissible_iff M c _).mp (gainDenominator_spec M c)
    exact ⟨hc.1, by simpa only [h] using hc.2⟩

theorem graphGain_eq_of_decode_eq (M : ℕ) (c c' : RationalCode)
    (h : RationalCode.decode c = RationalCode.decode c') : graphGain M c = graphGain M c' := by
  unfold graphGain
  rw [gainDenominator_eq_of_decode_eq M c c' h]

noncomputable section

variable {eqs vars : ℕ}

def rhsPrimitiveBudgetCode (I : DQLSystem eqs vars) (p : Fin (vars + eqs) → ℕ)
    (rhs : Fin eqs → ℤ) : RationalCode :=
  RationalCode.mul (RationalCode.encode (detectorPrimitiveBudget I p (sourceRadiusIndex I)))
    (RationalCode.pow
      (fourierRadiusCode (linearRadiusExponent I) (quadraticRadiusExponent I))
      (4 * detectorDriftDegree I * ∑ row, (rhs row).natAbs))

theorem decode_rhsPrimitiveBudgetCode (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) (rhs : Fin eqs → ℤ) :
    RationalCode.decode (rhsPrimitiveBudgetCode I p rhs) =
      detectorPrimitiveRhsBudget { I with rhs := rhs } p := by
  rw [rhsPrimitiveBudgetCode, RationalCode.decode_mul, RationalCode.decode_encode,
    RationalCode.decode_pow, decode_fourierRadiusCode]
  rfl

theorem rhsPrimitiveBudgetCode_primrec (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) : Primrec (rhsPrimitiveBudgetCode I p) := by
  apply RationalCode.mul_primrec.comp (Primrec.const _)
  apply RationalCode.pow_primrec.comp (Primrec.const _)
  apply Primrec.nat_mul.comp (Primrec.const _)
  apply NormalizedCorrectedCanonicalEffectivePrimitiveGain.primrec_fin_sum
  intro row
  exact Clocks.ControllerPhaseProductCharacterCode.intNatAbs_primrec.comp
    (Primrec.fin_app.comp Primrec.id (Primrec.const row))

def rhsGraphGainCode (I : DQLSystem eqs vars) (p : Fin (vars + eqs) → ℕ)
    (rhs : Fin eqs → ℤ) : RationalCode :=
  graphGainCode (sourceGraphSizeBudget eqs vars) (rhsPrimitiveBudgetCode I p rhs)

theorem rhsGraphGainCode_computable (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) : Computable (rhsGraphGainCode I p) :=
  graphGainCode_computable.comp (Computable.const _) (rhsPrimitiveBudgetCode_primrec I p).to_comp

/-- The raw budget code selects exactly the already defined semantic gain. -/
theorem decode_rhsGraphGainCode (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) (rhs : Fin eqs → ℤ) :
    RationalCode.decode (rhsGraphGainCode I p rhs) =
      detectorGraphGain { I with rhs := rhs } p := by
  rw [rhsGraphGainCode, decode_graphGainCode, detectorGraphGain]
  apply graphGain_eq_of_decode_eq
  rw [decode_rhsPrimitiveBudgetCode, RationalCode.decode_encode]

theorem decode_rhsGraphGainCode_pos (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) (rhs : Fin eqs → ℤ) :
    0 < RationalCode.decode (rhsGraphGainCode I p rhs) := by
  rw [decode_rhsGraphGainCode]
  exact detectorGraphGain_pos _ _

theorem decode_rhsGraphGainCode_quadratic_bound (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) (rhs : Fin eqs → ℤ) :
    RationalCode.decode (rhsGraphGainCode I p rhs) ^ 2 *
      detectorPrimitiveRhsBudget { I with rhs := rhs } p ^ 2 ≤
        detectorGraphMargin eqs vars := by
  rw [decode_rhsGraphGainCode]
  exact detectorGraphGain_quadratic_bound _ _

end

end Stability.Selection
