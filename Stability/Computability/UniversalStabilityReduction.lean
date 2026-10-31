import Stability.Computability.HomogeneousStabilityReduction
import Stability.Computability.RegisterMachineUniversal
import HGAS.Propagation.CofinalLyapunovReduction

/-!
# Unconditional many-one hardness of homogeneous Lyapunov stability

One fixed finite INC/DEC program supplies the universal halting source.
The actual polynomial-monitor compiler gives a fixed odd-degree target;
the preserved cubic and cofinal reductions give every sufficiently large
fixed dimension and every odd degree at least three. These are hardness
results, not assertions that Lyapunov stability is recursively enumerable.
-/

namespace Stability.UniversalStabilityReduction

open HGAS HGAS.Veronese

noncomputable section

def registers (n : ℕ) : Fin 5 → ℕ := Function.update 0 0 n

theorem registers_primrec : Primrec registers := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro i
  by_cases hi : i = 0
  · subst i
    simpa only [registers, Function.update_self] using (Primrec.id : Primrec (id : ℕ → ℕ))
  · simpa only [registers, Function.update_of_ne hi, Pi.zero_apply] using
      (Primrec.const 0 : Primrec (fun _ : ℕ ↦ 0))

def sourceDimension : ℕ :=
  ClockedMonitorCode.dimension UniversalRegisterMachine.program UniversalRegisterMachine.entry + 1

def sourceDegreeIndex : ℕ :=
  HomogeneousStabilityReduction.degreeIndex
    UniversalRegisterMachine.program UniversalRegisterMachine.entry

def fieldCode (n : ℕ) : PolynomialFieldCode sourceDimension :=
  HomogeneousStabilityReduction.fieldCode UniversalRegisterMachine.program
    UniversalRegisterMachine.entry (registers n)

theorem fieldCode_primrec : Primrec fieldCode :=
  (HomogeneousStabilityReduction.fieldCode_primrec
    UniversalRegisterMachine.program UniversalRegisterMachine.entry).comp registers_primrec

theorem hlsQ_fieldCode_iff (n : ℕ) :
    HLSQ sourceDimension (2 * sourceDegreeIndex + 1) (fieldCode n) ↔
      UniversalRegisterMachine.Halts n :=
  HomogeneousStabilityReduction.hlsQ_fieldCode_iff
    UniversalRegisterMachine.program UniversalRegisterMachine.entry (registers n)

theorem halts_manyOneReducible :
    UniversalRegisterMachine.Halts ≤₀ HLSQ sourceDimension (2 * sourceDegreeIndex + 1) :=
  ⟨fieldCode, fieldCode_primrec.to_comp, fun n ↦ (hlsQ_fieldCode_iff n).symm⟩

/-- The entire raw map from Mathlib's code/argument universal source is
primitive recursive, including the ordinary input-stack encoding. -/
def universalFieldCode (input : Nat.Partrec.Code × ℕ) : PolynomialFieldCode sourceDimension :=
  fieldCode (UniversalRegisterMachine.inputCode input)

theorem universalFieldCode_primrec : Primrec universalFieldCode :=
  fieldCode_primrec.comp UniversalRegisterMachine.inputCode_primrec

theorem hlsQ_universalFieldCode_iff (input : Nat.Partrec.Code × ℕ) :
    HLSQ sourceDimension (2 * sourceDegreeIndex + 1) (universalFieldCode input) ↔
      UniversalHalts input :=
  (hlsQ_fieldCode_iff _).trans (UniversalRegisterMachine.halts_inputCode_iff input)

theorem universalHalts_manyOneReducible :
    UniversalHalts ≤₀ HLSQ sourceDimension (2 * sourceDegreeIndex + 1) :=
  ⟨universalFieldCode, universalFieldCode_primrec.to_comp,
    fun input ↦ (hlsQ_universalFieldCode_iff input).symm⟩

theorem source_manyOneHard : ManyOneHard (HLSQ sourceDimension (2 * sourceDegreeIndex + 1)) :=
  (show ManyOneHard UniversalRegisterMachine.Halts from
    UniversalRegisterMachine.halts_sigmaOneComplete.2).of_manyOneReducible halts_manyOneReducible

theorem source_not_computable :
    ¬ ComputablePred (HLSQ sourceDimension (2 * sourceDegreeIndex + 1)) :=
  source_manyOneHard.not_computable

theorem source_complement_not_re :
    ¬ REPred (fun F ↦ ¬ HLSQ sourceDimension (2 * sourceDegreeIndex + 1) F) :=
  source_manyOneHard.complement_not_re

theorem sourceDimension_ge_two : 2 ≤ sourceDimension :=
  ClockedMonitorCode.two_le_homogeneousDimension
    UniversalRegisterMachine.program UniversalRegisterMachine.entry

theorem sourceDegreeIndex_pos : 1 ≤ sourceDegreeIndex :=
  HomogeneousStabilityReduction.degreeIndex_pos
    UniversalRegisterMachine.program UniversalRegisterMachine.entry

/-- One fixed dimension suffices for every odd target degree at least three. -/
def cubicDimension : ℕ := cubicLiftCodeDimension sourceDimension sourceDegreeIndex

theorem halts_manyOneReducible_cubic :
    UniversalRegisterMachine.Halts ≤₀ HLSQ cubicDimension 3 :=
  halts_manyOneReducible.trans (Propagation.hlsQ_manyOneReducible_cubic
    sourceDimension sourceDegreeIndex sourceDimension_ge_two sourceDegreeIndex_pos)

theorem cubic_manyOneHard : ManyOneHard (HLSQ cubicDimension 3) :=
  source_manyOneHard.of_manyOneReducible (Propagation.hlsQ_manyOneReducible_cubic
    sourceDimension sourceDegreeIndex sourceDimension_ge_two sourceDegreeIndex_pos)

theorem cubic_not_computable : ¬ ComputablePred (HLSQ cubicDimension 3) :=
  cubic_manyOneHard.not_computable

theorem cubic_complement_not_re : ¬ REPred (fun F ↦ ¬ HLSQ cubicDimension 3 F) :=
  cubic_manyOneHard.complement_not_re

theorem halts_manyOneReducible_cofinal (N d : ℕ) (hN : cubicDimension ≤ N)
    (hd : Odd d) (hthree : 3 ≤ d) : UniversalRegisterMachine.Halts ≤₀ HLSQ N d :=
  halts_manyOneReducible.trans (Propagation.hlsQ_manyOneReducible_cofinalFixedPair
    sourceDimension sourceDegreeIndex N d sourceDimension_ge_two sourceDegreeIndex_pos hN hd hthree)

/-- No source-hardness or simulation hypothesis: the fixed register
machine and raw polynomial compiler discharge both. -/
theorem cofinal_manyOneHard (N d : ℕ) (hN : cubicDimension ≤ N)
    (hd : Odd d) (hthree : 3 ≤ d) : ManyOneHard (HLSQ N d) :=
  source_manyOneHard.of_manyOneReducible (Propagation.hlsQ_manyOneReducible_cofinalFixedPair
    sourceDimension sourceDegreeIndex N d sourceDimension_ge_two sourceDegreeIndex_pos hN hd hthree)

theorem cofinal_not_computable (N d : ℕ) (hN : cubicDimension ≤ N)
    (hd : Odd d) (hthree : 3 ≤ d) : ¬ ComputablePred (HLSQ N d) :=
  (cofinal_manyOneHard N d hN hd hthree).not_computable

theorem cofinal_complement_not_re (N d : ℕ) (hN : cubicDimension ≤ N)
    (hd : Odd d) (hthree : 3 ≤ d) : ¬ REPred (fun F ↦ ¬ HLSQ N d F) :=
  (cofinal_manyOneHard N d hN hd hthree).complement_not_re

end

end Stability.UniversalStabilityReduction
