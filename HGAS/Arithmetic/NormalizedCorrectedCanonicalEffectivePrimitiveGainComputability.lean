import HGAS.Arithmetic.NormalizedCorrectedCanonicalEffectivePrimitiveGain
import HGAS.Arithmetic.DetectorCharacterComputability
import Mathlib.Computability.Primrec.List
import Mathlib.Tactic

/-!
# Primitive-recursiveness of the effective canonical gain

The semantic gain theorem uses only a finite collection of natural-number
operations.  This companion file verifies that claim in Mathlib's
primitive-recursion framework.  Dimensions are fixed, so every finite
sum and every exponent is fixed at compile time; the runtime inputs are
only the finite DQL coefficient tuple and the finite radicand tuple.
-/

namespace HGAS.NormalizedCorrectedCanonicalEffectivePrimitiveGain

open HGAS
open HGAS.Analysis
open HGAS.Analysis.CanonicalEffectivePrimitiveBudget
open HGAS.CanonicalRawOrbitEffectiveBudget
open HGAS.DetectorCharacterCode
open HGAS.Clocks.ControllerPhaseProductCharacterCode

variable {eqs vars : ℕ}

/-- A fixed finite sum of primitive-recursive natural-valued functions is
primitive recursive. -/
theorem primrec_fin_sum
    {α : Type*} [Primcodable α]
    {n : ℕ}
    (f : Fin n → α → ℕ)
    (hf : ∀ i, Primrec (f i)) :
    Primrec (fun a ↦ ∑ i, f i a) := by
  classical
  have hsum :
      ∀ s : Finset (Fin n),
        Primrec (fun a ↦ ∑ i ∈ s, f i a) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa using (Primrec.const 0 : Primrec (fun _ : α ↦ 0))
    | @insert i s hi ih =>
        have hadd :=
          Primrec.nat_add.comp (hf i) ih
        exact hadd.of_eq (by
          intro a
          simp [Finset.sum_insert hi])
  simpa using hsum Finset.univ

/-- Raising a natural number to one fixed exponent is primitive
recursive. -/
theorem primrec_nat_pow_const (k : ℕ) :
    Primrec (fun n : ℕ ↦ n ^ k) := by
  induction k with
  | zero =>
      simpa using
        (Primrec.const 1 : Primrec (fun _ : ℕ ↦ 1))
  | succ k ih =>
      exact
        (Primrec.nat_mul.comp ih Primrec.id).of_eq (by
          intro n
          simp [pow_succ])

private abbrev GainInput (eqs vars : ℕ) :=
  DQLSystem eqs vars × (Fin (vars + eqs) → ℕ)

private theorem pEntry_primrec
    (i : Fin (vars + eqs)) :
    Primrec (fun z : GainInput eqs vars ↦ z.2 i) :=
  Primrec.fin_app.comp Primrec.snd (Primrec.const i)

private theorem radicalRootNatBound_pair_primrec :
    Primrec (fun z : GainInput eqs vars ↦
      radicalRootNatBound z.2) := by
  have hsum :=
    primrec_fin_sum
      (fun i : Fin (vars + eqs) ↦
        fun z : GainInput eqs vars ↦ z.2 i + 1)
      (fun i ↦
        Primrec.nat_add.comp
          (pEntry_primrec i) (Primrec.const 1))
  exact hsum.of_eq (by
    intro z
    rfl)

private theorem quadraticNatAbs_pair_primrec
    (row : Fin eqs) (j : Fin vars) :
    Primrec (fun z : GainInput eqs vars ↦
      (z.1.quadratic row j).natAbs) :=
  intNatAbs_primrec.comp
    ((quadraticEntry_primrec row j).comp Primrec.fst)

private theorem linearNatAbs_pair_primrec
    (row : Fin eqs) (j : Fin vars) :
    Primrec (fun z : GainInput eqs vars ↦
      (z.1.linear row j).natAbs) :=
  intNatAbs_primrec.comp
    ((linearEntry_primrec row j).comp Primrec.fst)

private theorem rhsNatAbs_pair_primrec
    (row : Fin eqs) :
    Primrec (fun z : GainInput eqs vars ↦
      (z.1.rhs row).natAbs) :=
  intNatAbs_primrec.comp
    ((rhsEntry_primrec row).comp Primrec.fst)

private theorem dqlRowCoefficientWeight_pair_primrec
    (row : Fin eqs) :
    Primrec (fun z : GainInput eqs vars ↦
      dqlRowCoefficientWeight z.1 row) := by
  have hsum :=
    primrec_fin_sum
      (fun j : Fin vars ↦
        fun z : GainInput eqs vars ↦
          (z.1.quadratic row j).natAbs +
            (z.1.linear row j).natAbs)
      (fun j ↦
        Primrec.nat_add.comp
          (quadraticNatAbs_pair_primrec row j)
          (linearNatAbs_pair_primrec row j))
  exact hsum.of_eq (by
    intro z
    rfl)

private theorem dqlRowWeight_pair_primrec
    (row : Fin eqs) :
    Primrec (fun z : GainInput eqs vars ↦
      dqlRowWeight z.1 row) :=
  (Primrec.nat_add.comp
    (rhsNatAbs_pair_primrec row)
    (dqlRowCoefficientWeight_pair_primrec row)).of_eq
      (by intro z; rfl)

private theorem dqlSystemWeight_pair_primrec :
    Primrec (fun z : GainInput eqs vars ↦
      dqlSystemWeight z.1) := by
  have hsum :=
    primrec_fin_sum
      (fun row : Fin eqs ↦
        fun z : GainInput eqs vars ↦
          dqlRowWeight z.1 row)
      dqlRowWeight_pair_primrec
  exact
    (Primrec.nat_add.comp (Primrec.const 1) hsum).of_eq
      (by intro z; rfl)

private theorem selectorHeightNatBound_pair_primrec :
    Primrec (fun z : GainInput eqs vars ↦
      selectorHeightNatBound z.1 z.2) := by
  let hright :
      Primrec (fun z : GainInput eqs vars ↦
        4 * (1 + dqlSystemWeight z.1)) :=
    Primrec.nat_mul.comp (Primrec.const 4)
      (Primrec.nat_add.comp (Primrec.const 1)
        dqlSystemWeight_pair_primrec)
  exact
    (Primrec.nat_mul.comp
      radicalRootNatBound_pair_primrec hright).of_eq
        (by intro z; rfl)

private theorem detectorHeightNatBound_pair_primrec :
    Primrec (fun z : GainInput eqs vars ↦
      detectorHeightNatBound z.1 z.2) := by
  let hright :
      Primrec (fun z : GainInput eqs vars ↦
        4 * (vars + eqs) * dqlSystemWeight z.1) :=
    Primrec.nat_mul.comp
      (Primrec.nat_mul.comp
        (Primrec.const 4) (Primrec.const (vars + eqs)))
      dqlSystemWeight_pair_primrec
  exact
    (Primrec.nat_mul.comp
      radicalRootNatBound_pair_primrec hright).of_eq
        (by intro z; rfl)

private theorem selectorRawBudget_pair_primrec :
    Primrec (fun z : GainInput eqs vars ↦
      selectorRawBudget z.1 z.2) := by
  let hbase :
      Primrec (fun z : GainInput eqs vars ↦
        1 + selectorHeightNatBound z.1 z.2) :=
    Primrec.nat_add.comp (Primrec.const 1)
      selectorHeightNatBound_pair_primrec
  let hpow :
      Primrec (fun z : GainInput eqs vars ↦
        (1 + selectorHeightNatBound z.1 z.2) ^
          effectiveHeightPower eqs vars) :=
    (primrec_nat_pow_const
      (effectiveHeightPower eqs vars)).comp hbase
  let hmul :
      Primrec (fun z : GainInput eqs vars ↦
        (1 + selectorHeightNatBound z.1 z.2) ^
            effectiveHeightPower eqs vars *
          oneDimensionalBudget eqs vars ^ 2) :=
    Primrec.nat_mul.comp hpow
      (Primrec.const (oneDimensionalBudget eqs vars ^ 2))
  exact
    (Primrec.nat_add.comp (Primrec.const 1) hmul).of_eq
      (by intro z; rfl)

private theorem detectorRawBudget_pair_primrec :
    Primrec (fun z : GainInput eqs vars ↦
      detectorRawBudget z.1 z.2) := by
  let hbase :
      Primrec (fun z : GainInput eqs vars ↦
        1 + detectorHeightNatBound z.1 z.2) :=
    Primrec.nat_add.comp (Primrec.const 1)
      detectorHeightNatBound_pair_primrec
  let hpow :
      Primrec (fun z : GainInput eqs vars ↦
        (1 + detectorHeightNatBound z.1 z.2) ^
          effectiveHeightPower eqs vars) :=
    (primrec_nat_pow_const
      (effectiveHeightPower eqs vars)).comp hbase
  exact
    (Primrec.nat_mul.comp hpow
      (Primrec.const
        (oneDimensionalBudget eqs vars ^ (vars + vars)))).of_eq
      (by intro z; rfl)

private theorem coordinatePrimitiveBudget_pair_primrec :
    Primrec (fun z : GainInput eqs vars ↦
      coordinatePrimitiveBudget z.1 z.2) :=
  (Primrec.nat_add.comp
    selectorRawBudget_pair_primrec
    detectorRawBudget_pair_primrec).of_eq
      (by intro z; rfl)

private theorem totalPrimitiveBudget_pair_primrec :
    Primrec (fun z : GainInput eqs vars ↦
      totalPrimitiveBudget z.1 z.2) := by
  let hsquare :
      Primrec (fun z : GainInput eqs vars ↦
        coordinatePrimitiveBudget z.1 z.2 ^ 2) :=
    (primrec_nat_pow_const 2).comp
      coordinatePrimitiveBudget_pair_primrec
  exact
    (Primrec.nat_mul.comp
      (Primrec.const (14 * vars + 3)) hsquare).of_eq
        (by intro z; rfl)

private theorem effectiveAccumulatorDenominator_pair_primrec :
    Primrec (fun z : GainInput eqs vars ↦
      effectiveAccumulatorDenominator z.1 z.2) := by
  let hmiddle :
      Primrec (fun z : GainInput eqs vars ↦
        totalPrimitiveBudget z.1 z.2 + 1) :=
    Primrec.nat_add.comp
      totalPrimitiveBudget_pair_primrec (Primrec.const 1)
  let hleft :
      Primrec (fun z : GainInput eqs vars ↦
        8 * (totalPrimitiveBudget z.1 z.2 + 1)) :=
    Primrec.nat_mul.comp (Primrec.const 8) hmiddle
  exact
    (Primrec.nat_mul.comp hleft
      (Primrec.const (rawNormSqNatBudget eqs vars + 1))).of_eq
      (by intro z; rfl)

/-- The complete two-input gain compiler is primitive recursive. -/
theorem effectiveAccumulatorScaleCode_primrec :
    Primrec₂
      (effectiveAccumulatorScaleCode :
        DQLSystem eqs vars →
          (Fin (vars + eqs) → ℕ) → RationalCode) := by
  have hpair :
      Primrec (fun z : GainInput eqs vars ↦
        effectiveAccumulatorScaleCode z.1 z.2) :=
    (RationalCode.unitFraction_primrec.comp
      effectiveAccumulatorDenominator_pair_primrec).of_eq
      (by intro z; rfl)
  exact hpair.to₂.of_eq (by
    intro I p
    rfl)

/-- In particular, the named gain compiler is total computable. -/
theorem effectiveAccumulatorScaleCode_computable :
    Computable₂
      (effectiveAccumulatorScaleCode :
        DQLSystem eqs vars →
          (Fin (vars + eqs) → ℕ) → RationalCode) :=
  effectiveAccumulatorScaleCode_primrec.to_comp

end HGAS.NormalizedCorrectedCanonicalEffectivePrimitiveGain
