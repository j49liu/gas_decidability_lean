import HGAS.Arithmetic.NormalizedCorrectedCanonicalEffectivePrimitiveGainComputability
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorCompactSourceCode
import HGAS.Clocks.ObservedTimeChangedControllerPhaseHaar
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

/-!
# A completely effective input for the normalized corrected compiler

The semantic detector construction needs three finite pieces of data in
addition to a DQL system:

* pairwise distinct prime controller parameters;
* a positive accumulator gain small enough for the primitive graph; and
* a positive reward margin smaller than the available central gap.

This file makes all three choices once and for all.  The `i`-th controller
uses the `i`-th prime.  The accumulator gain is the explicit unit fraction
constructed in
`NormalizedCorrectedCanonicalEffectivePrimitiveGain`, and the reward
margin is

```text
            1 / (16 (R + 1)),
```

where `R` is the natural raw-orbit norm budget.  In particular the whole
compiler input is a total computable function of the finite DQL code.
-/

namespace HGAS.NormalizedCorrectedEffectiveCompilerInput

open HGAS
open HGAS.NormalizedCorrectedCanonicalEffectivePrimitiveGain

noncomputable section

/-- The canonical finite family of pairwise distinct prime radicands. -/
def primeRadicand (q : ℕ) (i : Fin q) : ℕ :=
  Nat.nth Nat.Prime i

theorem primeRadicand_prime (q : ℕ) :
    ∀ i : Fin q, (primeRadicand q i).Prime := by
  intro i
  exact Nat.prime_nth_prime i

theorem primeRadicand_injective (q : ℕ) :
    Function.Injective (primeRadicand q) := by
  intro i j hij
  apply Fin.ext
  exact
    Nat.nth_injective Nat.infinite_setOf_prime hij

/-- Prime-valued rational controller codes in the exact detector-clock
index type. -/
def controllerParameters (eqs vars : ℕ) :
    Fin (vars + eqs) → RationalCode :=
  Clocks.ObservedTimeChangedControllerPhaseHaar.primeClockCodes
    (primeRadicand (vars + eqs))

theorem controllerParameters_gt_one (eqs vars : ℕ) :
    ∀ i,
      (1 : ℝ) <
        (RationalCode.decode (controllerParameters eqs vars i) : ℝ) :=
  Clocks.ObservedTimeChangedControllerPhaseHaar.primeClockCodes_gt_one
    (primeRadicand (vars + eqs))
    (primeRadicand_prime (vars + eqs))

/-- Positive integer denominator of the fixed reward margin. -/
def rewardMarginDenominator (eqs vars : ℕ) : ℕ :=
  16 *
    (CanonicalRawOrbitEffectiveBudget.rawNormSqNatBudget eqs vars + 1)

theorem rewardMarginDenominator_pos (eqs vars : ℕ) :
    0 < rewardMarginDenominator eqs vars := by
  unfold rewardMarginDenominator
  positivity

/-- A strictly positive rational margin leaving ample room below the
canonical finite-graph gap. -/
def rewardMarginCode (eqs vars : ℕ) : RationalCode :=
  RationalCode.unitFraction (rewardMarginDenominator eqs vars)

@[simp]
theorem decode_rewardMarginCode (eqs vars : ℕ) :
    (RationalCode.decode (rewardMarginCode eqs vars) : ℝ) =
      1 /
        (16 *
          ((CanonicalRawOrbitEffectiveBudget.rawNormSqNatBudget
              eqs vars : ℝ) + 1)) := by
  unfold rewardMarginCode
  rw [RationalCode.decode_unitFraction
    (rewardMarginDenominator_pos eqs vars)]
  unfold rewardMarginDenominator
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  push_cast
  ring

theorem decode_rewardMarginCode_pos (eqs vars : ℕ) :
    0 <
      (RationalCode.decode (rewardMarginCode eqs vars) : ℝ) := by
  rw [decode_rewardMarginCode]
  positivity

/-- The effective reward margin is at most the explicit graph allowance
computed from the rational effective central lower bound. -/
theorem decode_rewardMarginCode_le_effectiveGap (eqs vars : ℕ) :
    (RationalCode.decode (rewardMarginCode eqs vars) : ℝ) ≤
      3 *
          (1 /
            (1 +
              (CanonicalRawOrbitEffectiveBudget.rawNormSqNatBudget
                eqs vars : ℝ))) /
        8 := by
  rw [decode_rewardMarginCode]
  have hR :
      0 ≤
        (CanonicalRawOrbitEffectiveBudget.rawNormSqNatBudget
          eqs vars : ℝ) := by
    positivity
  have hden :
      0 <
        1 +
          (CanonicalRawOrbitEffectiveBudget.rawNormSqNatBudget
            eqs vars : ℝ) := by
    positivity
  field_simp
  nlinarith

/-- The literal normalized compiler input associated to a finite DQL
system.  Every choice in this definition is named and effective. -/
def compilerInput {eqs vars : ℕ}
    (I : DQLSystem eqs vars) :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
  eqs vars :=
  (((controllerParameters eqs vars, I),
      effectiveAccumulatorScaleCode I (primeRadicand (vars + eqs))),
    rewardMarginCode eqs vars)

@[simp]
theorem compilerInput_parameters {eqs vars : ℕ}
    (I : DQLSystem eqs vars) :
    NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
        (compilerInput I) =
      controllerParameters eqs vars :=
  rfl

@[simp]
theorem compilerInput_system {eqs vars : ℕ}
    (I : DQLSystem eqs vars) :
    NormalizedCorrectedFixedDetectorCompactSourceCode.system
        (compilerInput I) =
      I :=
  rfl

@[simp]
theorem compilerInput_accumulatorScale {eqs vars : ℕ}
    (I : DQLSystem eqs vars) :
    NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
        (compilerInput I) =
      effectiveAccumulatorScaleCode I (primeRadicand (vars + eqs)) :=
  rfl

@[simp]
theorem compilerInput_rewardMargin {eqs vars : ℕ}
    (I : DQLSystem eqs vars) :
    NormalizedCorrectedFixedDetectorCompactSourceCode.rewardMargin
        (compilerInput I) =
      rewardMarginCode eqs vars :=
  rfl

theorem compilerInput_accumulatorScale_pos {eqs vars : ℕ}
    (I : DQLSystem eqs vars) :
    0 <
      (RationalCode.decode
        (NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          (compilerInput I)) : ℝ) := by
  rw [compilerInput_accumulatorScale]
  exact
    decode_effectiveAccumulatorScaleCode_pos
      I (primeRadicand (vars + eqs))

theorem compilerInput_computable {eqs vars : ℕ} :
    Computable
      (compilerInput :
        DQLSystem eqs vars →
          NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
            eqs vars) := by
  let hgain :
      Computable
        (fun I : DQLSystem eqs vars ↦
          effectiveAccumulatorScaleCode
            I (primeRadicand (vars + eqs))) :=
    effectiveAccumulatorScaleCode_computable.comp
        Computable.id
        (Computable.const (primeRadicand (vars + eqs)))
  exact
    (Computable.pair
      (Computable.pair
        (Computable.pair
          (Computable.const (controllerParameters eqs vars))
          Computable.id)
        hgain)
      (Computable.const (rewardMarginCode eqs vars))).of_eq
        (fun _ ↦ rfl)

/-- The complete normalized compact-source syntax is computable from the
DQL code. -/
theorem compiledSourceCode_computable {eqs vars : ℕ} :
    Computable
      (fun I : DQLSystem eqs vars ↦
        NormalizedCorrectedFixedDetectorCompactSourceCode.compile
          (compilerInput I)) :=
  NormalizedCorrectedFixedDetectorCompactSourceCode.compile_computable.comp
    compilerInput_computable

end

end HGAS.NormalizedCorrectedEffectiveCompilerInput
