import HGAS.Analysis.CanonicalDetectorNoInstanceAggregatedFamily
import HGAS.Analysis.CanonicalSelectorMomentSupportedCrosswalk
import HGAS.Analysis.ExplicitPolynomialGeometricBudget
import HGAS.Analysis.ExplicitSupportedRadicalPrimitiveBudget
import HGAS.Clocks.ExplicitRadicalDegreeBound
import Mathlib.Tactic

/-!
# A computable numerical budget for the canonical Fourier primitive

This module replaces the qualitative finite primitive bound by one
explicit natural number.  The constants are intentionally very coarse.
Their only roles are:

* to depend effectively on the finite DQL coefficients and finite prime
  clock data;
* to dominate every selector and detector Fourier primitive coordinate;
* to contain no `tsum`, choice, field `finrank`, square root, or `π`.

The exact radical-field exponent is bounded by `2^d-1`.  Every radical
height is bounded by an integer coefficient times a quadratic polynomial
in the lattice `ℓ¹` energy.  Finally,
`ExplicitPolynomialGeometricBudget` bounds the remaining infinite lattice
sum by factorials and powers of two.
-/

noncomputable section

open scoped BigOperators

namespace HGAS.Analysis.CanonicalEffectivePrimitiveBudget

open HGAS
open HGAS.Clocks
open HGAS.Clocks.RadicalSmallDivisor
open HGAS.Analysis
open HGAS.Analysis.CanonicalSelectorMomentRadicalSummability
open HGAS.Analysis.CanonicalSelectorMomentAggregatedFamilies
open HGAS.Analysis.CanonicalSelectorMomentSupportedCrosswalk
open HGAS.Analysis.CanonicalDetectorNoInstanceAggregatedFamily

variable {eqs vars : ℕ}

/-- Computable replacement for the exact radical small-divisor exponent. -/
def effectiveHeightPower (eqs vars : ℕ) : ℕ :=
  2 ^ (vars + eqs) - 1

/-- Integer upper bound for the sum of the square roots of the radicands. -/
def radicalRootNatBound
    (p : Fin (vars + eqs) → ℕ) : ℕ :=
  ∑ i, (p i + 1)

/-- Common integer height coefficient for all seven selector moments. -/
def selectorHeightNatBound
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) : ℕ :=
  radicalRootNatBound p *
    (4 * (1 + dqlSystemWeight I))

/-- Integer height coefficient for the arithmetic detector family. -/
def detectorHeightNatBound
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) : ℕ :=
  radicalRootNatBound p *
    (4 * (vars + eqs) * dqlSystemWeight I)

/-- One-dimensional factorial/geometric budget at the effective
quadratic height power. -/
def oneDimensionalBudget (eqs vars : ℕ) : ℕ :=
  halfPolynomialIntBudget
    (2 * effectiveHeightPower eqs vars)

/-- Common raw weighted budget for every centered selector family. -/
def selectorRawBudget
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) : ℕ :=
  1 +
    (1 + selectorHeightNatBound I p) ^
        effectiveHeightPower eqs vars *
      oneDimensionalBudget eqs vars ^ 2

/-- Raw weighted budget for the no-instance detector family. -/
def detectorRawBudget
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) : ℕ :=
  (1 + detectorHeightNatBound I p) ^
      effectiveHeightPower eqs vars *
    oneDimensionalBudget eqs vars ^ (vars + vars)

/-- One natural number dominating every unscaled primitive coordinate. -/
def coordinatePrimitiveBudget
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) : ℕ :=
  selectorRawBudget I p + detectorRawBudget I p

/-- Natural squared budget for the complete normalized drift vector. -/
def totalPrimitiveBudget
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) : ℕ :=
  (14 * vars + 3) *
    coordinatePrimitiveBudget I p ^ 2

theorem effectiveHeightPower_dominates_exact
    (p : Fin (vars + eqs) → ℕ) :
    radicalDegree p - 1 ≤ effectiveHeightPower eqs vars := by
  unfold effectiveHeightPower
  simpa using
    (Nat.sub_le_sub_right
      (radicalDegree_le_two_pow_card p) 1)

theorem radicalRootSum_le_natBound
    (p : Fin (vars + eqs) → ℕ) :
    radicalRootSum p ≤ radicalRootNatBound p := by
  unfold radicalRootSum radicalRootNatBound
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro i _
  have hsquare :
      Real.sqrt (p i : ℝ) ^ 2 = (p i : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg (p i))
  have hsqrt : 0 ≤ Real.sqrt (p i : ℝ) :=
    Real.sqrt_nonneg _
  push_cast
  nlinarith

theorem linearColumnEnergy_le_systemWeight
    (I : DQLSystem eqs vars) (j : Fin vars) :
    DetectorCharacterCode.linearColumnEnergy I j ≤
      dqlSystemWeight I := by
  unfold DetectorCharacterCode.linearColumnEnergy
  have hterm :
      ∀ row : Fin eqs,
        (I.linear row j).natAbs ≤ dqlRowWeight I row := by
    intro row
    have hsingle :
        (I.linear row j).natAbs ≤
          dqlRowCoefficientWeight I row := by
      unfold dqlRowCoefficientWeight
      calc
        (I.linear row j).natAbs ≤
            (I.quadratic row j).natAbs +
              (I.linear row j).natAbs := by omega
        _ ≤
            ∑ k : Fin vars,
              ((I.quadratic row k).natAbs +
                (I.linear row k).natAbs) :=
          Finset.single_le_sum
            (f := fun k : Fin vars ↦
              (I.quadratic row k).natAbs +
                (I.linear row k).natAbs)
            (fun _ _ ↦ Nat.zero_le _)
            (Finset.mem_univ j)
    unfold dqlRowWeight
    omega
  calc
    (∑ row : Fin eqs, (I.linear row j).natAbs) ≤
        ∑ row : Fin eqs, dqlRowWeight I row :=
      Finset.sum_le_sum fun row _ ↦ hterm row
    _ ≤ dqlSystemWeight I := by
      unfold dqlSystemWeight
      omega

/-- Any selector character satisfying the common quadratic energy bound
has a completely integral radical-height majorant. -/
theorem selectorCharacterHeight_le
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ)
    (j : Fin vars)
    (a : DetectorPhase eqs vars → ℤ)
    (L : ℕ)
    (henergy :
      DetectorCharacterCode.detectorCharacterEnergy a ≤
        4 * (1 +
          DetectorCharacterCode.linearColumnEnergy I j) *
            (1 + L) ^ 2) :
    characterHeight p a ≤
      (selectorHeightNatBound I p : ℝ) *
        (1 + (L : ℝ)) ^ 2 := by
  have hroot := radicalRootSum_le_natBound p
  have hcolumn := linearColumnEnergy_le_systemWeight I j
  calc
    characterHeight p a ≤
        radicalRootSum p *
          (DetectorCharacterCode.detectorCharacterEnergy a : ℝ) :=
      characterHeight_le_rootSum_mul_energy p a
    _ ≤
        (radicalRootNatBound p : ℝ) *
          ((4 * (1 +
              DetectorCharacterCode.linearColumnEnergy I j) *
                (1 + L) ^ 2 : ℕ) : ℝ) := by
      exact mul_le_mul hroot
        (Nat.cast_le.mpr henergy)
        (Nat.cast_nonneg _)
        (Nat.cast_nonneg _)
    _ ≤
        (radicalRootNatBound p : ℝ) *
          ((4 * (1 + dqlSystemWeight I) *
                (1 + L) ^ 2 : ℕ) : ℝ) := by
      gcongr
    _ =
        (selectorHeightNatBound I p : ℝ) *
          (1 + (L : ℝ)) ^ 2 := by
      simp only [selectorHeightNatBound, Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_add, Nat.cast_pow]
      ring

/-- Pair-selector version, obtained by weakening its sharper energy
constant to the common selector constant. -/
theorem pairSelectorCharacterHeight_le
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ)
    (j : Fin vars)
    (a : DetectorPhase eqs vars → ℤ)
    (L : ℕ)
    (henergy :
      DetectorCharacterCode.detectorCharacterEnergy a ≤
        4 * (1 + L) ^ 2) :
    characterHeight p a ≤
      (selectorHeightNatBound I p : ℝ) *
        (1 + (L : ℝ)) ^ 2 := by
  apply selectorCharacterHeight_le I p j a L
  have hW : 1 ≤ 1 +
      DetectorCharacterCode.linearColumnEnergy I j := by omega
  nlinarith

/-- The detector height coefficient also admits the integral root bound. -/
theorem detectorHeight_le
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ)
    (x : DetectorIndex vars) :
    RadicalSmallDivisor.radicalConjugateHeight p
        (DetectorCharacterCode.flattenCharacter
          (detectorExponent I x)) ≤
      (detectorHeightNatBound I p : ℝ) *
        (1 + (integerPairL1Energy x : ℝ)) ^ 2 := by
  calc
    RadicalSmallDivisor.radicalConjugateHeight p
        (DetectorCharacterCode.flattenCharacter
          (detectorExponent I x)) ≤
      detectorRadicalHeightConstant p I *
        (1 + (integerPairL1Energy x : ℝ)) ^ 2 :=
      radicalHeight_flattenedDetectorExponent_le_quadratic p I x
    _ ≤
      (detectorHeightNatBound I p : ℝ) *
        (1 + (integerPairL1Energy x : ℝ)) ^ 2 := by
      apply mul_le_mul_of_nonneg_right
      · unfold detectorRadicalHeightConstant
          detectorHeightNatBound
        push_cast
        exact mul_le_mul_of_nonneg_right
          (radicalRootSum_le_natBound p)
          (by positivity)
      · positivity

/-! ## Generic quantitative lattice lemma -/

/-- A coefficient with `2^{-L}` decay and a quadratic height bound has
an explicit weighted `tsum` bound. -/
theorem weightedTsum_le_geometricBudget
    {X : Type*}
    (energy : X → ℕ)
    (coefficient : X → ℂ)
    (height : X → ℝ)
    (D E : ℕ)
    (C B : ℕ)
    (hDE : D ≤ E)
    (hheight0 : ∀ x, 0 ≤ height x)
    (hcoefficient :
      ∀ x,
        ‖coefficient x‖ ≤
          (1 / 2 : ℝ) ^ energy x)
    (hheight :
      ∀ x,
        height x ≤
          (C : ℝ) * (1 + (energy x : ℝ)) ^ 2)
    (hbase :
      Summable fun x ↦
        (1 + (energy x : ℝ)) ^ (2 * E) *
          (1 / 2 : ℝ) ^ energy x)
    (hbaseBound :
      (∑' x,
        (1 + (energy x : ℝ)) ^ (2 * E) *
          (1 / 2 : ℝ) ^ energy x) ≤
        (B : ℝ)) :
    (∑' x,
      ‖coefficient x‖ * height x ^ D) ≤
        ((1 + C) ^ E * B : ℕ) := by
  let base : X → ℝ :=
    fun x ↦
      (1 + (energy x : ℝ)) ^ (2 * E) *
        (1 / 2 : ℝ) ^ energy x
  let majorant : X → ℝ :=
    fun x ↦ ((1 + C : ℕ) : ℝ) ^ E * base x
  have hmajorant : Summable majorant :=
    hbase.mul_left (((1 + C : ℕ) : ℝ) ^ E)
  have hpoint :
      ∀ x,
        ‖coefficient x‖ * height x ^ D ≤
          majorant x := by
    intro x
    have hheightOne :
        height x ≤ 1 + height x := by linarith
    have hpowDE :
        height x ^ D ≤ (1 + height x) ^ E := by
      calc
        height x ^ D ≤ (1 + height x) ^ D :=
          pow_le_pow_left₀ (hheight0 x) hheightOne D
        _ ≤ (1 + height x) ^ E := by
          exact pow_le_pow_right₀ (by
            linarith [hheight0 x]) hDE
    have hheightMajor :
        1 + height x ≤
          (1 + (C : ℝ)) *
            (1 + (energy x : ℝ)) ^ 2 := by
      have hpoly :
          1 ≤ (1 + (energy x : ℝ)) ^ 2 := by
        nlinarith [show 0 ≤ (energy x : ℝ) from
          Nat.cast_nonneg (energy x)]
      calc
        1 + height x ≤
            1 + (C : ℝ) *
              (1 + (energy x : ℝ)) ^ 2 := by
          linarith [hheight x]
        _ ≤
            (1 + (C : ℝ)) *
              (1 + (energy x : ℝ)) ^ 2 := by
          nlinarith [hpoly,
            show 0 ≤ (C : ℝ) from Nat.cast_nonneg C]
    have hpow :
        height x ^ D ≤
          ((1 + (C : ℝ)) *
            (1 + (energy x : ℝ)) ^ 2) ^ E :=
      hpowDE.trans
        (pow_le_pow_left₀ (by
          linarith [hheight0 x]) hheightMajor E)
    unfold majorant base
    calc
      ‖coefficient x‖ * height x ^ D ≤
          (1 / 2 : ℝ) ^ energy x *
            (((1 + (C : ℝ)) *
              (1 + (energy x : ℝ)) ^ 2) ^ E) :=
        mul_le_mul (hcoefficient x) hpow
          (pow_nonneg (hheight0 x) _)
          (by positivity)
      _ =
          ((1 + C : ℕ) : ℝ) ^ E *
            ((1 + (energy x : ℝ)) ^ (2 * E) *
              (1 / 2 : ℝ) ^ energy x) := by
        push_cast
        rw [mul_pow, ← pow_mul]
        ring
  have hleft :
      Summable fun x ↦
        ‖coefficient x‖ * height x ^ D :=
    Summable.of_nonneg_of_le
      (fun x ↦ mul_nonneg (norm_nonneg _)
        (pow_nonneg (hheight0 x) _))
      hpoint hmajorant
  calc
    (∑' x,
      ‖coefficient x‖ * height x ^ D) ≤
        ∑' x, majorant x :=
      hleft.tsum_le_tsum hpoint hmajorant
    _ =
        (((1 + C : ℕ) : ℝ) ^ E) *
          ∑' x, base x := by
      exact tsum_mul_left
    _ ≤
        (((1 + C : ℕ) : ℝ) ^ E) * (B : ℝ) := by
      exact mul_le_mul_of_nonneg_left hbaseBound (by positivity)
    _ = (((1 + C) ^ E * B : ℕ) : ℝ) := by
      push_cast
      ring

/-! ## Explicit coefficient decay -/

theorem norm_thetaCoefficient_le_halfGeometric
    (n : ℤ) :
    ‖CanonicalSelectorMomentZeroModes.thetaCoefficient n‖ ≤
      (1 / 2 : ℝ) ^ n.natAbs := by
  rw [norm_thetaCoefficient]
  have henergy :
      n.natAbs ≤ n.natAbs ^ 2 := by
    simpa only [pow_two] using n.natAbs.le_mul_self
  calc
    (1 / 256 : ℝ) ^ (n.natAbs ^ 2) ≤
        (1 / 256 : ℝ) ^ n.natAbs :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) henergy
    _ ≤ (1 / 2 : ℝ) ^ n.natAbs := by
      exact pow_le_pow_left₀ (by norm_num)
        (by norm_num) n.natAbs

theorem norm_rootP4Coefficient_le_halfGeometric
    (nm : ℤ × ℤ) :
    ‖CanonicalSelectorMomentZeroModes.rootP4Coefficient nm‖ ≤
      (1 / 2 : ℝ) ^ integerPairAbsEnergy nm := by
  rw [norm_rootP4Coefficient]
  have henergy :
      integerPairAbsEnergy nm ≤
        nm.1.natAbs ^ 2 + nm.2.natAbs ^ 2 := by
    unfold integerPairAbsEnergy
    exact Nat.add_le_add
      (by simpa only [pow_two] using nm.1.natAbs.le_mul_self)
      (by simpa only [pow_two] using nm.2.natAbs.le_mul_self)
  calc
    (1 / 256 : ℝ) ^
        (nm.1.natAbs ^ 2 + nm.2.natAbs ^ 2) ≤
      (1 / 256 : ℝ) ^ integerPairAbsEnergy nm :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) henergy
    _ ≤
      (1 / 2 : ℝ) ^ integerPairAbsEnergy nm := by
        exact pow_le_pow_left₀ (by norm_num)
          (by norm_num) _

private theorem natAbs_le_oddSquare_effective (n : ℤ) :
    n.natAbs ≤ (2 * n + 1).natAbs ^ 2 := by
  cases n with
  | ofNat k =>
      change
        k ≤ (2 * (Int.ofNat k) + 1).natAbs ^ 2
      have heq :
          2 * (Int.ofNat k) + 1 =
            Int.ofNat (2 * k + 1) := by norm_num
      have habs :
          (2 * (Int.ofNat k) + 1).natAbs =
            2 * k + 1 := by
        rw [heq]
        rfl
      rw [habs]
      nlinarith
  | negSucc k =>
      have heq :
          2 * Int.negSucc k + 1 =
            Int.negSucc (2 * k) := by omega
      rw [heq]
      simp
      nlinarith

theorem norm_rootP2Coefficient_le_halfGeometric
    (nm : ℤ × ℤ) :
    ‖CanonicalSelectorMomentZeroModes.rootP2Coefficient nm‖ ≤
      (1 / 2 : ℝ) ^ integerPairAbsEnergy nm := by
  rw [norm_rootP2Coefficient]
  have henergy :
      integerPairAbsEnergy nm ≤
        (2 * nm.1 + 1).natAbs ^ 2 +
          (2 * nm.2 + 1).natAbs ^ 2 := by
    unfold integerPairAbsEnergy
    exact Nat.add_le_add
      (natAbs_le_oddSquare_effective nm.1)
      (natAbs_le_oddSquare_effective nm.2)
  calc
    (1 / 4 : ℝ) ^
        ((2 * nm.1 + 1).natAbs ^ 2 +
          (2 * nm.2 + 1).natAbs ^ 2) ≤
      (1 / 4 : ℝ) ^ integerPairAbsEnergy nm :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) henergy
    _ ≤
      (1 / 2 : ℝ) ^ integerPairAbsEnergy nm := by
        exact pow_le_pow_left₀ (by norm_num)
          (by norm_num) _

theorem norm_detectorCoefficient_le_halfGeometric
    (x : DetectorIndex vars) :
    ‖detectorCoefficient
        thetaParameter poissonParameter x‖ ≤
      (1 / 2 : ℝ) ^ integerPairL1Energy x := by
  exact
    norm_detectorCoefficient_le_pairGeometric
      (lambda := thetaParameter)
      (eta := poissonParameter)
      (q := (1 / 2 : ℝ))
      (by norm_num [thetaParameter])
      (by norm_num [thetaParameter])
      (by norm_num [poissonParameter])
      (by norm_num [poissonParameter])
      (by norm_num) (by norm_num) x

/-! ## Raw weighted sums -/

/-- Common quantitative theorem for a one-index theta selector. -/
theorem thetaWeightedTsum_le
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ)
    (j : Fin vars)
    (a : ℤ → DetectorPhase eqs vars → ℤ)
    (henergy :
      ∀ n,
        DetectorCharacterCode.detectorCharacterEnergy (a n) ≤
          4 * (1 +
            DetectorCharacterCode.linearColumnEnergy I j) *
              (1 + n.natAbs) ^ 2) :
    (∑' n : ℤ,
      ‖CanonicalSelectorMomentZeroModes.thetaCoefficient n‖ *
        characterHeight p (a n) ^
          (radicalDegree p - 1)) ≤
      ((1 + selectorHeightNatBound I p) ^
          effectiveHeightPower eqs vars *
        oneDimensionalBudget eqs vars : ℕ) := by
  let D := radicalDegree p - 1
  let E := effectiveHeightPower eqs vars
  let C := selectorHeightNatBound I p
  let B := oneDimensionalBudget eqs vars
  apply
    weightedTsum_le_geometricBudget
      (energy := fun n : ℤ ↦ n.natAbs)
      (coefficient :=
        CanonicalSelectorMomentZeroModes.thetaCoefficient)
      (height := fun n ↦ characterHeight p (a n))
      D E C B
  · exact effectiveHeightPower_dominates_exact p
  · intro n
    exact characterHeight_nonneg p (a n)
  · exact norm_thetaCoefficient_le_halfGeometric
  · intro n
    exact selectorCharacterHeight_le
      I p j (a n) n.natAbs (henergy n)
  · change
      Summable (halfPolynomialIntWeight (2 * E))
    exact summable_halfPolynomialIntWeight (2 * E)
  · change
      (∑' n : ℤ, halfPolynomialIntWeight (2 * E) n) ≤
        (B : ℝ)
    exact tsum_halfPolynomialIntWeight_le (2 * E)

/-- Common quantitative theorem for a two-index selector. -/
theorem pairWeightedTsum_le
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ)
    (j : Fin vars)
    (coefficient : ℤ × ℤ → ℂ)
    (a : ℤ × ℤ → DetectorPhase eqs vars → ℤ)
    (hcoefficient :
      ∀ nm,
        ‖coefficient nm‖ ≤
          (1 / 2 : ℝ) ^ integerPairAbsEnergy nm)
    (henergy :
      ∀ nm,
        DetectorCharacterCode.detectorCharacterEnergy (a nm) ≤
          4 * (1 + integerPairAbsEnergy nm) ^ 2) :
    (∑' nm : ℤ × ℤ,
      ‖coefficient nm‖ *
        characterHeight p (a nm) ^
          (radicalDegree p - 1)) ≤
      ((1 + selectorHeightNatBound I p) ^
          effectiveHeightPower eqs vars *
        oneDimensionalBudget eqs vars ^ 2 : ℕ) := by
  let D := radicalDegree p - 1
  let E := effectiveHeightPower eqs vars
  let C := selectorHeightNatBound I p
  let B := oneDimensionalBudget eqs vars ^ 2
  apply
    weightedTsum_le_geometricBudget
      (energy := integerPairAbsEnergy)
      (coefficient := coefficient)
      (height := fun nm ↦ characterHeight p (a nm))
      D E C B
  · exact effectiveHeightPower_dominates_exact p
  · intro nm
    exact characterHeight_nonneg p (a nm)
  · exact hcoefficient
  · intro nm
    exact pairSelectorCharacterHeight_le
      I p j (a nm) (integerPairAbsEnergy nm)
      (henergy nm)
  · exact
      summable_polynomialGeometricIntPairWeight
        (q := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
        (2 * E)
  · change
      (∑' nm : ℤ × ℤ,
        (1 + (integerPairAbsEnergy nm : ℝ)) ^ (2 * E) *
          (1 / 2 : ℝ) ^ integerPairAbsEnergy nm) ≤
        (B : ℝ)
    simpa [B, oneDimensionalBudget] using
      tsum_halfPolynomialIntPairWeight_le (2 * E)

/-- Quantitative raw detector sum. -/
theorem detectorWeightedTsum_le
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) :
    (∑' x : DetectorIndex vars,
      ‖detectorCoefficient
          thetaParameter poissonParameter x‖ *
        RadicalSmallDivisor.radicalConjugateHeight p
            (DetectorCharacterCode.flattenCharacter
              (detectorExponent I x)) ^
          (radicalDegree p - 1)) ≤
      (detectorRawBudget I p : ℕ) := by
  let D := radicalDegree p - 1
  let E := effectiveHeightPower eqs vars
  let C := detectorHeightNatBound I p
  let B := oneDimensionalBudget eqs vars ^ (vars + vars)
  apply
    weightedTsum_le_geometricBudget
      (energy := integerPairL1Energy)
      (coefficient :=
        detectorCoefficient thetaParameter poissonParameter)
      (height := fun x ↦
        RadicalSmallDivisor.radicalConjugateHeight p
          (DetectorCharacterCode.flattenCharacter
            (detectorExponent I x)))
      D E C B
  · exact effectiveHeightPower_dominates_exact p
  · intro x
    exact RadicalSmallDivisor.radicalConjugateHeight_nonneg _ _
  · exact norm_detectorCoefficient_le_halfGeometric
  · exact detectorHeight_le I p
  · change
      Summable (halfPolynomialPairWeight vars (2 * E))
    exact summable_halfPolynomialPairWeight vars (2 * E)
  · change
      (∑' x : DetectorIndex vars,
        halfPolynomialPairWeight vars (2 * E) x) ≤
          (B : ℝ)
    simpa [B, oneDimensionalBudget] using
      tsum_halfPolynomialPairWeight_le vars (2 * E)

/-! ## The seven centered selector families -/

/-- Adjoining one constant centering term costs at most one unit in a
weighted `ℓ¹` budget.  This is stated independently of the canonical
families because the same adapter is useful for any explicitly centered
Fourier expansion. -/
theorem centeredRawWeightedTsum_le_one_add
    {X : Type*}
    (center : ℂ)
    (rawCoefficient : X → ℂ)
    (rawExponent : X → DetectorPhase eqs vars → ℤ)
    (p : Fin (vars + eqs) → ℕ)
    (D : ℕ)
    (B : ℝ)
    (hcenter : ‖center‖ ≤ 1)
    (hrawSummable :
      Summable fun x : X ↦
        ‖rawCoefficient x‖ *
          characterHeight p (rawExponent x) ^ D)
    (hrawBound :
      (∑' x : X,
        ‖rawCoefficient x‖ *
          characterHeight p (rawExponent x) ^ D) ≤ B) :
    (∑' i : CenteredFourierIndex X,
      ‖centeredFourierCoefficient center rawCoefficient i‖ *
        characterHeight p
            (centeredFourierExponent rawExponent i) ^ D) ≤
      1 + B := by
  let term : CenteredFourierIndex X → ℝ :=
    fun i ↦
      ‖centeredFourierCoefficient center rawCoefficient i‖ *
        characterHeight p
            (centeredFourierExponent rawExponent i) ^ D
  have hleft :
      Summable (term ∘ Sum.inl) :=
    (hasSum_fintype (term ∘ Sum.inl)).summable
  have hright :
      Summable (term ∘ Sum.inr) := by
    simpa [term, centeredFourierCoefficient,
      centeredFourierExponent] using hrawSummable
  rw [hleft.tsum_sum hright]
  apply add_le_add
  · cases D with
    | zero =>
        simpa [term, centeredFourierCoefficient,
          centeredFourierExponent] using hcenter
    | succ D =>
        simp [term, centeredFourierCoefficient,
          centeredFourierExponent, characterHeight,
          RadicalSmallDivisor.radicalConjugateHeight,
          DetectorCharacterCode.flattenCharacter]
  · simpa [term, centeredFourierCoefficient,
      centeredFourierExponent] using hrawBound

/-- Common effective estimate for a centered one-dimensional theta
family.  The extra square on `oneDimensionalBudget` is deliberate: it
lets all seven selector moments share one numerical budget. -/
theorem centeredThetaRawWeightedTsum_le_selectorRawBudget
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ)
    (j : Fin vars)
    (center : ℂ)
    (rawExponent : ℤ → DetectorPhase eqs vars → ℤ)
    (hcenter : ‖center‖ ≤ 1)
    (hrawSummable :
      Summable fun n : ℤ ↦
        ‖CanonicalSelectorMomentZeroModes.thetaCoefficient n‖ *
          characterHeight p (rawExponent n) ^
            (radicalDegree p - 1))
    (henergy :
      ∀ n,
        DetectorCharacterCode.detectorCharacterEnergy
            (rawExponent n) ≤
          4 * (1 +
            DetectorCharacterCode.linearColumnEnergy I j) *
              (1 + n.natAbs) ^ 2) :
    (∑' i : CenteredFourierIndex ℤ,
      ‖centeredFourierCoefficient center
          CanonicalSelectorMomentZeroModes.thetaCoefficient i‖ *
        characterHeight p
            (centeredFourierExponent rawExponent i) ^
          (radicalDegree p - 1)) ≤
      (selectorRawBudget I p : ℕ) := by
  let D := radicalDegree p - 1
  let A :=
    (1 + selectorHeightNatBound I p) ^
      effectiveHeightPower eqs vars
  let B := oneDimensionalBudget eqs vars
  have hraw :
      (∑' n : ℤ,
        ‖CanonicalSelectorMomentZeroModes.thetaCoefficient n‖ *
          characterHeight p (rawExponent n) ^ D) ≤
        ((A * B : ℕ) : ℝ) := by
    simpa [D, A, B] using
      thetaWeightedTsum_le I p j rawExponent henergy
  have hcentered :=
    centeredRawWeightedTsum_le_one_add
      (eqs := eqs) (vars := vars)
      center
      CanonicalSelectorMomentZeroModes.thetaCoefficient
      rawExponent p D (((A * B : ℕ) : ℝ))
      hcenter
      (by simpa [D] using hrawSummable)
      hraw
  have hBpositive : 0 < B := by
    unfold B oneDimensionalBudget halfPolynomialIntBudget
    positivity
  have hB : B ≤ B ^ 2 := by
    simpa only [pow_two] using
      Nat.le_mul_of_pos_left B hBpositive
  calc
    (∑' i : CenteredFourierIndex ℤ,
      ‖centeredFourierCoefficient center
          CanonicalSelectorMomentZeroModes.thetaCoefficient i‖ *
        characterHeight p
            (centeredFourierExponent rawExponent i) ^
          (radicalDegree p - 1)) ≤
        1 + (((A * B : ℕ) : ℝ)) := by
      simpa [D] using hcentered
    _ ≤ (selectorRawBudget I p : ℕ) := by
      unfold selectorRawBudget
      push_cast
      have hnat : 1 + A * B ≤ 1 + A * B ^ 2 :=
        Nat.add_le_add_left (Nat.mul_le_mul_left A hB) 1
      exact_mod_cast hnat

/-- Common effective estimate for a centered two-dimensional selector
family. -/
theorem centeredPairRawWeightedTsum_le_selectorRawBudget
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ)
    (j : Fin vars)
    (center : ℂ)
    (rawCoefficient : ℤ × ℤ → ℂ)
    (rawExponent :
      ℤ × ℤ → DetectorPhase eqs vars → ℤ)
    (hcenter : ‖center‖ ≤ 1)
    (hrawSummable :
      Summable fun nm : ℤ × ℤ ↦
        ‖rawCoefficient nm‖ *
          characterHeight p (rawExponent nm) ^
            (radicalDegree p - 1))
    (hcoefficient :
      ∀ nm,
        ‖rawCoefficient nm‖ ≤
          (1 / 2 : ℝ) ^ integerPairAbsEnergy nm)
    (henergy :
      ∀ nm,
        DetectorCharacterCode.detectorCharacterEnergy
            (rawExponent nm) ≤
          4 * (1 + integerPairAbsEnergy nm) ^ 2) :
    (∑' i : CenteredFourierIndex (ℤ × ℤ),
      ‖centeredFourierCoefficient center rawCoefficient i‖ *
        characterHeight p
            (centeredFourierExponent rawExponent i) ^
          (radicalDegree p - 1)) ≤
      (selectorRawBudget I p : ℕ) := by
  let D := radicalDegree p - 1
  let M :=
    (1 + selectorHeightNatBound I p) ^
        effectiveHeightPower eqs vars *
      oneDimensionalBudget eqs vars ^ 2
  have hraw :
      (∑' nm : ℤ × ℤ,
        ‖rawCoefficient nm‖ *
          characterHeight p (rawExponent nm) ^ D) ≤
        (M : ℝ) := by
    simpa [D, M] using
      pairWeightedTsum_le
        I p j rawCoefficient rawExponent
        hcoefficient henergy
  have hcentered :=
    centeredRawWeightedTsum_le_one_add
      (eqs := eqs) (vars := vars)
      center rawCoefficient rawExponent p D (M : ℝ)
      hcenter
      (by simpa [D] using hrawSummable)
      hraw
  simpa [selectorRawBudget, M, D] using hcentered

/-- Explicit raw budget for the centered unary mean selector. -/
theorem unaryMeanRawWeightedTsum_le
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ)
    (j : Fin vars) :
    (∑' i : (unaryMean I j).Index,
      ‖(unaryMean I j).coefficient i‖ *
        RadicalSmallDivisor.radicalConjugateHeight p
            ((unaryMean I j).flatExponent i) ^
          (radicalDegree p - 1)) ≤
      (selectorRawBudget I p : ℕ) := by
  let D := radicalDegree p - 1
  have hraw :
      (∑' n : ℤ,
        ‖CanonicalSelectorMomentZeroModes.thetaCoefficient n‖ *
          characterHeight p
              (CanonicalSelectorMomentZeroModes.unaryExponent
                (eqs := eqs) j n) ^ D) ≤
        ((1 + selectorHeightNatBound I p) ^
            effectiveHeightPower eqs vars *
          oneDimensionalBudget eqs vars : ℕ) :=
    thetaWeightedTsum_le I p j
      (CanonicalSelectorMomentZeroModes.unaryExponent
        (eqs := eqs) j)
      (fun n ↦ by
        have hbase := unaryExponent_energy_le
          (eqs := eqs) j n
        have hfactor :
            1 ≤
              1 +
                DetectorCharacterCode.linearColumnEnergy I j := by
          omega
        nlinarith)
  have hrawSummable :
      Summable fun n : ℤ ↦
        ‖CanonicalSelectorMomentZeroModes.thetaCoefficient n‖ *
          characterHeight p
              (CanonicalSelectorMomentZeroModes.unaryExponent
                (eqs := eqs) j n) ^ D := by
    have htotal := (unaryMean I j).summable_height p D
    simpa [unaryMean, RawCenteredFamily.flatExponent,
      characterHeight, centeredFourierCoefficient,
      centeredFourierExponent] using
      htotal.comp_injective Sum.inr_injective
  have hcentered :=
    centeredRawWeightedTsum_le_one_add
      (eqs := eqs) (vars := vars)
      (1 : ℂ)
      CanonicalSelectorMomentZeroModes.thetaCoefficient
      (CanonicalSelectorMomentZeroModes.unaryExponent
        (eqs := eqs) j)
      p D
      (((1 + selectorHeightNatBound I p) ^
          effectiveHeightPower eqs vars *
        oneDimensionalBudget eqs vars : ℕ) : ℝ)
      (by simp)
      hrawSummable
      (by simpa [D] using hraw)
  calc
    (∑' i : (unaryMean I j).Index,
      ‖(unaryMean I j).coefficient i‖ *
        RadicalSmallDivisor.radicalConjugateHeight p
            ((unaryMean I j).flatExponent i) ^
          (radicalDegree p - 1)) ≤
        1 +
          (((1 + selectorHeightNatBound I p) ^
              effectiveHeightPower eqs vars *
            oneDimensionalBudget eqs vars : ℕ) : ℝ) := by
      simpa [unaryMean, RawCenteredFamily.flatExponent,
        characterHeight, D] using hcentered
    _ ≤ (selectorRawBudget I p : ℕ) := by
      unfold selectorRawBudget
      push_cast
      have hBpositive : 0 < oneDimensionalBudget eqs vars := by
        unfold oneDimensionalBudget halfPolynomialIntBudget
        positivity
      have hBpos : 1 ≤ oneDimensionalBudget eqs vars := by omega
      have hpow :
          oneDimensionalBudget eqs vars ≤
            oneDimensionalBudget eqs vars ^ 2 := by
        simpa only [pow_two] using
          Nat.le_mul_of_pos_left
            (oneDimensionalBudget eqs vars)
            (by omega)
      gcongr
      exact_mod_cast hpow

/-- Explicit raw budget for the centered first unary harmonic. -/
theorem unaryFirstRawWeightedTsum_le
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ)
    (j : Fin vars) :
    (∑' i : (unaryFirst I j).Index,
      ‖(unaryFirst I j).coefficient i‖ *
        RadicalSmallDivisor.radicalConjugateHeight p
            ((unaryFirst I j).flatExponent i) ^
          (radicalDegree p - 1)) ≤
      (selectorRawBudget I p : ℕ) := by
  let D := radicalDegree p - 1
  have htotal := (unaryFirst I j).summable_height p D
  have hrawSummable :
      Summable fun n : ℤ ↦
        ‖CanonicalSelectorMomentZeroModes.thetaCoefficient n‖ *
          characterHeight p
              (CanonicalSelectorMomentZeroModes.unaryFirstExponent
                (eqs := eqs) j n) ^ D := by
    simpa [unaryFirst, RawCenteredFamily.flatExponent,
      characterHeight, centeredFourierCoefficient,
      centeredFourierExponent] using
      htotal.comp_injective Sum.inr_injective
  have hbound :=
    centeredThetaRawWeightedTsum_le_selectorRawBudget
      I p j (((1 / 128 : ℝ) : ℂ))
      (CanonicalSelectorMomentZeroModes.unaryFirstExponent
        (eqs := eqs) j)
      (by norm_num)
      (by simpa [D] using hrawSummable)
      (fun n ↦ by
        have hbase := unaryFirstExponent_energy_le
          (eqs := eqs) j n
        have hfactor :
            1 ≤
              1 +
                DetectorCharacterCode.linearColumnEnergy I j := by
          omega
        nlinarith)
  simpa [unaryFirst, RawCenteredFamily.flatExponent,
    characterHeight] using hbound

/-- Explicit raw budget for the centered fourth-theta root moment. -/
theorem rootP4RawWeightedTsum_le
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ)
    (j : Fin vars) :
    (∑' i : (rootP4 (eqs := eqs) j).Index,
      ‖(rootP4 (eqs := eqs) j).coefficient i‖ *
        RadicalSmallDivisor.radicalConjugateHeight p
            ((rootP4 (eqs := eqs) j).flatExponent i) ^
          (radicalDegree p - 1)) ≤
      (selectorRawBudget I p : ℕ) := by
  let D := radicalDegree p - 1
  have htotal := (rootP4 (eqs := eqs) j).summable_height p D
  have hrawSummable :
      Summable fun nm : ℤ × ℤ ↦
        ‖CanonicalSelectorMomentZeroModes.rootP4Coefficient nm‖ *
          characterHeight p
              (CanonicalSelectorMomentZeroModes.rootP4Exponent
                (eqs := eqs) j nm) ^ D := by
    simpa [rootP4, RawCenteredFamily.flatExponent,
      characterHeight, centeredFourierCoefficient,
      centeredFourierExponent] using
      htotal.comp_injective Sum.inr_injective
  have hbound :=
    centeredPairRawWeightedTsum_le_selectorRawBudget
      I p j (1 : ℂ)
      CanonicalSelectorMomentZeroModes.rootP4Coefficient
      (CanonicalSelectorMomentZeroModes.rootP4Exponent
        (eqs := eqs) j)
      (by simp)
      (by simpa [D] using hrawSummable)
      norm_rootP4Coefficient_le_halfGeometric
      (rootP4Exponent_energy_le (eqs := eqs) j)
  simpa [rootP4, RawCenteredFamily.flatExponent,
    characterHeight] using hbound

/-- Explicit raw budget for the centered second-theta root moment. -/
theorem rootP2RawWeightedTsum_le
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ)
    (j : Fin vars) :
    (∑' i : (rootP2 (eqs := eqs) j).Index,
      ‖(rootP2 (eqs := eqs) j).coefficient i‖ *
        RadicalSmallDivisor.radicalConjugateHeight p
            ((rootP2 (eqs := eqs) j).flatExponent i) ^
          (radicalDegree p - 1)) ≤
      (selectorRawBudget I p : ℕ) := by
  let D := radicalDegree p - 1
  have htotal := (rootP2 (eqs := eqs) j).summable_height p D
  have hrawSummable :
      Summable fun nm : ℤ × ℤ ↦
        ‖CanonicalSelectorMomentZeroModes.rootP2Coefficient nm‖ *
          characterHeight p
              (CanonicalSelectorMomentZeroModes.rootP2Exponent
                (eqs := eqs) j nm) ^ D := by
    simpa [rootP2, RawCenteredFamily.flatExponent,
      characterHeight, centeredFourierCoefficient,
      centeredFourierExponent] using
      htotal.comp_injective Sum.inr_injective
  have hbound :=
    centeredPairRawWeightedTsum_le_selectorRawBudget
      I p j (((1 / 4 : ℝ) : ℂ))
      CanonicalSelectorMomentZeroModes.rootP2Coefficient
      (CanonicalSelectorMomentZeroModes.rootP2Exponent
        (eqs := eqs) j)
      (by norm_num)
      (by simpa [D] using hrawSummable)
      norm_rootP2Coefficient_le_halfGeometric
      (rootP2Exponent_energy_le (eqs := eqs) j)
  simpa [rootP2, RawCenteredFamily.flatExponent,
    characterHeight] using hbound

/-- Explicit raw budget for the centered Jacobi mean. -/
theorem jacobiMeanRawWeightedTsum_le
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ)
    (j : Fin vars) :
    (∑' i : (jacobiMean I j).Index,
      ‖(jacobiMean I j).coefficient i‖ *
        RadicalSmallDivisor.radicalConjugateHeight p
            ((jacobiMean I j).flatExponent i) ^
          (radicalDegree p - 1)) ≤
      (selectorRawBudget I p : ℕ) := by
  let D := radicalDegree p - 1
  have htotal := (jacobiMean I j).summable_height p D
  have hrawSummable :
      Summable fun n : ℤ ↦
        ‖CanonicalSelectorMomentZeroModes.thetaCoefficient n‖ *
          characterHeight p
              (CanonicalSelectorMomentZeroModes.jacobiMeanExponent
                I j n) ^ D := by
    simpa [jacobiMean, RawCenteredFamily.flatExponent,
      characterHeight, centeredFourierCoefficient,
      centeredFourierExponent] using
      htotal.comp_injective Sum.inr_injective
  have hbound :=
    centeredThetaRawWeightedTsum_le_selectorRawBudget
      I p j (1 : ℂ)
      (CanonicalSelectorMomentZeroModes.jacobiMeanExponent I j)
      (by simp)
      (by simpa [D] using hrawSummable)
      (jacobiMeanExponent_energy_le I j)
  simpa [jacobiMean, RawCenteredFamily.flatExponent,
    characterHeight] using hbound

/-- The rational Jacobi center always has complex norm at most one. -/
theorem norm_selectorCenter_le_one
    (I : DQLSystem eqs vars)
    (j : Fin vars) :
    ‖(((CorrectedJacobiSelectorCentering.selectorCenter
        I j : ℚ) : ℂ))‖ ≤ 1 := by
  unfold CorrectedJacobiSelectorCentering.selectorCenter
  split <;> norm_num

/-- Explicit raw budget for the corrected positive Jacobi selector. -/
theorem jacobiPlusRawWeightedTsum_le
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ)
    (j : Fin vars) :
    (∑' i : (jacobiPlus I j).Index,
      ‖(jacobiPlus I j).coefficient i‖ *
        RadicalSmallDivisor.radicalConjugateHeight p
            ((jacobiPlus I j).flatExponent i) ^
          (radicalDegree p - 1)) ≤
      (selectorRawBudget I p : ℕ) := by
  let D := radicalDegree p - 1
  have htotal := (jacobiPlus I j).summable_height p D
  have hrawSummable :
      Summable fun n : ℤ ↦
        ‖CanonicalSelectorMomentZeroModes.thetaCoefficient n‖ *
          characterHeight p
              (CorrectedJacobiSelectorCentering.plusExponent
                I j n) ^ D := by
    simpa [jacobiPlus, RawCenteredFamily.flatExponent,
      characterHeight,
      CorrectedJacobiSelectorCentering.centeredCoefficient,
      CorrectedJacobiSelectorCentering.centeredPlusExponent] using
      htotal.comp_injective Sum.inr_injective
  have hbound :=
    centeredThetaRawWeightedTsum_le_selectorRawBudget
      I p j
      (((CorrectedJacobiSelectorCentering.selectorCenter
          I j : ℚ) : ℂ))
      (CorrectedJacobiSelectorCentering.plusExponent I j)
      (norm_selectorCenter_le_one I j)
      (by simpa [D] using hrawSummable)
      (plusExponent_energy_le I j)
  calc
    (∑' i : (jacobiPlus I j).Index,
      ‖(jacobiPlus I j).coefficient i‖ *
        RadicalSmallDivisor.radicalConjugateHeight p
            ((jacobiPlus I j).flatExponent i) ^
          (radicalDegree p - 1)) =
        ∑' i : CenteredFourierIndex ℤ,
          ‖centeredFourierCoefficient
              (((CorrectedJacobiSelectorCentering.selectorCenter
                  I j : ℚ) : ℂ))
              CanonicalSelectorMomentZeroModes.thetaCoefficient i‖ *
            characterHeight p
                (centeredFourierExponent
                  (CorrectedJacobiSelectorCentering.plusExponent
                    I j) i) ^
              (radicalDegree p - 1) := by
      apply tsum_congr
      intro i
      rcases i with u | n
      · simp [jacobiPlus, RawCenteredFamily.flatExponent,
          characterHeight, centeredFourierCoefficient,
          centeredFourierExponent,
          CorrectedJacobiSelectorCentering.centeredCoefficient,
          CorrectedJacobiSelectorCentering.centeredPlusExponent]
      · simp [jacobiPlus, RawCenteredFamily.flatExponent,
          characterHeight, centeredFourierCoefficient,
          centeredFourierExponent,
          CorrectedJacobiSelectorCentering.centeredCoefficient,
          CorrectedJacobiSelectorCentering.centeredPlusExponent,
          CanonicalSelectorMomentZeroModes.thetaCoefficient]
    _ ≤ (selectorRawBudget I p : ℕ) := hbound

/-- Explicit raw budget for the corrected negative Jacobi selector. -/
theorem jacobiMinusRawWeightedTsum_le
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ)
    (j : Fin vars) :
    (∑' i : (jacobiMinus I j).Index,
      ‖(jacobiMinus I j).coefficient i‖ *
        RadicalSmallDivisor.radicalConjugateHeight p
            ((jacobiMinus I j).flatExponent i) ^
          (radicalDegree p - 1)) ≤
      (selectorRawBudget I p : ℕ) := by
  let D := radicalDegree p - 1
  have htotal := (jacobiMinus I j).summable_height p D
  have hrawSummable :
      Summable fun n : ℤ ↦
        ‖CanonicalSelectorMomentZeroModes.thetaCoefficient n‖ *
          characterHeight p
              (CorrectedJacobiSelectorCentering.minusExponent
                I j n) ^ D := by
    simpa [jacobiMinus, RawCenteredFamily.flatExponent,
      characterHeight,
      CorrectedJacobiSelectorCentering.centeredCoefficient,
      CorrectedJacobiSelectorCentering.centeredMinusExponent] using
      htotal.comp_injective Sum.inr_injective
  have hbound :=
    centeredThetaRawWeightedTsum_le_selectorRawBudget
      I p j
      (((CorrectedJacobiSelectorCentering.selectorCenter
          I j : ℚ) : ℂ))
      (CorrectedJacobiSelectorCentering.minusExponent I j)
      (norm_selectorCenter_le_one I j)
      (by simpa [D] using hrawSummable)
      (minusExponent_energy_le I j)
  calc
    (∑' i : (jacobiMinus I j).Index,
      ‖(jacobiMinus I j).coefficient i‖ *
        RadicalSmallDivisor.radicalConjugateHeight p
            ((jacobiMinus I j).flatExponent i) ^
          (radicalDegree p - 1)) =
        ∑' i : CenteredFourierIndex ℤ,
          ‖centeredFourierCoefficient
              (((CorrectedJacobiSelectorCentering.selectorCenter
                  I j : ℚ) : ℂ))
              CanonicalSelectorMomentZeroModes.thetaCoefficient i‖ *
            characterHeight p
                (centeredFourierExponent
                  (CorrectedJacobiSelectorCentering.minusExponent
                    I j) i) ^
              (radicalDegree p - 1) := by
      apply tsum_congr
      intro i
      rcases i with u | n
      · simp [jacobiMinus, RawCenteredFamily.flatExponent,
          characterHeight, centeredFourierCoefficient,
          centeredFourierExponent,
          CorrectedJacobiSelectorCentering.centeredCoefficient,
          CorrectedJacobiSelectorCentering.centeredMinusExponent]
      · simp [jacobiMinus, RawCenteredFamily.flatExponent,
          characterHeight, centeredFourierCoefficient,
          centeredFourierExponent,
          CorrectedJacobiSelectorCentering.centeredCoefficient,
          CorrectedJacobiSelectorCentering.centeredMinusExponent,
          CanonicalSelectorMomentZeroModes.thetaCoefficient]
    _ ≤ (selectorRawBudget I p : ℕ) := hbound

/-! ## Uniform selector-family packaging -/

/-- Every one of the seven local selector families obeys the same
effective raw weighted bound. -/
theorem localFamilyRawWeightedTsum_le
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ)
    (j : Fin vars)
    (r : Fin CorrectedFixedDetectorMomentCode.localMomentCount) :
    (∑' i : (localFamily I j r).Index,
      ‖(localFamily I j r).coefficient i‖ *
        RadicalSmallDivisor.radicalConjugateHeight p
            ((localFamily I j r).flatExponent i) ^
          (radicalDegree p - 1)) ≤
      (selectorRawBudget I p : ℕ) := by
  fin_cases r
  · simpa [localFamily] using unaryMeanRawWeightedTsum_le I p j
  · simpa [localFamily] using unaryFirstRawWeightedTsum_le I p j
  · simpa [localFamily] using rootP4RawWeightedTsum_le I p j
  · simpa [localFamily] using rootP2RawWeightedTsum_le I p j
  · simpa [localFamily] using jacobiMeanRawWeightedTsum_le I p j
  · simpa [localFamily] using jacobiPlusRawWeightedTsum_le I p j
  · simpa [localFamily] using jacobiMinusRawWeightedTsum_le I p j

/-- The compiler-flattened complex selector index inherits the uniform
raw weighted bound. -/
theorem momentFamilyRawWeightedTsum_le
    (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ)
    (k : Fin (CorrectedFixedDetectorMomentCode.momentCount vars)) :
    (∑' i : (momentFamily I k).Index,
      ‖(momentFamily I k).coefficient i‖ *
        RadicalSmallDivisor.radicalConjugateHeight p
            ((momentFamily I k).flatExponent i) ^
          (radicalDegree p - 1)) ≤
      (selectorRawBudget I p : ℕ) := by
  let jr := finProdFinEquiv.symm k
  change
    (∑' i : (localFamily I jr.1 jr.2).Index,
      ‖(localFamily I jr.1 jr.2).coefficient i‖ *
        RadicalSmallDivisor.radicalConjugateHeight p
            ((localFamily I jr.1 jr.2).flatExponent i) ^
          (radicalDegree p - 1)) ≤
      (selectorRawBudget I p : ℕ)
  exact localFamilyRawWeightedTsum_le I p jr.1 jr.2

end HGAS.Analysis.CanonicalEffectivePrimitiveBudget
