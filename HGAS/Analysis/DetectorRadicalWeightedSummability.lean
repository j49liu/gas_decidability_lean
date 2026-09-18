import HGAS.Analysis.PolynomialWeightedLatticeSummability
import HGAS.Arithmetic.DetectorCharacterCode
import HGAS.Arithmetic.DetectorCharacterDegrees
import HGAS.Clocks.RadicalSmallDivisor
import Mathlib.Tactic

/-!
# Weighted Fourier summability for the arithmetic detector

The detector coefficient attached to `(x,s)` is

```text
       λ^(Σ |x_j|²) η^(Σ |s_j|).
```

If `λ` and `η` are bounded by one common `q < 1`, this is bounded by
`q^(Σ |x_j| + Σ |s_j|)`.  Thus any fixed polynomial loss in the lattice
height is summable.  In particular this absorbs the polynomial
small-divisor loss from the prime-square-root clock.

The final theorem is deliberately phrased using a polynomial bound on the
radical conjugate height.  This separates two logically different facts:

* the analytic fact proved here, that exponential detector decay absorbs
  every fixed polynomial loss;
* the finite algebraic estimate, specific to the chosen DQL instance,
  bounding its explicit quadratic-linear exponent map.

This separation makes the analytic module reusable for other
quadratic-exponential detectors.
-/

noncomputable section

open scoped BigOperators

namespace HGAS.Analysis

open HGAS.Clocks

variable {eqs vars : ℕ}

/-- The ordinary `ℓ¹` energy never exceeds the Gaussian energy
`Σ |x_j|²`. -/
theorem integerL1Energy_le_integerVectorEnergy
    (x : Fin vars → ℤ) :
    integerL1Energy x ≤ integerVectorEnergy x := by
  unfold integerL1Energy integerVectorEnergy
  apply Finset.sum_le_sum
  intro j _
  simpa only [pow_two] using (x j).natAbs.le_mul_self

/-- Exact norm of a detector coefficient under nonnegative parameters. -/
theorem norm_detectorCoefficient_eq
    {lambda eta : ℝ}
    (hlambda0 : 0 ≤ lambda) (heta0 : 0 ≤ eta)
    (p : DetectorIndex vars) :
    ‖detectorCoefficient lambda eta p‖ =
      lambda ^ integerVectorEnergy p.1 *
        eta ^ poissonEnergy p.2 := by
  simp only [detectorCoefficient, Complex.norm_real]
  exact abs_of_nonneg
    (mul_nonneg
      (pow_nonneg hlambda0 _)
      (pow_nonneg heta0 _))

/-- A detector coefficient is bounded by one common geometric weight on
the paired lattice. -/
theorem norm_detectorCoefficient_le_pairGeometric
    {lambda eta q : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambdaq : lambda ≤ q)
    (heta0 : 0 ≤ eta) (hetaq : eta ≤ q)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (p : DetectorIndex vars) :
    ‖detectorCoefficient lambda eta p‖ ≤
      q ^ integerPairL1Energy p := by
  have hxParameter :
      lambda ^ integerVectorEnergy p.1 ≤
        q ^ integerVectorEnergy p.1 :=
    pow_le_pow_left₀ hlambda0 hlambdaq _
  have hxExponent :
      q ^ integerVectorEnergy p.1 ≤
        q ^ integerL1Energy p.1 :=
    pow_le_pow_of_le_one hq0 hq1
      (integerL1Energy_le_integerVectorEnergy p.1)
  have hx :
      lambda ^ integerVectorEnergy p.1 ≤
        q ^ integerL1Energy p.1 :=
    hxParameter.trans hxExponent
  have hs :
      eta ^ poissonEnergy p.2 ≤
        q ^ poissonEnergy p.2 :=
    pow_le_pow_left₀ heta0 hetaq _
  rw [norm_detectorCoefficient_eq hlambda0 heta0 p]
  calc
    lambda ^ integerVectorEnergy p.1 *
        eta ^ poissonEnergy p.2 ≤
      q ^ integerL1Energy p.1 *
        q ^ poissonEnergy p.2 :=
      mul_le_mul hx hs
        (pow_nonneg heta0 _)
        (pow_nonneg hq0 _)
    _ = q ^
        (integerL1Energy p.1 + poissonEnergy p.2) := by
      rw [pow_add]
    _ = q ^ integerPairL1Energy p := by
      rw [integerPairL1Energy_eq]
      rfl

/-- Exponential detector decay absorbs any height which is polynomially
bounded in the paired `ℓ¹` lattice energy. -/
theorem
    summable_norm_detectorCoefficient_mul_height_pow_of_polynomial_bound
    {lambda eta q C : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambdaq : lambda ≤ q)
    (heta0 : 0 ≤ eta) (hetaq : eta ≤ q)
    (hq0 : 0 < q) (hq1 : q < 1)
    (heightPower growthPower : ℕ)
    (height : DetectorIndex vars → ℝ)
    (hheight0 : ∀ p, 0 ≤ height p)
    (hheight :
      ∀ p,
        height p ≤
          C * (1 + (integerPairL1Energy p : ℝ)) ^
            growthPower) :
    Summable fun p : DetectorIndex vars ↦
      ‖detectorCoefficient lambda eta p‖ *
        height p ^ heightPower := by
  have hmajor :
      Summable fun p : DetectorIndex vars ↦
        q ^ integerPairL1Energy p *
          height p ^ heightPower :=
    summable_pair_geometric_mul_height_pow_of_polynomial_bound
      hq0 hq1 vars heightPower growthPower
      height hheight0 hheight
  apply Summable.of_nonneg_of_le
  · intro p
    exact mul_nonneg (norm_nonneg _)
      (pow_nonneg (hheight0 p) _)
  · intro p
    exact mul_le_mul_of_nonneg_right
      (norm_detectorCoefficient_le_pairGeometric
        hlambda0 hlambdaq heta0 hetaq hq0.le hq1.le p)
      (pow_nonneg (hheight0 p) _)
  · exact hmajor

/-! ## A generic radical-height comparison -/

/-- Sum of the positive radical sizes in a fixed clock family. -/
def radicalRootSum {d : Type*} [Fintype d]
    (radicand : d → ℕ) : ℝ :=
  ∑ i : d, Real.sqrt (radicand i : ℝ)

theorem radicalRootSum_nonneg
    {d : Type*} [Fintype d]
    (radicand : d → ℕ) :
    0 ≤ radicalRootSum radicand := by
  unfold radicalRootSum
  exact Finset.sum_nonneg fun i _ ↦ Real.sqrt_nonneg _

private theorem abs_intCast_eq_natAbs_cast (z : ℤ) :
    |(z : ℝ)| = (z.natAbs : ℝ) := by
  rw [← Int.cast_abs]
  exact congrArg (fun a : ℤ ↦ (a : ℝ))
    (Int.natCast_natAbs z).symm

/-- The weighted radical height is at most the unweighted exponent
`ℓ¹`-energy times the fixed sum of the radical sizes. -/
theorem radicalConjugateHeight_le_rootSum_mul_integerL1Energy
    {d : Type*} [Fintype d]
    (radicand : d → ℕ) (exponent : d → ℤ) :
    RadicalSmallDivisor.radicalConjugateHeight
        radicand exponent ≤
      radicalRootSum radicand *
        ((∑ i : d, (exponent i).natAbs : ℕ) : ℝ) := by
  unfold RadicalSmallDivisor.radicalConjugateHeight
  have hroot :
      ∀ i : d,
        Real.sqrt (radicand i : ℝ) ≤
          radicalRootSum radicand := by
    intro i
    unfold radicalRootSum
    exact Finset.single_le_sum
      (fun j _ ↦ Real.sqrt_nonneg (radicand j : ℝ))
      (Finset.mem_univ i)
  calc
    (∑ i : d,
        |(exponent i : ℝ)| *
          Real.sqrt (radicand i : ℝ)) ≤
      ∑ i : d,
        |(exponent i : ℝ)| *
          radicalRootSum radicand := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (hroot i) (abs_nonneg _)
    _ =
        radicalRootSum radicand *
          ((∑ i : d,
            (exponent i).natAbs : ℕ) : ℝ) := by
      rw [Nat.cast_sum]
      simp_rw [abs_intCast_eq_natAbs_cast]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-! ## Quadratic growth of the explicit detector exponent -/

/-- Unsigned coefficient size in one equation row. -/
def dqlRowCoefficientWeight
    (I : DQLSystem eqs vars) (row : Fin eqs) : ℕ :=
  ∑ j : Fin vars,
    ((I.quadratic row j).natAbs +
      (I.linear row j).natAbs)

/-- Unsigned size of one entire equation row, including its right-hand
side. -/
def dqlRowWeight
    (I : DQLSystem eqs vars) (row : Fin eqs) : ℕ :=
  (I.rhs row).natAbs + dqlRowCoefficientWeight I row

/-- A positive size bound for all rows of a fixed DQL instance. -/
def dqlSystemWeight (I : DQLSystem eqs vars) : ℕ :=
  1 + ∑ row : Fin eqs, dqlRowWeight I row

theorem one_le_dqlSystemWeight
    (I : DQLSystem eqs vars) :
    1 ≤ dqlSystemWeight I := by
  unfold dqlSystemWeight
  omega

theorem dqlRowWeight_le_systemWeight
    (I : DQLSystem eqs vars) (row : Fin eqs) :
    dqlRowWeight I row ≤ dqlSystemWeight I := by
  unfold dqlSystemWeight
  have hsingle :
      dqlRowWeight I row ≤
        ∑ r : Fin eqs, dqlRowWeight I r :=
    Finset.single_le_sum
      (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ row)
  omega

private theorem left_natAbs_le_pairEnergy
    (x s : Fin vars → ℤ) (j : Fin vars) :
    (x j).natAbs ≤ integerPairL1Energy (x, s) := by
  rw [integerPairL1Energy_eq]
  have hsingle :
      (x j).natAbs ≤ integerL1Energy x := by
    unfold integerL1Energy
    exact Finset.single_le_sum
      (f := fun i : Fin vars ↦ (x i).natAbs)
      (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ j)
  change
    (x j).natAbs ≤
      integerL1Energy x + integerL1Energy s
  omega

private theorem right_natAbs_le_pairEnergy
    (x s : Fin vars → ℤ) (j : Fin vars) :
    (s j).natAbs ≤ integerPairL1Energy (x, s) := by
  rw [integerPairL1Energy_eq]
  have hsingle :
      (s j).natAbs ≤ integerL1Energy s := by
    unfold integerL1Energy
    exact Finset.single_le_sum
      (f := fun i : Fin vars ↦ (s i).natAbs)
      (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ j)
  change
    (s j).natAbs ≤
      integerL1Energy x + integerL1Energy s
  omega

/-- Every private exponent has quadratic growth in the paired lattice
energy. -/
theorem privatePhaseExponent_natAbs_le_quadratic
    (I : DQLSystem eqs vars)
    (x s : Fin vars → ℤ) (j : Fin vars) :
    (privatePhaseExponent x s j).natAbs ≤
      dqlSystemWeight I *
        (1 + integerPairL1Energy (x, s)) ^ 2 := by
  let L := integerPairL1Energy (x, s)
  let W := dqlSystemWeight I
  have hx : (x j).natAbs ≤ L :=
    left_natAbs_le_pairEnergy x s j
  have hs : (s j).natAbs ≤ L :=
    right_natAbs_le_pairEnergy x s j
  have hsub :=
    Int.natAbs_sub_le (x j ^ 2) (s j)
  have hW : 1 ≤ W :=
    one_le_dqlSystemWeight I
  simp only [privatePhaseExponent, Int.natAbs_pow] at hsub ⊢
  have hsq :
      (x j).natAbs ^ 2 ≤ L ^ 2 := by
    exact Nat.pow_le_pow_left hx 2
  nlinarith

/-- Every equation exponent has quadratic growth in the paired lattice
energy. -/
theorem equationPhaseExponent_natAbs_le_quadratic
    (I : DQLSystem eqs vars)
    (x s : Fin vars → ℤ) (row : Fin eqs) :
    (equationPhaseExponent I x s row).natAbs ≤
      dqlSystemWeight I *
        (1 + integerPairL1Energy (x, s)) ^ 2 := by
  let L := integerPairL1Energy (x, s)
  let W := dqlSystemWeight I
  let coefficientWeight := dqlRowCoefficientWeight I row
  let rowWeight := dqlRowWeight I row
  have hx :
      ∀ j : Fin vars, (x j).natAbs ≤ L :=
    fun j ↦ left_natAbs_le_pairEnergy x s j
  have hs :
      ∀ j : Fin vars, (s j).natAbs ≤ L :=
    fun j ↦ right_natAbs_le_pairEnergy x s j
  have hterm :
      ∀ j : Fin vars,
        (I.quadratic row j * s j +
          I.linear row j * x j).natAbs ≤
        ((I.quadratic row j).natAbs +
          (I.linear row j).natAbs) * L := by
    intro j
    calc
      (I.quadratic row j * s j +
          I.linear row j * x j).natAbs ≤
        (I.quadratic row j * s j).natAbs +
          (I.linear row j * x j).natAbs :=
        Int.natAbs_add_le _ _
      _ =
        (I.quadratic row j).natAbs * (s j).natAbs +
          (I.linear row j).natAbs * (x j).natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_mul]
      _ ≤
        (I.quadratic row j).natAbs * L +
          (I.linear row j).natAbs * L := by
        exact Nat.add_le_add
          (Nat.mul_le_mul_left _ (hs j))
          (Nat.mul_le_mul_left _ (hx j))
      _ =
        ((I.quadratic row j).natAbs +
          (I.linear row j).natAbs) * L := by
        exact (Nat.add_mul _ _ _).symm
  have hsum :
      (∑ j : Fin vars,
          (I.quadratic row j * s j +
            I.linear row j * x j)).natAbs ≤
        coefficientWeight * L := by
    calc
      (∑ j : Fin vars,
          (I.quadratic row j * s j +
            I.linear row j * x j)).natAbs ≤
        ∑ j : Fin vars,
          (I.quadratic row j * s j +
            I.linear row j * x j).natAbs :=
        Int.natAbs_sum_le _ _
      _ ≤
        ∑ j : Fin vars,
          ((I.quadratic row j).natAbs +
            (I.linear row j).natAbs) * L := by
        exact Finset.sum_le_sum fun j _ ↦ hterm j
      _ = coefficientWeight * L := by
        dsimp [coefficientWeight]
        unfold dqlRowCoefficientWeight
        exact
          (Finset.sum_mul
            (Finset.univ : Finset (Fin vars))
            (fun j ↦
              (I.quadratic row j).natAbs +
                (I.linear row j).natAbs)
            L).symm
  have hsub :
      (equationPhaseExponent I x s row).natAbs ≤
        coefficientWeight * L +
          (I.rhs row).natAbs := by
    unfold equationPhaseExponent
    exact
      (Int.natAbs_sub_le
        (∑ j : Fin vars,
          (I.quadratic row j * s j +
            I.linear row j * x j))
        (I.rhs row)).trans
        (Nat.add_le_add_right hsum _)
  have hrow :
      coefficientWeight * L +
          (I.rhs row).natAbs ≤
        rowWeight * (L + 1) := by
    dsimp [rowWeight, coefficientWeight]
    unfold dqlRowWeight
    calc
      dqlRowCoefficientWeight I row * L +
          (I.rhs row).natAbs ≤
        (dqlRowCoefficientWeight I row * L +
          (I.rhs row).natAbs) +
            ((I.rhs row).natAbs * L +
              dqlRowCoefficientWeight I row) := by
        omega
      _ =
        ((I.rhs row).natAbs +
          dqlRowCoefficientWeight I row) * (L + 1) := by
        ring
  have hrowW : rowWeight ≤ W := by
    exact dqlRowWeight_le_systemWeight I row
  have hW0 : 0 ≤ W := Nat.zero_le _
  have hlinear :
      rowWeight * (L + 1) ≤ W * (L + 1) :=
    Nat.mul_le_mul_right (L + 1) hrowW
  have hquadratic :
      W * (L + 1) ≤ W * (1 + L) ^ 2 := by
    apply Nat.mul_le_mul_left
    simpa only [Nat.add_comm, pow_two] using
      Nat.le_mul_self (L + 1)
  exact hsub.trans (hrow.trans (hlinear.trans hquadratic))

/-- The complete flattened detector exponent has a uniform quadratic
`ℓ¹` bound. -/
theorem flattenedDetectorExponent_energy_le_quadratic
    (I : DQLSystem eqs vars)
    (p : DetectorIndex vars) :
    integerL1Energy
        (DetectorCharacterCode.flattenCharacter
          (detectorExponent I p)) ≤
      4 * (vars + eqs) * dqlSystemWeight I *
        (1 + integerPairL1Energy p) ^ 2 := by
  let B :=
    dqlSystemWeight I *
      (1 + integerPairL1Energy p) ^ 2
  have hprivate :
      (∑ j : Fin vars,
        (privatePhaseExponent p.1 p.2 j).natAbs) ≤
        vars * B := by
    simpa [B] using
      (Finset.sum_le_card_nsmul
        (Finset.univ : Finset (Fin vars))
        (fun j ↦
          (privatePhaseExponent p.1 p.2 j).natAbs)
        B
        (fun j _ ↦
          privatePhaseExponent_natAbs_le_quadratic
            I p.1 p.2 j))
  have hequation :
      (∑ row : Fin eqs,
        (equationPhaseExponent I p.1 p.2 row).natAbs) ≤
        eqs * B := by
    simpa [B] using
      (Finset.sum_le_card_nsmul
        (Finset.univ : Finset (Fin eqs))
        (fun row ↦
          (equationPhaseExponent I p.1 p.2 row).natAbs)
        B
        (fun row _ ↦
          equationPhaseExponent_natAbs_le_quadratic
            I p.1 p.2 row))
  have hexpanded :
      DetectorCharacterCode.expandedTermEnergy
          I p.1 p.2 ≤
        (vars + eqs) * B := by
    unfold DetectorCharacterCode.expandedTermEnergy
    calc
      _ ≤ vars * B + eqs * B :=
        Nat.add_le_add hprivate hequation
      _ = (vars + eqs) * B :=
        (Nat.add_mul vars eqs B).symm
  have hexact :
      integerL1Energy
          (DetectorCharacterCode.flattenCharacter
            (detectorExponent I p)) =
        4 *
          DetectorCharacterCode.expandedTermEnergy
            I p.1 p.2 := by
    change
      DetectorCharacterCode.detectorCharacterEnergy
          (detectorExponent I p) =
        4 *
          DetectorCharacterCode.expandedTermEnergy
            I p.1 p.2
    rw [←
      DetectorCharacterCode.expandedTermCharacter_eq_detectorExponent]
    exact
      DetectorCharacterCode.detectorCharacterEnergy_expandedTermCharacter
        I p.1 p.2
  rw [hexact]
  dsimp [B] at hexpanded ⊢
  nlinarith

/-- Explicit constant in the radical-height bound for a fixed detector. -/
def detectorRadicalHeightConstant
    (radicand : Fin (vars + eqs) → ℕ)
    (I : DQLSystem eqs vars) : ℝ :=
  radicalRootSum radicand *
    (4 * (vars + eqs) * dqlSystemWeight I : ℕ)

/-- The full radical conjugate height of the detector exponent grows at
most quadratically in the two input lattice energies. -/
theorem radicalHeight_flattenedDetectorExponent_le_quadratic
    (radicand : Fin (vars + eqs) → ℕ)
    (I : DQLSystem eqs vars)
    (p : DetectorIndex vars) :
    RadicalSmallDivisor.radicalConjugateHeight
        radicand
        (DetectorCharacterCode.flattenCharacter
          (detectorExponent I p)) ≤
      detectorRadicalHeightConstant radicand I *
        (1 + (integerPairL1Energy p : ℝ)) ^ 2 := by
  have henergy :=
    flattenedDetectorExponent_energy_le_quadratic I p
  calc
    RadicalSmallDivisor.radicalConjugateHeight
        radicand
        (DetectorCharacterCode.flattenCharacter
          (detectorExponent I p)) ≤
      radicalRootSum radicand *
        (integerL1Energy
          (DetectorCharacterCode.flattenCharacter
            (detectorExponent I p)) : ℝ) :=
      radicalConjugateHeight_le_rootSum_mul_integerL1Energy
        radicand
        (DetectorCharacterCode.flattenCharacter
          (detectorExponent I p))
    _ ≤
      radicalRootSum radicand *
        ((4 * (vars + eqs) * dqlSystemWeight I *
          (1 + integerPairL1Energy p) ^ 2 : ℕ) : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr henergy)
        (radicalRootSum_nonneg radicand)
    _ =
      detectorRadicalHeightConstant radicand I *
        (1 + (integerPairL1Energy p : ℝ)) ^ 2 := by
      simp only [detectorRadicalHeightConstant, Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_add, Nat.cast_pow]
      ring

/-- Detector-specialized weighted summability in exactly the form needed
by `RadicalTimeChangedTorusFourierComponent`.

The only remaining input is the elementary polynomial-growth estimate for
the explicit exponent map of the fixed DQL instance. -/
theorem
    summable_norm_detectorCoefficient_mul_radicalHeight_pow
    {lambda eta q C : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambdaq : lambda ≤ q)
    (heta0 : 0 ≤ eta) (hetaq : eta ≤ q)
    (hq0 : 0 < q) (hq1 : q < 1)
    (radicand : Fin (vars + eqs) → ℕ)
    (I : DQLSystem eqs vars)
    (heightPower growthPower : ℕ)
    (hheight :
      ∀ p : DetectorIndex vars,
        RadicalSmallDivisor.radicalConjugateHeight
            radicand
            (DetectorCharacterCode.flattenCharacter
              (detectorExponent I p)) ≤
          C * (1 + (integerPairL1Energy p : ℝ)) ^
            growthPower) :
    Summable fun p : DetectorIndex vars ↦
      ‖detectorCoefficient lambda eta p‖ *
        RadicalSmallDivisor.radicalConjugateHeight
            radicand
            (DetectorCharacterCode.flattenCharacter
              (detectorExponent I p)) ^
          heightPower := by
  exact
    summable_norm_detectorCoefficient_mul_height_pow_of_polynomial_bound
      hlambda0 hlambdaq heta0 hetaq hq0 hq1
      heightPower growthPower
      (fun p ↦
        RadicalSmallDivisor.radicalConjugateHeight
          radicand
          (DetectorCharacterCode.flattenCharacter
            (detectorExponent I p)))
      (fun p ↦
        RadicalSmallDivisor.radicalConjugateHeight_nonneg
          radicand
          (DetectorCharacterCode.flattenCharacter
            (detectorExponent I p)))
      hheight

/-- Fully automatic detector small-divisor summability: no
instance-specific growth estimate remains to be supplied. -/
theorem
    summable_norm_detectorCoefficient_mul_radicalHeight_pow_automatic
    {lambda eta q : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambdaq : lambda ≤ q)
    (heta0 : 0 ≤ eta) (hetaq : eta ≤ q)
    (hq0 : 0 < q) (hq1 : q < 1)
    (radicand : Fin (vars + eqs) → ℕ)
    (I : DQLSystem eqs vars)
    (heightPower : ℕ) :
    Summable fun p : DetectorIndex vars ↦
      ‖detectorCoefficient lambda eta p‖ *
        RadicalSmallDivisor.radicalConjugateHeight
            radicand
            (DetectorCharacterCode.flattenCharacter
              (detectorExponent I p)) ^
          heightPower := by
  exact
    summable_norm_detectorCoefficient_mul_radicalHeight_pow
      hlambda0 hlambdaq heta0 hetaq hq0 hq1
      radicand I heightPower 2
      (radicalHeight_flattenedDetectorExponent_le_quadratic
        radicand I)

end HGAS.Analysis
