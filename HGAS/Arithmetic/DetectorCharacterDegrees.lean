import HGAS.Arithmetic.DetectorCharacterCode
import HGAS.Clocks.ControllerPhaseProductCharacterDegrees
import Mathlib.Tactic

/-!
# Exact exponent energies and degree bounds for detector characters

The polynomial degree of a compiled Laurent character is controlled by
the `ℓ¹` energy of its integral exponent vector.  This module evaluates
that energy for every character appearing in the DQL detector and records
the corresponding raw sparse-polynomial degree bound.

The bounds are data-dependent and therefore stronger than any estimate in
terms of a maximum coefficient.  The arithmetic detector uses fourth
powers of the fundamental polynomial clocks, so every flattened exponent
is multiplied by four.  For the fully expanded term the exact exponent
energy is consequently four times the sum of the unsigned private and
equation-phase exponents.  No triangle inequality, coefficient
normalization, or unit-circle identity is used.
-/

namespace HGAS.DetectorCharacterCode

open HGAS.Clocks.ControllerPhaseProductCharacterCode
open scoped BigOperators

variable {eqs vars : ℕ}

/-- `ℓ¹` energy of a sum-indexed detector character after flattening. -/
def detectorCharacterEnergy
    (a : DetectorPhase eqs vars → ℤ) : ℕ :=
  exponentEnergy (flattenCharacter a)

/-- Flattening reindexes the private and equation coordinates and applies
the manuscript's fourth-power clock convention. -/
theorem detectorCharacterEnergy_eq
    (a : DetectorPhase eqs vars → ℤ) :
    detectorCharacterEnergy a =
      4 * ((∑ j : Fin vars, (a (Sum.inl j)).natAbs) +
        (∑ row : Fin eqs, (a (Sum.inr row)).natAbs)) := by
  unfold detectorCharacterEnergy exponentEnergy flattenCharacter
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [Int.natAbs_mul]
  simp [Finset.mul_sum, Nat.mul_add]

private theorem sum_natAbs_single
    (j : Fin vars) (z : ℤ) :
    (∑ k : Fin vars,
      (if k = j then z else 0).natAbs) =
        z.natAbs := by
  classical
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [hkj]
  · simp

/-- Unsigned energy of one quadratic coefficient column. -/
def quadraticColumnEnergy
    (I : DQLSystem eqs vars) (j : Fin vars) : ℕ :=
  ∑ row : Fin eqs, (I.quadratic row j).natAbs

/-- Unsigned energy of one linear coefficient column. -/
def linearColumnEnergy
    (I : DQLSystem eqs vars) (j : Fin vars) : ℕ :=
  ∑ row : Fin eqs, (I.linear row j).natAbs

/-- Unsigned energy of the right-hand-side character. -/
def rhsEnergy (I : DQLSystem eqs vars) : ℕ :=
  ∑ row : Fin eqs, (I.rhs row).natAbs

/-- Exact energy of one theta-series character. -/
def thetaTermEnergy
    (I : DQLSystem eqs vars)
    (x : Fin vars → ℤ) (j : Fin vars) : ℕ :=
  (x j ^ 2).natAbs +
    ∑ row : Fin eqs,
      (x j * I.linear row j).natAbs

/-- Exact energy of a fully expanded detector character. -/
def expandedTermEnergy
    (I : DQLSystem eqs vars)
    (x s : Fin vars → ℤ) : ℕ :=
  (∑ j : Fin vars,
      (privatePhaseExponent x s j).natAbs) +
    ∑ row : Fin eqs,
      (equationPhaseExponent I x s row).natAbs

theorem detectorCharacterEnergy_privateCharacter
    (j : Fin vars) :
    detectorCharacterEnergy
        (privateCharacter (eqs := eqs) j) = 4 := by
  rw [detectorCharacterEnergy_eq]
  simp only [privateCharacter, Int.natAbs_zero,
    Finset.sum_const_zero, add_zero]
  rw [sum_natAbs_single]
  norm_num

theorem detectorCharacterEnergy_quadraticCharacter
    (I : DQLSystem eqs vars) (j : Fin vars) :
    detectorCharacterEnergy (quadraticCharacter I j) =
      4 * quadraticColumnEnergy I j := by
  rw [detectorCharacterEnergy_eq]
  simp [quadraticCharacter, quadraticColumnEnergy]

theorem detectorCharacterEnergy_linearCharacter
    (I : DQLSystem eqs vars) (j : Fin vars) :
    detectorCharacterEnergy (linearCharacter I j) =
      4 * linearColumnEnergy I j := by
  rw [detectorCharacterEnergy_eq]
  simp [linearCharacter, linearColumnEnergy]

theorem detectorCharacterEnergy_rhsCharacter
    (I : DQLSystem eqs vars) :
    detectorCharacterEnergy (rhsCharacter I) =
      4 * rhsEnergy I := by
  rw [detectorCharacterEnergy_eq]
  simp [rhsCharacter, rhsEnergy]

theorem detectorCharacterEnergy_poissonArgumentCharacter
    (I : DQLSystem eqs vars) (j : Fin vars) :
    detectorCharacterEnergy
        (poissonArgumentCharacter I j) =
      4 * (1 + quadraticColumnEnergy I j) := by
  rw [detectorCharacterEnergy_eq]
  simp only [poissonArgumentCharacter, privateCharacter,
    quadraticCharacter, add_zero]
  have hprivate :
      (∑ k : Fin vars,
        (-if k = j then (1 : ℤ) else 0).natAbs) = 1 := by
    simp_rw [Int.natAbs_neg]
    rw [sum_natAbs_single]
    norm_num
  rw [hprivate]
  simp only [neg_zero, zero_add]
  rfl

theorem detectorCharacterEnergy_thetaTermCharacter
    (I : DQLSystem eqs vars)
    (x : Fin vars → ℤ) (j : Fin vars) :
    detectorCharacterEnergy (thetaTermCharacter I x j) =
      4 * thetaTermEnergy I x j := by
  rw [detectorCharacterEnergy_eq]
  simp only [thetaTermCharacter, privateCharacter,
    linearCharacter, mul_ite, mul_one, mul_zero,
    add_zero, zero_add]
  rw [sum_natAbs_single]
  rfl

theorem detectorCharacterEnergy_expandedTermCharacter
    (I : DQLSystem eqs vars)
    (x s : Fin vars → ℤ) :
    detectorCharacterEnergy (expandedTermCharacter I x s) =
      4 * expandedTermEnergy I x s := by
  rw [expandedTermCharacter_eq_detectorExponent,
    detectorCharacterEnergy_eq]
  rfl

/-! ## Additional literal character codes -/

/-- Polynomial character code of one theta-series term
`Q_j^(x_j²) V_j^(x_j)`. -/
def thetaTermCode
    (I : DQLSystem eqs vars)
    (x : Fin vars → ℤ) (j : Fin vars) :
    ComplexPairCode
      (HGAS.Clocks.ControllerPhaseProductPolynomialCode.dimension
        (clockCount eqs vars)) :=
  characterCode
    (flattenCharacter (thetaTermCharacter I x j))

/-- Polynomial character code of one fully expanded detector term. -/
def expandedTermCode
    (I : DQLSystem eqs vars)
    (x s : Fin vars → ℤ) :
    ComplexPairCode
      (HGAS.Clocks.ControllerPhaseProductPolynomialCode.dimension
        (clockCount eqs vars)) :=
  characterCode
    (flattenCharacter (expandedTermCharacter I x s))

/-! ## Strong data-dependent degree bounds -/

theorem privateCode_termsDegreeLE
    (j : Fin vars) :
    TermsDegreeLE 4 (privateCode (eqs := eqs) j) := by
  have h :=
    characterCode_termsDegreeLE
      (flattenCharacter
        (privateCharacter (eqs := eqs) j))
  change
    TermsDegreeLE
      (detectorCharacterEnergy
        (privateCharacter (eqs := eqs) j))
      (privateCode (eqs := eqs) j) at h
  rw [detectorCharacterEnergy_privateCharacter] at h
  exact h

theorem quadraticCode_termsDegreeLE
    (I : DQLSystem eqs vars) (j : Fin vars) :
    TermsDegreeLE (4 * quadraticColumnEnergy I j)
      (quadraticCode I j) := by
  have h :=
    characterCode_termsDegreeLE
      (flattenCharacter (quadraticCharacter I j))
  change
    TermsDegreeLE
      (detectorCharacterEnergy (quadraticCharacter I j))
      (quadraticCode I j) at h
  rw [detectorCharacterEnergy_quadraticCharacter] at h
  exact h

theorem linearCode_termsDegreeLE
    (I : DQLSystem eqs vars) (j : Fin vars) :
    TermsDegreeLE (4 * linearColumnEnergy I j)
      (linearCode I j) := by
  have h :=
    characterCode_termsDegreeLE
      (flattenCharacter (linearCharacter I j))
  change
    TermsDegreeLE
      (detectorCharacterEnergy (linearCharacter I j))
      (linearCode I j) at h
  rw [detectorCharacterEnergy_linearCharacter] at h
  exact h

theorem rhsCode_termsDegreeLE
    (I : DQLSystem eqs vars) :
    TermsDegreeLE (4 * rhsEnergy I) (rhsCode I) := by
  have h :=
    characterCode_termsDegreeLE
      (flattenCharacter (rhsCharacter I))
  change
    TermsDegreeLE
      (detectorCharacterEnergy (rhsCharacter I))
      (rhsCode I) at h
  rw [detectorCharacterEnergy_rhsCharacter] at h
  exact h

theorem poissonArgumentCode_termsDegreeLE
    (I : DQLSystem eqs vars) (j : Fin vars) :
    TermsDegreeLE (4 * (1 + quadraticColumnEnergy I j))
      (poissonArgumentCode I j) := by
  have h :=
    characterCode_termsDegreeLE
      (flattenCharacter
        (poissonArgumentCharacter I j))
  change
    TermsDegreeLE
      (detectorCharacterEnergy
        (poissonArgumentCharacter I j))
      (poissonArgumentCode I j) at h
  rw [detectorCharacterEnergy_poissonArgumentCharacter] at h
  exact h

theorem thetaTermCode_termsDegreeLE
    (I : DQLSystem eqs vars)
    (x : Fin vars → ℤ) (j : Fin vars) :
    TermsDegreeLE (4 * thetaTermEnergy I x j)
      (thetaTermCode I x j) := by
  have h :=
    characterCode_termsDegreeLE
      (flattenCharacter (thetaTermCharacter I x j))
  change
    TermsDegreeLE
      (detectorCharacterEnergy (thetaTermCharacter I x j))
      (thetaTermCode I x j) at h
  rw [detectorCharacterEnergy_thetaTermCharacter] at h
  exact h

theorem expandedTermCode_termsDegreeLE
    (I : DQLSystem eqs vars)
    (x s : Fin vars → ℤ) :
    TermsDegreeLE (4 * expandedTermEnergy I x s)
      (expandedTermCode I x s) := by
  have h :=
    characterCode_termsDegreeLE
      (flattenCharacter (expandedTermCharacter I x s))
  change
    TermsDegreeLE
      (detectorCharacterEnergy
        (expandedTermCharacter I x s))
      (expandedTermCode I x s) at h
  rw [detectorCharacterEnergy_expandedTermCharacter] at h
  exact h

/-! ## Degree-one controller readouts -/

/-- The private-character readout built from `omegaWeights` is linear in
the controller coordinates. -/
theorem omegaFrequencyCode_termsDegreeLE
    (parameters :
      Fin (clockCount eqs vars) → RationalCode)
    (j : Fin vars) :
    PolynomialCode.TermsDegreeLE 1
      (HGAS.Clocks.ControllerPhaseProductLinearFrequencyCode.code
        (omegaWeights (eqs := eqs) j) parameters) := by
  rw [← privateFrequencyCode_eq parameters j]
  exact frequencyCode_termsDegreeLE _ _

/-- The linear-character readout built from `numberWeights` is likewise
linear, independently of coefficient size. -/
theorem numberFrequencyCode_termsDegreeLE
    (parameters :
      Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars) (j : Fin vars) :
    PolynomialCode.TermsDegreeLE 1
      (HGAS.Clocks.ControllerPhaseProductLinearFrequencyCode.code
        (numberWeights I j) parameters) := by
  rw [← linearFrequencyCode_eq parameters I j]
  exact frequencyCode_termsDegreeLE _ _

end HGAS.DetectorCharacterCode
