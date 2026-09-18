import HGAS.Arithmetic.DetectorPoissonReciprocalCode
import HGAS.Clocks.ControllerPhaseProductCharacterUnit
import HGAS.Compiler.ReciprocalGraphDynamics
import Mathlib.Tactic

/-!
# Exact unit-circle semantics of the detector Poisson factors

The sparse clock compiler represents negative character exponents by
complex conjugates.  On the intended phase circles those conjugates are
literal multiplicative inverses.  This file specializes that reusable fact
to the detector character

```text
                         Wⱼ = Qⱼ⁻¹Sⱼ
```

and then identifies the compiled fixed-degree factor

```text
                         (3/4) Gⱼ,+ Gⱼ,-
```

with the exact Poisson reciprocal expression whenever the two polynomial
reciprocal graph residuals vanish.

Every hypothesis is explicit.  In particular, no inverse identity is
claimed at arbitrary off-circle ambient points.
-/

namespace HGAS

namespace DetectorPoissonReciprocalCode

open _root_.MvPolynomial
open Clocks
open Clocks.ControllerPhaseProductCharacterCode
open Modular

noncomputable section

variable {eqs vars : ℕ}

/-! ## The positive and negative detector characters -/

/-- Semantic value of the Poisson argument `Wⱼ = Qⱼ⁻¹Sⱼ`. -/
def poissonCharacterValue
    (I : DQLSystem eqs vars)
    (z : State eqs vars)
    (j : Fin vars) : ℂ :=
  characterValue (poissonExponent I j)
    z.base.source.controllers

/-- On the phase circles, every detector Poisson character has norm one. -/
theorem norm_poissonCharacterValue_eq_one
    (I : DQLSystem eqs vars)
    (z : State eqs vars)
    (j : Fin vars)
    (hz : OnPhaseCircles z.base.source.controllers) :
    ‖poissonCharacterValue I z j‖ = 1 :=
  norm_characterValue_eq_one
    (poissonExponent I j) z.base.source.controllers hz

@[simp]
theorem characterValue_positiveIndex
    (I : DQLSystem eqs vars)
    (z : State eqs vars)
    (j : Fin vars) :
    characterValue
        (reciprocalExponent I (positiveIndex j))
        z.base.source.controllers =
      poissonCharacterValue I z j := by
  simp [poissonCharacterValue]

/-- The negative reciprocal block is the literal inverse character on the
phase circles. -/
theorem characterValue_negativeIndex_eq_inv
    (I : DQLSystem eqs vars)
    (z : State eqs vars)
    (j : Fin vars)
    (hz : OnPhaseCircles z.base.source.controllers) :
    characterValue
        (reciprocalExponent I (negativeIndex j))
        z.base.source.controllers =
      (poissonCharacterValue I z j)⁻¹ := by
  rw [reciprocalExponent_negativeIndex]
  exact
    characterValue_neg_eq_inv
      (poissonExponent I j) z.base.source.controllers hz

@[simp]
theorem evalPair_characterBaseCode_positiveIndex
    (I : DQLSystem eqs vars)
    (z : State eqs vars)
    (j : Fin vars) :
    evalPair (characterBaseCode I (positiveIndex j))
        (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
          z.base) =
      poissonCharacterValue I z j := by
  simp [poissonCharacterValue]

/-- Polynomial evaluation of the negative character is the inverse of the
positive character on the phase circles. -/
theorem evalPair_characterBaseCode_negativeIndex_eq_inv
    (I : DQLSystem eqs vars)
    (z : State eqs vars)
    (j : Fin vars)
    (hz : OnPhaseCircles z.base.source.controllers) :
    evalPair (characterBaseCode I (negativeIndex j))
        (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
          z.base) =
      (poissonCharacterValue I z j)⁻¹ := by
  rw [evalPair_characterBaseCode]
  exact characterValue_negativeIndex_eq_inv I z j hz

/-! ## Specialized reciprocal graph semantics -/

/-- The semantic complex residual belonging to one detector reciprocal
block. -/
def reciprocalGraphResidual
    (I : DQLSystem eqs vars)
    (z : State eqs vars)
    (k : Fin (reciprocalCount vars)) : ℂ :=
  ComplexReciprocalFamilyPolynomialCode.residual
    etaCode (characterBaseCode I) (rawState z) k

/-- Unfolding a specialized residual produces exactly
`((1 - W/2)G - 1)` for the corresponding signed character. -/
theorem reciprocalGraphResidual_eq
    (I : DQLSystem eqs vars)
    (z : State eqs vars)
    (k : Fin (reciprocalCount vars)) :
    reciprocalGraphResidual I z k =
      reciprocalResidual ((1 / 2 : ℝ) : ℂ)
        (characterValue (reciprocalExponent I k)
          z.base.source.controllers)
        (z.reciprocal k) := by
  unfold reciprocalGraphResidual
  change
    reciprocalResidual
        (((RationalCode.decode (etaCode k) : ℝ) : ℂ))
        (evalPair (characterBaseCode I k)
          (ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
            z.base))
        (z.reciprocal k) =
      _
  rw [evalPair_characterBaseCode]
  simp [etaCode]

/-- Vanishing of all compiled real residual coordinates is exactly
simultaneous vanishing of the specialized complex graph residuals. -/
theorem forall_eval_residualCode_eq_zero_iff_graphResidual
    (I : DQLSystem eqs vars)
    (z : State eqs vars) :
    (∀ r,
      eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode (residualCode I r)) = 0) ↔
      ∀ k, reciprocalGraphResidual I z k = 0 := by
  simpa [point, residualCode, reciprocalGraphResidual] using
    (ComplexReciprocalFamilyPolynomialCode.forall_eval_residualCode_eq_zero_iff
      (η := etaCode)
      (w := characterBaseCode I)
      (z := rawState z))

/-- A zero positive graph residual selects the literal reciprocal
`(1-W/2)⁻¹`. -/
theorem positiveReciprocal_eq_inv
    (I : DQLSystem eqs vars)
    (z : State eqs vars)
    (j : Fin vars)
    (hz : OnPhaseCircles z.base.source.controllers)
    (hres :
      reciprocalGraphResidual I z (positiveIndex j) = 0) :
    z.reciprocal (positiveIndex j) =
      (1 - (((1 / 2 : ℝ) : ℂ) *
        poissonCharacterValue I z j))⁻¹ := by
  rw [reciprocalGraphResidual_eq,
    characterValue_positiveIndex] at hres
  exact
    (reciprocalResidual_eq_zero_iff_eq_inv_of_unit
      (η := (1 / 2 : ℝ))
      (w := poissonCharacterValue I z j)
      (g := z.reciprocal (positiveIndex j))
      (by norm_num) (by norm_num)
      (norm_poissonCharacterValue_eq_one I z j hz)).1 hres

/-- A zero negative graph residual selects
`(1-W⁻¹/2)⁻¹`. -/
theorem negativeReciprocal_eq_inv
    (I : DQLSystem eqs vars)
    (z : State eqs vars)
    (j : Fin vars)
    (hz : OnPhaseCircles z.base.source.controllers)
    (hres :
      reciprocalGraphResidual I z (negativeIndex j) = 0) :
    z.reciprocal (negativeIndex j) =
      (1 - (((1 / 2 : ℝ) : ℂ) *
        (poissonCharacterValue I z j)⁻¹))⁻¹ := by
  rw [reciprocalGraphResidual_eq,
    characterValue_negativeIndex_eq_inv I z j hz] at hres
  exact
    (reciprocalResidual_eq_zero_iff_eq_inv_of_unit
      (η := (1 / 2 : ℝ))
      (w := (poissonCharacterValue I z j)⁻¹)
      (g := z.reciprocal (negativeIndex j))
      (by norm_num) (by norm_num)
      (by
        rw [norm_inv,
          norm_poissonCharacterValue_eq_one I z j hz]
        simp)).1 hres

/-! ## Exact evaluation of the fixed-degree Poisson factor -/

/-- If the two reciprocal graph residuals vanish, the fixed-degree
polynomial factor evaluates to the exact product of Poisson reciprocals. -/
theorem evalPair_poissonFactorCode_of_graphResiduals
    (I : DQLSystem eqs vars)
    (z : State eqs vars)
    (j : Fin vars)
    (hz : OnPhaseCircles z.base.source.controllers)
    (hpositive :
      reciprocalGraphResidual I z (positiveIndex j) = 0)
    (hnegative :
      reciprocalGraphResidual I z (negativeIndex j) = 0) :
    evalPair (poissonFactorCode (eqs := eqs) j) (point z) =
      ((3 / 4 : ℝ) : ℂ) *
        (1 - (((1 / 2 : ℝ) : ℂ) *
          poissonCharacterValue I z j))⁻¹ *
        (1 - (((1 / 2 : ℝ) : ℂ) *
          (poissonCharacterValue I z j)⁻¹))⁻¹ := by
  rw [evalPair_poissonFactorCode,
    positiveReciprocal_eq_inv I z j hz hpositive,
    negativeReciprocal_eq_inv I z j hz hnegative]

/-- Version driven directly by simultaneous vanishing of the compiled
scalar residual codes. -/
theorem evalPair_poissonFactorCode_of_compiledResiduals
    (I : DQLSystem eqs vars)
    (z : State eqs vars)
    (j : Fin vars)
    (hz : OnPhaseCircles z.base.source.controllers)
    (hres :
      ∀ r,
        eval₂Hom (algebraMap ℚ ℝ) (point z)
          (PolynomialCode.decode (residualCode I r)) = 0) :
    evalPair (poissonFactorCode (eqs := eqs) j) (point z) =
      ((3 / 4 : ℝ) : ℂ) *
        (1 - (((1 / 2 : ℝ) : ℂ) *
          poissonCharacterValue I z j))⁻¹ *
        (1 - (((1 / 2 : ℝ) : ℂ) *
          (poissonCharacterValue I z j)⁻¹))⁻¹ := by
  have hall :
      ∀ k, reciprocalGraphResidual I z k = 0 :=
    (forall_eval_residualCode_eq_zero_iff_graphResidual I z).1 hres
  exact
    evalPair_poissonFactorCode_of_graphResiduals I z j hz
      (hall (positiveIndex j)) (hall (negativeIndex j))

end

end DetectorPoissonReciprocalCode

end HGAS
