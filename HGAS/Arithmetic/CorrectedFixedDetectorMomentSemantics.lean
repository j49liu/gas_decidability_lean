import HGAS.Arithmetic.CorrectedFixedDetectorMomentCode
import Mathlib.Tactic

/-!
# Flattened semantics of the corrected selector family

This file completes the human-facing interface of the corrected
seven-moment compiler.  It separates the mathematical complex moments
from their sparse-polynomial encoding and proves that the adjacent real
and imaginary coordinates decode exactly to those moments.
-/

namespace HGAS.CorrectedFixedDetectorMomentCode

open HGAS
open HGAS.Clocks.ControllerPhaseProductCharacterCode
open _root_.MvPolynomial

variable {eqs vars : ℕ}

/-- The flattened complex selector-moment vector. -/
noncomputable def momentValue
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    Fin (momentCount vars) → ℂ :=
  fun k ↦
    let jm := finProdFinEquiv.symm k
    localMomentValue I jm.1 z jm.2

/-- Realification of the corrected complex moment vector, with real and
imaginary parts in adjacent coordinates. -/
noncomputable def scalarMomentValue
    (I : DQLSystem eqs vars)
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    Fin (scalarMomentCount vars) → ℝ :=
  fun k ↦
    let mc := finProdFinEquiv.symm k
    ![(momentValue I z mc.1).re,
      (momentValue I z mc.1).im] mc.2

@[simp]
theorem evalPair_momentCode
    (I : DQLSystem eqs vars)
    (k : Fin (momentCount vars))
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    evalPair (momentCode I k)
        (FixedDetectorPolynomialCode.point z) =
      momentValue I z k := by
  simp [momentCode, momentValue]

@[simp]
theorem eval_scalarMomentCode
    (I : DQLSystem eqs vars)
    (k : Fin (scalarMomentCount vars))
    (z : FixedDetectorPolynomialCode.State eqs vars) :
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode (scalarMomentCode I k)) =
      scalarMomentValue I z k := by
  let mc := finProdFinEquiv.symm k
  have h := evalPair_momentCode I mc.1 z
  change
    eval₂Hom (algebraMap ℚ ℝ)
        (FixedDetectorPolynomialCode.point z)
        (PolynomialCode.decode
          (![(momentCode I mc.1).1,
            (momentCode I mc.1).2] mc.2)) =
      ![(momentValue I z mc.1).re,
        (momentValue I z mc.1).im] mc.2
  have hmc : mc.2 = 0 ∨ mc.2 = 1 := by omega
  rcases hmc with hzero | hone
  · rw [hzero]
    exact congrArg Complex.re h
  · rw [hone]
    exact congrArg Complex.im h

end HGAS.CorrectedFixedDetectorMomentCode
