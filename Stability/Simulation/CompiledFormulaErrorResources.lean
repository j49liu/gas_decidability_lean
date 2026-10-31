import Stability.Simulation.CompiledFormulaError
import Stability.Simulation.RadicalDefectResources

/-!
# Degree bounds for the actual compiled error weight

Every generated output numerator and radicand shares the compiler's
shape-dependent degree budget. The error-weight construction therefore
has one bound determined by that degree and the actual root count.
Summing output weights does not add degrees.
-/

namespace Stability.Simulation.CompiledFormulaLift

noncomputable section

open AbsFormula RadicalDefectBounds

variable {σ : Type*} [Fintype σ]

def errorDegreeBound (degree rootCount : ℕ) : ℕ :=
  (rootCount + 1) * (degree * RadicalComparison.cubeDegreeBound degree rootCount)

theorem outputErrorWeight_totalDegree_le (L : MvPolynomial σ ℚ) {d : ℕ}
    (hL : L.totalDegree ≤ d) (es : List (AbsFormula σ)) (i : Fin es.length) :
    (outputErrorWeight L es i).totalDegree ≤
      errorDegreeBound (radicalFamilyDegreeBound d es) (finiteRadicalFamily L es).rootCount := by
  have h := polynomialWeight_totalDegree_le (finiteRadicalFamily L es).radicands
    (outputAt L es i).numerator (finiteRadicalFamily_totalDegree_le L hL es).1
    (outputAt_numerator_totalDegree_le L hL es i)
  exact h.trans_eq (by unfold errorDegreeBound; ring)

/-- A bound for the actual common error polynomial, valid even without
precision positivity and when the formula or root family is empty. -/
theorem familyErrorWeight_totalDegree_le (L : MvPolynomial σ ℚ) {d : ℕ}
    (hL : L.totalDegree ≤ d) (es : List (AbsFormula σ)) :
    (familyErrorWeight L es).totalDegree ≤
      errorDegreeBound (radicalFamilyDegreeBound d es) (finiteRadicalFamily L es).rootCount := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le (by simp)
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  exact outputErrorWeight_totalDegree_le L hL es i

end

end Stability.Simulation.CompiledFormulaLift
