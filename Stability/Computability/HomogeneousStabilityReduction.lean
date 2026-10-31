import Stability.Computability.ClockedMonitorPolynomialCode
import Stability.Computability.ClockedMonitorCoordinates
import Stability.Computability.PolynomialCodeConjugacy
import Stability.Computability.PolynomialOutputReduction

/-!
# From a fixed register program to homogeneous Lyapunov stability

The actual primitive-recursive polynomial monitor is reindexed into fixed
finite coordinates and sent through the executable projective compiler.
The smoothing accuracy is the fixed rational `1/1024`. No simulation,
effectivity, or source-hardness premise remains in the correctness theorem.
-/

namespace Stability.HomogeneousStabilityReduction

open HGAS Simulation ClockedMonitorCode

noncomputable section

variable {k s : ℕ}

def degreeIndex (program : RegisterMachine.Program k s) (entry : Fin s) : ℕ :=
  ClockedMonitor.clearedPenalizedDegreeBound program entry + 2

def fieldCode (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) : PolynomialFieldCode (dimension program entry + 1) :=
  PolynomialOutputReduction.compile (ClockedMonitor.clearedPenalizedDegreeBound program entry)
    (pairCode program entry (1 / 1024) (fixedEquiv program entry) initial)

theorem fieldCode_primrec (program : RegisterMachine.Program k s) (entry : Fin s) :
    Primrec (fieldCode program entry) :=
  (PolynomialOutputReduction.compile_primrec _).comp
    (pairCode_primrec program entry (1 / 1024) (fixedEquiv program entry))

/-- Exact correctness of the raw homogeneous polynomial construction. -/
theorem hlsQ_fieldCode_iff (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) :
    HLSQ (dimension program entry + 1) (2 * degreeIndex program entry + 1)
      (fieldCode program entry initial) ↔ RegisterMachine.Halts program ⟨some entry, initial⟩ := by
  let d := ClockedMonitor.clearedPenalizedDegreeBound program entry
  let e := fixedEquiv program entry
  let pair := pairCode program entry (1 / 1024) e initial
  have hdeg : 2 * degreeIndex program entry + 1 = 2 * d + 5 := by
    simp only [degreeIndex, d]
    omega
  rw [hdeg]
  have hb := pairCode_totalDegree_le program entry (1 / 1024) e initial
  have hprojective := PolynomialOutputReduction.hlsQ_compile_iff d pair.1 pair.2 hb.1 hb.2
  have hcoordinates := PolynomialCodeRealization.hasBoundedFiniteOutput_codes_iff
    (coordinateEquiv program entry (1 / 1024) e initial) pair.1 pair.2
    (ClockedMonitor.clearedField program entry initial (1 / 1024))
    (ClockedMonitor.clearedPenalizedOutput program entry initial (1 / 1024))
    (fun i ↦ decode_clearedFieldCode program entry (1 / 1024) e i initial)
    (decode_clearedPenalizedOutputCode program entry (1 / 1024) e initial)
  exact hprojective.trans (hcoordinates.trans
    (ClockedMonitor.halts_iff_bounded_polynomialOutput program entry initial
      (ε := 1 / 1024) (by norm_num) le_rfl).symm)

theorem homogeneous_fieldCode (program : RegisterMachine.Program k s) (entry : Fin s)
    (initial : Fin k → ℕ) :
    PolynomialFieldCode.homogeneous (2 * degreeIndex program entry + 1)
      (fieldCode program entry initial) = true := by
  have hb := pairCode_totalDegree_le program entry (1 / 1024) (fixedEquiv program entry) initial
  have h := PolynomialOutputReduction.homogeneous_compile
    (ClockedMonitor.clearedPenalizedDegreeBound program entry) _ _ hb.1 hb.2
  have hdeg : 2 * degreeIndex program entry + 1 =
      2 * ClockedMonitor.clearedPenalizedDegreeBound program entry + 5 := by
    unfold degreeIndex
    omega
  rw [hdeg]
  exact h

theorem degreeIndex_pos (program : RegisterMachine.Program k s) (entry : Fin s) :
    1 ≤ degreeIndex program entry := by
  unfold degreeIndex
  omega

end

end Stability.HomogeneousStabilityReduction
