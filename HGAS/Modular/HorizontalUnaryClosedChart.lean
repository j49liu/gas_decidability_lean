import HGAS.Modular.ClosedUnaryHorocycleChart
import HGAS.Modular.HorizontalUnaryExactAmplitude
import Mathlib.Tactic

/-!
# A horizontal generic unary lift is a closed unary chart

A horizontal upper-half-plane line is already a horocycle around the
infinity cusp.  Its standard upper-triangular frame has a primitive
horizontal lattice row and is therefore periodic in the level-two frame
quotient.  On the generic unary locus, comparison with the canonical
theta lift also forces the horizontal speed to be nonzero.

This module packages those elementary observations as an actual
`ClosedUnaryHorocycleChart`.
-/

namespace HGAS.Modular

open Matrix Set
open UpperHalfPlane hiding I
open scoped MatrixGroups

noncomputable section

/-- The canonical frame based at a horizontal line is periodic in the
level-two frame quotient. -/
theorem horizontalBaseFrame_isPeriodic
    (x y : ℝ) (hy : 0 < y) :
    IsPeriodicHorocyclePoint 1
      (gammaTwoFrameQuotientMk
        (horizontalBaseFrame x y hy)) := by
  let row : Fin 2 → ℤ := ![0, 1]
  have hrow :
      row ∈ EisensteinSeries.gammaSet 1 1
        (0 : Fin 2 → ZMod 1) := by
    rw [EisensteinSeries.gammaSet_one_mem_iff]
    norm_num [row]
  let v : PrimitiveIntegralRow := ⟨row, hrow⟩
  apply
    isPeriodicHorocyclePoint_of_primitiveRowMul_fst_eq_zero
      v (horizontalBaseFrame x y hy)
  simp [primitiveIntegralRowMul, v, row,
    horizontalBaseFrame, horizontalLine]

/-- A generic standard-clock unary trajectory with a horizontal
canonical-lambda lift admits a closed unary horocycle chart. -/
theorem exists_closedUnaryHorocycleChart_of_horizontalLine
    {z : ℝ → UnaryModularState ℂ}
    {T : ℝ → UpperHalfPlane}
    (hz :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock z)
    (hB : ∀ t, UnaryModularState.B (z t) ≠ 0)
    (hlambda :
      ∀ t,
        UnaryModularState.lambdaCoordinate (z t) =
          canonicalLambda (T t))
    (x y s : ℝ) (hy : 0 < y)
    (hline :
      ∀ t, T t = horizontalLine x y s hy t) :
    Nonempty (ClosedUnaryHorocycleChart z T) := by
  have hs : s ≠ 0 :=
    (hasCuspQuarticAmplitude_of_horizontalLine
      hz hB hlambda x y s hy hline).1
  have hspeed : s / y ≠ 0 :=
    div_ne_zero hs (ne_of_gt hy)
  apply
    exists_closedUnaryHorocycleChart
      z T (horizontalBaseFrame x y hy) (s / y)
      hspeed
  · intro t
    rw [hline t]
    exact
      horizontalBaseFrame_upperUnipotent_basePoint
        x y s t hy |>.symm
  · exact horizontalBaseFrame_isPeriodic x y hy

end

end HGAS.Modular
