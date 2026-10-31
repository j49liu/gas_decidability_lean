import Stability.Selection.OrdinaryTimeDetectorResources
import Stability.Selection.OrdinaryTimeGainChoice

/-!
# The printed gain applied to the actual detector primitive

The RHS enters through the stated integer exponent. The least positive
gain denominator is applied to that rational bound. This module proves
the graph's pointwise reward estimate; invariance and zero-mode vanishing
are separate dynamical statements.
-/

namespace Stability.Selection

noncomputable section

open HGAS HGAS.Analysis HGAS.Clocks

def detectorPrimitiveRhsBudget {eqs vars : ℕ} (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) : ℚ :=
  detectorPrimitiveBudget I p (sourceRadiusIndex I) *
    fourierRadius (linearRadiusExponent I) (quadraticRadiusExponent I) ^
      (4 * detectorDriftDegree I * ∑ row, (I.rhs row).natAbs)

theorem detectorPrimitiveRhsBudget_pos {eqs vars : ℕ} (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) : 0 < detectorPrimitiveRhsBudget I p := by
  unfold detectorPrimitiveRhsBudget
  exact mul_pos (detectorPrimitiveBudget_pos _ _ _)
    (pow_pos (zero_lt_one.trans (fourierRadius_gt_one _ _)) _)

theorem detectorPrimitiveRhsBudget_cast {eqs vars : ℕ} (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) :
    (detectorPrimitiveRhsBudget I p : ℝ) =
      (detectorPrimitiveBudget I p (sourceRadiusIndex I) : ℝ) *
        (1 + 1 / (sourceRadiusIndex I : ℝ)) ^
          (4 * (detectorDriftDegree I : ℝ) * ∑ row, |(I.rhs row : ℝ)|) := by
  have he : ((4 * detectorDriftDegree I * ∑ row, (I.rhs row).natAbs : ℕ) : ℝ) =
      4 * (detectorDriftDegree I : ℝ) * ∑ row, |(I.rhs row : ℝ)| := by
    simp [Nat.cast_sum, Nat.cast_natAbs, Int.cast_abs]
  rw [← he, Real.rpow_natCast]
  simp [detectorPrimitiveRhsBudget, fourierRadius, sourceRadiusIndex]

def detectorGraphGain {eqs vars : ℕ} (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) : ℚ :=
  graphGain (sourceGraphSizeBudget eqs vars) (RationalCode.encode (detectorPrimitiveRhsBudget I p))

def detectorGraphMargin (eqs vars : ℕ) : ℚ := graphWeightBudget (sourceGraphSizeBudget eqs vars) / 4

theorem detectorGraphGain_pos {eqs vars : ℕ} (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) : 0 < detectorGraphGain I p := graphGain_pos _ _

theorem detectorGraphMargin_pos (eqs vars : ℕ) : 0 < detectorGraphMargin eqs vars :=
  div_pos (graphWeightBudget_pos _) (by norm_num)

theorem detectorGraphGain_quadratic_bound {eqs vars : ℕ} (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) :
    detectorGraphGain I p ^ 2 * detectorPrimitiveRhsBudget I p ^ 2 ≤
      detectorGraphMargin eqs vars := by
  simpa only [detectorGraphGain, detectorGraphMargin, RationalCode.decode_encode] using
    graphGain_quadratic_bound (sourceGraphSizeBudget eqs vars)
      (RationalCode.encode (detectorPrimitiveRhsBudget I p))

theorem detectorSourcePrimitive_normSq_bound {eqs vars : ℕ}
    (I : DQLSystem eqs vars) (p : Fin (vars + eqs) → ℕ)
    (hp : ∀ i, (p i).Prime) (hinjective : Function.Injective p)
    (x : UnitAddTorus (Fin (vars + eqs))) :
    normSq (detectorSourcePrimitive I p x) ≤ (detectorPrimitiveRhsBudget I p : ℝ) ^ 2 := by
  rw [detectorPrimitiveRhsBudget_cast]
  exact (detectorSourcePrimitive_resources I p hp hinjective (sourceRadiusIndex I)
    (sourceRadiusIndex_pos I) (sourceRadiusIndex_bounds I).1 (sourceRadiusIndex_bounds I).2).2.1 x

theorem detectorScaledPrimitive_normSq_bound {eqs vars : ℕ}
    (I : DQLSystem eqs vars) (p : Fin (vars + eqs) → ℕ)
    (hp : ∀ i, (p i).Prime) (hinjective : Function.Injective p)
    (x : UnitAddTorus (Fin (vars + eqs))) :
    normSq ((detectorGraphGain I p : ℝ) • detectorSourcePrimitive I p x) ≤
      (detectorGraphMargin eqs vars : ℝ) := by
  rw [normSq_smul]
  refine (mul_le_mul_of_nonneg_left (detectorSourcePrimitive_normSq_bound I p hp hinjective x)
    (sq_nonneg _)).trans ?_
  exact_mod_cast detectorGraphGain_quadratic_bound I p

/-- The central chart contributes at least the prescribed graph weight. -/
theorem intendedSourceGraph_weight_lower_bound {eqs vars : ℕ}
    (I : DQLSystem eqs vars) (p : Fin (vars + eqs) → ℕ)
    (x : UnitAddTorus (Fin (vars + eqs))) :
    (graphWeightBudget (sourceGraphSizeBudget eqs vars) : ℝ) ≤
      1 / (1 + normSq (intendedSourceGraph I
        (fun i ↦ ExplicitPositiveControllerEquilibrium.state (p i : ℝ)) x)) := by
  have hs := positiveControllerSourceGraph_normSq_le I (fun i ↦ (p i : ℝ)) x
  have hn := normSq_nonneg (intendedSourceGraph I
    (fun i ↦ ExplicitPositiveControllerEquilibrium.state (p i : ℝ)) x)
  simp only [graphWeightBudget, Rat.cast_div, Rat.cast_one, Rat.cast_add, Rat.cast_natCast]
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

/-- The literal stereographic reward on the bounded source/primitive graph. -/
theorem detectorGraph_reward_lower_bound {eqs vars : ℕ}
    (I : DQLSystem eqs vars) (p : Fin (vars + eqs) → ℕ)
    (hp : ∀ i, (p i).Prime) (hinjective : Function.Injective p)
    (x : UnitAddTorus (Fin (vars + eqs))) :
    5 * (graphWeightBudget (sourceGraphSizeBudget eqs vars) : ℝ) / 4 ≤
      (1 - normSq ((detectorGraphGain I p : ℝ) • detectorSourcePrimitive I p x)) /
        (1 + normSq ((detectorGraphGain I p : ℝ) • detectorSourcePrimitive I p x)) +
      2 / (1 + normSq (intendedSourceGraph I
        (fun i ↦ ExplicitPositiveControllerEquilibrium.state (p i : ℝ)) x)) -
      1 - (detectorGraphMargin eqs vars : ℝ) := by
  let h2 := normSq ((detectorGraphGain I p : ℝ) • detectorSourcePrimitive I p x)
  have hh0 : 0 ≤ h2 := normSq_nonneg _
  have hu : 1 - 2 * h2 ≤ (1 - h2) / (1 + h2) := by
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith [sq_nonneg h2]
  have hw := intendedSourceGraph_weight_lower_bound I p x
  have hh := detectorScaledPrimitive_normSq_bound I p hp hinjective x
  have he : (detectorGraphMargin eqs vars : ℝ) =
      (graphWeightBudget (sourceGraphSizeBudget eqs vars) : ℝ) / 4 := by
    simp only [detectorGraphMargin, Rat.cast_div, Rat.cast_ofNat]
  change h2 ≤ _ at hh
  have hb := graph_reward_lower_bound hw (hh.trans_eq he) he
  change _ ≤ (1 - h2) / (1 + h2) + _ - 1 - _
  simp only [div_eq_mul_inv, one_mul] at hu hb ⊢
  linarith

end

end Stability.Selection
