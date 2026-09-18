import HGAS.Wrapper.UnitSphereWrapperChart
import Mathlib.Tactic

/-!
# An attained proper-face equilibrium

The exact maximal-average identity needs the auxiliary reward value `-1`
to be attained, not merely approached.  The canonical witness is the
chart pole

```
e₀ = (1,0,…,0).
```

At this point the chart block has scaled squared radius `L`, every source
block has radius zero, and the radius average is `1-L`.  The chart block
deviation therefore vanishes; all other velocity coordinates contain a
zero coordinate factor.  Hence the raw cleanup field, and therefore its
parity-homogenized angular field, vanish at `e₀`.  Every source block is
absent, so the wrapper reward is exactly `-1`.
-/

namespace HGAS

open _root_.MvPolynomial
open scoped BigOperators

noncomputable section

namespace UnitSpherePolynomialWrapper

variable {n k : ℕ}

/-- The canonical pole supported only in the chart coordinate. -/
def chartPole : Fin (n + 1) → ℝ :=
  PolynomialCode.unitChartPoint 1 0

@[simp]
theorem chartPole_zero :
    (chartPole : Fin (n + 1) → ℝ) 0 = 1 :=
  rfl

@[simp]
theorem chartPole_succ (j : Fin n) :
    (chartPole : Fin (n + 1) → ℝ) j.succ = 0 :=
  rfl

@[simp]
theorem normSq_chartPole :
    normSq (chartPole : Fin (n + 1) → ℝ) = 1 := by
  rw [normSq, dot, Fin.sum_univ_succ]
  simp

@[simp]
theorem scaledBlockRadius_chartPole_zero
    (sourceBlock : Fin n → Fin k) :
    scaledBlockRadius sourceBlock
      (chartPole : Fin (n + 1) → ℝ) 0 = (k + 1 : ℝ) := by
  simpa [chartPole] using
    scaledBlockRadius_chart_zero sourceBlock (1 : ℝ) (0 : Fin n → ℝ)

@[simp]
theorem sourceBlockNormSq_zero
    (sourceBlock : Fin n → Fin k) (i : Fin k) :
    sourceBlockNormSq sourceBlock (0 : Fin n → ℝ) i = 0 := by
  simp [sourceBlockNormSq]

@[simp]
theorem scaledBlockRadius_chartPole_succ
    (sourceBlock : Fin n → Fin k) (i : Fin k) :
    scaledBlockRadius sourceBlock
      (chartPole : Fin (n + 1) → ℝ) i.succ = 0 := by
  simpa [chartPole] using
    scaledBlockRadius_chart_succ sourceBlock
      (1 : ℝ) (0 : Fin n → ℝ) i

/-- The radius average at the pole is `1-L`. -/
theorem radiusAverage_chartPole
    (sourceBlock : Fin n → Fin k) :
    radiusAverage (k + 1 : ℝ)
      (fun b ↦ scaledBlockRadius sourceBlock
        (chartPole : Fin (n + 1) → ℝ) b) =
      1 - (k + 1 : ℝ) := by
  rw [radiusAverage]
  rw [Fin.sum_univ_succ]
  simp only [scaledBlockRadius_chartPole_zero,
    scaledBlockRadius_chartPole_succ, zero_mul, Finset.sum_const_zero,
    add_zero]
  have hL : (k + 1 : ℝ) ≠ 0 := by positivity
  field_simp

/-- The chart-block cleanup deviation vanishes at the pole. -/
theorem radiusDeviation_chartPole_zero
    (sourceBlock : Fin n → Fin k) :
    radiusDeviation (k + 1 : ℝ)
      (fun b ↦ scaledBlockRadius sourceBlock
        (chartPole : Fin (n + 1) → ℝ) b) 0 = 0 := by
  rw [radiusDeviation, scaledBlockRadius_chartPole_zero,
    radiusAverage_chartPole]
  ring

/-- Every chart-field block dot product vanishes at the pole. -/
theorem blockDotValue_chartField_chartPole
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j)) :
    ∀ b,
      blockDotValue sourceBlock
        (chartPole : Fin (n + 1) → ℝ)
        (PolynomialFieldCode.realize (chartFieldCode k D P)
          (chartPole : Fin (n + 1) → ℝ)) b = 0 := by
  intro b
  refine Fin.cases ?_ (fun i ↦ ?_) b
  · exact blockDotValue_chartField_zero sourceBlock D P _
  · simpa [chartPole, sourceBlockDot] using
      blockDotValue_chartField_succ_scaled
        sourceBlock D P hP (1 : ℝ) (0 : Fin n → ℝ) i

/-- The raw angular cleanup field fixes the pole. -/
theorem realize_rawWrapperFieldCode_chartPole
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j)) :
    PolynomialFieldCode.realize
        (rawWrapperFieldCode sourceBlock D P)
        (chartPole : Fin (n + 1) → ℝ) = 0 := by
  have hdots :=
    blockDotValue_chartField_chartPole sourceBlock D P hP
  funext j
  refine Fin.cases ?_ (fun q ↦ ?_) j
  · rw [eval_rawWrapperFieldCode, eval_tangentFieldCode]
    simp only [ambientBlock_zero]
    rw [scaledBlockRadius_chartPole_zero, hdots,
      radiusDeviation_chartPole_zero]
    have hchart :
        PolynomialFieldCode.realize (chartFieldCode k D P)
          (chartPole : Fin (n + 1) → ℝ) 0 = 0 :=
      eval_chartFieldCode_zero D P _
    rw [hchart]
    simp
  · rw [eval_rawWrapperFieldCode, eval_tangentFieldCode]
    simp only [ambientBlock_succ]
    rw [scaledBlockRadius_chartPole_succ, hdots]
    simp

/-- Parity homogenization is invisible at the unit pole, so the final
angular field also fixes it. -/
theorem realize_homogeneousAngularCode_chartPole
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j)) :
    PolynomialFieldCode.realize
        (homogeneousAngularCode sourceBlock D P)
        (chartPole : Fin (n + 1) → ℝ) = 0 := by
  rw [realize_homogeneousAngularCode_of_normSq_one
    sourceBlock D P _ normSq_chartPole]
  exact realize_rawWrapperFieldCode_chartPole sourceBlock D P hP

/-- Any source block is absent at the pole, so the raw reward is `-1`. -/
theorem eval_rawWrapperRewardCode_chartPole
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (a : PolynomialCode n)
    (i : Fin k) :
    eval₂Hom (algebraMap ℚ ℝ)
        (chartPole : Fin (n + 1) → ℝ)
        (PolynomialCode.decode
          (rawWrapperRewardCode sourceBlock D a)) = -1 := by
  rw [eval_rawWrapperRewardCode]
  exact wrapperReward_eq_neg_one_of_zero_coordinate
    (fun b ↦ scaledBlockRadius sourceBlock
      (chartPole : Fin (n + 1) → ℝ) b)
    _ (scaledBlockRadius_chartPole_succ sourceBlock i)

/-- The final homogeneous radial reward also equals `-1` at the pole. -/
theorem eval_homogeneousRewardCode_chartPole
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (a : PolynomialCode n)
    (i : Fin k) :
    eval₂Hom (algebraMap ℚ ℝ)
        (chartPole : Fin (n + 1) → ℝ)
        (PolynomialCode.decode
          (homogeneousRewardCode sourceBlock D a)) = -1 := by
  rw [eval_homogeneousRewardCode_of_normSq_one
    sourceBlock D a _ normSq_chartPole]
  exact eval_rawWrapperRewardCode_chartPole sourceBlock D a i

end UnitSpherePolynomialWrapper

end

end HGAS
