import HGAS.Compiler.CompactAccumulatorPipelineTangency
import HGAS.Accumulator.RewardGap
import Mathlib.Tactic

/-!
# Exact reward bounds for the compiled compact accumulator

The pipeline emits the literal polynomial

```
                 R = W + 2 ∏ᵦ wᵦ² - 1 - ε.
```

This file connects that finite code to the three pointwise estimates used
in the compact sign argument:

* a source equator has reward at most `-ε`;
* accumulator infinity has reward at most `-ε`;
* the designated finite graph has the advertised positive lower bound.

All estimates are derived from the product-sphere equations, including the
facts `W ≤ 1` and `∏wᵦ² ≤ 1`.
-/

namespace HGAS

open _root_.MvPolynomial
open scoped BigOperators

noncomputable section

namespace CompactAccumulatorPipelineCode

variable {n k l m : ℕ}

/-- Evaluation of the central-weight polynomial at an arbitrary mixed
ambient point. -/
theorem eval₂Hom_centralWeightProductCode_chartPoint
    (x : Fin n → ℝ) (w : Fin k → ℝ) :
    eval₂Hom (algebraMap ℚ ℝ)
        (MixedCentralPolynomialCode.chartPoint x w)
        (PolynomialCode.decode
          (centralWeightProductCode (n := n) (k := k))) =
      ∏ b, w b ^ 2 := by
  have hfold :
      ∀ ps : List (PolynomialCode (n + k)),
        eval₂Hom (algebraMap ℚ ℝ)
            (MixedCentralPolynomialCode.chartPoint x w)
            (PolynomialCode.decode
              (ps.foldr PolynomialCode.mul PolynomialCode.one)) =
          (ps.map fun p ↦
            eval₂Hom (algebraMap ℚ ℝ)
              (MixedCentralPolynomialCode.chartPoint x w)
              (PolynomialCode.decode p)).prod := by
    intro ps
    induction ps with
    | nil => simp
    | cons p ps ih =>
        simp only [List.foldr_cons,
          PolynomialCode.decode_mul_code, map_mul,
          List.map_cons, List.prod_cons]
        rw [ih]
  rw [centralWeightProductCode, hfold, List.map_ofFn,
    List.prod_ofFn]
  simp

/-- The reward code has its literal paper semantics at every source and
accumulator point. -/
theorem eval₂Hom_rewardCode_chartPoint
    (ε : RationalCode)
    (x : Fin n → ℝ) (w : Fin k → ℝ)
    (u : Fin m → ℝ) (W : ℝ) :
    eval₂Hom (algebraMap ℚ ℝ)
        (AccumulatorPolynomialCode.combinedPoint
          (MixedCentralPolynomialCode.chartPoint x w) u W)
        (PolynomialCode.decode
          (rewardCode (n := n) (k := k) (m := m) ε)) =
      accumulatorReward W (∏ b, w b ^ 2)
        (ε.decode : ℝ) := by
  simp only [rewardCode, PolynomialCode.decode_sub_code,
    PolynomialCode.decode_add_code,
    PolynomialCode.decode_mul_code,
    PolynomialCode.decode_varCode,
    PolynomialCode.decode_constant,
    PolynomialCode.decode_one_code,
    map_sub, map_add, map_mul, map_one,
    eval₂Hom_X', eval₂Hom_C,
    AccumulatorPolynomialCode.combinedPoint_wIndex,
    RationalCode.decode_ofNat]
  unfold liftedCentralWeightProductCode
  rw [AccumulatorPolynomialCode.eval₂Hom_liftBase,
    eval₂Hom_centralWeightProductCode_chartPoint]
  have hε :
      (algebraMap ℚ ℝ) ε.decode = (ε.decode : ℝ) := by
    rfl
  rw [hε]
  norm_num
  unfold accumulatorReward
  ring

/-- Every affine chart-square belongs to `[0,1]` on the mixed source
product of spheres. -/
theorem chartWeight_sq_le_one
    (layout : Fin n → Fin k ⊕ Fin l)
    (x : Fin n → ℝ) (w : Fin k → ℝ)
    (hspheres :
      UnitSpherePolynomialWrapper.OnSourceProductSpheres
        (MixedCentralPolynomialCode.targetBlock layout)
        (MixedCentralPolynomialCode.chartPoint x w))
    (b : Fin k) :
    0 ≤ w b ^ 2 ∧ w b ^ 2 ≤ 1 := by
  have haffine :=
    (MixedCentralPolynomialCode.onSourceProductSpheres_targetBlock_iff
        layout x w).mp hspheres |>.1 b
  constructor
  · positivity
  · have hnorm :
        0 ≤
          MixedCentralPolynomialCode.affineBlockNormSq
            layout x b := by
      unfold MixedCentralPolynomialCode.affineBlockNormSq
      apply Finset.sum_nonneg
      intro j _
      split_ifs
      · positivity
      · exact le_rfl
    linarith

/-- Consequently the complete central-weight product is at most one. -/
theorem centralWeightProduct_le_one
    (layout : Fin n → Fin k ⊕ Fin l)
    (x : Fin n → ℝ) (w : Fin k → ℝ)
    (hspheres :
      UnitSpherePolynomialWrapper.OnSourceProductSpheres
        (MixedCentralPolynomialCode.targetBlock layout)
        (MixedCentralPolynomialCode.chartPoint x w)) :
    (∏ b, w b ^ 2) ≤ 1 := by
  apply Finset.prod_le_one
  · intro b _
    exact (chartWeight_sq_le_one
      layout x w hspheres b).1
  · intro b _
    exact (chartWeight_sq_le_one
      layout x w hspheres b).2

/-- The stereographic scalar coordinate is at most one on its unit
sphere. -/
theorem accumulatorW_le_one
    (u : Fin m → ℝ) (W : ℝ)
    (hsphere : normSq u + W ^ 2 = 1) :
    W ≤ 1 := by
  have hu : 0 ≤ normSq u := normSq_nonneg u
  nlinarith [sq_nonneg (W + 1)]

/-- If one source chart coordinate vanishes, the complete compiled reward
is at most `-ε`. -/
theorem eval₂Hom_rewardCode_le_neg_epsilon_on_sourceFace
    (ε : RationalCode)
    (x : Fin n → ℝ) (w : Fin k → ℝ)
    (u : Fin m → ℝ) (W : ℝ)
    (haccumulator : normSq u + W ^ 2 = 1)
    (hface : ∃ b, w b = 0) :
    eval₂Hom (algebraMap ℚ ℝ)
        (AccumulatorPolynomialCode.combinedPoint
          (MixedCentralPolynomialCode.chartPoint x w) u W)
        (PolynomialCode.decode
          (rewardCode (n := n) (k := k) (m := m) ε)) ≤
      -(ε.decode : ℝ) := by
  rw [eval₂Hom_rewardCode_chartPoint]
  apply accumulatorReward_le_neg_epsilon_on_source_face
    (accumulatorW_le_one u W haccumulator)
  obtain ⟨b, hb⟩ := hface
  apply Finset.prod_eq_zero (Finset.mem_univ b)
  simp [hb]

/-- At accumulator infinity the complete compiled reward is at most
`-ε`. -/
theorem eval₂Hom_rewardCode_le_neg_epsilon_at_infinity
    (ε : RationalCode)
    (layout : Fin n → Fin k ⊕ Fin l)
    (x : Fin n → ℝ) (w : Fin k → ℝ)
    (u : Fin m → ℝ) (W : ℝ)
    (hbase :
      UnitSpherePolynomialWrapper.OnSourceProductSpheres
        (MixedCentralPolynomialCode.targetBlock layout)
        (MixedCentralPolynomialCode.chartPoint x w))
    (hinfinity : W = -1) :
    eval₂Hom (algebraMap ℚ ℝ)
        (AccumulatorPolynomialCode.combinedPoint
          (MixedCentralPolynomialCode.chartPoint x w) u W)
        (PolynomialCode.decode
          (rewardCode (n := n) (k := k) (m := m) ε)) ≤
      -(ε.decode : ℝ) := by
  rw [eval₂Hom_rewardCode_chartPoint]
  exact
    accumulatorReward_le_neg_epsilon_at_infinity
      hinfinity
      (centralWeightProduct_le_one layout x w hbase)

/-- Pointwise finite-graph lower bound for the literal compiled reward. -/
theorem finiteGraphGap_le_eval₂Hom_rewardCode
    (ε : RationalCode)
    (x : Fin n → ℝ) (w : Fin k → ℝ)
    (u : Fin m → ℝ) (W wStar : ℝ)
    (hW : 1 - wStar / 2 ≤ W)
    (hweight : wStar ≤ ∏ b, w b ^ 2) :
    3 * wStar / 2 - (ε.decode : ℝ) ≤
      eval₂Hom (algebraMap ℚ ℝ)
        (AccumulatorPolynomialCode.combinedPoint
          (MixedCentralPolynomialCode.chartPoint x w) u W)
        (PolynomialCode.decode
          (rewardCode (n := n) (k := k) (m := m) ε)) := by
  rw [eval₂Hom_rewardCode_chartPoint]
  exact accumulatorReward_ge_finite_graph hW hweight

end CompactAccumulatorPipelineCode

end

end HGAS
