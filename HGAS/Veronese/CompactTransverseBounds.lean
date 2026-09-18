import HGAS.Veronese.RealCone
import HGAS.Veronese.TransverseStabilization
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic

/-!
# Compact bounds for Veronese transverse stabilization

The complete constraint energy is

```
W(y) = ∑ r, q_r(y)^2,
```

where `r` ranges over every balanced quadratic Veronese relation.  The
real-cone theorem identifies its zero set on `Q=1` exactly with the two
signed Veronese sheets.

This module also records everything needed in the stabilization argument
that follows from compactness alone:

* `Q=1` is compact;
* every continuous radial reward is uniformly bounded there;
* for every continuous field `V`, the penalty derivative satisfies the
  universal weaker estimate `|V W| ≤ B sqrt(W)`.

The stronger estimate `|V W| ≤ C W` and the coercive estimate
`D ≥ c W` do **not** follow from compactness plus equality of zero sets.
They require first-order tangency/error-bound information and the
Morse--Bott conormal-rank argument, respectively.  No such conclusion is
assumed in this file.
-/

namespace HGAS.Veronese

open scoped BigOperators

noncomputable section

variable {n k : ℕ}

/-- The weighted unit ellipsoid `Q=1`. -/
def weightedUnitSphere (n k : ℕ) :
    Set (RealVeroneseSpace n k) :=
  {y | Q y = 1}

/-- The complete balanced-quadratic constraint energy. -/
abbrev completeToricEnergy
    (y : RealVeroneseSpace n k) : ℝ :=
  toricPenalty y

theorem continuous_Q_real :
    Continuous (fun y : RealVeroneseSpace n k ↦ Q y) := by
  unfold Q
  fun_prop

theorem continuous_toricRelation_real
    (r : ToricRelationIndex n k) :
    Continuous
      (fun y : RealVeroneseSpace n k ↦ toricRelation r y) := by
  unfold toricRelation
  fun_prop

theorem continuous_completeToricEnergy :
    Continuous
      (fun y : RealVeroneseSpace n k ↦ completeToricEnergy y) := by
  unfold completeToricEnergy toricPenalty
  apply continuous_finsetSum
  intro r _
  exact (continuous_toricRelation_real r).pow 2

/-- The complete energy vanishes on `Q=1` exactly on the signed unit
Veronese sheets. -/
theorem completeToricEnergy_eq_zero_on_weightedUnitSphere_iff
    (hk : 1 ≤ k) (y : RealVeroneseSpace n k)
    (hQ : Q y = 1) :
    completeToricEnergy y = 0 ↔
      ∃ u : Fin n → ℝ,
        sourceRadiusSq u = 1 ∧
          (y = veroneseMap (k := k) u ∨
            y = -veroneseMap (k := k) u) := by
  rw [toricPenalty_eq_zero_iff_mem_toricZeroSet_real]
  have hsphere :
      y ∈ toricSphereZeroSet n k ↔
        y ∈ toricZeroSet (R := ℝ) n k := by
    simp only [mem_toricSphereZeroSet_iff, hQ, and_true]
  rw [← hsphere,
    mem_toricSphereZeroSet_iff_exists_signed_veronese hk y]

/-! ## Compactness of the weighted unit sphere -/

theorem isClosed_weightedUnitSphere :
    IsClosed (weightedUnitSphere n k) := by
  exact isClosed_eq continuous_Q_real continuous_const

/-- Every coordinate, hence the product norm, is at most one on `Q=1`.
The multinomial weights are positive integers and therefore at least
one. -/
theorem norm_le_one_of_Q_eq_one
    (y : RealVeroneseSpace n k) (hQ : Q y = 1) :
    ‖y‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro a
  rw [Real.norm_eq_abs]
  have hterm :
      (multinomialWeight a : ℝ) * y a ^ 2 ≤ Q y := by
    unfold Q
    exact Finset.single_le_sum
      (fun b _ ↦
        mul_nonneg (Nat.cast_nonneg _) (sq_nonneg (y b)))
      (Finset.mem_univ a)
  have hweight : (1 : ℝ) ≤ multinomialWeight a := by
    exact_mod_cast multinomialWeight_pos a
  have hsquare : y a ^ 2 ≤ 1 := by
    rw [hQ] at hterm
    nlinarith [sq_nonneg (y a)]
  exact (sq_le_one_iff_abs_le_one (y a)).mp hsquare

theorem isBounded_weightedUnitSphere :
    Bornology.IsBounded (weightedUnitSphere n k) := by
  rw [isBounded_iff_forall_norm_le]
  exact
    ⟨1, fun y hy ↦
      norm_le_one_of_Q_eq_one y hy⟩

/-- The ellipsoid `Q=1` is compact in finite-dimensional Veronese
coordinate space. -/
theorem isCompact_weightedUnitSphere :
    IsCompact (weightedUnitSphere n k) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact
    ⟨isClosed_weightedUnitSphere,
      isBounded_weightedUnitSphere⟩

/-! ## Uniform bounds for continuous fields -/

/-- A reusable absolute-value bound for a continuous scalar function on
the weighted unit sphere. -/
theorem exists_nonneg_abs_bound_on_weightedUnitSphere
    (f : RealVeroneseSpace n k → ℝ)
    (hf : Continuous f) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ y : RealVeroneseSpace n k,
        Q y = 1 → |f y| ≤ A := by
  obtain ⟨C, hC⟩ :=
    isCompact_weightedUnitSphere.exists_bound_of_continuousOn
      hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro y hQ
  have hCy := hC y hQ
  rw [Real.norm_eq_abs] at hCy
  exact hCy.trans (le_max_left _ _)

theorem continuous_weightedRadialReward
    {G : RealVeroneseSpace n k → RealVeroneseSpace n k}
    (hG : Continuous G) :
    Continuous (weightedRadialReward G) := by
  unfold weightedRadialReward weightedInner
  fun_prop

theorem continuous_weightedAngularField
    {G : RealVeroneseSpace n k → RealVeroneseSpace n k}
    (hG : Continuous G) :
    Continuous (weightedAngularField G) := by
  unfold weightedAngularField
  exact hG.sub
    ((continuous_weightedRadialReward hG).smul continuous_id)

/-- Compactness supplies the global reward constant `A` used outside
the stabilization tube. -/
theorem exists_radialReward_bound_on_weightedUnitSphere
    {G : RealVeroneseSpace n k → RealVeroneseSpace n k}
    (hG : Continuous G) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ y : RealVeroneseSpace n k,
        Q y = 1 →
          |weightedRadialReward G y| ≤ A :=
  exists_nonneg_abs_bound_on_weightedUnitSphere
    (weightedRadialReward G)
    (continuous_weightedRadialReward hG)

/-- Continuity of one relation differential evaluated along a continuous
field. -/
theorem continuous_toricRelationDifferential_along
    (r : ToricRelationIndex n k)
    {V : RealVeroneseSpace n k → RealVeroneseSpace n k}
    (hV : Continuous V) :
    Continuous
      (fun y ↦ toricRelationDifferential r y (V y)) := by
  unfold toricRelationDifferential
  fun_prop

/-- Sum of absolute relation differentials along `V`. -/
def relationDifferentialAbsSum
    (V : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (y : RealVeroneseSpace n k) : ℝ :=
  ∑ r : ToricRelationIndex n k,
    |toricRelationDifferential r y (V y)|

theorem continuous_relationDifferentialAbsSum
    {V : RealVeroneseSpace n k → RealVeroneseSpace n k}
    (hV : Continuous V) :
    Continuous (relationDifferentialAbsSum V) := by
  unfold relationDifferentialAbsSum
  apply continuous_finsetSum
  intro r _
  exact (continuous_toricRelationDifferential_along r hV).abs

theorem relationDifferentialAbsSum_nonneg
    (V : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (y : RealVeroneseSpace n k) :
    0 ≤ relationDifferentialAbsSum V y :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-! ## The compactness-level square-root estimate -/

/-- Each individual squared relation is one nonnegative summand of
`W`, so `|q_r| ≤ sqrt W`. -/
theorem abs_toricRelation_le_sqrt_completeToricEnergy
    (r : ToricRelationIndex n k)
    (y : RealVeroneseSpace n k) :
    |toricRelation r y| ≤
      Real.sqrt (completeToricEnergy y) := by
  have hsquare :
      toricRelation r y ^ 2 ≤ completeToricEnergy y := by
    unfold completeToricEnergy toricPenalty
    exact Finset.single_le_sum
      (fun s _ ↦ sq_nonneg (toricRelation s y))
      (Finset.mem_univ r)
  calc
    |toricRelation r y| =
        Real.sqrt (toricRelation r y ^ 2) :=
      (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (completeToricEnergy y) :=
      Real.sqrt_le_sqrt hsquare

/-- Purely algebraic pointwise estimate for the energy derivative. -/
theorem abs_toricPenaltyDirectional_le_sqrt_mul_absSum
    (V : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (y : RealVeroneseSpace n k) :
    |toricPenaltyDirectional y (V y)| ≤
      2 * Real.sqrt (completeToricEnergy y) *
        relationDifferentialAbsSum V y := by
  rw [toricPenaltyDirectional]
  calc
    |∑ r : ToricRelationIndex n k,
        2 * toricRelation r y *
          toricRelationDifferential r y (V y)| ≤
      ∑ r : ToricRelationIndex n k,
        |2 * toricRelation r y *
          toricRelationDifferential r y (V y)| :=
      Finset.abs_sum_le_sum_abs
        (s := (Finset.univ :
          Finset (ToricRelationIndex n k)))
        (f := fun r ↦
          2 * toricRelation r y *
            toricRelationDifferential r y (V y))
    _ ≤
      ∑ r : ToricRelationIndex n k,
        2 * Real.sqrt (completeToricEnergy y) *
          |toricRelationDifferential r y (V y)| := by
      apply Finset.sum_le_sum
      intro r _
      calc
        |2 * toricRelation r y *
            toricRelationDifferential r y (V y)| =
          2 * |toricRelation r y| *
            |toricRelationDifferential r y (V y)| := by
              simp only [abs_mul]
              norm_num
        _ ≤
          2 * Real.sqrt (completeToricEnergy y) *
            |toricRelationDifferential r y (V y)| := by
              gcongr
              exact
                abs_toricRelation_le_sqrt_completeToricEnergy r y
    _ =
      2 * Real.sqrt (completeToricEnergy y) *
        relationDifferentialAbsSum V y := by
      rw [relationDifferentialAbsSum, Finset.mul_sum]

/-- Compactness and the sum-of-squares formula always give
`|V W| ≤ B sqrt W` for a continuous field `V`. -/
theorem exists_penaltyDirectional_sqrt_bound_on_weightedUnitSphere
    {V : RealVeroneseSpace n k → RealVeroneseSpace n k}
    (hV : Continuous V) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ y : RealVeroneseSpace n k,
        Q y = 1 →
          |toricPenaltyDirectional y (V y)| ≤
            B * Real.sqrt (completeToricEnergy y) := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_nonneg_abs_bound_on_weightedUnitSphere
      (relationDifferentialAbsSum V)
      (continuous_relationDifferentialAbsSum hV)
  refine ⟨2 * A, mul_nonneg (by norm_num) hA, ?_⟩
  intro y hQ
  have hsum :
      relationDifferentialAbsSum V y ≤ A := by
    have habs := hbound y hQ
    rwa [abs_of_nonneg
      (relationDifferentialAbsSum_nonneg V y)] at habs
  calc
    |toricPenaltyDirectional y (V y)| ≤
        2 * Real.sqrt (completeToricEnergy y) *
          relationDifferentialAbsSum V y :=
      abs_toricPenaltyDirectional_le_sqrt_mul_absSum V y
    _ ≤
        2 * Real.sqrt (completeToricEnergy y) * A := by
      gcongr
    _ = (2 * A) * Real.sqrt (completeToricEnergy y) := by
      ring

/-- Gradient-pairing form of the preceding square-root estimate. -/
theorem exists_penaltyLieDerivative_sqrt_bound_on_weightedUnitSphere
    {V : RealVeroneseSpace n k → RealVeroneseSpace n k}
    (hV : Continuous V) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ y : RealVeroneseSpace n k,
        Q y = 1 →
          |penaltyLieDerivative V y| ≤
            B * Real.sqrt (completeToricEnergy y) := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_penaltyDirectional_sqrt_bound_on_weightedUnitSphere hV
  refine ⟨B, hB, ?_⟩
  intro y hQ
  rw [penaltyLieDerivative,
    ← toricPenaltyDirectional_eq_weightedInner]
  exact hbound y hQ

/-- In particular the unstabilized angular field has the universal
square-root tangency bound.  Improving `sqrt W` to `W` is the separate
first-order tangency/Morse--Bott step. -/
theorem exists_angularPenaltyLieDerivative_sqrt_bound
    {G : RealVeroneseSpace n k → RealVeroneseSpace n k}
    (hG : Continuous G) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ y : RealVeroneseSpace n k,
        Q y = 1 →
          |penaltyLieDerivative (weightedAngularField G) y| ≤
            B * Real.sqrt (completeToricEnergy y) :=
  exists_penaltyLieDerivative_sqrt_bound_on_weightedUnitSphere
    (continuous_weightedAngularField hG)

/-! ## Exact relation factorization upgrades `sqrt W` to `W`

The hypothesis below is intentionally displayed in full:

```
dq_r(y) V(y) = ∑ s, c_{r,s}(y) q_s(y).
```

It is an algebraic toric-ideal membership statement.  Once coefficient
functions `c_{r,s}` are supplied, compactness bounds them and the desired
`O(W)` tangency estimate follows without any Morse--Bott assumption. -/

/-- Absolute row sum of explicit relation-factorization coefficients. -/
def relationFactorizationRowAbsSum
    (coeff :
      ToricRelationIndex n k → ToricRelationIndex n k →
        RealVeroneseSpace n k → ℝ)
    (r : ToricRelationIndex n k)
    (y : RealVeroneseSpace n k) : ℝ :=
  ∑ s : ToricRelationIndex n k, |coeff r s y|

/-- Absolute sum of all relation-factorization coefficients. -/
def relationFactorizationAbsSum
    (coeff :
      ToricRelationIndex n k → ToricRelationIndex n k →
        RealVeroneseSpace n k → ℝ)
    (y : RealVeroneseSpace n k) : ℝ :=
  ∑ r : ToricRelationIndex n k,
    relationFactorizationRowAbsSum coeff r y

theorem continuous_relationFactorizationAbsSum
    (coeff :
      ToricRelationIndex n k → ToricRelationIndex n k →
        RealVeroneseSpace n k → ℝ)
    (hcoeff : ∀ r s, Continuous (coeff r s)) :
    Continuous (relationFactorizationAbsSum coeff) := by
  unfold relationFactorizationAbsSum
    relationFactorizationRowAbsSum
  apply continuous_finsetSum
  intro r _
  apply continuous_finsetSum
  intro s _
  exact (hcoeff r s).abs

theorem relationFactorizationAbsSum_nonneg
    (coeff :
      ToricRelationIndex n k → ToricRelationIndex n k →
        RealVeroneseSpace n k → ℝ)
    (y : RealVeroneseSpace n k) :
    0 ≤ relationFactorizationAbsSum coeff y := by
  exact Finset.sum_nonneg fun r _ ↦
    Finset.sum_nonneg fun s _ ↦ abs_nonneg (coeff r s y)

/-- One factored relation derivative is bounded by `sqrt W` times its
coefficient row sum. -/
theorem abs_toricRelationDifferential_le_of_factorization
    (V : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (coeff :
      ToricRelationIndex n k → ToricRelationIndex n k →
        RealVeroneseSpace n k → ℝ)
    (hfactor :
      ∀ r y,
        toricRelationDifferential r y (V y) =
          ∑ s : ToricRelationIndex n k,
            coeff r s y * toricRelation s y)
    (r : ToricRelationIndex n k)
    (y : RealVeroneseSpace n k) :
    |toricRelationDifferential r y (V y)| ≤
      Real.sqrt (completeToricEnergy y) *
        relationFactorizationRowAbsSum coeff r y := by
  rw [hfactor]
  calc
    |∑ s : ToricRelationIndex n k,
        coeff r s y * toricRelation s y| ≤
      ∑ s : ToricRelationIndex n k,
        |coeff r s y * toricRelation s y| :=
      Finset.abs_sum_le_sum_abs
        (s := (Finset.univ :
          Finset (ToricRelationIndex n k)))
        (f := fun s ↦ coeff r s y * toricRelation s y)
    _ ≤
      ∑ s : ToricRelationIndex n k,
        Real.sqrt (completeToricEnergy y) *
          |coeff r s y| := by
      apply Finset.sum_le_sum
      intro s _
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (abs_toricRelation_le_sqrt_completeToricEnergy s y)
        (abs_nonneg _)
    _ =
      Real.sqrt (completeToricEnergy y) *
        relationFactorizationRowAbsSum coeff r y := by
      rw [relationFactorizationRowAbsSum, Finset.mul_sum]

/-- Pointwise `O(W)` estimate obtained from an exact relation
factorization. -/
theorem abs_toricPenaltyDirectional_le_of_factorization
    (V : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (coeff :
      ToricRelationIndex n k → ToricRelationIndex n k →
        RealVeroneseSpace n k → ℝ)
    (hfactor :
      ∀ r y,
        toricRelationDifferential r y (V y) =
          ∑ s : ToricRelationIndex n k,
            coeff r s y * toricRelation s y)
    (y : RealVeroneseSpace n k) :
    |toricPenaltyDirectional y (V y)| ≤
      2 * completeToricEnergy y *
        relationFactorizationAbsSum coeff y := by
  rw [toricPenaltyDirectional]
  calc
    |∑ r : ToricRelationIndex n k,
        2 * toricRelation r y *
          toricRelationDifferential r y (V y)| ≤
      ∑ r : ToricRelationIndex n k,
        |2 * toricRelation r y *
          toricRelationDifferential r y (V y)| :=
      Finset.abs_sum_le_sum_abs
        (s := (Finset.univ :
          Finset (ToricRelationIndex n k)))
        (f := fun r ↦
          2 * toricRelation r y *
            toricRelationDifferential r y (V y))
    _ ≤
      ∑ r : ToricRelationIndex n k,
        2 * completeToricEnergy y *
          relationFactorizationRowAbsSum coeff r y := by
      apply Finset.sum_le_sum
      intro r _
      have hq :=
        abs_toricRelation_le_sqrt_completeToricEnergy r y
      have hd :=
        abs_toricRelationDifferential_le_of_factorization
          V coeff hfactor r y
      have hW := toricPenalty_nonneg_real y
      calc
        |2 * toricRelation r y *
            toricRelationDifferential r y (V y)| =
          2 * |toricRelation r y| *
            |toricRelationDifferential r y (V y)| := by
              simp only [abs_mul]
              norm_num
        _ ≤
          2 * Real.sqrt (completeToricEnergy y) *
            (Real.sqrt (completeToricEnergy y) *
              relationFactorizationRowAbsSum coeff r y) := by
                gcongr
        _ =
          2 * completeToricEnergy y *
            relationFactorizationRowAbsSum coeff r y := by
              calc
                2 * Real.sqrt (completeToricEnergy y) *
                    (Real.sqrt (completeToricEnergy y) *
                      relationFactorizationRowAbsSum coeff r y) =
                  2 *
                    (Real.sqrt (completeToricEnergy y) *
                      Real.sqrt (completeToricEnergy y)) *
                    relationFactorizationRowAbsSum coeff r y := by
                      ring
                _ =
                  2 * completeToricEnergy y *
                    relationFactorizationRowAbsSum coeff r y := by
                      rw [Real.mul_self_sqrt hW]
    _ =
      2 * completeToricEnergy y *
        relationFactorizationAbsSum coeff y := by
      rw [relationFactorizationAbsSum, Finset.mul_sum]

/-- Compactness upgrades the explicit algebraic factorization to a
uniform `|V W| ≤ C W` bound on `Q=1`. -/
theorem exists_penaltyDirectional_linear_bound_of_factorization
    {V : RealVeroneseSpace n k → RealVeroneseSpace n k}
    (coeff :
      ToricRelationIndex n k → ToricRelationIndex n k →
        RealVeroneseSpace n k → ℝ)
    (hcoeff : ∀ r s, Continuous (coeff r s))
    (hfactor :
      ∀ r y,
        toricRelationDifferential r y (V y) =
          ∑ s : ToricRelationIndex n k,
            coeff r s y * toricRelation s y) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : RealVeroneseSpace n k,
        Q y = 1 →
          |toricPenaltyDirectional y (V y)| ≤
            C * completeToricEnergy y := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_nonneg_abs_bound_on_weightedUnitSphere
      (relationFactorizationAbsSum coeff)
      (continuous_relationFactorizationAbsSum coeff hcoeff)
  refine ⟨2 * A, mul_nonneg (by norm_num) hA, ?_⟩
  intro y hQ
  have hsum :
      relationFactorizationAbsSum coeff y ≤ A := by
    have habs := hbound y hQ
    rwa [abs_of_nonneg
      (relationFactorizationAbsSum_nonneg coeff y)] at habs
  calc
    |toricPenaltyDirectional y (V y)| ≤
        2 * completeToricEnergy y *
          relationFactorizationAbsSum coeff y :=
      abs_toricPenaltyDirectional_le_of_factorization
        V coeff hfactor y
    _ ≤ 2 * completeToricEnergy y * A := by
      gcongr
      exact mul_nonneg (by norm_num) (toricPenalty_nonneg_real y)
    _ = (2 * A) * completeToricEnergy y := by ring

/-- Gradient-pairing version of the exact-factorization `O(W)` bound. -/
theorem exists_penaltyLieDerivative_linear_bound_of_factorization
    {V : RealVeroneseSpace n k → RealVeroneseSpace n k}
    (coeff :
      ToricRelationIndex n k → ToricRelationIndex n k →
        RealVeroneseSpace n k → ℝ)
    (hcoeff : ∀ r s, Continuous (coeff r s))
    (hfactor :
      ∀ r y,
        toricRelationDifferential r y (V y) =
          ∑ s : ToricRelationIndex n k,
            coeff r s y * toricRelation s y) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : RealVeroneseSpace n k,
        Q y = 1 →
          |penaltyLieDerivative V y| ≤
            C * completeToricEnergy y := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_penaltyDirectional_linear_bound_of_factorization
      coeff hcoeff hfactor
  refine ⟨C, hC, ?_⟩
  intro y hQ
  rw [penaltyLieDerivative,
    ← toricPenaltyDirectional_eq_weightedInner]
  exact hbound y hQ

end

end HGAS.Veronese
