import HGAS.Veronese.Conormal
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# An explicit transverse affine chart for the Veronese cone

Fix a source coordinate `i`.  The pure target coordinate `k e_i` and
the adjacent coordinates `(k-1)e_i+e_j` form an affine coordinate chart
where the pure coordinate is nonzero.  For an arbitrary target point
`y` in that chart, define

```
C_i(y) = y_(k e_i) ν_k(x(y)),
x(y)_j = y_((k-1)e_i+e_j) / y_(k e_i).
```

This raw chart reconstruction has three decisive properties:

* `C_i(y)` is always a point of the Veronese cone;
* it agrees with `y` in the pure and all adjacent coordinates;
* it fixes every point of the cone in the chart.

Consequently the error `y - C_i(y)` vanishes in all affine chart
coordinates.  The final theorem gives the elementary conormal fact used
by the local coercivity proof: if such a chart-gauged vector annihilates
the differentials of all balanced quadrics at a point with nonzero pure
coordinate, then it is zero.  Its proof is only an induction using the
one-token transfer quadrics; no manifold or tubular-neighborhood
machinery is involved.
-/

namespace HGAS.Veronese

open scoped BigOperators

noncomputable section

variable {n k : ℕ}

/-- Raw reconstruction from the pure and adjacent coordinates in the
affine chart based at `i`. -/
def affineConeChart
    (y : MultiIndex n k → ℝ) (hk : 1 ≤ k) (i : Fin n) :
    MultiIndex n k → ℝ :=
  y (pureMultiIndex i) •
    veroneseMap (k := k) (affineSource y hk i)

/-- In the affine chart, the monomial belonging to an adjacent
multiindex is the corresponding affine source coordinate. -/
theorem monomial_affineSource_edge
    (y : MultiIndex n k → ℝ) (hk : 1 ≤ k) (i j : Fin n)
    (hpure : y (pureMultiIndex i) ≠ 0) :
    monomial (affineSource y hk i) (edgeMultiIndex hk i j) =
      affineSource y hk i j := by
  by_cases hji : j = i
  · subst j
    rw [edgeMultiIndex_same, monomial_pureMultiIndex,
      affineSource_apply_base y hk i hpure]
    simp
  · rw [edgeMultiIndex_of_ne hk i j hji]
    have hmoving :=
      monomial_transfer_mul
        (affineSource y hk i)
        (pureMultiIndex (k := k) i) j i hji
        (by simpa using hk)
    rw [affineSource_apply_base y hk i hpure,
      monomial_pureMultiIndex,
      affineSource_apply_base y hk i hpure,
      one_pow, mul_one, one_mul] at hmoving
    exact hmoving

/-- The raw reconstruction agrees with the input in the pure and every
adjacent coordinate.  Taking `j=i` gives the pure coordinate itself. -/
@[simp]
theorem affineConeChart_edge
    (y : MultiIndex n k → ℝ) (hk : 1 ≤ k) (i j : Fin n)
    (hpure : y (pureMultiIndex i) ≠ 0) :
    affineConeChart y hk i (edgeMultiIndex hk i j) =
      y (edgeMultiIndex hk i j) := by
  rw [affineConeChart, Pi.smul_apply, smul_eq_mul,
    veroneseMap_apply, ← monomial]
  rw [monomial_affineSource_edge y hk i j hpure]
  exact mul_div_cancel₀ _ hpure

/-- The raw reconstruction is a scalar multiple of a Veronese point, so
it satisfies every balanced quadratic relation. -/
theorem affineConeChart_mem_toricZeroSet
    (y : MultiIndex n k → ℝ) (hk : 1 ≤ k) (i : Fin n) :
    affineConeChart y hk i ∈ toricZeroSet (R := ℝ) n k := by
  intro r
  rw [affineConeChart, toricRelation_smul,
    toricRelation_veronese, mul_zero]

/-- The affine reconstruction is a retraction onto the cone wherever
the chosen pure coordinate is nonzero. -/
theorem affineConeChart_eq_of_mem_toricZeroSet
    (y : MultiIndex n k → ℝ) (hk : 1 ≤ k)
    (hy : y ∈ toricZeroSet (R := ℝ) n k)
    (i : Fin n) (hpure : y (pureMultiIndex i) ≠ 0) :
    affineConeChart y hk i = y := by
  funext a
  rw [affineConeChart, Pi.smul_apply, smul_eq_mul,
    veroneseMap_apply, ← monomial]
  exact (coordinate_eq_pure_mul_monomial_affineSource
    hk hy i hpure a).symm

/-- The affine reconstruction is continuous at every point in its
chart.  The proof is coordinatewise: each output coordinate is a finite
product of powers of quotients whose common denominator is the chosen
nonzero pure coordinate. -/
theorem continuousAt_affineConeChart
    (y : MultiIndex n k → ℝ) (hk : 1 ≤ k) (i : Fin n)
    (hpure : y (pureMultiIndex i) ≠ 0) :
    ContinuousAt (affineConeChart (k := k) · hk i) y := by
  apply continuousAt_pi.mpr
  intro a
  change ContinuousAt
    (fun z : MultiIndex n k → ℝ =>
      z (pureMultiIndex i) *
        ∏ j : Fin n,
          (z (edgeMultiIndex hk i j) /
            z (pureMultiIndex i)) ^ a.1 j) y
  apply (continuous_apply (pureMultiIndex i)).continuousAt.mul
  apply tendsto_finsetProd
  intro j _
  apply ContinuousAt.pow
  exact
    (continuous_apply (edgeMultiIndex hk i j)).continuousAt.div
      (continuous_apply (pureMultiIndex i)).continuousAt hpure

/-- Cauchy--Schwarz for the explicit diagonal metric.

The square-root weights are unnecessary: apply the elementary finite
Cauchy--Schwarz inequality to
`r_a=w_a u_a v_a`, `f_a=w_a u_a^2`, and `g_a=w_a v_a^2`. -/
theorem weightedInner_sq_le
    (u v : MultiIndex n k → ℝ) :
    weightedInner u v ^ 2 ≤ Q u * Q v := by
  unfold weightedInner Q
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro a _
    exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg (u a))
  · intro a _
    exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg (v a))
  · intro a _
    ring_nf
    exact le_rfl

/-! ## The exact chart error and quadratic expansions -/

/-- Error left after reconstructing the cone point with the same affine
chart coordinates. -/
def affineConeError
    (y : MultiIndex n k → ℝ) (hk : 1 ≤ k) (i : Fin n) :
    MultiIndex n k → ℝ :=
  y - affineConeChart y hk i

/-- The chart error vanishes in the pure and all adjacent
coordinates. -/
@[simp]
theorem affineConeError_edge
    (y : MultiIndex n k → ℝ) (hk : 1 ≤ k) (i j : Fin n)
    (hpure : y (pureMultiIndex i) ≠ 0) :
    affineConeError y hk i (edgeMultiIndex hk i j) = 0 := by
  rw [affineConeError, Pi.sub_apply,
    affineConeChart_edge y hk i j hpure, sub_self]

/-- The input is exactly the sum of its chart reconstruction and chart
error. -/
theorem affineConeChart_add_error
    (y : MultiIndex n k → ℝ) (hk : 1 ≤ k) (i : Fin n) :
    affineConeChart y hk i + affineConeError y hk i = y := by
  simp only [affineConeError]
  abel

/-- A point with nonzero toric penalty has nonzero chart error. -/
theorem affineConeError_ne_zero_of_toricPenalty_ne_zero
    (y : MultiIndex n k → ℝ) (hk : 1 ≤ k) (i : Fin n)
    (hW : toricPenalty y ≠ 0) :
    affineConeError y hk i ≠ 0 := by
  intro herr
  have hy : y = affineConeChart y hk i := by
    simpa only [affineConeError, sub_eq_zero] using herr
  rw [hy, affineConeChart, toricPenalty_smul,
    toricPenalty_veronese, mul_zero] at hW
  exact hW rfl

/-- Exact quadratic Taylor formula for one balanced relation. -/
theorem toricRelation_add
    (r : ToricRelationIndex n k)
    (z e : MultiIndex n k → ℝ) :
    toricRelation r (z + e) =
      toricRelation r z +
        toricRelationDifferential r z e +
        toricRelation r e := by
  simp only [toricRelation, toricRelationDifferential, Pi.add_apply]
  ring

/-- The relation differential is linear in its direction. -/
theorem toricRelationDifferential_smul_right
    (r : ToricRelationIndex n k)
    (z h : MultiIndex n k → ℝ) (c : ℝ) :
    toricRelationDifferential r z (c • h) =
      c * toricRelationDifferential r z h := by
  simp only [toricRelationDifferential, Pi.smul_apply, smul_eq_mul]
  ring

/-- The relation differential is linear in its base point. -/
theorem toricRelationDifferential_smul_left
    (r : ToricRelationIndex n k)
    (z h : MultiIndex n k → ℝ) (c : ℝ) :
    toricRelationDifferential r (c • z) h =
      c * toricRelationDifferential r z h := by
  simp only [toricRelationDifferential, Pi.smul_apply, smul_eq_mul]
  ring

/-- Exact relation expansion around the reconstructed cone point. -/
theorem toricRelation_eq_differential_chart_add_error
    (r : ToricRelationIndex n k)
    (y : MultiIndex n k → ℝ) (hk : 1 ≤ k) (i : Fin n) :
    toricRelation r y =
      toricRelationDifferential r
          (affineConeChart y hk i) (affineConeError y hk i) +
        toricRelation r (affineConeError y hk i) := by
  have hzero :=
    affineConeChart_mem_toricZeroSet y hk i r
  calc
    toricRelation r y =
        toricRelation r
          (affineConeChart y hk i + affineConeError y hk i) := by
      rw [affineConeChart_add_error]
    _ =
        toricRelation r (affineConeChart y hk i) +
          toricRelationDifferential r
            (affineConeChart y hk i) (affineConeError y hk i) +
          toricRelation r (affineConeError y hk i) :=
      toricRelation_add r _ _
    _ =
        toricRelationDifferential r
            (affineConeChart y hk i) (affineConeError y hk i) +
          toricRelation r (affineConeError y hk i) := by
      rw [hzero, zero_add]

/-- Normalized form of the preceding expansion.  If the chart error is
`ρ • v`, then each relation divided by `ρ` is its linear part plus
`ρ` times the quadratic remainder. -/
theorem toricRelation_div_eq_differential_add
    (r : ToricRelationIndex n k)
    (y : MultiIndex n k → ℝ) (hk : 1 ≤ k) (i : Fin n)
    (ρ : ℝ) (v : MultiIndex n k → ℝ)
    (hρ : ρ ≠ 0)
    (herr : affineConeError y hk i = ρ • v) :
    toricRelation r y / ρ =
      toricRelationDifferential r (affineConeChart y hk i) v +
        ρ * toricRelation r v := by
  rw [toricRelation_eq_differential_chart_add_error r y hk i,
    herr,
    toricRelationDifferential_smul_right
      r (affineConeChart y hk i) v ρ,
    toricRelation_smul r ρ v]
  field_simp

/-- The chart-gauged kernel of the complete relation differential is
trivial.

Suppose `h` vanishes in the pure/adjacent affine coordinates and
annihilates every balanced-relation differential at `p`.  Induct on the
number of exponent tokens outside the base coordinate.  A one-token
transfer relation expresses the current coordinate in terms of a
coordinate one step closer to the base.  All other differential terms
are chart coordinates and therefore vanish.  Since the pure coordinate
of `p` is nonzero, the current coordinate of `h` must vanish too.

Notice that `p` itself need not satisfy the toric relations.  This
stronger formulation is both simpler and more reusable. -/
theorem eq_zero_of_toricRelationDifferential_eq_zero_of_edge_eq_zero
    (hk : 1 ≤ k)
    (p h : MultiIndex n k → ℝ)
    (i : Fin n)
    (hpure : p (pureMultiIndex i) ≠ 0)
    (hedge : ∀ j : Fin n, h (edgeMultiIndex hk i j) = 0)
    (hdiff :
      ∀ r : ToricRelationIndex n k,
        toricRelationDifferential r p h = 0) :
    h = 0 := by
  funext a
  generalize hm : k - a.1 i = m
  induction m using Nat.strong_induction_on generalizing a with
  | h m ih =>
      by_cases hai : a.1 i = k
      · have ha : a = pureMultiIndex i :=
          multiIndex_eq_pure_of_apply_eq_degree a i hai
        subst a
        simpa using hedge i
      · have hailt : a.1 i < k :=
          lt_of_le_of_ne (multiIndex_apply_le_degree a i) hai
        obtain ⟨j, hji, hj⟩ :=
          exists_ne_base_apply_pos a i hailt
        let ap :=
          transferMultiIndex a i j hji.symm hj
        have hapi : ap.1 i = a.1 i + 1 := by
          exact transferMultiIndex_apply_same
            a i j hji.symm hj
        have hmeasure : k - ap.1 i < m := by
          rw [hapi, ← hm]
          omega
        have hIH : h ap = 0 :=
          ih (k - ap.1 i) hmeasure ap rfl
        have hrelation :=
          hdiff (baseTransferRelation a hk i j hji hj)
        have hbase : h (pureMultiIndex i) = 0 := by
          simpa using hedge i
        have hjedge : h (edgeMultiIndex hk i j) = 0 :=
          hedge j
        simp only [toricRelationDifferential,
          baseTransferRelation] at hrelation
        rw [hbase, hIH, hjedge] at hrelation
        simp only [mul_zero, zero_mul, add_zero,
          sub_zero] at hrelation
        exact (mul_eq_zero.mp hrelation).resolve_right hpure

end

end HGAS.Veronese
