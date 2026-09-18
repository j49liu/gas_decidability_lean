import HGAS.Algebra.FiniteEuclidean
import Mathlib.Tactic

/-!
# Algebra behind the product-sphere wrapper

The product-sphere wrapper has two independent pieces.

First, a source velocity `p` in one coordinate block is projected to

```
T(v,p) = ‖v‖² p - (v·p)v.
```

This is polynomial and tangent to every sphere centered at the origin.

Second, on a sphere whose total squared radius is `L`, the block squared
radii `sᵢ` obey

```
ṡᵢ = 2 sᵢ (1 - sᵢ - f̄),
f̄ = L⁻¹ ∑ⱼ sⱼ(1-sⱼ).
```

The weighted deviations sum to zero, so total radius is preserved.  The
Lyapunov function `Φ(s)=∑(sᵢ-sᵢ²/2)` has derivative
`2∑sᵢ(1-sᵢ-f̄)²`.  We prove these identities in a form independent of
ODE infrastructure.  This is the exact algebraic core of equations
(12.7)--(12.10) in the paper.
-/

namespace HGAS

open scoped BigOperators

noncomputable section

variable {n blocks : ℕ}

/-- Division-free projection of `p` to the sphere through `v`. -/
def blockTangent (v p : FinVector n ℝ) : FinVector n ℝ :=
  fun i ↦ normSq v * p i - dot v p * v i

/-- The projected field is tangent to every centered sphere. -/
theorem dot_blockTangent (v p : FinVector n ℝ) :
    dot v (blockTangent v p) = 0 := by
  simp only [dot, blockTangent, normSq]
  rw [Finset.sum_congr rfl (fun i _ ↦ by
    change v i *
        ((∑ j, v j * v j) * p i - (∑ j, v j * p j) * v i) =
      (∑ j, v j * v j) * (v i * p i) -
        (∑ j, v j * p j) * (v i * v i)
    ring)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- The common radial correction in the wrapper. -/
def radiusAverage (L : ℝ) (s : FinVector blocks ℝ) : ℝ :=
  (∑ i, s i * (1 - s i)) / L

/-- Deviation of block `i` from its corrected target radius. -/
def radiusDeviation (L : ℝ) (s : FinVector blocks ℝ) (i : Fin blocks) : ℝ :=
  1 - s i - radiusAverage L s

/-- Right-hand side of the squared-radius system. -/
def radiusRhs (L : ℝ) (s : FinVector blocks ℝ) :
    FinVector blocks ℝ :=
  fun i ↦ 2 * s i * radiusDeviation L s i

/-- The nonnegative expression appearing as `Φ̇`. -/
def radiusDissipation (L : ℝ) (s : FinVector blocks ℝ) : ℝ :=
  2 * ∑ i, s i * (radiusDeviation L s i) ^ 2

/-- On the total-radius hyperplane, the weighted radial deviations cancel. -/
theorem weighted_radiusDeviation_sum_zero
    (L : ℝ) (s : FinVector blocks ℝ) (hL : L ≠ 0)
    (hsum : ∑ i, s i = L) :
    ∑ i, s i * radiusDeviation L s i = 0 := by
  simp only [radiusDeviation]
  rw [Finset.sum_congr rfl (fun i _ ↦ by
    change s i * (1 - s i - radiusAverage L s) =
      s i * (1 - s i) - radiusAverage L s * s i
    ring)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsum]
  simp only [radiusAverage]
  field_simp
  ring

/-- The cleanup preserves the total squared radius. -/
theorem sum_radiusRhs_eq_zero
    (L : ℝ) (s : FinVector blocks ℝ) (hL : L ≠ 0)
    (hsum : ∑ i, s i = L) :
    ∑ i, radiusRhs L s i = 0 := by
  simp only [radiusRhs]
  rw [Finset.sum_congr rfl (fun i _ ↦ by
    change 2 * s i * radiusDeviation L s i =
      2 * (s i * radiusDeviation L s i)
    ring)]
  rw [← Finset.mul_sum, weighted_radiusDeviation_sum_zero L s hL hsum]
  ring

/-- Algebraic chain-rule expression for the derivative of
`Φ(s)=∑ᵢ(sᵢ-sᵢ²/2)`. -/
def radiusPhiDerivative (L : ℝ) (s : FinVector blocks ℝ) : ℝ :=
  ∑ i, (1 - s i) * radiusRhs L s i

/-- The wrapper's key Lyapunov identity. -/
theorem radiusPhiDerivative_eq_dissipation
    (L : ℝ) (s : FinVector blocks ℝ) (hL : L ≠ 0)
    (hsum : ∑ i, s i = L) :
    radiusPhiDerivative L s = radiusDissipation L s := by
  have hdev := weighted_radiusDeviation_sum_zero L s hL hsum
  simp only [radiusPhiDerivative, radiusRhs, radiusDissipation]
  rw [Finset.sum_congr rfl (fun i _ ↦ by
    change (1 - s i) * (2 * s i * radiusDeviation L s i) =
      2 * (s i * (radiusDeviation L s i) ^ 2) +
        2 * radiusAverage L s * (s i * radiusDeviation L s i)
    simp only [radiusDeviation]
    ring)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hdev]
  ring

/-- Squared radii make the Lyapunov derivative nonnegative. -/
theorem radiusDissipation_nonneg
    (L : ℝ) (s : FinVector blocks ℝ)
    (hs : ∀ i, 0 ≤ s i) :
    0 ≤ radiusDissipation L s := by
  simp only [radiusDissipation]
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg
    (fun i _ ↦ mul_nonneg (hs i) (sq_nonneg _))

/-- Equality in the Lyapunov identity forces each block either to vanish or
to have zero corrected deviation.  This is the local form of the recurrent
face classification (12.11). -/
theorem radiusDissipation_eq_zero_coordinate
    (L : ℝ) (s : FinVector blocks ℝ)
    (hs : ∀ i, 0 ≤ s i)
    (hzero : radiusDissipation L s = 0)
    (i : Fin blocks) :
    s i = 0 ∨ radiusDeviation L s i = 0 := by
  have hsum :
      ∑ j, s j * (radiusDeviation L s j) ^ 2 = 0 := by
    simp only [radiusDissipation] at hzero
    linarith
  have hterm :
      s i * (radiusDeviation L s i) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ ↦ mul_nonneg (hs j) (sq_nonneg _))).mp hsum i
      (Finset.mem_univ i)
  rcases mul_eq_zero.mp hterm with hi | hi
  · exact Or.inl hi
  · exact Or.inr (sq_eq_zero_iff.mp hi)

/-- All nonzero equilibrium radii have the same value. -/
theorem positive_radii_equal_of_zero_dissipation
    (L : ℝ) (s : FinVector blocks ℝ)
    (hs : ∀ i, 0 ≤ s i)
    (hzero : radiusDissipation L s = 0)
    {i j : Fin blocks} (hi : s i ≠ 0) (hj : s j ≠ 0) :
    s i = s j := by
  have hi' :=
    (radiusDissipation_eq_zero_coordinate L s hs hzero i).resolve_left hi
  have hj' :=
    (radiusDissipation_eq_zero_coordinate L s hs hzero j).resolve_left hj
  simp only [radiusDeviation] at hi' hj'
  linarith

/-- The support of a radius vector, used to state the complete face
classification without choosing an ordering of the nonzero blocks. -/
def radiusSupport (s : FinVector blocks ℝ) : Finset (Fin blocks) :=
  Finset.univ.filter (fun i ↦ s i ≠ 0)

/-- Exact equilibrium-face formula.  If the total radius is the nonzero
number `L` and the dissipation vanishes, then every block is either absent
or has squared radius `L / |support(s)|`.  This is equation (12.11) of the
paper, including the assertion that the support cannot be empty. -/
theorem radius_eq_zero_or_eq_card_quotient
    (L : ℝ) (s : FinVector blocks ℝ)
    (hL : L ≠ 0) (hsum : ∑ i, s i = L)
    (hs : ∀ i, 0 ≤ s i)
    (hzero : radiusDissipation L s = 0)
    (i : Fin blocks) :
    s i = 0 ∨ s i = L / (radiusSupport s).card := by
  classical
  let I := radiusSupport s
  have hsupport_sum : (∑ j ∈ I, s j) = ∑ j, s j := by
    apply Finset.sum_subset (Finset.subset_univ I)
    intro j _ hj
    have hj' : j ∉ radiusSupport s := by simpa [I] using hj
    simpa [radiusSupport] using hj'
  have hI : I.Nonempty := by
    by_contra hempty
    have hIempty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    have hzero_sum : ∑ j, s j = 0 := by
      rw [← hsupport_sum, hIempty]
      simp
    have : L = 0 := by linarith [hsum]
    exact hL this
  by_cases hi : s i = 0
  · exact Or.inl hi
  · right
    have hsame : ∀ j ∈ I, s j = s i := by
      intro j hj
      have hjne : s j ≠ 0 := by
        simpa [I, radiusSupport] using hj
      exact positive_radii_equal_of_zero_dissipation L s hs hzero hjne hi
    have hcard_mul : ((I.card : ℕ) : ℝ) * s i = L := by
      calc
        ((I.card : ℕ) : ℝ) * s i = ∑ _j ∈ I, s i := by simp
        _ = ∑ j ∈ I, s j := by
          apply Finset.sum_congr rfl
          intro j hj
          exact (hsame j hj).symm
        _ = ∑ j, s j := hsupport_sum
        _ = L := hsum
    have hcard_ne : ((I.card : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr hI)
    change s i = L / ((I.card : ℕ) : ℝ)
    field_simp
    nlinarith

end

end HGAS
