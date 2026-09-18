import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# A concrete topological model for finite complex projective data

For a nonzero finite complex vector `v`, its normalized Hermitian
rank-one matrix

```
             G(v)ᵢⱼ = vᵢ conj(vⱼ) / ∑ₖ |vₖ|²
```

is unchanged when `v` is multiplied by a nonzero complex scalar.  This
gives a convenient, entirely elementary way to carry projective data
in an ordinary Hausdorff finite-dimensional space.

The construction below is independent of theta functions.  It records
nonvanishing of the normalizing denominator, scalar invariance, joint
continuity for continuously varying vectors, and recovery of affine
coordinates from the chart whose zeroth coordinate is one.
-/

namespace HGAS.Topology

open Complex Finset
open scoped BigOperators ComplexConjugate

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Sum of squared complex norms of a finite vector. -/
def complexProjectiveGramNormSq
    (v : ι → ℂ) : ℝ :=
  ∑ i, Complex.normSq (v i)

/-- Normalized rank-one Hermitian matrix of a finite complex vector. -/
def complexProjectiveGram
    (v : ι → ℂ) : ι → ι → ℂ :=
  fun i j =>
    v i * conj (v j) /
      (complexProjectiveGramNormSq v : ℂ)

theorem complexProjectiveGramNormSq_pos
    {v : ι → ℂ} (hv : v ≠ 0) :
    0 < complexProjectiveGramNormSq v := by
  have hexists : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hexists
  exact
    Finset.sum_pos'
      (fun j _ => Complex.normSq_nonneg (v j))
      ⟨i, Finset.mem_univ i,
        Complex.normSq_pos.mpr hi⟩

theorem complexProjectiveGramNormSq_ne_zero
    {v : ι → ℂ} (hv : v ≠ 0) :
    complexProjectiveGramNormSq v ≠ 0 :=
  ne_of_gt (complexProjectiveGramNormSq_pos hv)

theorem complexProjectiveGramNormSq_smul
    (c : ℂ) (v : ι → ℂ) :
    complexProjectiveGramNormSq
        (c • v) =
      Complex.normSq c *
        complexProjectiveGramNormSq v := by
  simp only [complexProjectiveGramNormSq,
    Pi.smul_apply, smul_eq_mul, Complex.normSq_mul,
    Finset.mul_sum]

/-- The normalized Gram matrix is invariant under every nonzero scalar. -/
theorem complexProjectiveGram_smul
    (c : ℂ) (v : ι → ℂ) (hc : c ≠ 0) :
    complexProjectiveGram (c • v) =
      complexProjectiveGram v := by
  funext i j
  have hnorm :
      Complex.normSq c ≠ 0 :=
    (Complex.normSq_pos.mpr hc).ne'
  unfold complexProjectiveGram
  rw [complexProjectiveGramNormSq_smul]
  simp only [Pi.smul_apply, smul_eq_mul,
    map_mul]
  calc
    c * v i * (conj c * conj (v j)) /
          (↑(Complex.normSq c *
            complexProjectiveGramNormSq v) : ℂ) =
        (Complex.normSq c : ℂ) *
              (v i * conj (v j)) /
            ((Complex.normSq c : ℂ) *
              (complexProjectiveGramNormSq v : ℂ)) := by
      rw [← Complex.ofReal_mul]
      congr 1
      rw [← Complex.mul_conj c]
      ring
    _ =
        v i * conj (v j) /
          (complexProjectiveGramNormSq v : ℂ) :=
      mul_div_mul_left
        (v i * conj (v j))
        (complexProjectiveGramNormSq v : ℂ)
        (Complex.ofReal_ne_zero.mpr hnorm)

/-- Continuity of the Gram matrix for a continuously varying nonzero
finite vector. -/
theorem continuous_complexProjectiveGram
    {X : Type*} [TopologicalSpace X]
    (v : X → ι → ℂ)
    (hv : ∀ i, Continuous (fun x => v x i))
    (hne : ∀ x, v x ≠ 0) :
    Continuous
      (fun x => complexProjectiveGram (v x)) := by
  have hden :
      Continuous
        (fun x =>
          complexProjectiveGramNormSq (v x)) := by
    unfold complexProjectiveGramNormSq
    exact
      continuous_finsetSum _ fun i _ =>
        Complex.continuous_normSq.comp (hv i)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact
    ((hv i).mul
      (continuous_conj.comp (hv j))).div
      (Complex.continuous_ofReal.comp hden)
      (fun x =>
        Complex.ofReal_ne_zero.mpr
          (complexProjectiveGramNormSq_ne_zero
            (hne x)))

/-- In the affine chart `v₀=1`, the zeroth Gram entry is nonzero. -/
theorem complexProjectiveGram_apply_self_ne_zero
    (v : ι → ℂ) (i : ι)
    (hi : v i ≠ 0) :
    complexProjectiveGram v i i ≠ 0 := by
  have hv : v ≠ 0 := by
    intro hz
    exact hi (congrFun hz i)
  unfold complexProjectiveGram
  exact
    div_ne_zero
      (mul_ne_zero hi
        ((map_ne_zero (starRingEnd ℂ)).mpr hi))
      (Complex.ofReal_ne_zero.mpr
        (complexProjectiveGramNormSq_ne_zero hv))

/-- Recover an affine coordinate by dividing one Gram column by its
nonzero diagonal entry. -/
theorem complexProjectiveGram_div_diagonal
    (v : ι → ℂ) (i j : ι)
    (hi : v i ≠ 0) :
    complexProjectiveGram v j i /
        complexProjectiveGram v i i =
      v j / v i := by
  have hv : v ≠ 0 := by
    intro hz
    exact hi (congrFun hz i)
  have hden :
      (complexProjectiveGramNormSq v : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (complexProjectiveGramNormSq_ne_zero hv)
  unfold complexProjectiveGram
  field_simp [hi,
    (map_ne_zero (starRingEnd ℂ)).mpr hi, hden]

/-- Equality of normalized Gram matrices determines vectors in the
same affine chart. -/
theorem complexProjectiveGram_affine_injective
    {v w : ι → ℂ} (i : ι)
    (hvi : v i = 1) (hwi : w i = 1)
    (h : complexProjectiveGram v =
      complexProjectiveGram w) :
    v = w := by
  funext j
  have hvi_ne : v i ≠ 0 := by
    rw [hvi]
    exact one_ne_zero
  have hwi_ne : w i ≠ 0 := by
    rw [hwi]
    exact one_ne_zero
  calc
    v j =
        complexProjectiveGram v j i /
          complexProjectiveGram v i i := by
      rw [complexProjectiveGram_div_diagonal
        v i j hvi_ne, hvi, div_one]
    _ =
        complexProjectiveGram w j i /
          complexProjectiveGram w i i := by
      rw [h]
    _ = w j := by
      rw [complexProjectiveGram_div_diagonal
        w i j hwi_ne, hwi, div_one]

end

end HGAS.Topology
