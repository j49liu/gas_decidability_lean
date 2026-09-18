import HGAS.Analysis.TensorBernsteinPolynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

/-!
# Coordinate derivatives of tensor Bernstein polynomials

This file develops the exact derivative identities needed for `C¹`
convergence.  The first lemma is deliberately general: differentiating a
univariate polynomial embedded in coordinate `j` gives its ordinary
derivative in coordinate `j` and zero in all other coordinates.
-/

namespace HGAS

open Filter ContinuousMap
open scoped BigOperators Polynomial Topology

noncomputable section

variable {n : ℕ}

/-- Evaluation of a coordinate partial derivative commutes with the
canonical embedding of a univariate polynomial. -/
theorem eval_pderiv_toMvPolynomial
    (q : ℝ[X]) (i j : Fin n) (x : Fin n → ℝ) :
    MvPolynomial.eval x
        (MvPolynomial.pderiv i (q.toMvPolynomial j)) =
      if i = j then q.derivative.eval (x j) else 0 := by
  classical
  let γ : ℝ → (Fin n → ℝ) :=
    Function.update x i
  have hγ :
      HasDerivAt γ (Pi.single i (1 : ℝ)) (x i) :=
    hasDerivAt_update x i (x i)
  have hp :=
    HGAS.HasDerivAt.mvPolynomial_eval hγ (q.toMvPolynomial j)
  have hγ_at : γ (x i) = x := by
    simpa only [γ] using Function.update_eq_self i x
  have hp' :
      HasDerivAt
        (fun t : ℝ ↦ q.eval (γ t j))
        (MvPolynomial.eval x
          (MvPolynomial.pderiv i (q.toMvPolynomial j))) (x i) := by
    simpa only [MvPolynomial.eval_toMvPolynomial, hγ_at,
      Finset.mul_sum, Finset.sum_ite_irrel, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] using hp
  by_cases hij : i = j
  · subst j
    have hfun :
        (fun t : ℝ ↦ q.eval (γ t i)) =
          (fun t : ℝ ↦ q.eval t) := by
      funext t
      simp [γ]
    rw [if_pos rfl]
    rw [hfun] at hp'
    exact hp'.unique
      (_root_.Polynomial.hasDerivAt q (x i))
  · have hfun :
        (fun t : ℝ ↦ q.eval (γ t j)) =
          (fun _t : ℝ ↦ q.eval (x j)) := by
      funext t
      simp [γ, Ne.symm hij]
    rw [if_neg hij]
    rw [hfun] at hp'
    exact hp'.unique (hasDerivAt_const (x i) (q.eval (x j)))

/-- Exact product-rule formula for a coordinate derivative of one tensor
Bernstein basis polynomial. -/
theorem eval_pderiv_tensorBernsteinBasis
    (m : ℕ) (k : Fin n → Fin (m + 1))
    (i : Fin n) (x : Fin n → ℝ) :
    MvPolynomial.eval x
        (MvPolynomial.pderiv i (tensorBernsteinBasis m k)) =
      (_root_.bernsteinPolynomial ℝ m (k i)).derivative.eval (x i) *
        ∏ j ∈ Finset.univ.erase i,
          (_root_.bernsteinPolynomial ℝ m (k j)).eval (x j) := by
  classical
  let q : Fin n → ℝ[X] :=
    fun j ↦ _root_.bernsteinPolynomial ℝ m (k j)
  let γ : ℝ → (Fin n → ℝ) :=
    Function.update x i
  have hγ :
      HasDerivAt γ (Pi.single i (1 : ℝ)) (x i) :=
    hasDerivAt_update x i (x i)
  have hγ_at : γ (x i) = x := by
    simpa only [γ] using Function.update_eq_self i x
  have hp :=
    HGAS.HasDerivAt.mvPolynomial_eval hγ
      (tensorBernsteinBasis m k)
  have hp' :
      HasDerivAt
        (fun t : ℝ ↦ ∏ j : Fin n, (q j).eval (γ t j))
        (MvPolynomial.eval x
          (MvPolynomial.pderiv i (tensorBernsteinBasis m k)))
          (x i) := by
    simpa only [tensorBernsteinBasis,
      coordinateBernsteinPolynomial,
      MvPolynomial.eval_prod,
      MvPolynomial.eval_toMvPolynomial, q, hγ_at,
      Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] using hp
  have hfactor :
      ∀ j ∈ (Finset.univ : Finset (Fin n)),
        HasDerivAt (fun t : ℝ ↦ (q j).eval (γ t j))
          (if i = j then (q j).derivative.eval (x j) else 0)
          (x i) := by
    intro j hj
    by_cases hij : i = j
    · subst j
      have hsame :
          (fun t : ℝ ↦ (q i).eval (γ t i)) =
            (fun t : ℝ ↦ (q i).eval t) := by
        funext t
        simp [γ]
      rw [hsame, if_pos rfl]
      exact _root_.Polynomial.hasDerivAt (q i) (x i)
    · have hconst :
          (fun t : ℝ ↦ (q j).eval (γ t j)) =
            (fun _t : ℝ ↦ (q j).eval (x j)) := by
        funext t
        simp [γ, Ne.symm hij]
      rw [if_neg hij, hconst]
      exact hasDerivAt_const (x i) ((q j).eval (x j))
  have hprod :=
    _root_.HasDerivAt.fun_finsetProd hfactor
  simp only [hγ_at, smul_eq_mul] at hprod
  have hsum :
      (∑ j ∈ (Finset.univ : Finset (Fin n)),
        (∏ l ∈ Finset.univ.erase j, (q l).eval (x l)) *
          if i = j then (q j).derivative.eval (x j) else 0) =
        (q i).derivative.eval (x i) *
          ∏ j ∈ Finset.univ.erase i, (q j).eval (x j) := by
    rw [Finset.sum_eq_single i]
    · simp only [if_true]
      rw [mul_comm]
    · intro j hj hji
      have hij : i ≠ j := Ne.symm hji
      simp [hij]
    · simp
  have hprod' :
      HasDerivAt
        (fun t : ℝ ↦ ∏ j : Fin n, (q j).eval (γ t j))
        ((q i).derivative.eval (x i) *
          ∏ j ∈ Finset.univ.erase i, (q j).eval (x j))
        (x i) := by
    rw [hsum] at hprod
    exact hprod
  have heq := hp'.unique hprod'
  simpa only [q] using heq

/-- Exact partial-derivative formula before the one-dimensional Bernstein
summation-by-parts step. -/
theorem eval_pderiv_tensorBernsteinPolynomial
    (m : ℕ) (f : (Fin n → ℝ) → ℝ)
    (i : Fin n) (x : Fin n → ℝ) :
    MvPolynomial.eval x
        (MvPolynomial.pderiv i
          (tensorBernsteinPolynomial m f)) =
      ∑ k : Fin n → Fin (m + 1),
        f (tensorBernsteinGrid m k) *
          (_root_.bernsteinPolynomial ℝ m
            (k i)).derivative.eval (x i) *
          ∏ j ∈ Finset.univ.erase i,
            (_root_.bernsteinPolynomial ℝ m (k j)).eval (x j) := by
  classical
  simp only [tensorBernsteinPolynomial, map_sum,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C,
    zero_mul, zero_add,
    MvPolynomial.eval_mul, MvPolynomial.eval_C,
    eval_pderiv_tensorBernsteinBasis]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-! ## Univariate summation by parts -/

/-- A polynomial written in the Bernstein basis with coefficient vector
`a`. -/
def bernsteinCombination
    (N : ℕ) (a : Fin (N + 1) → ℝ) : ℝ[X] :=
  ∑ ν : Fin (N + 1),
    _root_.Polynomial.C (a ν) *
      _root_.bernsteinPolynomial ℝ N ν

theorem eval_bernsteinCombination
    (N : ℕ) (a : Fin (N + 1) → ℝ)
    (x : Set.Icc (0 : ℝ) 1) :
    (bernsteinCombination N a).eval (x : ℝ) =
      ∑ k : Fin (N + 1), a k * _root_.bernstein N k x := by
  rw [bernsteinCombination,
    _root_.Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [_root_.Polynomial.eval_mul,
    _root_.Polynomial.eval_C, _root_.bernstein]
  rfl

/-- Endpoint bookkeeping for the summation-by-parts identity: shifting all
Bernstein indices up by one loses the zero-index term and creates only a
vanishing out-of-range term at the other endpoint. -/
theorem sum_succ_bernstein_eq_sum_castSucc
    (n : ℕ) (a : Fin (n + 2) → ℝ) :
    _root_.Polynomial.C (a 0) *
          _root_.bernsteinPolynomial ℝ n 0 +
        ∑ x : Fin (n + 1),
          _root_.Polynomial.C (a x.succ) *
            _root_.bernsteinPolynomial ℝ n (x + 1) =
      ∑ x : Fin (n + 1),
        _root_.Polynomial.C (a x.castSucc) *
          _root_.bernsteinPolynomial ℝ n x := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  have hlast :
      _root_.bernsteinPolynomial ℝ n
          ((Fin.last n : ℕ) + 1) = 0 :=
    _root_.bernsteinPolynomial.eq_zero_of_lt
      (R := ℝ) (by simp only [Fin.val_last]; omega)
  rw [hlast, mul_zero, add_zero]
  congr 1

/-- Differentiating a Bernstein combination replaces its coefficients by
scaled forward differences and lowers the degree by one. -/
theorem derivative_bernsteinCombination_succ
    (n : ℕ) (a : Fin (n + 2) → ℝ) :
    (bernsteinCombination (n + 1) a).derivative =
      _root_.Polynomial.C (n + 1 : ℝ) *
        bernsteinCombination n
          (fun k : Fin (n + 1) ↦
            a k.succ - a k.castSucc) := by
  classical
  rw [bernsteinCombination, map_sum, Fin.sum_univ_succ]
  simp only [_root_.Polynomial.derivative_mul,
    _root_.Polynomial.derivative_C, zero_mul, zero_add]
  simp only [Fin.val_zero, Fin.val_succ]
  rw [_root_.bernsteinPolynomial.derivative_zero]
  simp_rw [_root_.bernsteinPolynomial.derivative_succ_aux]
  have hnsub : n + 1 - 1 = n := by omega
  rw [hnsub]
  simp only [← _root_.Polynomial.C_eq_natCast]
  rw [bernsteinCombination]
  simp only [map_sub]
  let B : ℕ → ℝ[X] :=
    fun k ↦ _root_.bernsteinPolynomial ℝ n k
  have hshift :
      _root_.Polynomial.C (a 0) * B 0 +
          ∑ x : Fin (n + 1),
            _root_.Polynomial.C (a x.succ) * B (x + 1) =
        ∑ x : Fin (n + 1),
          _root_.Polynomial.C (a x.castSucc) * B x := by
    simpa only [B] using
      sum_succ_bernstein_eq_sum_castSucc n a
  have hinterior :
      -(_root_.Polynomial.C (a 0) * B 0) +
          ∑ x : Fin (n + 1),
            _root_.Polynomial.C (a x.succ) *
              (B x - B (x + 1)) =
        ∑ x : Fin (n + 1),
          (_root_.Polynomial.C (a x.succ) -
            _root_.Polynomial.C (a x.castSucc)) * B x := by
    calc
      -(_root_.Polynomial.C (a 0) * B 0) +
            ∑ x : Fin (n + 1),
              _root_.Polynomial.C (a x.succ) *
                (B x - B (x + 1)) =
          (∑ x : Fin (n + 1),
              _root_.Polynomial.C (a x.succ) * B x) -
            (_root_.Polynomial.C (a 0) * B 0 +
              ∑ x : Fin (n + 1),
                _root_.Polynomial.C (a x.succ) *
                  B (x + 1)) := by
        simp_rw [mul_sub, Finset.sum_sub_distrib]
        ring
      _ = (∑ x : Fin (n + 1),
              _root_.Polynomial.C (a x.succ) * B x) -
            ∑ x : Fin (n + 1),
              _root_.Polynomial.C (a x.castSucc) * B x := by
        rw [hshift]
      _ = ∑ x : Fin (n + 1),
          (_root_.Polynomial.C (a x.succ) -
            _root_.Polynomial.C (a x.castSucc)) * B x := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        ring
  have hC :
      _root_.Polynomial.C (n + 1 : ℝ) =
        _root_.Polynomial.C (n : ℝ) + 1 := by
    rw [map_add, map_one]
  have hCnat :
      _root_.Polynomial.C ((n + 1 : ℕ) : ℝ) =
        _root_.Polynomial.C (n : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one, map_add, map_one]
  rw [hC, hCnat]
  calc
    _ = (_root_.Polynomial.C (n : ℝ) + 1) *
        (-(_root_.Polynomial.C (a 0) * B 0) +
          ∑ x : Fin (n + 1),
            _root_.Polynomial.C (a x.succ) *
              (B x - B (x + 1))) := by
      rw [mul_add, Finset.mul_sum]
      apply congrArg₂ (· + ·)
      · ring
      · apply Finset.sum_congr rfl
        intro x hx
        ring
    _ = (_root_.Polynomial.C (n : ℝ) + 1) *
        ∑ x : Fin (n + 1),
          (_root_.Polynomial.C (a x.succ) -
            _root_.Polynomial.C (a x.castSucc)) * B x := by
      rw [hinterior]
    _ = _ := by
      apply congrArg
      apply Finset.sum_congr rfl
      intro x hx
      simp only [B]

/-- Pointwise forward-difference form of the previous polynomial
identity. -/
theorem eval_derivative_bernsteinCombination_succ
    (n : ℕ) (a : Fin (n + 2) → ℝ)
    (x : Set.Icc (0 : ℝ) 1) :
    (bernsteinCombination (n + 1) a).derivative.eval (x : ℝ) =
      (n + 1 : ℝ) *
        ∑ k : Fin (n + 1),
          (a k.succ - a k.castSucc) *
            _root_.bernstein n k x := by
  rw [derivative_bernsteinCombination_succ,
    _root_.Polynomial.eval_mul,
    _root_.Polynomial.eval_C, bernsteinCombination,
    _root_.Polynomial.eval_finsetSum, Finset.mul_sum]
  simp only [
    _root_.Polynomial.eval_mul,
    _root_.Polynomial.eval_C]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [_root_.bernstein]
  rfl

/-- The degree-`n` Bernstein grid point `k/n` lies in the interval whose
endpoints are the adjacent degree-`n+1` grid points. -/
theorem bernsteinGrid_mem_adjacentInterval
    {n : ℕ} (hn : n ≠ 0) (k : Fin (n + 1)) :
    (k : ℝ) / (n + 1 : ℕ) ≤ (k : ℝ) / n ∧
      (k : ℝ) / n ≤ ((k : ℕ) + 1 : ℕ) / (n + 1 : ℕ) := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hsuccpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  constructor
  · rw [div_le_div_iff₀ hsuccpos hnpos]
    have hk0 : 0 ≤ (k : ℝ) := by positivity
    norm_num [Nat.cast_add, Nat.cast_one]
    nlinarith
  · rw [div_le_div_iff₀ hnpos hsuccpos]
    have hkle : (k : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast k.is_le
    norm_num [Nat.cast_add, Nat.cast_one]
    nlinarith

/-- Quantitative core of derivative convergence: a scaled forward
difference of a `C¹` function is close to the derivative sampled at the
degree-`n` Bernstein grid point, provided the mesh is below a modulus of
continuity for the derivative. -/
theorem bernsteinForwardDifference_near_derivative
    (f g : ℝ → ℝ)
    (hf :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt f (g t) t)
    {δ ε : ℝ}
    (hmodulus :
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        ∀ v ∈ Set.Icc (0 : ℝ) 1,
          |u - v| < δ → |g u - g v| < ε)
    {n : ℕ} (hn : n ≠ 0)
    (hmesh : 1 / ((n + 1 : ℕ) : ℝ) < δ)
    (k : Fin (n + 1)) :
    |((n + 1 : ℕ) : ℝ) *
          (f ((k.succ : ℝ) /
              ((n + 1 : ℕ) : ℝ)) -
            f ((k.castSucc : ℝ) /
              ((n + 1 : ℕ) : ℝ))) -
        g ((k : ℕ) / (n : ℝ))| < ε := by
  let a : Set.Icc (0 : ℝ) 1 :=
    _root_.bernstein.z k.castSucc
  let b : Set.Icc (0 : ℝ) 1 :=
    _root_.bernstein.z k.succ
  let z : Set.Icc (0 : ℝ) 1 :=
    _root_.bernstein.z k
  have ha :
      (a : ℝ) =
        (k.castSucc : ℝ) /
          ((n + 1 : ℕ) : ℝ) := by
    rfl
  have hb :
      (b : ℝ) =
        (k.succ : ℝ) /
          ((n + 1 : ℕ) : ℝ) := by
    rfl
  have hz :
      (z : ℝ) = (k : ℕ) / (n : ℝ) := by
    rfl
  have hab : (a : ℝ) < b := by
    rw [ha, hb, div_lt_div_iff₀]
    · norm_num [Nat.cast_add, Nat.cast_one]
      have hpositive : 0 < (n : ℝ) + 1 := by positivity
      nlinarith
    · positivity
    · positivity
  have hsub :
      Set.Icc (a : ℝ) b ⊆ Set.Icc (0 : ℝ) 1 := by
    intro t ht
    exact ⟨(a.property.1.trans ht.1),
      ht.2.trans b.property.2⟩
  have hcont :
      ContinuousOn f (Set.Icc (a : ℝ) b) := by
    intro t ht
    exact (hf t (hsub ht)).continuousAt.continuousWithinAt
  have hderiv :
      ∀ t ∈ Set.Ioo (a : ℝ) b,
        HasDerivAt f (g t) t := by
    intro t ht
    exact hf t (hsub ⟨ht.1.le, ht.2.le⟩)
  obtain ⟨c, hc, hcSlope⟩ :=
    exists_hasDerivAt_eq_slope
      (f := f) (f' := g) hab hcont hderiv
  have hba :
      (b : ℝ) - a = 1 / ((n + 1 : ℕ) : ℝ) := by
    rw [ha, hb]
    simp only [Fin.val_succ, Fin.val_castSucc]
    have hN :
        (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp
    norm_num [Nat.cast_add, Nat.cast_one]
  have hforward :
      ((n + 1 : ℕ) : ℝ) *
          (f b - f a) = g c := by
    rw [hcSlope, hba]
    have hN :
        (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp
  have hz_interval :
      (a : ℝ) ≤ z ∧ (z : ℝ) ≤ b := by
    simpa only [ha, hb, hz, Fin.val_castSucc,
      Fin.val_succ] using
        bernsteinGrid_mem_adjacentInterval hn k
  have hcz :
      |c - (z : ℝ)| < 1 / ((n + 1 : ℕ) : ℝ) := by
    rw [← hba, abs_lt]
    constructor <;> linarith [hc.1, hc.2,
      hz_interval.1, hz_interval.2]
  have hclose : |c - (z : ℝ)| < δ :=
    hcz.trans hmesh
  have hcunit : c ∈ Set.Icc (0 : ℝ) 1 :=
    hsub ⟨hc.1.le, hc.2.le⟩
  have hgclose :=
    hmodulus c hcunit z z.property hclose
  rw [← ha, ← hb, ← hz, hforward]
  exact hgclose

/-- A uniform coefficient bound passes through the positive Bernstein
averaging operator without amplification. -/
theorem abs_bernsteinWeightedDifference_le
    {n : ℕ} (d e : Fin (n + 1) → ℝ)
    (C : ℝ)
    (hde : ∀ k, |d k - e k| ≤ C)
    (x : Set.Icc (0 : ℝ) 1) :
    |(∑ k : Fin (n + 1),
          _root_.bernstein n k x * d k) -
        ∑ k : Fin (n + 1),
          _root_.bernstein n k x * e k| ≤ C := by
  calc
    |(∑ k : Fin (n + 1),
          _root_.bernstein n k x * d k) -
        ∑ k : Fin (n + 1),
          _root_.bernstein n k x * e k| =
        |∑ k : Fin (n + 1),
          _root_.bernstein n k x * (d k - e k)| := by
      rw [← Finset.sum_sub_distrib]
      apply congrArg abs
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ ∑ k : Fin (n + 1),
        |_root_.bernstein n k x * (d k - e k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin (n + 1),
        _root_.bernstein n k x * |d k - e k| := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [abs_mul, abs_of_nonneg _root_.bernstein_nonneg]
    _ ≤ ∑ k : Fin (n + 1),
        _root_.bernstein n k x * C := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left
        (hde k) _root_.bernstein_nonneg
    _ = C := by
      rw [← Finset.sum_mul,
        _root_.bernstein.probability, one_mul]

/-- Full one-dimensional Bernstein `C¹` approximation theorem.

Unlike `exists_polynomial_near_with_derivative`, this theorem proves that
the *Bernstein polynomials themselves* work.  That operator-level fact is
what permits tensorization: derivatives in the untouched coordinates
commute with Bernstein averaging. -/
theorem exists_bernsteinCombination_near_with_derivative
    (f g : ℝ → ℝ)
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1))
    (hf :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt f (g t) t)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, n ≠ 0 ∧
      let p : ℝ[X] :=
        bernsteinCombination (n + 1)
          (fun k : Fin (n + 2) ↦
            f ((k : ℝ) / ((n + 1 : ℕ) : ℝ)))
      (∀ x : Set.Icc (0 : ℝ) 1,
        |p.eval (x : ℝ) - f x| < ε) ∧
      (∀ x : Set.Icc (0 : ℝ) 1,
        |p.derivative.eval (x : ℝ) - g x| < ε) := by
  let fI : C(Set.Icc (0 : ℝ) 1, ℝ) :=
    { toFun := fun x ↦ f x
      continuous_toFun :=
      continuousOn_iff_continuous_restrict.mp
        (fun t ht ↦
          (hf t ht).continuousAt.continuousWithinAt) }
  let gI : C(Set.Icc (0 : ℝ) 1, ℝ) :=
    { toFun := fun x ↦ g x
      continuous_toFun :=
        continuousOn_iff_continuous_restrict.mp hg }
  have hquarter : 0 < ε / 4 := by positivity
  have hhalf : 0 < ε / 2 := by positivity
  have hgUniform : UniformContinuous gI :=
    CompactSpace.uniformContinuous_of_continuous
      (map_continuous gI)
  obtain ⟨δ, hδ, hmodulusI⟩ :=
    Metric.uniformContinuous_iff.mp hgUniform
      (ε / 4) hquarter
  have hmodulus :
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        ∀ v ∈ Set.Icc (0 : ℝ) 1,
          |u - v| < δ → |g u - g v| < ε / 4 := by
    intro u hu v hv huv
    have hdist :
        dist (⟨u, hu⟩ : Set.Icc (0 : ℝ) 1)
            (⟨v, hv⟩ : Set.Icc (0 : ℝ) 1) < δ := by
      simpa only [Subtype.dist_eq, Real.dist_eq] using huv
    have hout := hmodulusI hdist
    simpa only [gI, Real.dist_eq] using hout
  obtain ⟨Nf, hNf⟩ :=
    Metric.tendsto_atTop.mp
      (_root_.bernsteinApproximation_uniform fI)
      (ε / 2) hhalf
  obtain ⟨Ng, hNg⟩ :=
    Metric.tendsto_atTop.mp
      (_root_.bernsteinApproximation_uniform gI)
      (ε / 4) hquarter
  have hmeshTendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          (1 : ℝ) / ((n + 1 : ℕ) : ℝ))
        Filter.atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add,
      Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
        (tendsto_add_atTop_nat 1)
  have hmeshEventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        (1 : ℝ) / ((n + 1 : ℕ) : ℝ) < δ :=
    hmeshTendsto.eventually_lt_const hδ
  have hchoices :
      ∀ᶠ n : ℕ in Filter.atTop,
        Nf ≤ n ∧ Ng ≤ n ∧ n ≠ 0 ∧
          (1 : ℝ) / ((n + 1 : ℕ) : ℝ) < δ := by
    filter_upwards [Filter.eventually_ge_atTop Nf,
      Filter.eventually_ge_atTop Ng,
      Filter.eventually_ne_atTop 0,
      hmeshEventually] with n hnF hnG hn0 hmesh
    exact ⟨hnF, hnG, hn0, hmesh⟩
  obtain ⟨n, hnF, hnG, hn0, hmesh⟩ :=
    hchoices.exists
  let a : Fin (n + 2) → ℝ :=
    fun k ↦ f ((k : ℝ) / ((n + 1 : ℕ) : ℝ))
  let p : ℝ[X] :=
    bernsteinCombination (n + 1) a
  refine ⟨n, hn0, ?_, ?_⟩
  · intro x
    have hfn :=
      hNf (n + 1) (hnF.trans (Nat.le_succ n))
    rw [dist_eq_norm, norm_lt_iff _ hhalf] at hfn
    have hpoint := hfn x
    have hpoint' :
        |_root_.bernsteinApproximation (n + 1) fI x -
          f x| < ε / 2 := by
      simpa only [ContinuousMap.sub_apply, fI,
        Real.norm_eq_abs] using hpoint
    have hpBA :
        p.eval (x : ℝ) =
          _root_.bernsteinApproximation (n + 1) fI x := by
      dsimp only [p]
      rw [eval_bernsteinCombination,
        _root_.bernsteinApproximation.apply]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [a, fI, _root_.bernstein.z,
        smul_eq_mul]
      change
        f ((k : ℝ) / ((n + 1 : ℕ) : ℝ)) *
            _root_.bernstein (n + 1) k x =
          _root_.bernstein (n + 1) k x *
            f ((k : ℝ) / ((n + 1 : ℕ) : ℝ))
      rw [mul_comm]
    rw [hpBA]
    exact hpoint'.trans (half_lt_self hε)
  · intro x
    let d : Fin (n + 1) → ℝ :=
      fun k ↦ ((n + 1 : ℕ) : ℝ) *
        (a k.succ - a k.castSucc)
    let e : Fin (n + 1) → ℝ :=
      fun k ↦ g ((k : ℕ) / (n : ℝ))
    have hcoeff : ∀ k, |d k - e k| ≤ ε / 4 := by
      intro k
      exact (bernsteinForwardDifference_near_derivative
        f g hf hmodulus hn0 hmesh k).le
    have hweighted :=
      abs_bernsteinWeightedDifference_le
        d e (ε / 4) hcoeff x
    have hpEval :
        p.derivative.eval (x : ℝ) =
          ∑ k : Fin (n + 1),
            _root_.bernstein n k x * d k := by
      dsimp only [p]
      rw [eval_derivative_bernsteinCombination_succ]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only [d]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring
    have hgEval :
        _root_.bernsteinApproximation n gI x =
          ∑ k : Fin (n + 1),
            _root_.bernstein n k x * e k := by
      rw [_root_.bernsteinApproximation.apply]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [smul_eq_mul]
      rfl
    rw [← hpEval, ← hgEval] at hweighted
    have hgn := hNg n hnG
    rw [dist_eq_norm, norm_lt_iff _ hquarter] at hgn
    have hgpoint := hgn x
    have htriangle :
        |p.derivative.eval (x : ℝ) - g x| ≤
          |p.derivative.eval (x : ℝ) -
              _root_.bernsteinApproximation n gI x| +
            |_root_.bernsteinApproximation n gI x - g x| := by
      calc
        |p.derivative.eval (x : ℝ) - g x| =
            |(p.derivative.eval (x : ℝ) -
                _root_.bernsteinApproximation n gI x) +
              (_root_.bernsteinApproximation n gI x -
                g x)| := by
          congr 1
          ring
        _ ≤ _ := abs_add_le _ _
    have hgpoint' :
        |_root_.bernsteinApproximation n gI x - g x| <
          ε / 4 := by
      simpa only [gI, Real.norm_eq_abs] using hgpoint
    nlinarith

end

end HGAS
