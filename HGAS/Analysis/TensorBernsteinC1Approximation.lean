import HGAS.Analysis.AnisotropicBernsteinApproximation
import Mathlib.Tactic

/-!
# `C¹` convergence of tensor Bernstein polynomials

This file combines the analytic approximation results with exact
summation by parts in one selected tensor coordinate.  The derivative of
the degree-`m+1` tensor Bernstein polynomial is an average of scaled
forward differences in that coordinate.  The averaging degrees are
`m` in the differentiated coordinate and `m+1` in all other
coordinates.
-/

namespace HGAS

open Filter ContinuousMap
open scoped BigOperators Topology unitInterval Polynomial

noncomputable section

variable {n : ℕ}

/-- Scalar summation by parts, written directly as an identity between
the sum of derivatives of Bernstein basis polynomials and a Bernstein
average of forward differences. -/
theorem sum_mul_eval_derivative_bernsteinPolynomial_succ
    (m : ℕ) (a : Fin (m + 2) → ℝ)
    (x : Set.Icc (0 : ℝ) 1) :
    (∑ k : Fin (m + 2),
        a k *
          (_root_.bernsteinPolynomial ℝ (m + 1) k).derivative.eval
            (x : ℝ)) =
      (m + 1 : ℝ) *
        ∑ q : Fin (m + 1),
          (a q.succ - a q.castSucc) *
            _root_.bernstein m q x := by
  calc
    (∑ k : Fin (m + 2),
        a k *
          (_root_.bernsteinPolynomial ℝ (m + 1) k).derivative.eval
            (x : ℝ)) =
        (bernsteinCombination (m + 1) a).derivative.eval
          (x : ℝ) := by
      rw [bernsteinCombination, map_sum,
        _root_.Polynomial.eval_finsetSum]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [_root_.Polynomial.derivative_mul,
        _root_.Polynomial.derivative_C, zero_mul,
        zero_add, _root_.Polynomial.eval_mul,
        _root_.Polynomial.eval_C]
    _ = _ :=
      eval_derivative_bernsteinCombination_succ m a x

/-- Evaluation of the ordinary tensor polynomial is the isotropic
special case of anisotropic Bernstein averaging. -/
theorem eval_tensorBernsteinPolynomial_eq_anisotropic
    (m : ℕ) (f : (Fin n → ℝ) → ℝ)
    (x : UnitCube n) :
    MvPolynomial.eval (unitCubeRealPoint x)
        (tensorBernsteinPolynomial m f) =
      anisotropicBernsteinValue (fun _ : Fin n ↦ m)
        (fun y ↦ f (unitCubeRealPoint y)) x := by
  rw [eval_tensorBernsteinPolynomial,
    anisotropicBernsteinValue]
  apply Finset.sum_congr rfl
  intro k hk
  have hgrid :
      tensorBernsteinGrid m k =
        unitCubeRealPoint
          (anisotropicBernsteinGrid
            (fun _ : Fin n ↦ m) k) := by
    funext i
    rfl
  rw [hgrid]
  apply congrArg (f _ * ·)
  simp only [tensorBernsteinWeight,
    anisotropicBernsteinWeight,
    _root_.bernstein_apply,
    unitCubeRealPoint_apply]

/-- Indices other than the selected coordinate `i`. -/
abbrev CoordinateComplement (i : Fin n) :=
  {j : Fin n // j ≠ i}

/-- The mixed index set for a tensor derivative: degree `m` in
coordinate `i`, degree `m+1` in every complementary coordinate. -/
abbrev DerivativeBernsteinIndex
    (m : ℕ) (i : Fin n) :=
  Fin (m + 1) ×
    (CoordinateComplement i → Fin (m + 2))

/-- Coordinatewise degree profile underlying a tensor derivative. -/
def derivativeBernsteinDegree
    (m : ℕ) (i : Fin n) (j : Fin n) : ℕ :=
  if j = i then m else m + 1

@[simp]
theorem derivativeBernsteinDegree_same
    (m : ℕ) (i : Fin n) :
    derivativeBernsteinDegree m i i = m := by
  simp [derivativeBernsteinDegree]

@[simp]
theorem derivativeBernsteinDegree_of_ne
    (m : ℕ) (i j : Fin n) (hji : j ≠ i) :
    derivativeBernsteinDegree m i j = m + 1 := by
  simp [derivativeBernsteinDegree, hji]

/-- The dependent anisotropic index type for the mixed derivative
degrees is equivalent to the explicit selected-coordinate product
`DerivativeBernsteinIndex`. -/
def derivativeBernsteinIndexEquiv
    (m : ℕ) (i : Fin n) :
    (∀ j, Fin (derivativeBernsteinDegree m i j + 1)) ≃
      DerivativeBernsteinIndex m i where
  toFun k :=
    (Fin.cast (by simp [derivativeBernsteinDegree]) (k i),
      fun j ↦
        Fin.cast
          (by simp [derivativeBernsteinDegree, j.property])
          (k j))
  invFun q j :=
    if h : j = i then
      Fin.cast
        (by subst j; simp [derivativeBernsteinDegree])
        q.1
    else
      Fin.cast
        (by simp [derivativeBernsteinDegree, h])
        (q.2 ⟨j, h⟩)
  left_inv k := by
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]
  right_inv q := by
    apply Prod.ext
    · simp
    · funext j
      simp [j.property]

@[simp]
theorem derivativeBernsteinIndexEquiv_fst_val
    (m : ℕ) (i : Fin n)
    (k : ∀ j,
      Fin (derivativeBernsteinDegree m i j + 1)) :
    ((derivativeBernsteinIndexEquiv m i k).1 : ℕ) =
      (k i : ℕ) := by
  rfl

@[simp]
theorem derivativeBernsteinIndexEquiv_snd_val
    (m : ℕ) (i : Fin n)
    (k : ∀ j,
      Fin (derivativeBernsteinDegree m i j + 1))
    (j : CoordinateComplement i) :
    ((derivativeBernsteinIndexEquiv m i k).2 j : ℕ) =
      (k j : ℕ) := by
  rfl

@[simp]
theorem derivativeBernsteinIndexEquiv_fst_real
    (m : ℕ) (i : Fin n)
    (k : ∀ j,
      Fin (derivativeBernsteinDegree m i j + 1)) :
    ((derivativeBernsteinIndexEquiv m i k).1 : ℝ) =
      (k i : ℝ) := by
  exact_mod_cast
    derivativeBernsteinIndexEquiv_fst_val m i k

@[simp]
theorem derivativeBernsteinIndexEquiv_snd_real
    (m : ℕ) (i : Fin n)
    (k : ∀ j,
      Fin (derivativeBernsteinDegree m i j + 1))
    (j : CoordinateComplement i) :
    ((derivativeBernsteinIndexEquiv m i k).2 j : ℝ) =
      (k j : ℝ) := by
  exact_mod_cast
    derivativeBernsteinIndexEquiv_snd_val m i k j

/-- Mixed Bernstein grid associated with a tensor derivative. -/
def derivativeBernsteinGrid
    (m : ℕ) (i : Fin n)
    (q : DerivativeBernsteinIndex m i) :
    UnitCube n :=
  fun j ↦
    if h : j = i then
      _root_.bernstein.z q.1
    else
      _root_.bernstein.z (q.2 ⟨j, h⟩)

@[simp]
theorem derivativeBernsteinGrid_apply_same
    (m : ℕ) (i : Fin n)
    (q : DerivativeBernsteinIndex m i) :
    derivativeBernsteinGrid m i q i =
      _root_.bernstein.z q.1 := by
  simp [derivativeBernsteinGrid]

@[simp]
theorem derivativeBernsteinGrid_apply_of_ne
    (m : ℕ) (i j : Fin n) (hji : j ≠ i)
    (q : DerivativeBernsteinIndex m i) :
    derivativeBernsteinGrid m i q j =
      _root_.bernstein.z (q.2 ⟨j, hji⟩) := by
  simp [derivativeBernsteinGrid, hji]

/-- The explicit mixed grid agrees with the anisotropic grid under
`derivativeBernsteinIndexEquiv`. -/
theorem anisotropicBernsteinGrid_derivativeIndexEquiv
    (m : ℕ) (i : Fin n)
    (k : ∀ j,
      Fin (derivativeBernsteinDegree m i j + 1)) :
    anisotropicBernsteinGrid
        (derivativeBernsteinDegree m i) k =
      derivativeBernsteinGrid m i
        (derivativeBernsteinIndexEquiv m i k) := by
  funext j
  by_cases hji : j = i
  · subst j
    rw [derivativeBernsteinGrid_apply_same]
    apply Subtype.ext
    change
      (k i : ℝ) /
          (derivativeBernsteinDegree m i i : ℝ) =
        ((derivativeBernsteinIndexEquiv m i k).1 : ℝ) /
          (m : ℝ)
    calc
      (k i : ℝ) /
          (derivativeBernsteinDegree m i i : ℝ) =
        ((derivativeBernsteinIndexEquiv m i k).1 : ℝ) /
          (derivativeBernsteinDegree m i i : ℝ) :=
        congrArg
          (fun z : ℝ ↦
            z / (derivativeBernsteinDegree m i i : ℝ))
          (derivativeBernsteinIndexEquiv_fst_real
            m i k).symm
      _ = _ := by
        congr 1
        exact_mod_cast derivativeBernsteinDegree_same m i
  · rw [derivativeBernsteinGrid_apply_of_ne
      m i j hji]
    apply Subtype.ext
    change
      (k j : ℝ) /
          (derivativeBernsteinDegree m i j : ℝ) =
        ((derivativeBernsteinIndexEquiv m i k).2
            ⟨j, hji⟩ : ℝ) /
          ((m + 1 : ℕ) : ℝ)
    calc
      (k j : ℝ) /
          (derivativeBernsteinDegree m i j : ℝ) =
        ((derivativeBernsteinIndexEquiv m i k).2
            ⟨j, hji⟩ : ℝ) /
          (derivativeBernsteinDegree m i j : ℝ) :=
        congrArg
          (fun z : ℝ ↦
            z / (derivativeBernsteinDegree m i j : ℝ))
          (derivativeBernsteinIndexEquiv_snd_real
            m i k ⟨j, hji⟩).symm
      _ = _ := by
        congr 1
        exact_mod_cast
          derivativeBernsteinDegree_of_ne m i j hji

/-- Product weight on the mixed derivative grid. -/
def derivativeBernsteinWeight
    (m : ℕ) (i : Fin n)
    (q : DerivativeBernsteinIndex m i)
    (x : UnitCube n) : ℝ :=
  _root_.bernstein m q.1 (x i) *
    ∏ j : CoordinateComplement i,
      _root_.bernstein (m + 1) (q.2 j) (x j)

/-- The explicit mixed weight agrees with the anisotropic weight under
`derivativeBernsteinIndexEquiv`. -/
theorem anisotropicBernsteinWeight_derivativeIndexEquiv
    (m : ℕ) (i : Fin n)
    (k : ∀ j,
      Fin (derivativeBernsteinDegree m i j + 1))
    (x : UnitCube n) :
    anisotropicBernsteinWeight
        (derivativeBernsteinDegree m i) k x =
      derivativeBernsteinWeight m i
        (derivativeBernsteinIndexEquiv m i k) x := by
  rw [anisotropicBernsteinWeight,
    derivativeBernsteinWeight]
  rw [← Finset.mul_prod_erase
    (s := Finset.univ) (f := fun j : Fin n ↦
      _root_.bernstein
        (derivativeBernsteinDegree m i j)
        (k j) (x j)) (by simp)]
  change
    _root_.bernstein
          (derivativeBernsteinDegree m i i)
          (k i) (x i) *
        (∏ j ∈ Finset.univ.erase i,
          _root_.bernstein
            (derivativeBernsteinDegree m i j)
            (k j) (x j)) =
      _root_.bernstein m
          (derivativeBernsteinIndexEquiv m i k).1
          (x i) *
        ∏ j : CoordinateComplement i,
          _root_.bernstein (m + 1)
            ((derivativeBernsteinIndexEquiv m i k).2 j)
            (x j)
  apply congrArg₂ (· * ·)
  · simp only [derivativeBernsteinDegree_same]
    rw [derivativeBernsteinIndexEquiv_fst_val]
  · rw [Finset.prod_subtype
      (p := fun j : Fin n ↦ j ≠ i)
      (Finset.univ.erase i)
      (by intro j; simp)]
    apply Finset.prod_congr rfl
    intro j hj
    simp only [derivativeBernsteinDegree_of_ne
      m i j j.property]
    rw [derivativeBernsteinIndexEquiv_snd_val]

/-- Mixed Bernstein average used by the derivative formula. -/
def derivativeBernsteinValue
    (m : ℕ) (i : Fin n)
    (a : DerivativeBernsteinIndex m i → ℝ)
    (x : UnitCube n) : ℝ :=
  ∑ q : DerivativeBernsteinIndex m i,
    a q *
      derivativeBernsteinWeight m i q x

/-- A mixed derivative-grid average is exactly the corresponding
anisotropic Bernstein average. -/
theorem derivativeBernsteinValue_eq_anisotropic
    (m : ℕ) (i : Fin n)
    (f : UnitCube n → ℝ)
    (x : UnitCube n) :
    derivativeBernsteinValue m i
        (fun q ↦ f (derivativeBernsteinGrid m i q)) x =
      anisotropicBernsteinValue
        (derivativeBernsteinDegree m i) f x := by
  rw [derivativeBernsteinValue,
    anisotropicBernsteinValue]
  let e := derivativeBernsteinIndexEquiv m i
  have h :=
    e.sum_comp
      (fun q : DerivativeBernsteinIndex m i ↦
        f (derivativeBernsteinGrid m i q) *
          derivativeBernsteinWeight m i q x)
  symm
  simpa only [e,
    anisotropicBernsteinGrid_derivativeIndexEquiv,
    anisotropicBernsteinWeight_derivativeIndexEquiv] using h

/-- Every mixed tensor-derivative weight is nonnegative. -/
theorem derivativeBernsteinWeight_nonneg
    (m : ℕ) (i : Fin n)
    (q : DerivativeBernsteinIndex m i)
    (x : UnitCube n) :
    0 ≤ derivativeBernsteinWeight m i q x := by
  rw [derivativeBernsteinWeight]
  apply mul_nonneg _root_.bernstein_nonneg
  apply Finset.prod_nonneg
  intro j hj
  exact _root_.bernstein_nonneg

/-- The mixed tensor-derivative weights form a partition of unity. -/
theorem sum_derivativeBernsteinWeight_eq_one
    (m : ℕ) (i : Fin n) (x : UnitCube n) :
    ∑ q : DerivativeBernsteinIndex m i,
      derivativeBernsteinWeight m i q x = 1 := by
  let e := derivativeBernsteinIndexEquiv m i
  calc
    (∑ q : DerivativeBernsteinIndex m i,
        derivativeBernsteinWeight m i q x) =
        ∑ k : ∀ j,
          Fin (derivativeBernsteinDegree m i j + 1),
          derivativeBernsteinWeight m i (e k) x := by
      symm
      exact e.sum_comp
        (fun q : DerivativeBernsteinIndex m i ↦
          derivativeBernsteinWeight m i q x)
    _ = ∑ k : ∀ j,
          Fin (derivativeBernsteinDegree m i j + 1),
          anisotropicBernsteinWeight
            (derivativeBernsteinDegree m i) k x := by
      apply Finset.sum_congr rfl
      intro k hk
      exact
        (anisotropicBernsteinWeight_derivativeIndexEquiv
          m i k x).symm
    _ = 1 :=
      sum_anisotropicBernsteinWeight_eq_one
        (derivativeBernsteinDegree m i) x

/-- Positive mixed Bernstein averaging does not amplify a uniform
coefficient error.  Unlike the convergence theorem above, this result
applies to arbitrary coefficient arrays, not only to samples of a
function on the cube. -/
theorem abs_derivativeBernsteinDifference_le
    (m : ℕ) (i : Fin n)
    (a b : DerivativeBernsteinIndex m i → ℝ)
    (C : ℝ)
    (hab : ∀ q, |a q - b q| ≤ C)
    (x : UnitCube n) :
    |derivativeBernsteinValue m i a x -
        derivativeBernsteinValue m i b x| ≤ C := by
  calc
    |derivativeBernsteinValue m i a x -
          derivativeBernsteinValue m i b x| =
        |∑ q : DerivativeBernsteinIndex m i,
          (a q - b q) *
            derivativeBernsteinWeight m i q x| := by
      rw [derivativeBernsteinValue,
        derivativeBernsteinValue,
        ← Finset.sum_sub_distrib]
      apply congrArg abs
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ ∑ q : DerivativeBernsteinIndex m i,
        |(a q - b q) *
          derivativeBernsteinWeight m i q x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ q : DerivativeBernsteinIndex m i,
        derivativeBernsteinWeight m i q x *
          |a q - b q| := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [abs_mul,
        abs_of_nonneg
          (derivativeBernsteinWeight_nonneg m i q x),
        mul_comm]
    _ ≤ ∑ q : DerivativeBernsteinIndex m i,
        derivativeBernsteinWeight m i q x * C := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left
        (hab q)
        (derivativeBernsteinWeight_nonneg m i q x)
    _ = C := by
      rw [← Finset.sum_mul,
        sum_derivativeBernsteinWeight_eq_one, one_mul]

/-- The mixed degree profile tends coordinatewise to infinity. -/
theorem tendsto_derivativeBernsteinDegree_atTop
    (i : Fin n) :
    Tendsto
      (fun m : ℕ ↦ derivativeBernsteinDegree m i)
      atTop atTop := by
  rw [tendsto_atTop]
  intro lower
  filter_upwards [
    eventually_ge_atTop
      ((Finset.univ : Finset (Fin n)).sup lower)] with m hm
  intro j
  have hj :
      lower j ≤
        (Finset.univ : Finset (Fin n)).sup lower :=
    Finset.le_sup (by simp)
  simp only [derivativeBernsteinDegree]
  split_ifs <;> omega

/-- Mixed Bernstein averages of samples of a continuous function
converge uniformly to that function. -/
theorem eventually_derivativeBernsteinValue_near
    (i : Fin n)
    (f : (Fin n → ℝ) → ℝ)
    (hf : ContinuousOn f (closedUnitCubeSet n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      ∀ x : UnitCube n,
        |derivativeBernsteinValue m i
            (fun q ↦
              f (unitCubeRealPoint
                (derivativeBernsteinGrid m i q))) x -
          f (unitCubeRealPoint x)| < ε := by
  have hprofile :=
    eventually_anisotropicBernsteinValue_near
      f hf hε
  have hpull :=
    (tendsto_derivativeBernsteinDegree_atTop i).eventually
      hprofile
  filter_upwards [hpull] with m hm
  intro x
  rw [show
    derivativeBernsteinValue m i
        (fun q ↦
          f (unitCubeRealPoint
            (derivativeBernsteinGrid m i q))) x =
      anisotropicBernsteinValue
        (derivativeBernsteinDegree m i)
          (fun y ↦ f (unitCubeRealPoint y)) x from
    derivativeBernsteinValue_eq_anisotropic
      m i (fun y ↦ f (unitCubeRealPoint y)) x]
  exact hm x

/-- The lower degree-`m+1` endpoint of the small interval associated
with a derivative-grid index. -/
def derivativeGridLowerEndpoint
    (m : ℕ) (i : Fin n)
    (q : DerivativeBernsteinIndex m i) :
    UnitCube n :=
  replaceCubeCoordinate i
    (_root_.bernstein.z q.1.castSucc)
    (derivativeBernsteinGrid m i q)

/-- The upper degree-`m+1` endpoint of the small interval associated
with a derivative-grid index. -/
def derivativeGridUpperEndpoint
    (m : ℕ) (i : Fin n)
    (q : DerivativeBernsteinIndex m i) :
    UnitCube n :=
  replaceCubeCoordinate i
    (_root_.bernstein.z q.1.succ)
    (derivativeBernsteinGrid m i q)

/-- Scaled forward difference sampled by the tensor derivative. -/
def tensorBernsteinForwardDifference
    (m : ℕ) (i : Fin n)
    (f : (Fin n → ℝ) → ℝ)
    (q : DerivativeBernsteinIndex m i) : ℝ :=
  (m + 1 : ℝ) *
    (f (unitCubeRealPoint
        (derivativeGridUpperEndpoint m i q)) -
      f (unitCubeRealPoint
        (derivativeGridLowerEndpoint m i q)))

/-- Forgetting interval proofs commutes with replacement of a cube
coordinate.  This elementary bridge lets the one-dimensional
mean-value theorem act on a slice of the real-coordinate cube. -/
theorem unitCubeRealPoint_replaceCubeCoordinate
    (i : Fin n) (t : Set.Icc (0 : ℝ) 1)
    (x : UnitCube n) :
    unitCubeRealPoint (replaceCubeCoordinate i t x) =
      Function.update (unitCubeRealPoint x) i (t : ℝ) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

/-- The selected coordinate of a mixed grid point is the ordinary
degree-`m` Bernstein grid point. -/
theorem unitCubeRealPoint_derivativeBernsteinGrid_apply_same
    (m : ℕ) (i : Fin n)
    (q : DerivativeBernsteinIndex m i) :
    unitCubeRealPoint (derivativeBernsteinGrid m i q) i =
      (q.1 : ℕ) / (m : ℝ) := by
  rw [unitCubeRealPoint_apply,
    derivativeBernsteinGrid_apply_same]
  rfl

/-- Replacing the selected coordinate of a mixed grid point by its own
real value changes nothing. -/
theorem update_unitCubeRealPoint_derivativeBernsteinGrid_same
    (m : ℕ) (i : Fin n)
    (q : DerivativeBernsteinIndex m i) :
    Function.update
        (unitCubeRealPoint
          (derivativeBernsteinGrid m i q))
        i ((q.1 : ℕ) / (m : ℝ)) =
      unitCubeRealPoint
        (derivativeBernsteinGrid m i q) := by
  rw [Function.update_eq_self_iff]
  exact
    (unitCubeRealPoint_derivativeBernsteinGrid_apply_same
      m i q).symm

/-- Quantitative coefficient estimate for tensor Bernstein
derivatives.  It is just the one-dimensional mean-value theorem on the
slice obtained by freezing all coordinates except `i`. -/
theorem tensorBernsteinForwardDifference_near_coordinateDerivative
    (m : ℕ) (i : Fin n)
    (f : (Fin n → ℝ) → ℝ)
    (D : (Fin n → ℝ) → Fin n → ℝ)
    (hderiv :
      ∀ y ∈ closedUnitCubeSet n, ∀ j,
        HasDerivAt
          (fun t : ℝ ↦
            f (Function.update y j t))
          (D y j) (y j))
    {δ ε : ℝ}
    (hmodulus :
      ∀ u ∈ closedUnitCubeSet n,
        ∀ v ∈ closedUnitCubeSet n,
          dist u v < δ →
            |D u i - D v i| < ε)
    (hδ : 0 < δ)
    (hm : m ≠ 0)
    (hmesh : 1 / ((m + 1 : ℕ) : ℝ) < δ)
    (q : DerivativeBernsteinIndex m i) :
    |tensorBernsteinForwardDifference m i f q -
        D (unitCubeRealPoint
          (derivativeBernsteinGrid m i q)) i| < ε := by
  let y : Fin n → ℝ :=
    unitCubeRealPoint
      (derivativeBernsteinGrid m i q)
  let fs : ℝ → ℝ :=
    fun t ↦ f (Function.update y i t)
  let gs : ℝ → ℝ :=
    fun t ↦ D (Function.update y i t) i
  have hupdate_mem :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Function.update y i t ∈
          closedUnitCubeSet n := by
    intro t ht
    rw [mem_closedUnitCubeSet]
    intro j
    by_cases hji : j = i
    · subst j
      simpa using ht
    · have hy :=
        ((mem_closedUnitCubeSet
          (unitCubeRealPoint
            (derivativeBernsteinGrid m i q))).mp
          (unitCubeRealPoint_mem
            (derivativeBernsteinGrid m i q))) j
      simpa [Function.update, hji, y] using hy
  have hslice :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivAt fs (gs t) t := by
    intro t ht
    have hd :=
      hderiv (Function.update y i t)
        (hupdate_mem t ht) i
    simpa only [fs, gs, Function.update_idem,
      Function.update_self] using hd
  have hslice_modulus :
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        ∀ v ∈ Set.Icc (0 : ℝ) 1,
          |u - v| < δ →
            |gs u - gs v| < ε := by
    intro u hu v hv huv
    apply hmodulus
      (Function.update y i u) (hupdate_mem u hu)
      (Function.update y i v) (hupdate_mem v hv)
    rw [dist_pi_lt_iff hδ]
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self,
        Real.dist_eq] using huv
    · simp [hji, hδ]
  have hscalar :=
    bernsteinForwardDifference_near_derivative
      fs gs hslice hslice_modulus hm hmesh q.1
  have hsample :
      gs ((q.1 : ℕ) / (m : ℝ)) =
        D y i := by
    change
      D (Function.update y i
          ((q.1 : ℕ) / (m : ℝ))) i =
        D y i
    rw [update_unitCubeRealPoint_derivativeBernsteinGrid_same]
  have hlower :
      unitCubeRealPoint
          (derivativeGridLowerEndpoint m i q) =
        Function.update y i
          ((q.1.castSucc : ℝ) /
            ((m + 1 : ℕ) : ℝ)) := by
    rw [derivativeGridLowerEndpoint,
      unitCubeRealPoint_replaceCubeCoordinate]
    rfl
  have hupper :
      unitCubeRealPoint
          (derivativeGridUpperEndpoint m i q) =
        Function.update y i
          ((q.1.succ : ℝ) /
            ((m + 1 : ℕ) : ℝ)) := by
    rw [derivativeGridUpperEndpoint,
      unitCubeRealPoint_replaceCubeCoordinate]
    rfl
  rw [tensorBernsteinForwardDifference,
    hlower, hupper]
  simpa only [fs, hsample, y, Nat.cast_add,
    Nat.cast_one] using hscalar

/-- Reassemble a full degree-`m+1` tensor index from its selected
coordinate and complementary coordinates. -/
def fullBernsteinIndexFromSplit
    (m : ℕ) (i : Fin n)
    (q : Fin (m + 2) ×
      (CoordinateComplement i → Fin (m + 2))) :
    Fin n → Fin (m + 2) :=
  (Equiv.funSplitAt i (Fin (m + 2))).symm q

@[simp]
theorem fullBernsteinIndexFromSplit_apply_same
    (m : ℕ) (i : Fin n)
    (q : Fin (m + 2) ×
      (CoordinateComplement i → Fin (m + 2))) :
    fullBernsteinIndexFromSplit m i q i = q.1 := by
  simp [fullBernsteinIndexFromSplit,
    Equiv.funSplitAt, Equiv.piSplitAt]

@[simp]
theorem fullBernsteinIndexFromSplit_apply_of_ne
    (m : ℕ) (i j : Fin n) (hji : j ≠ i)
    (q : Fin (m + 2) ×
      (CoordinateComplement i → Fin (m + 2))) :
    fullBernsteinIndexFromSplit m i q j =
      q.2 ⟨j, hji⟩ := by
  simp [fullBernsteinIndexFromSplit,
    Equiv.funSplitAt, Equiv.piSplitAt, hji]

/-- Reassembling with the successor selected index gives the upper
forward-difference endpoint. -/
theorem tensorBernsteinGrid_split_succ
    (m : ℕ) (i : Fin n)
    (q : Fin (m + 1))
    (r : CoordinateComplement i → Fin (m + 2)) :
    tensorBernsteinGrid (m + 1)
        (fullBernsteinIndexFromSplit m i (q.succ, r)) =
      unitCubeRealPoint
        (derivativeGridUpperEndpoint m i (q, r)) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [tensorBernsteinGrid,
      derivativeGridUpperEndpoint,
      _root_.bernstein.z]
  · simp [tensorBernsteinGrid,
      derivativeGridUpperEndpoint,
      derivativeBernsteinGrid, hji,
      _root_.bernstein.z]

/-- Reassembling with the cast-successor selected index gives the lower
forward-difference endpoint. -/
theorem tensorBernsteinGrid_split_castSucc
    (m : ℕ) (i : Fin n)
    (q : Fin (m + 1))
    (r : CoordinateComplement i → Fin (m + 2)) :
    tensorBernsteinGrid (m + 1)
        (fullBernsteinIndexFromSplit m i (q.castSucc, r)) =
      unitCubeRealPoint
        (derivativeGridLowerEndpoint m i (q, r)) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [tensorBernsteinGrid,
      derivativeGridLowerEndpoint,
      _root_.bernstein.z]
  · simp [tensorBernsteinGrid,
      derivativeGridLowerEndpoint,
      derivativeBernsteinGrid, hji,
      _root_.bernstein.z]

/-- The product of untouched Bernstein factors after splitting off one
coordinate. -/
theorem prod_erase_eval_bernsteinPolynomial_split
    (m : ℕ) (i : Fin n)
    (k : Fin (m + 2))
    (r : CoordinateComplement i → Fin (m + 2))
    (x : UnitCube n) :
    (∏ j ∈ Finset.univ.erase i,
        (_root_.bernsteinPolynomial ℝ (m + 1)
          (fullBernsteinIndexFromSplit m i (k, r) j)).eval
            (x j : ℝ)) =
      ∏ j : CoordinateComplement i,
        _root_.bernstein (m + 1) (r j) (x j) := by
  rw [Finset.prod_subtype
    (p := fun j : Fin n ↦ j ≠ i)
    (Finset.univ.erase i)
    (by intro j; simp)]
  apply Finset.prod_congr rfl
  intro j hj
  rw [fullBernsteinIndexFromSplit_apply_of_ne
    m i j j.property]
  rfl

/-- Exact tensor summation by parts in coordinate `i`. -/
theorem eval_pderiv_tensorBernsteinPolynomial_eq_forwardAverage
    (m : ℕ) (f : (Fin n → ℝ) → ℝ)
    (i : Fin n) (x : UnitCube n) :
    MvPolynomial.eval (unitCubeRealPoint x)
        (MvPolynomial.pderiv i
          (tensorBernsteinPolynomial (m + 1) f)) =
      derivativeBernsteinValue m i
        (tensorBernsteinForwardDifference m i f)
        x := by
  rw [eval_pderiv_tensorBernsteinPolynomial]
  let raw :
      (Fin n → Fin (m + 2)) → ℝ :=
    fun k ↦
      f (tensorBernsteinGrid (m + 1) k) *
        (_root_.bernsteinPolynomial ℝ (m + 1)
          (k i)).derivative.eval
            (unitCubeRealPoint x i) *
        ∏ j ∈ Finset.univ.erase i,
          (_root_.bernsteinPolynomial ℝ (m + 1)
            (k j)).eval (unitCubeRealPoint x j)
  change (∑ k : Fin n → Fin (m + 2), raw k) = _
  have hsplit :
      (∑ k : Fin n → Fin (m + 2), raw k) =
        ∑ kr :
            Fin (m + 2) ×
              (CoordinateComplement i → Fin (m + 2)),
          raw (fullBernsteinIndexFromSplit m i kr) := by
    let e :=
      Equiv.funSplitAt i (Fin (m + 2))
    have h :=
      e.sum_comp
        (fun kr ↦ raw
          (fullBernsteinIndexFromSplit m i kr))
    simpa only [e, fullBernsteinIndexFromSplit,
      Equiv.symm_apply_apply] using h
  rw [hsplit, Fintype.sum_prod_type_right]
  rw [derivativeBernsteinValue,
    Fintype.sum_prod_type_right]
  apply Finset.sum_congr rfl
  intro r hr
  have hone :
      unitCubeRealPoint x i = (x i : ℝ) :=
    rfl
  have hother :
      ∀ k : Fin (m + 2),
        (∏ j ∈ Finset.univ.erase i,
            (_root_.bernsteinPolynomial ℝ (m + 1)
              (fullBernsteinIndexFromSplit m i (k, r) j)).eval
                (unitCubeRealPoint x j)) =
          ∏ j : CoordinateComplement i,
            _root_.bernstein (m + 1) (r j) (x j) := by
    intro k
    simpa only [unitCubeRealPoint_apply] using
      prod_erase_eval_bernsteinPolynomial_split
        m i k r x
  let a : Fin (m + 2) → ℝ :=
    fun k ↦
      f (tensorBernsteinGrid (m + 1)
        (fullBernsteinIndexFromSplit m i (k, r)))
  let P : ℝ :=
    ∏ j : CoordinateComplement i,
      _root_.bernstein (m + 1) (r j) (x j)
  have hscalar :=
    sum_mul_eval_derivative_bernsteinPolynomial_succ
      m a (x i)
  calc
    (∑ k : Fin (m + 2),
        raw (fullBernsteinIndexFromSplit m i (k, r))) =
        (∑ k : Fin (m + 2),
          a k *
            (_root_.bernsteinPolynomial ℝ (m + 1) k).derivative.eval
              (x i : ℝ)) * P := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [raw, a, P,
        fullBernsteinIndexFromSplit_apply_same]
      rw [hother k, hone]
    _ = ((m + 1 : ℝ) *
          ∑ q : Fin (m + 1),
            (a q.succ - a q.castSucc) *
              _root_.bernstein m q (x i)) * P := by
      rw [hscalar]
    _ = ∑ q : Fin (m + 1),
        tensorBernsteinForwardDifference m i f (q, r) *
          derivativeBernsteinWeight m i (q, r) x := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      dsimp only [a]
      rw [tensorBernsteinGrid_split_succ,
        tensorBernsteinGrid_split_castSucc]
      simp only [tensorBernsteinForwardDifference,
        derivativeBernsteinWeight, P]
      ring

/-- Uniformly over all mixed-grid indices, the scaled forward
differences in coordinate `i` converge to the prescribed coordinate
derivative.  Compactness enters only through Heine--Cantor uniform
continuity of that derivative component. -/
theorem eventually_tensorBernsteinForwardDifference_near
    (i : Fin n)
    (f : (Fin n → ℝ) → ℝ)
    (D : (Fin n → ℝ) → Fin n → ℝ)
    (hDi :
      ContinuousOn (fun y ↦ D y i)
        (closedUnitCubeSet n))
    (hderiv :
      ∀ y ∈ closedUnitCubeSet n, ∀ j,
        HasDerivAt
          (fun t : ℝ ↦
            f (Function.update y j t))
          (D y j) (y j))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      ∀ q : DerivativeBernsteinIndex m i,
        |tensorBernsteinForwardDifference m i f q -
          D (unitCubeRealPoint
            (derivativeBernsteinGrid m i q)) i| < ε := by
  have huniform :
      UniformContinuousOn (fun y ↦ D y i)
        (closedUnitCubeSet n) :=
    IsCompact.uniformContinuousOn_of_continuous
      (isCompact_closedUnitCubeSet (n := n)) hDi
  obtain ⟨δ, hδ, hmodulusDist⟩ :=
    (Metric.uniformContinuousOn_iff.mp huniform)
      ε hε
  have hmodulus :
      ∀ u ∈ closedUnitCubeSet n,
        ∀ v ∈ closedUnitCubeSet n,
          dist u v < δ →
            |D u i - D v i| < ε := by
    intro u hu v hv huv
    simpa only [Real.dist_eq] using
      hmodulusDist u hu v hv huv
  have hmeshTendsto :
      Tendsto
        (fun m : ℕ ↦
          (1 : ℝ) / ((m + 1 : ℕ) : ℝ))
        atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add,
      Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat
        (1 : ℝ)).comp
        (tendsto_add_atTop_nat 1)
  have hmeshEventually :
      ∀ᶠ m : ℕ in atTop,
        (1 : ℝ) / ((m + 1 : ℕ) : ℝ) < δ :=
    hmeshTendsto.eventually_lt_const hδ
  filter_upwards [Filter.eventually_ne_atTop 0,
    hmeshEventually] with m hm hmesh
  intro q
  exact
    tensorBernsteinForwardDifference_near_coordinateDerivative
      m i f D hderiv hmodulus hδ hm hmesh q

/-- For one fixed coordinate, the corresponding partial derivatives
of tensor Bernstein polynomials converge uniformly on the cube. -/
theorem eventually_eval_pderiv_tensorBernsteinPolynomial_near
    (i : Fin n)
    (f : (Fin n → ℝ) → ℝ)
    (D : (Fin n → ℝ) → Fin n → ℝ)
    (hDi :
      ContinuousOn (fun y ↦ D y i)
        (closedUnitCubeSet n))
    (hderiv :
      ∀ y ∈ closedUnitCubeSet n, ∀ j,
        HasDerivAt
          (fun t : ℝ ↦
            f (Function.update y j t))
          (D y j) (y j))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      ∀ x : UnitCube n,
        |MvPolynomial.eval (unitCubeRealPoint x)
              (MvPolynomial.pderiv i
                (tensorBernsteinPolynomial (m + 1) f)) -
          D (unitCubeRealPoint x) i| < ε := by
  have hhalf : 0 < ε / 2 := by
    positivity
  have hforward :=
    eventually_tensorBernsteinForwardDifference_near
      i f D hDi hderiv hhalf
  have haverage :=
    eventually_derivativeBernsteinValue_near
      i (fun y ↦ D y i) hDi hhalf
  filter_upwards [hforward, haverage] with
    m hmForward hmAverage
  intro x
  let sampled :
      DerivativeBernsteinIndex m i → ℝ :=
    fun q ↦
      D (unitCubeRealPoint
        (derivativeBernsteinGrid m i q)) i
  have hcoefficientAverage :
      |derivativeBernsteinValue m i
            (tensorBernsteinForwardDifference m i f) x -
          derivativeBernsteinValue m i sampled x| ≤
        ε / 2 := by
    apply abs_derivativeBernsteinDifference_le
    intro q
    exact (hmForward q).le
  have hsampleAverage :
      |derivativeBernsteinValue m i sampled x -
          D (unitCubeRealPoint x) i| < ε / 2 := by
    exact hmAverage x
  rw [
    eval_pderiv_tensorBernsteinPolynomial_eq_forwardAverage]
  have htriangle :
      |derivativeBernsteinValue m i
            (tensorBernsteinForwardDifference m i f) x -
          D (unitCubeRealPoint x) i| ≤
        |derivativeBernsteinValue m i
              (tensorBernsteinForwardDifference m i f) x -
            derivativeBernsteinValue m i sampled x| +
          |derivativeBernsteinValue m i sampled x -
            D (unitCubeRealPoint x) i| := by
    calc
      |derivativeBernsteinValue m i
              (tensorBernsteinForwardDifference m i f) x -
            D (unitCubeRealPoint x) i| =
          |(derivativeBernsteinValue m i
                (tensorBernsteinForwardDifference m i f) x -
              derivativeBernsteinValue m i sampled x) +
            (derivativeBernsteinValue m i sampled x -
              D (unitCubeRealPoint x) i)| := by
        congr 1
        ring
      _ ≤ _ := abs_add_le _ _
  linarith

/-- All coordinate derivatives converge uniformly and simultaneously;
finiteness of `Fin n` is used to combine the coordinatewise eventual
statements. -/
theorem eventually_eval_all_pderiv_tensorBernsteinPolynomial_near
    (f : (Fin n → ℝ) → ℝ)
    (D : (Fin n → ℝ) → Fin n → ℝ)
    (hD :
      ∀ i,
        ContinuousOn (fun y ↦ D y i)
          (closedUnitCubeSet n))
    (hderiv :
      ∀ y ∈ closedUnitCubeSet n, ∀ j,
        HasDerivAt
          (fun t : ℝ ↦
            f (Function.update y j t))
          (D y j) (y j))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      ∀ x : UnitCube n, ∀ i,
        |MvPolynomial.eval (unitCubeRealPoint x)
              (MvPolynomial.pderiv i
                (tensorBernsteinPolynomial (m + 1) f)) -
          D (unitCubeRealPoint x) i| < ε := by
  have hall :
      ∀ᶠ m : ℕ in atTop,
        ∀ i, ∀ x : UnitCube n,
          |MvPolynomial.eval (unitCubeRealPoint x)
                (MvPolynomial.pderiv i
                  (tensorBernsteinPolynomial (m + 1) f)) -
            D (unitCubeRealPoint x) i| < ε := by
    rw [Filter.eventually_all]
    intro i
    exact
      eventually_eval_pderiv_tensorBernsteinPolynomial_near
        i f D (hD i) hderiv hε
  filter_upwards [hall] with m hm
  intro x i
  exact hm i x

/-- The isotropic degree profile `m+1` tends to infinity in every
coordinate. -/
theorem tendsto_isotropicBernsteinDegreeSucc_atTop :
    Tendsto
      (fun m : ℕ ↦ fun _ : Fin n ↦ m + 1)
      atTop atTop := by
  rw [tendsto_atTop]
  intro lower
  filter_upwards [
    eventually_ge_atTop
      ((Finset.univ : Finset (Fin n)).sup lower)] with m hm
  intro i
  have hi :
      lower i ≤
        (Finset.univ : Finset (Fin n)).sup lower :=
    Finset.le_sup (by simp)
  exact hi.trans (hm.trans (Nat.le_succ m))

/-- Tensor Bernstein polynomial values of degree `m+1` converge
uniformly on the cube. -/
theorem eventually_eval_tensorBernsteinPolynomial_near
    (f : (Fin n → ℝ) → ℝ)
    (hf : ContinuousOn f (closedUnitCubeSet n))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      ∀ x : UnitCube n,
        |MvPolynomial.eval (unitCubeRealPoint x)
              (tensorBernsteinPolynomial (m + 1) f) -
          f (unitCubeRealPoint x)| < ε := by
  have hprofile :=
    eventually_anisotropicBernsteinValue_near
      f hf hε
  have hpull :=
    (tendsto_isotropicBernsteinDegreeSucc_atTop
      (n := n)).eventually hprofile
  filter_upwards [hpull] with m hm
  intro x
  rw [eval_tensorBernsteinPolynomial_eq_anisotropic]
  exact hm x

/-- The value and every coordinate derivative of the same tensor
Bernstein polynomial converge uniformly on the cube. -/
theorem eventually_tensorBernsteinPolynomial_c1_near
    (f : (Fin n → ℝ) → ℝ)
    (D : (Fin n → ℝ) → Fin n → ℝ)
    (hf : ContinuousOn f (closedUnitCubeSet n))
    (hD :
      ∀ i,
        ContinuousOn (fun y ↦ D y i)
          (closedUnitCubeSet n))
    (hderiv :
      ∀ y ∈ closedUnitCubeSet n, ∀ j,
        HasDerivAt
          (fun t : ℝ ↦
            f (Function.update y j t))
          (D y j) (y j))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      (∀ x : UnitCube n,
        |MvPolynomial.eval (unitCubeRealPoint x)
              (tensorBernsteinPolynomial (m + 1) f) -
          f (unitCubeRealPoint x)| < ε) ∧
      (∀ x : UnitCube n, ∀ i,
        |MvPolynomial.eval (unitCubeRealPoint x)
              (MvPolynomial.pderiv i
                (tensorBernsteinPolynomial (m + 1) f)) -
          D (unitCubeRealPoint x) i| < ε) := by
  filter_upwards [
    eventually_eval_tensorBernsteinPolynomial_near
      f hf hε,
    eventually_eval_all_pderiv_tensorBernsteinPolynomial_near
      f D hD hderiv hε] with m hmValue hmDerivative
  exact ⟨hmValue, hmDerivative⟩

end

end HGAS
