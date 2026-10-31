import Stability.Simulation.PolynomialEnvelope
import Stability.Simulation.RadicalDependencies

/-!
# Polynomial bounds for a triangular root graph

The j-th root is bounded using coefficient mass and polynomial bounds for
the earlier roots. A finite recursion constructs all bounds as rational
polynomials in the base variables. Later roots are set to zero when
estimating a radicand; triangularity proves that this does not change its
value. No boundedness of the root graph is assumed.
-/

namespace Stability.Simulation.RadicalMajorant

noncomputable section

open AbsFormula

variable {σ : Type*} [Fintype σ] {J : ℕ}

def radius (bounds : Fin J → MvPolynomial σ ℚ) : MvPolynomial σ ℚ :=
  coordinateEnvelope + ∑ i, bounds i ^ 2

theorem radius_value (bounds : Fin J → MvPolynomial σ ℚ) (x : σ → ℝ) :
    polynomialValue x (radius bounds) =
      1 + ∑ i, x i ^ 2 + ∑ i, polynomialValue x (bounds i) ^ 2 := by
  simp [radius, coordinateEnvelope, polynomialValue]

theorem radius_one_le (bounds : Fin J → MvPolynomial σ ℚ) (x : σ → ℝ) :
    1 ≤ polynomialValue x (radius bounds) := by
  rw [radius_value]
  have hbase := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦ sq_nonneg (x i)
  have hroots := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦
    sq_nonneg (polynomialValue x (bounds i))
  linarith

theorem abs_base_le_radius (bounds : Fin J → MvPolynomial σ ℚ) (x : σ → ℝ) (i : σ) :
    |x i| ≤ polynomialValue x (radius bounds) := by
  have h := abs_coordinate_le_envelope x i
  rw [coordinateEnvelope_value] at h
  rw [radius_value]
  exact h.trans (le_add_of_nonneg_right (Finset.sum_nonneg fun j _ ↦
    sq_nonneg (polynomialValue x (bounds j))))

theorem bound_le_radius (bounds : Fin J → MvPolynomial σ ℚ) (x : σ → ℝ) (i : Fin J) :
    polynomialValue x (bounds i) ≤ polynomialValue x (radius bounds) := by
  rw [radius_value]
  have hsingle := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) ↦
    sq_nonneg (polynomialValue x (bounds j))) (Finset.mem_univ i)
  have hbase := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) ↦ sq_nonneg (x j)
  nlinarith [sq_nonneg (polynomialValue x (bounds i) - 1)]

def step (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (bounds : Fin J → MvPolynomial σ ℚ) (j : Fin J) : MvPolynomial σ ℚ :=
  1 + MvPolynomial.C (coefficientMass (D j)) * radius bounds ^ (D j).totalDegree

theorem step_one_le (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (bounds : Fin J → MvPolynomial σ ℚ) (x : σ → ℝ) (j : Fin J) :
    1 ≤ polynomialValue x (step D bounds j) := by
  have hc : (0 : ℝ) ≤ coefficientMass (D j) := by exact_mod_cast coefficientMass_nonneg (D j)
  have hr := (zero_le_one.trans (radius_one_le bounds x))
  simp only [step, polynomialValue, MvPolynomial.eval₂_add, MvPolynomial.eval₂_one,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_pow]
  exact le_add_of_nonneg_right (mul_nonneg hc (pow_nonneg hr _))

def boundPrefix (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ) :
    ℕ → Fin J → MvPolynomial σ ℚ
  | 0 => fun _ ↦ 0
  | count + 1 =>
      let previous := boundPrefix D count
      if h : count < J then Function.update previous ⟨count, h⟩
        (step D previous ⟨count, h⟩) else previous

def majorants (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ) : Fin J → MvPolynomial σ ℚ :=
  boundPrefix D J

theorem prefix_succ_of_ne (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (count : ℕ) (i : Fin J) (hi : i.val ≠ count) :
    boundPrefix D (count + 1) i = boundPrefix D count i := by
  change (if h : count < J then Function.update (boundPrefix D count) ⟨count, h⟩
    (step D (boundPrefix D count) ⟨count, h⟩) else boundPrefix D count) i = _
  split_ifs with h
  · apply Function.update_of_ne
    intro heq
    exact hi (congrArg Fin.val heq)
  · rfl

theorem prefix_eq_of_le (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    {a b : ℕ} (hab : a ≤ b) (i : Fin J) (hi : i.val < a) :
    boundPrefix D b i = boundPrefix D a i := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih => rw [prefix_succ_of_ne D b i (by omega), ih]

theorem majorants_eq_step (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ) (i : Fin J) :
    majorants D i = step D (boundPrefix D i.val) i := by
  rw [majorants, prefix_eq_of_le D (a := i.val + 1) (by omega) i (by omega)]
  simp [boundPrefix, i.isLt]

theorem prefix_nonneg (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (x : σ → ℝ) (count : ℕ) (i : Fin J) : 0 ≤ polynomialValue x (boundPrefix D count i) := by
  induction count generalizing i with
  | zero => simp [boundPrefix, polynomialValue]
  | succ count ih =>
      unfold boundPrefix
      split_ifs with h
      · by_cases hi : i = ⟨count, h⟩
        · subst i
          rw [Function.update_self]
          exact zero_le_one.trans (step_one_le D _ x _)
        · rw [Function.update_of_ne hi]
          exact ih i
      · exact ih i

/-- The constructed polynomials bound every solution of the positive
triangular square-root equations, in particular the compiler's evaluator. -/
theorem abs_root_le_majorant (D : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (htri : ∀ j, RadicalProgram.FiniteDependsBelow (D j) j.val)
    (x : σ → ℝ) (roots : Fin J → ℝ)
    (hroots : ∀ j, roots j = Real.sqrt (polynomialValue (Sum.elim x roots) (D j))) :
    ∀ j, |roots j| ≤ polynomialValue x (majorants D j) := by
  apply Fin.strong_induction_on
  intro j ih
  let truncatedRoots : Fin J → ℝ := fun i ↦ if i.val < j.val then roots i else 0
  have hagree : polynomialValue (Sum.elim x roots) (D j) =
      polynomialValue (Sum.elim x truncatedRoots) (D j) := by
    apply MvPolynomial.eval₂Hom_congr' rfl _ rfl
    intro i hi _
    cases i with
    | inl i => rfl
    | inr i =>
        change roots i = if i.val < j.val then roots i else 0
        rw [if_pos (htri j i hi)]
  have hpartial (i : Fin J) : |truncatedRoots i| ≤ polynomialValue x (boundPrefix D j.val i) := by
    by_cases hij : i.val < j.val
    · simp only [truncatedRoots, hij, if_true]
      have h := ih i hij
      rw [majorants, prefix_eq_of_le D j.isLt.le i hij] at h
      exact h
    · simp only [truncatedRoots, hij, if_false, abs_zero]
      exact prefix_nonneg D x j.val i
  have hbox : ∀ i : σ ⊕ Fin J,
      |Sum.elim x truncatedRoots i| ≤ polynomialValue x (radius (boundPrefix D j.val)) := by
    intro i
    cases i with
    | inl i => exact abs_base_le_radius _ x i
    | inr i => exact (hpartial i).trans (bound_le_radius _ x i)
  have hpoly := abs_polynomialValue_le_cube (D j) (Sum.elim x truncatedRoots)
    (radius_one_le (boundPrefix D j.val) x) hbox
  have hsqrt : Real.sqrt (polynomialValue (Sum.elim x truncatedRoots) (D j)) ≤
      1 + |polynomialValue (Sum.elim x truncatedRoots) (D j)| := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [le_abs_self (polynomialValue (Sum.elim x truncatedRoots) (D j)),
        abs_nonneg (polynomialValue (Sum.elim x truncatedRoots) (D j)),
        sq_nonneg (polynomialValue (Sum.elim x truncatedRoots) (D j))]
  rw [hroots j, abs_of_nonneg (Real.sqrt_nonneg _), hagree, majorants_eq_step]
  exact hsqrt.trans (by simpa [step, polynomialValue] using add_le_add_left hpoly 1)

end

end Stability.Simulation.RadicalMajorant

namespace Stability.Simulation.AbsFormula

noncomputable section

variable {σ : Type*} [Fintype σ]

/-- Global rational polynomial majorants for the actual generated roots.
Even the bounds, rather than only their existence, are explicitly defined. -/
theorem finiteRadicalRoots_le_polynomialMajorants (L : MvPolynomial σ ℚ)
    (es : List (AbsFormula σ)) (x : σ → ℝ)
    (j : Fin (finiteRadicalFamily L es).rootCount) :
    |finiteRadicalRoots L es x j| ≤ polynomialValue x
      (RadicalMajorant.majorants (finiteRadicalFamily L es).radicands j) :=
  RadicalMajorant.abs_root_le_majorant _ (finiteRadicalFamily_radicand_dependsBelow L es)
    x _ (finiteRadicalRoots_equation L es x) j

end

end Stability.Simulation.AbsFormula
