import Stability.Simulation.RadicalLiftPolynomials
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Triangular dependencies of the finite lift polynomials

The compiler's order survives finite restriction and root-square
substitution. In particular, every formal partial derivative of the
j-th lifted radicand with respect to root j or a later root is zero.
This is the algebraic fact that makes its differential lift recursive.
-/

namespace Stability.Simulation.RadicalProgram

noncomputable section

variable {σ : Type*}

theorem Triangular.get_dependsBelow {ps : Program σ} {start : ℕ}
    (htri : Triangular ps start) (i : Fin ps.length) :
    DependsBelow (ps.get i) (start + i.val) := by
  induction ps generalizing start with
  | nil => exact Fin.elim0 i
  | cons p ps ih =>
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa using htri.1
      · simpa only [List.get_cons_succ, Fin.val_succ, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using ih htri.2 j

/-- Finite-coordinate version of the strict earlier-root dependency. -/
def FiniteDependsBelow {n : ℕ} (p : MvPolynomial (σ ⊕ Fin n) ℚ) (cut : ℕ) : Prop :=
  ∀ i : Fin n, Sum.inr i ∈ p.vars → i.val < cut

theorem finitePolynomial_dependsBelow {bound cut : ℕ} {p : Polynomial σ}
    (hp : DependsBelow p cut) : FiniteDependsBelow (finitePolynomial bound p) cut := by
  classical
  intro j hj
  obtain ⟨i, hi, hji⟩ := MvPolynomial.mem_vars_bind₁ (finiteVariable bound) p hj
  cases i with
  | inl i => simp [finiteVariable] at hji
  | inr i =>
      by_cases hib : i < bound
      · have hji' : (Sum.inr j : σ ⊕ Fin bound) = Sum.inr ⟨i, hib⟩ := by
          simpa [finiteVariable, hib] using hji
        have hval : j.val = i := congrArg Fin.val (Sum.inr.inj hji')
        rw [hval]
        exact hp i hi
      · simp [finiteVariable, hib] at hji

theorem FiniteDependsBelow.squareRootsPolynomial {n cut : ℕ}
    {p : MvPolynomial (σ ⊕ Fin n) ℚ} (hp : FiniteDependsBelow p cut) :
    FiniteDependsBelow (squareRootsPolynomial p) cut := by
  classical
  intro j hj
  obtain ⟨i, hi, hji⟩ := MvPolynomial.mem_vars_bind₁ squareRootVariable p hj
  cases i with
  | inl i => simp [squareRootVariable] at hji
  | inr i =>
      have hvar := MvPolynomial.vars_pow
        (MvPolynomial.X (Sum.inr i) : MvPolynomial (σ ⊕ Fin n) ℚ) 2 hji
      have hji' : (Sum.inr j : σ ⊕ Fin n) = Sum.inr i := by simpa using hvar
      have hsame : j = i := Sum.inr.inj hji'
      subst j
      exact hp i hi

/-- A current or future root has identically zero formal partial derivative. -/
theorem FiniteDependsBelow.pderiv_eq_zero {n cut : ℕ}
    {p : MvPolynomial (σ ⊕ Fin n) ℚ} (hp : FiniteDependsBelow p cut)
    (i : Fin n) (hi : cut ≤ i.val) : MvPolynomial.pderiv (Sum.inr i) p = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro hmem
  exact (not_lt_of_ge hi) (hp i hmem)

end

end Stability.Simulation.RadicalProgram

namespace Stability.Simulation.AbsFormula

noncomputable section

open RadicalProgram

variable {σ : Type*}

theorem finiteRadicalFamily_radicand_dependsBelow (L : MvPolynomial σ ℚ)
    (es : List (AbsFormula σ)) (i : Fin (finiteRadicalFamily L es).rootCount) :
    FiniteDependsBelow ((finiteRadicalFamily L es).radicands i) i.val := by
  apply finitePolynomial_dependsBelow
  simpa using (extractRadicalFamily_wellFormed L es 0).1.get_dependsBelow i

theorem liftRadicand_dependsBelow (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ))
    (i : Fin (finiteRadicalFamily L es).rootCount) :
    FiniteDependsBelow (liftRadicand L es i) i.val :=
  (finiteRadicalFamily_radicand_dependsBelow L es i).squareRootsPolynomial

/-- The actual compiled lift is triangular at the formal derivative level. -/
theorem liftRadicand_pderiv_root_eq_zero (L : MvPolynomial σ ℚ)
    (es : List (AbsFormula σ)) (i j : Fin (finiteRadicalFamily L es).rootCount)
    (hij : i.val ≤ j.val) : MvPolynomial.pderiv (Sum.inr j) (liftRadicand L es i) = 0 :=
  (liftRadicand_dependsBelow L es i).pderiv_eq_zero j hij

end

end Stability.Simulation.AbsFormula
