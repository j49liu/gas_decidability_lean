import Stability.Simulation.PowerFraction
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Finite triangular programs of polynomial square roots

A program lists its radicands in evaluation order. Base variables are
tagged separately from root indices. Triangularity states that each
radicand uses only earlier roots. Sequential evaluation then constructs
an assignment satisfying every root equation in the final state.

Natural-number indices avoid repeated casts when concatenating programs;
the dependency bound makes the finite variable range explicit.
-/

namespace Stability.Simulation.RadicalProgram

noncomputable section

variable {σ : Type*}

abbrev Polynomial (σ : Type*) := MvPolynomial (σ ⊕ ℕ) ℚ

abbrev Program (σ : Type*) := List (Polynomial σ)

def point (x : σ → ℝ) (roots : ℕ → ℝ) : σ ⊕ ℕ → ℝ := Sum.elim x roots

def polynomialValue (x : σ → ℝ) (roots : ℕ → ℝ) (p : Polynomial σ) : ℝ :=
  AbsFormula.polynomialValue (point x roots) p

def basePolynomial (p : MvPolynomial σ ℚ) : Polynomial σ := MvPolynomial.rename Sum.inl p

@[simp]
theorem basePolynomial_value (p : MvPolynomial σ ℚ) (x : σ → ℝ) (roots : ℕ → ℝ) :
    polynomialValue x roots (basePolynomial p) = AbsFormula.polynomialValue x p := by
  simp [polynomialValue, basePolynomial, AbsFormula.polynomialValue, point,
    MvPolynomial.eval₂_rename, Function.comp_def]

/-- Only root variables with index strictly below `bound` may occur. -/
def DependsBelow (p : Polynomial σ) (bound : ℕ) : Prop :=
  ∀ i : ℕ, Sum.inr i ∈ p.vars → i < bound

theorem DependsBelow.mono {p : Polynomial σ} {a b : ℕ}
    (hp : DependsBelow p a) (hab : a ≤ b) : DependsBelow p b :=
  fun i hi ↦ (hp i hi).trans_le hab

theorem dependsBelow_basePolynomial (p : MvPolynomial σ ℚ) (bound : ℕ) :
    DependsBelow (basePolynomial p) bound := by
  intro i hi
  obtain ⟨j, _, hji⟩ := MvPolynomial.mem_vars_rename Sum.inl p hi
  cases hji

theorem dependsBelow_C (c : ℚ) (bound : ℕ) :
    DependsBelow (MvPolynomial.C c : Polynomial σ) bound := by
  simp [DependsBelow]

theorem dependsBelow_X_base (i : σ) (bound : ℕ) :
    DependsBelow (MvPolynomial.X (Sum.inl i) : Polynomial σ) bound := by
  simp [DependsBelow]

theorem dependsBelow_X_root {i bound : ℕ} (hi : i < bound) :
    DependsBelow (MvPolynomial.X (Sum.inr i) : Polynomial σ) bound := by
  simpa [DependsBelow] using hi

theorem DependsBelow.add {p q : Polynomial σ} {bound : ℕ}
    (hp : DependsBelow p bound) (hq : DependsBelow q bound) : DependsBelow (p + q) bound := by
  classical
  intro i hi
  rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset p q hi) with hi | hi
  · exact hp i hi
  · exact hq i hi

theorem DependsBelow.mul {p q : Polynomial σ} {bound : ℕ}
    (hp : DependsBelow p bound) (hq : DependsBelow q bound) : DependsBelow (p * q) bound := by
  classical
  intro i hi
  rcases Finset.mem_union.mp (MvPolynomial.vars_mul p q hi) with hi | hi
  · exact hp i hi
  · exact hq i hi

theorem DependsBelow.pow {p : Polynomial σ} {bound : ℕ}
    (hp : DependsBelow p bound) (k : ℕ) : DependsBelow (p ^ k) bound :=
  fun i hi ↦ hp i (MvPolynomial.vars_pow p k hi)

/-- Earlier-root agreement suffices for evaluating a bounded polynomial. -/
theorem polynomialValue_eq_of_agree_below {p : Polynomial σ} {bound : ℕ}
    (hp : DependsBelow p bound) (x : σ → ℝ) {r s : ℕ → ℝ}
    (hrs : ∀ i < bound, r i = s i) : polynomialValue x r p = polynomialValue x s p := by
  apply MvPolynomial.eval₂Hom_congr' rfl _ rfl
  intro i hi _
  cases i with
  | inl i => rfl
  | inr i => exact hrs i (hp i hi)

/-- All radicands depend only on roots preceding their own output index. -/
def Triangular : Program σ → ℕ → Prop
  | [], _ => True
  | p :: ps, start => DependsBelow p start ∧ Triangular ps (start + 1)

/-- Root equations are evaluated using the final assignment, rather than
intermediate states of the sequential evaluator. -/
def Satisfies (x : σ → ℝ) (roots : ℕ → ℝ) : Program σ → ℕ → Prop
  | [], _ => True
  | p :: ps, start =>
      roots start = Real.sqrt (polynomialValue x roots p) ∧ Satisfies x roots ps (start + 1)

theorem triangular_append (ps qs : Program σ) (start : ℕ) :
    Triangular (ps ++ qs) start ↔ Triangular ps start ∧ Triangular qs (start + ps.length) := by
  induction ps generalizing start with
  | nil => simp [Triangular]
  | cons p ps ih =>
      simp only [List.cons_append, Triangular, ih, List.length_cons]
      simp only [Nat.add_left_comm, Nat.add_comm, and_assoc]

theorem satisfies_append (ps qs : Program σ) (start : ℕ) (x : σ → ℝ) (roots : ℕ → ℝ) :
    Satisfies x roots (ps ++ qs) start ↔
      Satisfies x roots ps start ∧ Satisfies x roots qs (start + ps.length) := by
  induction ps generalizing start with
  | nil => simp [Satisfies]
  | cons p ps ih =>
      simp only [List.cons_append, Satisfies, ih, List.length_cons]
      simp only [Nat.add_left_comm, Nat.add_comm, and_assoc]

/-- Read any equation by its position in the finite program. -/
theorem Satisfies.get {ps : Program σ} {start : ℕ} {x : σ → ℝ} {roots : ℕ → ℝ}
    (hsat : Satisfies x roots ps start) (i : Fin ps.length) :
    roots (start + i.val) = Real.sqrt (polynomialValue x roots (ps.get i)) := by
  induction ps generalizing start with
  | nil => exact Fin.elim0 i
  | cons p ps ih =>
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa using hsat.1
      · simpa only [List.get_cons_succ, Fin.val_succ, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using ih hsat.2 j

/-- Evaluate in order, replacing only the newly computed root coordinate. -/
def run : Program σ → ℕ → (σ → ℝ) → (ℕ → ℝ) → ℕ → ℝ
  | [], _, _, roots => roots
  | p :: ps, start, x, roots =>
      run ps (start + 1) x
        (Function.update roots start (Real.sqrt (polynomialValue x roots p)))

theorem run_eq_below (ps : Program σ) (start : ℕ) (x : σ → ℝ) (roots : ℕ → ℝ)
    {i : ℕ} (hi : i < start) : run ps start x roots i = roots i := by
  induction ps generalizing start roots with
  | nil => rfl
  | cons p ps ih =>
      rw [run, ih _ _ (by omega)]
      exact Function.update_of_ne (Nat.ne_of_lt hi) _ _

/-- The sequential evaluator solves every generated triangular equation.
No solution assignment is assumed or selected by choice. -/
theorem run_satisfies (ps : Program σ) (start : ℕ) (x : σ → ℝ) (roots : ℕ → ℝ)
    (htri : Triangular ps start) : Satisfies x (run ps start x roots) ps start := by
  induction ps generalizing start roots with
  | nil => trivial
  | cons p ps ih =>
      rcases htri with ⟨hp, hps⟩
      let updated := Function.update roots start (Real.sqrt (polynomialValue x roots p))
      change run ps (start + 1) x updated start =
          Real.sqrt (polynomialValue x (run ps (start + 1) x updated) p) ∧ _
      refine ⟨?_, ih _ _ hps⟩
      rw [run_eq_below ps (start + 1) x updated (by omega)]
      rw [show updated start = Real.sqrt (polynomialValue x roots p) from
        Function.update_self _ _ _]
      congr 1
      apply polynomialValue_eq_of_agree_below hp
      intro i hi
      rw [run_eq_below ps (start + 1) x updated (by omega)]
      exact (Function.update_of_ne (Nat.ne_of_lt hi) _ _).symm

end

end Stability.Simulation.RadicalProgram
