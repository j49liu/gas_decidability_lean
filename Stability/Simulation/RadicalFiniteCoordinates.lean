import Stability.Simulation.RadicalProgram
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Restricting a root program to its finite coordinates

Natural root indices simplify concatenation, but a polynomial vector
field needs a finite coordinate type. The restriction below sends an
out-of-range variable to zero. For a polynomial satisfying the proved
dependency bound, no such variable occurs, so renaming back recovers the
original polynomial exactly, with unchanged degree and evaluation.

The construction also handles an empty root range. It does not choose a
default element of `Fin 0` or assume that at least one radical occurs.
-/

namespace Stability.Simulation.RadicalProgram

noncomputable section

variable {σ : Type*}

def includeRoot (bound : ℕ) : σ ⊕ Fin bound → σ ⊕ ℕ := Sum.map id Fin.val

theorem includeRoot_injective (bound : ℕ) : Function.Injective (includeRoot (σ := σ) bound) :=
  Sum.map_injective.mpr ⟨Function.injective_id, Fin.val_injective⟩

/-- Replace a root index by its finite counterpart, or zero outside the range. -/
def finiteVariable (bound : ℕ) : σ ⊕ ℕ → MvPolynomial (σ ⊕ Fin bound) ℚ
  | .inl i => MvPolynomial.X (.inl i)
  | .inr i => if h : i < bound then MvPolynomial.X (.inr ⟨i, h⟩) else 0

def finitePolynomial (bound : ℕ) (p : Polynomial σ) : MvPolynomial (σ ⊕ Fin bound) ℚ :=
  MvPolynomial.bind₁ (finiteVariable bound) p

@[simp]
theorem finiteVariable_includeRoot (bound : ℕ) (i : σ ⊕ Fin bound) :
    finiteVariable bound (includeRoot bound i) = MvPolynomial.X i := by
  cases i with
  | inl i => rfl
  | inr i => simp [includeRoot, finiteVariable, i.isLt]

theorem finitePolynomial_rename (bound : ℕ) (p : MvPolynomial (σ ⊕ Fin bound) ℚ) :
    finitePolynomial bound (MvPolynomial.rename (includeRoot bound) p) = p := by
  unfold finitePolynomial
  rw [MvPolynomial.bind₁_rename]
  have hmap : finiteVariable (σ := σ) bound ∘ includeRoot bound = MvPolynomial.X := by
    funext i
    exact finiteVariable_includeRoot bound i
  rw [hmap]
  simp

/-- Bounded natural-index polynomials are exactly finite-coordinate polynomials. -/
theorem rename_finitePolynomial {bound : ℕ} {p : Polynomial σ}
    (hp : DependsBelow p bound) :
    MvPolynomial.rename (includeRoot bound) (finitePolynomial bound p) = p := by
  have hvars : (p.vars : Set (σ ⊕ ℕ)) ⊆ Set.range (includeRoot (σ := σ) bound) := by
    intro i hi
    cases i with
    | inl i => exact ⟨Sum.inl i, rfl⟩
    | inr i => exact ⟨Sum.inr ⟨i, hp i hi⟩, rfl⟩
  obtain ⟨q, rfl⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range p
    (includeRoot bound) (includeRoot_injective bound) hvars
  rw [finitePolynomial_rename]

/-- Injective coordinate renaming preserves total degree, including cancellations. -/
theorem totalDegree_rename_eq_of_injective {α β : Type*} (f : α → β)
    (hf : Function.Injective f) (p : MvPolynomial α ℚ) :
    (MvPolynomial.rename f p).totalDegree = p.totalDegree := by
  classical
  apply le_antisymm (MvPolynomial.totalDegree_rename_le f p)
  apply Finset.sup_le
  intro s hs
  have hmem : s.mapDomain f ∈ (MvPolynomial.rename f p).support := by
    rw [MvPolynomial.support_rename_of_injective hf]
    exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
  have hdegree := MvPolynomial.le_totalDegree hmem
  rw [Finsupp.sum_mapDomain_index (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)] at hdegree
  exact hdegree

theorem finitePolynomial_totalDegree {bound : ℕ} {p : Polynomial σ}
    (hp : DependsBelow p bound) : (finitePolynomial bound p).totalDegree = p.totalDegree := by
  rw [← totalDegree_rename_eq_of_injective (includeRoot bound)
    (includeRoot_injective bound), rename_finitePolynomial hp]

/-- Extending a finite root assignment by zero is only an evaluation device. -/
def extendRoots {bound : ℕ} (roots : Fin bound → ℝ) (i : ℕ) : ℝ :=
  if h : i < bound then roots ⟨i, h⟩ else 0

@[simp]
theorem extendRoots_val {bound : ℕ} (roots : Fin bound → ℝ) (i : Fin bound) :
    extendRoots roots i.val = roots i := by
  simp [extendRoots, i.isLt]

theorem finitePolynomial_value {bound : ℕ} {p : Polynomial σ}
    (hp : DependsBelow p bound) (x : σ → ℝ) (roots : Fin bound → ℝ) :
    AbsFormula.polynomialValue (Sum.elim x roots) (finitePolynomial bound p) =
      polynomialValue x (extendRoots roots) p := by
  conv_rhs => rw [← rename_finitePolynomial hp]
  simp only [polynomialValue, AbsFormula.polynomialValue, MvPolynomial.eval₂_rename,
    point, includeRoot, Function.comp_def]
  congr 1
  funext i
  cases i <;> simp

/-- Restricting any full assignment gives the same value of a bounded polynomial. -/
theorem finitePolynomial_value_restrict {bound : ℕ} {p : Polynomial σ}
    (hp : DependsBelow p bound) (x : σ → ℝ) (roots : ℕ → ℝ) :
    AbsFormula.polynomialValue (Sum.elim x (fun i : Fin bound ↦ roots i.val))
      (finitePolynomial bound p) = polynomialValue x roots p := by
  rw [finitePolynomial_value hp]
  apply polynomialValue_eq_of_agree_below hp
  intro i hi
  simp [extendRoots, hi]

/-- All radicands of a triangular program lie in the final finite range. -/
theorem Triangular.dependsBelow_end {ps : Program σ} {start : ℕ}
    (htri : Triangular ps start) :
    ∀ p ∈ ps, DependsBelow p (start + ps.length) := by
  induction ps generalizing start with
  | nil => simp
  | cons p ps ih =>
      intro q hq
      rcases List.mem_cons.mp hq with hq | hq
      · subst q
        exact htri.1.mono (by simp)
      · have h := ih htri.2 q hq
        simpa only [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

end

end Stability.Simulation.RadicalProgram
