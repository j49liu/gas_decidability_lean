import Stability.Simulation.FormulaSmoothing
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Syntactic resource bounds for absolute-value formulas

The input parameter in the simulation construction changes rational constants,
not formula shape. This module proves that the degree bounds for the
smoothing majorants and the number of introduced square roots depend only
on that shape. Every absolute-value node is counted, including nodes whose
values might simplify for special constants.

This is not yet a resource bound for the entire algebraization compiler:
the later radical-defect and denominator-clearing constructions are still
separate obligations.
-/

namespace Stability.Simulation.AbsFormula

variable {σ : Type*}

/-- A common upper degree bound for both smoothing majorants. -/
def majorantDegreeBound : AbsFormula σ → ℕ
  | .coordinate _ => 2
  | .constant _ => 0
  | .add e f => max (majorantDegreeBound e) (majorantDegreeBound f)
  | .mul e f => majorantDegreeBound e + majorantDegreeBound f
  | .abs e => majorantDegreeBound e

/-- Count the radicals introduced by inside-out smoothing, without
simplifying any node based on the values of its constants. -/
def radicalCount : AbsFormula σ → ℕ
  | .coordinate _ => 0
  | .constant _ => 0
  | .add e f => radicalCount e + radicalCount f
  | .mul e f => radicalCount e + radicalCount f
  | .abs e => radicalCount e + 1

/-- Change rational constants while retaining every syntactic operation. -/
def mapConstants (f : ℚ → ℚ) : AbsFormula σ → AbsFormula σ
  | .coordinate i => .coordinate i
  | .constant c => .constant (f c)
  | .add e g => .add (mapConstants f e) (mapConstants f g)
  | .mul e g => .mul (mapConstants f e) (mapConstants f g)
  | .abs e => .abs (mapConstants f e)

/-- Retain the syntax tree and coordinate labels but forget the value of
each constant occurrence separately. This permits input families in which
different occurrences of the same original constant change differently. -/
def eraseConstants : AbsFormula σ → AbsFormula σ
  | .coordinate i => .coordinate i
  | .constant _ => .constant 0
  | .add e f => .add (eraseConstants e) (eraseConstants f)
  | .mul e f => .mul (eraseConstants e) (eraseConstants f)
  | .abs e => .abs (eraseConstants e)

theorem majorantDegreeBound_eraseConstants (e : AbsFormula σ) :
    majorantDegreeBound (eraseConstants e) = majorantDegreeBound e := by
  induction e <;> simp_all [majorantDegreeBound, eraseConstants]

theorem radicalCount_eraseConstants (e : AbsFormula σ) :
    radicalCount (eraseConstants e) = radicalCount e := by
  induction e <;> simp_all [radicalCount, eraseConstants]

/-- Equal shape fixes both resource bounds, even when constants vary
independently at different positions in the formula. -/
theorem resources_eq_of_eraseConstants_eq {e f : AbsFormula σ}
    (hshape : eraseConstants e = eraseConstants f) :
    majorantDegreeBound e = majorantDegreeBound f ∧
      radicalCount e = radicalCount f := by
  constructor
  · simpa only [majorantDegreeBound_eraseConstants] using
      congrArg majorantDegreeBound hshape
  · simpa only [radicalCount_eraseConstants] using congrArg radicalCount hshape

/-- The majorant degree bound is independent of all constant values. -/
theorem majorantDegreeBound_mapConstants (f : ℚ → ℚ) (e : AbsFormula σ) :
    majorantDegreeBound (mapConstants f e) = majorantDegreeBound e := by
  induction e <;> simp_all [majorantDegreeBound, mapConstants]

/-- The number of radicals is independent of all constant values. -/
theorem radicalCount_mapConstants (f : ℚ → ℚ) (e : AbsFormula σ) :
    radicalCount (mapConstants f e) = radicalCount e := by
  induction e <;> simp_all [radicalCount, mapConstants]

/-- Both actual rational majorant polynomials obey the syntactic bound. -/
theorem majorants_totalDegree_le (e : AbsFormula σ) :
    (majorants e).1.totalDegree ≤ majorantDegreeBound e ∧
      (majorants e).2.totalDegree ≤ majorantDegreeBound e := by
  induction e with
  | coordinate i =>
    simp only [majorants, majorantDegreeBound, MvPolynomial.totalDegree_zero,
      Nat.zero_le, and_true]
    exact (MvPolynomial.totalDegree_add _ _).trans (by simp)
  | constant c =>
    simp only [majorants, majorantDegreeBound, MvPolynomial.totalDegree_C,
      MvPolynomial.totalDegree_zero, le_refl, and_self]
  | add e f he hf =>
    simp only [majorants, majorantDegreeBound]
    exact ⟨(MvPolynomial.totalDegree_add _ _).trans (max_le_max he.1 hf.1),
      (MvPolynomial.totalDegree_add _ _).trans (max_le_max he.2 hf.2)⟩
  | mul e f he hf =>
    simp only [majorants, majorantDegreeBound]
    refine ⟨(MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add he.1 hf.1), ?_⟩
    apply (MvPolynomial.totalDegree_add _ _).trans
    exact max_le
      ((MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add he.2 hf.1))
      ((MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add he.1 hf.2))
  | abs e he =>
    simp only [majorants, majorantDegreeBound]
    exact ⟨(MvPolynomial.totalDegree_add _ _).trans (max_le he.1 (by simp)),
      (MvPolynomial.totalDegree_add _ _).trans (max_le he.2 (by simp))⟩

/-- The same fixed degree bound applies after any substitution of rational
constant values. This is the fixed-resource fact needed for input families. -/
theorem majorants_mapConstants_totalDegree_le (f : ℚ → ℚ) (e : AbsFormula σ) :
    (majorants (mapConstants f e)).1.totalDegree ≤ majorantDegreeBound e ∧
      (majorants (mapConstants f e)).2.totalDegree ≤ majorantDegreeBound e := by
  simpa only [majorantDegreeBound_mapConstants] using
    majorants_totalDegree_le (mapConstants f e)

end Stability.Simulation.AbsFormula
