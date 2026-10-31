import Stability.Simulation.RadicalSmoothness

/-!
# Polynomial constraints for the fourth-root lift

Every finite root variable is replaced by the square of a new auxiliary
coordinate. This is literal polynomial substitution. The resulting
radicands stay at least one everywhere, and the smooth canonical
fourth-root graph satisfies all quartic constraints exactly.

This module constructs the constraint polynomials, not yet the rational
vector field that preserves them.
-/

namespace Stability.Simulation

noncomputable section

namespace RadicalProgram

variable {σ ι : Type*}

/-- Base coordinates are unchanged; auxiliary root coordinates are squared. -/
def squareRootVariable : σ ⊕ ι → MvPolynomial (σ ⊕ ι) ℚ
  | .inl i => MvPolynomial.X (.inl i)
  | .inr i => MvPolynomial.X (.inr i) ^ 2

def squareRootsPolynomial (p : MvPolynomial (σ ⊕ ι) ℚ) : MvPolynomial (σ ⊕ ι) ℚ :=
  MvPolynomial.bind₁ squareRootVariable p

theorem squareRootsPolynomial_value (p : MvPolynomial (σ ⊕ ι) ℚ)
    (x : σ → ℝ) (w : ι → ℝ) :
    AbsFormula.polynomialValue (Sum.elim x w) (squareRootsPolynomial p) =
      AbsFormula.polynomialValue (Sum.elim x (fun i ↦ w i ^ 2)) p := by
  unfold squareRootsPolynomial AbsFormula.polynomialValue
  change MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (Sum.elim x w)
    (MvPolynomial.bind₁ squareRootVariable p) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  apply MvPolynomial.eval₂Hom_congr' rfl _ rfl
  intro i _ _
  cases i <;> simp [squareRootVariable]

end RadicalProgram

namespace AbsFormula

variable {σ : Type*}

/-- Actual rational constraint polynomials in the finite lifted state space. -/
def liftRadicand (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ))
    (i : Fin (finiteRadicalFamily L es).rootCount) :
    MvPolynomial (σ ⊕ Fin (finiteRadicalFamily L es).rootCount) ℚ :=
  RadicalProgram.squareRootsPolynomial ((finiteRadicalFamily L es).radicands i)

theorem liftRadicand_value (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ))
    (x : σ → ℝ) (w : Fin (finiteRadicalFamily L es).rootCount → ℝ)
    (i : Fin (finiteRadicalFamily L es).rootCount) :
    polynomialValue (Sum.elim x w) (liftRadicand L es i) =
      polynomialValue (Sum.elim x (fun j ↦ w j ^ 2))
        ((finiteRadicalFamily L es).radicands i) :=
  RadicalProgram.squareRootsPolynomial_value _ x w

/-- The denominators used in the later lift cannot vanish, including far
from the exact root graph and for negative auxiliary coordinates. -/
theorem one_le_liftRadicand (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ))
    (x : σ → ℝ) (hL : 1 ≤ polynomialValue x L)
    (w : Fin (finiteRadicalFamily L es).rootCount → ℝ)
    (i : Fin (finiteRadicalFamily L es).rootCount) :
    1 ≤ polynomialValue (Sum.elim x w) (liftRadicand L es i) := by
  rw [liftRadicand_value]
  exact finiteRadicalFamily_radicands_one_le L es x (fun j ↦ w j ^ 2) hL i

/-- The explicitly generated smooth graph satisfies every quartic
constraint; the graph point is not postulated as a solution of equations. -/
theorem finiteLiftRoots_fourth (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ))
    (x : σ → ℝ) (hL : 1 ≤ polynomialValue x L)
    (i : Fin (finiteRadicalFamily L es).rootCount) :
    (finiteLiftRoots L es x i) ^ 4 =
      polynomialValue (Sum.elim x (finiteLiftRoots L es x)) (liftRadicand L es i) := by
  have hsquares : (fun j ↦ (finiteLiftRoots L es x j) ^ 2) =
      finiteRadicalRoots L es x := funext (finiteLiftRoots_sq L es x hL)
  calc
    _ = ((finiteLiftRoots L es x i) ^ 2) ^ 2 := by ring
    _ = (finiteRadicalRoots L es x i) ^ 2 := by rw [finiteLiftRoots_sq L es x hL]
    _ = polynomialValue (Sum.elim x (finiteRadicalRoots L es x))
          ((finiteRadicalFamily L es).radicands i) := by
      rw [finiteRadicalRoots_equation L es x i]
      exact Real.sq_sqrt (zero_le_one.trans
        (finiteRadicalFamily_radicands_one_le L es x (finiteRadicalRoots L es x) hL i))
    _ = _ := by rw [liftRadicand_value, hsquares]

end AbsFormula

end

end Stability.Simulation
