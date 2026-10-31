import Stability.Simulation.CompiledFormulaLift
import Mathlib.Data.List.Forall2

/-!
# Polynomial formulas remain exact away from the root graph

A formula with no absolute-value nodes allocates no roots. Its extracted
value is therefore correct for every assignment of the auxiliary
variables, even when other members of the family contain radicals.
This ensures that the monitor's clock and oscillator are not perturbed
by the algebraic lift.
-/

namespace Stability.Simulation.AbsFormula

noncomputable section

open RadicalProgram

variable {σ : Type*}

theorem smoothEval_eq_eval_of_radicalCount_eq_zero (e : AbsFormula σ)
    (he : radicalCount e = 0) (L : ℝ) (x : σ → ℝ) : smoothEval L x e = eval x e := by
  induction e with
  | coordinate i => rfl
  | constant c => rfl
  | add e f ihE ihF =>
      obtain ⟨he, hf⟩ := Nat.add_eq_zero_iff.mp he
      simp only [smoothEval, eval, ihE he, ihF hf]
  | mul e f ihE ihF =>
      obtain ⟨he, hf⟩ := Nat.add_eq_zero_iff.mp he
      simp only [smoothEval, eval, ihE he, ihF hf]
  | abs e _ => simp [radicalCount] at he

theorem extractRadicals_value_of_radicalCount_eq_zero (L : MvPolynomial σ ℚ)
    (e : AbsFormula σ) (start : ℕ) (x : σ → ℝ) (roots : ℕ → ℝ)
    (hL : 0 < polynomialValue x L) (he : radicalCount e = 0) :
    PowerFraction.value (polynomialValue x L) (point x roots)
      (extractRadicals L e start).result = smoothEval (polynomialValue x L) x e := by
  apply extractRadicals_value L e start x roots hL
  have hnil : (extractRadicals L e start).program = [] := by
    apply List.length_eq_zero_iff.mp
    rw [extractRadicals_length, he]
  simp [hnil, Satisfies]

theorem extractRadicalFamily_polynomial_values (L : MvPolynomial σ ℚ)
    (es : List (AbsFormula σ)) (start : ℕ) (x : σ → ℝ) (roots : ℕ → ℝ)
    (hL : 0 < polynomialValue x L) :
    List.Forall₂ (fun e f ↦ radicalCount e = 0 →
      PowerFraction.value (polynomialValue x L) (point x roots) f =
        smoothEval (polynomialValue x L) x e)
      es (extractRadicalFamily L es start).results := by
  induction es generalizing start with
  | nil => exact .nil
  | cons e es ih =>
      exact .cons (extractRadicals_value_of_radicalCount_eq_zero L e start x roots hL)
        (ih (start + (extractRadicals L e start).program.length))

end

end Stability.Simulation.AbsFormula

namespace Stability.Simulation.CompiledFormulaLift

noncomputable section

open AbsFormula RadicalProgram

variable {σ : Type*}

theorem outputAt_value_of_radicalCount_eq_zero (L : MvPolynomial σ ℚ)
    (es : List (AbsFormula σ)) (x : σ → ℝ) (hL : 0 < polynomialValue x L)
    (roots : Fin (finiteRadicalFamily L es).rootCount → ℝ) (i : Fin es.length)
    (he : radicalCount (es.get i) = 0) :
    PowerFraction.value (polynomialValue x L) (Sum.elim x roots) (outputAt L es i) =
      smoothEval (polynomialValue x L) x (es.get i) := by
  let E := extractRadicalFamily L es 0
  have hi : i.val < E.results.length := by
    rw [(extractRadicalFamily_lengths L es 0).2]
    exact i.isLt
  have hvalue := (extractRadicalFamily_polynomial_values L es 0 x (extendRoots roots) hL).get
    i.isLt hi he
  have hbound : DependsBelow (E.results.get ⟨i.val, hi⟩).numerator E.program.length := by
    simpa only [zero_add] using (extractRadicalFamily_wellFormed L es 0).2 _
      (List.get_mem E.results ⟨i.val, hi⟩)
  have hfinite := finiteFraction_value hbound (polynomialValue x L) x (extendRoots roots)
  have hget : outputAt L es i = finiteFraction E.program.length (E.results.get ⟨i.val, hi⟩) := by
    simp [outputAt, finiteRadicalFamily, E, List.get_eq_getElem]
  rw [hget]
  simpa only [extendRoots_val] using hfinite.trans hvalue

/-- Exactness holds for every auxiliary assignment, independently of
the constraints imposed by other formulas in the family. -/
theorem baseFraction_value_of_radicalCount_eq_zero (L : MvPolynomial σ ℚ)
    (es : List (AbsFormula σ)) (x : σ → ℝ) (hL : 0 < polynomialValue x L)
    (w : Fin (finiteRadicalFamily L es).rootCount → ℝ) (i : Fin es.length)
    (he : radicalCount (es.get i) = 0) :
    PolynomialFraction.value (Sum.elim x w) (baseFraction L es i) = eval x (es.get i) := by
  have hvalue := outputAt_value_of_radicalCount_eq_zero L es x hL
    (fun j ↦ w j ^ 2) i he
  rw [smoothEval_eq_eval_of_radicalCount_eq_zero _ he] at hvalue
  change polynomialValue (Sum.elim x w)
      (RadicalProgram.squareRootsPolynomial (outputAt L es i).numerator) /
      polynomialValue (Sum.elim x w)
        (MvPolynomial.rename Sum.inl L ^ (outputAt L es i).exponent) = _
  rw [RadicalProgram.squareRootsPolynomial_value]
  have hden : polynomialValue (Sum.elim x w)
      (MvPolynomial.rename Sum.inl L ^ (outputAt L es i).exponent) =
      polynomialValue x L ^ (outputAt L es i).exponent := by
    simp [AbsFormula.polynomialValue, MvPolynomial.eval₂_rename, Function.comp_def]
  rw [hden]
  exact hvalue

end

end Stability.Simulation.CompiledFormulaLift
