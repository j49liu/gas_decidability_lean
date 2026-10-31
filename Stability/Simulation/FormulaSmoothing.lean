import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Polynomial bounds for smoothing absolute-value formulas

Reference: the structural-induction argument of Lemma 5.1,
https://arxiv.org/html/2609.22058v2#S5.

The syntax contains rational constants, coordinates, addition,
multiplication, and absolute value. Smoothing replaces each absolute value
from the inside out by `sqrt (t^2 + L⁻¹^2)`. The two rational polynomials
constructed below bound both evaluations and their difference. They do not
depend on the precision `L`.

These are explicit recursive constructions and semantic correctness
theorems. Syntactic degree bounds are proved in `FormulaResources`;
primitive-recursive raw encodings remain a separate obligation.
-/

namespace Stability.Simulation

/-- Finite formulas with absolute value and rational constants. -/
inductive AbsFormula (σ : Type*) where
  | coordinate : σ → AbsFormula σ
  | constant : ℚ → AbsFormula σ
  | add : AbsFormula σ → AbsFormula σ → AbsFormula σ
  | mul : AbsFormula σ → AbsFormula σ → AbsFormula σ
  | abs : AbsFormula σ → AbsFormula σ

noncomputable section

namespace AbsFormula

variable {σ : Type*}

/-- The ordinary real value of a formula. -/
def eval (x : σ → ℝ) : AbsFormula σ → ℝ
  | .coordinate i => x i
  | .constant c => c
  | .add e f => eval x e + eval x f
  | .mul e f => eval x e * eval x f
  | .abs e => |eval x e|

/-- Inside-out smoothing at a specified positive precision. -/
def smoothEval (L : ℝ) (x : σ → ℝ) : AbsFormula σ → ℝ
  | .coordinate i => x i
  | .constant c => c
  | .add e f => smoothEval L x e + smoothEval L x f
  | .mul e f => smoothEval L x e * smoothEval L x f
  | .abs e => Real.sqrt ((smoothEval L x e) ^ 2 + (L⁻¹) ^ 2)

/-- A value majorant and an error majorant, both rational polynomials.
The construction is independent of the smoothing precision. -/
def majorants : AbsFormula σ → MvPolynomial σ ℚ × MvPolynomial σ ℚ
  | .coordinate i => (1 + MvPolynomial.X i ^ 2, 0)
  | .constant c => (MvPolynomial.C (1 + |c|), 0)
  | .add e f =>
      ((majorants e).1 + (majorants f).1, (majorants e).2 + (majorants f).2)
  | .mul e f =>
      ((majorants e).1 * (majorants f).1,
        (majorants e).2 * (majorants f).1 + (majorants e).1 * (majorants f).2)
  | .abs e => ((majorants e).1 + 1, (majorants e).2 + 1)

/-- Evaluate a rational majorant at real coordinates. -/
def polynomialValue (x : σ → ℝ) (p : MvPolynomial σ ℚ) : ℝ :=
  p.eval₂ (algebraMap ℚ ℝ) x

private theorem sqrt_smoothing_bounds {L : ℝ} (hL : 1 ≤ L) (t : ℝ) :
    |t| ≤ Real.sqrt (t ^ 2 + (L⁻¹) ^ 2) ∧
      Real.sqrt (t ^ 2 + (L⁻¹) ^ 2) ≤ |t| + L⁻¹ := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hinv : 0 < L⁻¹ := inv_pos.mpr hLpos
  have hsqrt := Real.sq_sqrt (by positivity : 0 ≤ t ^ 2 + (L⁻¹) ^ 2)
  constructor
  · exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (L⁻¹)])
  · have hnonneg := Real.sqrt_nonneg (t ^ 2 + (L⁻¹) ^ 2)
    nlinarith [sq_abs t, abs_nonneg t, mul_nonneg (abs_nonneg t) hinv.le]

/-- The explicit majorants are nonnegative, bound the original and
smoothed formulas, and bound the smoothing error by `V / L`.
The precision may vary with the evaluation point: only its value here
is used, and the polynomials themselves do not depend on it. -/
theorem majorants_correct (e : AbsFormula σ) (x : σ → ℝ)
    {L : ℝ} (hL : 1 ≤ L) :
    0 ≤ polynomialValue x (majorants e).1 ∧
    0 ≤ polynomialValue x (majorants e).2 ∧
    |eval x e| ≤ polynomialValue x (majorants e).1 ∧
    |smoothEval L x e| ≤ polynomialValue x (majorants e).1 ∧
    |smoothEval L x e - eval x e| ≤ polynomialValue x (majorants e).2 * L⁻¹ := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hinv : 0 ≤ L⁻¹ := (inv_pos.mpr hLpos).le
  have hinvOne : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL
  induction e with
  | coordinate i =>
    simp only [majorants, polynomialValue, MvPolynomial.eval₂_add,
      MvPolynomial.eval₂_one, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X,
      MvPolynomial.eval₂_zero, eval, smoothEval, sub_self, abs_zero, zero_mul]
    have hbound : |x i| ≤ 1 + (x i) ^ 2 := by
      nlinarith [sq_nonneg (|x i| - 1), sq_abs (x i)]
    exact ⟨by positivity, le_rfl, hbound, hbound, le_rfl⟩
  | constant c =>
    simp only [majorants, polynomialValue, MvPolynomial.eval₂_C,
      MvPolynomial.eval₂_zero, eval, smoothEval, sub_self, abs_zero, zero_mul]
    norm_num
    positivity
  | add e f he hf =>
    rcases he with ⟨heU, heV, heRaw, heSmooth, heError⟩
    rcases hf with ⟨hfU, hfV, hfRaw, hfSmooth, hfError⟩
    simp only [majorants, polynomialValue, MvPolynomial.eval₂_add, eval, smoothEval]
    change 0 ≤ polynomialValue x (majorants e).1 + polynomialValue x (majorants f).1 ∧
      0 ≤ polynomialValue x (majorants e).2 + polynomialValue x (majorants f).2 ∧ _
    refine ⟨add_nonneg heU hfU, add_nonneg heV hfV,
      (abs_add_le _ _).trans (add_le_add heRaw hfRaw),
      (abs_add_le _ _).trans (add_le_add heSmooth hfSmooth), ?_⟩
    calc
      |smoothEval L x e + smoothEval L x f - (eval x e + eval x f)| =
          |(smoothEval L x e - eval x e) + (smoothEval L x f - eval x f)| := by ring_nf
      _ ≤ |smoothEval L x e - eval x e| + |smoothEval L x f - eval x f| := abs_add_le _ _
      _ ≤ polynomialValue x (majorants e).2 * L⁻¹ +
          polynomialValue x (majorants f).2 * L⁻¹ := add_le_add heError hfError
      _ = _ := by simp [polynomialValue]; ring
  | mul e f he hf =>
    rcases he with ⟨heU, heV, heRaw, heSmooth, heError⟩
    rcases hf with ⟨hfU, hfV, hfRaw, hfSmooth, hfError⟩
    simp only [majorants, polynomialValue, MvPolynomial.eval₂_add,
      MvPolynomial.eval₂_mul, eval, smoothEval, abs_mul]
    change 0 ≤ polynomialValue x (majorants e).1 * polynomialValue x (majorants f).1 ∧
      0 ≤ polynomialValue x (majorants e).2 * polynomialValue x (majorants f).1 +
        polynomialValue x (majorants e).1 * polynomialValue x (majorants f).2 ∧ _
    refine ⟨mul_nonneg heU hfU, add_nonneg (mul_nonneg heV hfU) (mul_nonneg heU hfV),
      mul_le_mul heRaw hfRaw (abs_nonneg _) heU,
      mul_le_mul heSmooth hfSmooth (abs_nonneg _) heU, ?_⟩
    calc
      |smoothEval L x e * smoothEval L x f - eval x e * eval x f| =
          |(smoothEval L x e - eval x e) * smoothEval L x f +
            eval x e * (smoothEval L x f - eval x f)| := by congr 1; ring
      _ ≤ |smoothEval L x e - eval x e| * |smoothEval L x f| +
          |eval x e| * |smoothEval L x f - eval x f| := by
        simpa only [abs_mul] using abs_add_le
          ((smoothEval L x e - eval x e) * smoothEval L x f)
          (eval x e * (smoothEval L x f - eval x f))
      _ ≤ (polynomialValue x (majorants e).2 * L⁻¹) * polynomialValue x (majorants f).1 +
          polynomialValue x (majorants e).1 * (polynomialValue x (majorants f).2 * L⁻¹) :=
        add_le_add (mul_le_mul heError hfSmooth (abs_nonneg _) (mul_nonneg heV hinv))
          (mul_le_mul heRaw hfError (abs_nonneg _) heU)
      _ = _ := by simp [polynomialValue]; ring
  | abs e he =>
    rcases he with ⟨heU, heV, heRaw, heSmooth, heError⟩
    obtain ⟨hlower, hupper⟩ := sqrt_smoothing_bounds hL (smoothEval L x e)
    have hroot := Real.sqrt_nonneg ((smoothEval L x e) ^ 2 + (L⁻¹) ^ 2)
    have hdiff : _root_.abs (Real.sqrt ((smoothEval L x e) ^ 2 + (L⁻¹) ^ 2) -
        |smoothEval L x e|) ≤ L⁻¹ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hlower)]
      linarith
    simp only [majorants, polynomialValue, MvPolynomial.eval₂_add,
      MvPolynomial.eval₂_one, eval, smoothEval, abs_abs, abs_of_nonneg hroot]
    change 0 ≤ polynomialValue x (majorants e).1 + 1 ∧
      0 ≤ polynomialValue x (majorants e).2 + 1 ∧ _
    refine ⟨by positivity, by positivity,
      heRaw.trans (le_add_of_nonneg_right zero_le_one),
      hupper.trans (add_le_add heSmooth hinvOne), ?_⟩
    calc
      _root_.abs (Real.sqrt ((smoothEval L x e) ^ 2 + (L⁻¹) ^ 2) - |eval x e|) ≤
          _root_.abs (Real.sqrt ((smoothEval L x e) ^ 2 + (L⁻¹) ^ 2) - |smoothEval L x e|) +
            _root_.abs (|smoothEval L x e| - |eval x e|) := abs_sub_le _ _ _
      _ ≤ L⁻¹ + |smoothEval L x e - eval x e| :=
        add_le_add hdiff (abs_abs_sub_abs_le _ _)
      _ ≤ L⁻¹ + polynomialValue x (majorants e).2 * L⁻¹ := add_le_add le_rfl heError
      _ = _ := by simp [polynomialValue]; ring

end AbsFormula

end

end Stability.Simulation
