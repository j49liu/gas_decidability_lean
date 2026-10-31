import Stability.Simulation.FormulaPrecision

/-!
# Polynomial numerators with powers of a common denominator

Sums and products of these fractions retain a power of one polynomial
denominator. One smoothed absolute-value node can then be written as a
new square root divided by a positive power of that denominator. Its
polynomial radicand is at least one whenever the denominator is.

This is the local algebra for extracting the triangular radical program,
not yet the recursive extraction of the entire program.
-/

namespace Stability.Simulation

/-- A polynomial numerator together with its denominator exponent. -/
structure PowerFraction (σ : Type*) where
  numerator : MvPolynomial σ ℚ
  exponent : ℕ

namespace PowerFraction

noncomputable section

variable {σ : Type*}

/-- Evaluate with a specified common real denominator. -/
def value (L : ℝ) (x : σ → ℝ) (f : PowerFraction σ) : ℝ :=
  AbsFormula.polynomialValue x f.numerator / L ^ f.exponent

def ofPolynomial (p : MvPolynomial σ ℚ) : PowerFraction σ := ⟨p, 0⟩

/-- Addition uses the sum of exponents as a common denominator. This
deliberately avoids cancellation depending on the coefficient values. -/
def add (L : MvPolynomial σ ℚ) (f g : PowerFraction σ) : PowerFraction σ :=
  ⟨f.numerator * L ^ g.exponent + g.numerator * L ^ f.exponent,
    f.exponent + g.exponent⟩

def mul (f g : PowerFraction σ) : PowerFraction σ :=
  ⟨f.numerator * g.numerator, f.exponent + g.exponent⟩

theorem value_ofPolynomial (L : ℝ) (x : σ → ℝ) (p : MvPolynomial σ ℚ) :
    value L x (ofPolynomial p) = AbsFormula.polynomialValue x p := by
  simp [value, ofPolynomial]

theorem value_add (L : MvPolynomial σ ℚ) (f g : PowerFraction σ)
    (x : σ → ℝ) (hL : AbsFormula.polynomialValue x L ≠ 0) :
    value (AbsFormula.polynomialValue x L) x (add L f g) =
      value (AbsFormula.polynomialValue x L) x f +
        value (AbsFormula.polynomialValue x L) x g := by
  simp only [value, add, AbsFormula.polynomialValue,
    MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow, pow_add]
  dsimp only [AbsFormula.polynomialValue] at hL
  field_simp [hL]

theorem value_mul (L : ℝ) (f g : PowerFraction σ) (x : σ → ℝ) :
    value L x (mul f g) = value L x f * value L x g := by
  simp only [value, mul, AbsFormula.polynomialValue,
    MvPolynomial.eval₂_mul, pow_add, div_mul_div_comm]

/-- With exponent `k+1`, the inner numerator is multiplied by `L`.
The resulting radicand is polynomial even when the original exponent
was zero. -/
def smoothingRadicand (L : MvPolynomial σ ℚ) (f : PowerFraction σ) :
    MvPolynomial σ ℚ := f.numerator ^ 2 * L ^ 2 + L ^ (2 * f.exponent)

theorem smoothingRadicand_value (L : MvPolynomial σ ℚ) (f : PowerFraction σ)
    (x : σ → ℝ) :
    AbsFormula.polynomialValue x (smoothingRadicand L f) =
      (AbsFormula.polynomialValue x f.numerator) ^ 2 *
        (AbsFormula.polynomialValue x L) ^ 2 +
          (AbsFormula.polynomialValue x L) ^ (2 * f.exponent) := by
  simp [smoothingRadicand, AbsFormula.polynomialValue]

/-- The polynomial radicand is globally at least one if the common
denominator is. This supplies the protected denominator in the lift. -/
theorem one_le_smoothingRadicand (L : MvPolynomial σ ℚ) (f : PowerFraction σ)
    (x : σ → ℝ) (hL : 1 ≤ AbsFormula.polynomialValue x L) :
    1 ≤ AbsFormula.polynomialValue x (smoothingRadicand L f) := by
  rw [smoothingRadicand_value]
  have hpower : 1 ≤ (AbsFormula.polynomialValue x L) ^ (2 * f.exponent) := one_le_pow₀ hL
  have hnonneg := mul_nonneg (sq_nonneg (AbsFormula.polynomialValue x f.numerator))
    (sq_nonneg (AbsFormula.polynomialValue x L))
  linarith

/-- The new radical exactly represents the smoothed absolute value,
with no approximation introduced in this algebraic step. -/
theorem sqrt_smoothingRadicand_div_eq (L : MvPolynomial σ ℚ) (f : PowerFraction σ)
    (x : σ → ℝ) (hL : 0 < AbsFormula.polynomialValue x L) :
    Real.sqrt (AbsFormula.polynomialValue x (smoothingRadicand L f)) /
        (AbsFormula.polynomialValue x L) ^ (f.exponent + 1) =
      Real.sqrt ((value (AbsFormula.polynomialValue x L) x f) ^ 2 +
        ((AbsFormula.polynomialValue x L)⁻¹) ^ 2) := by
  let l := AbsFormula.polynomialValue x L
  let p := AbsFormula.polynomialValue x f.numerator
  have hl : l ≠ 0 := ne_of_gt hL
  have hpow : l ^ (2 * f.exponent) = (l ^ f.exponent) ^ 2 := by
    rw [Nat.mul_comm 2 f.exponent, pow_mul]
  have hquotient :
      (p ^ 2 * l ^ 2 + l ^ (2 * f.exponent)) / (l ^ (f.exponent + 1)) ^ 2 =
        (p / l ^ f.exponent) ^ 2 + (l⁻¹) ^ 2 := by
    rw [hpow, pow_succ]
    field_simp
    ring
  rw [smoothingRadicand_value]
  change Real.sqrt (p ^ 2 * l ^ 2 + l ^ (2 * f.exponent)) / l ^ (f.exponent + 1) = _
  rw [← Real.sqrt_sq (show 0 ≤ l ^ (f.exponent + 1) by positivity),
    ← Real.sqrt_div' _ (sq_nonneg _), hquotient]
  rfl

end

end PowerFraction

end Stability.Simulation
