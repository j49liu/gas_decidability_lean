import Stability.Simulation.PowerFraction

/-!
# Explicit fractions of rational polynomials

The triangular differential lift divides by its positive radicands as
well as the common precision. Numerator/denominator pairs retain these
factors explicitly. Arithmetic does not cancel factors or choose an
equivalent fraction, so positivity and resource bounds can be checked
from the construction.
-/

namespace Stability.Simulation

/-- A literal polynomial numerator and denominator, before any cancellation. -/
structure PolynomialFraction (σ : Type*) where
  numerator : MvPolynomial σ ℚ
  denominator : MvPolynomial σ ℚ

namespace PolynomialFraction

noncomputable section

open AbsFormula

variable {σ ι : Type*}

def value (x : σ → ℝ) (f : PolynomialFraction σ) : ℝ :=
  polynomialValue x f.numerator / polynomialValue x f.denominator

def ofPolynomial (p : MvPolynomial σ ℚ) : PolynomialFraction σ := ⟨p, 1⟩

def ofPowerFraction (L : MvPolynomial σ ℚ) (f : PowerFraction σ) : PolynomialFraction σ :=
  ⟨f.numerator, L ^ f.exponent⟩

def add (f g : PolynomialFraction σ) : PolynomialFraction σ :=
  ⟨f.numerator * g.denominator + g.numerator * f.denominator,
    f.denominator * g.denominator⟩

def mulPolynomial (p : MvPolynomial σ ℚ) (f : PolynomialFraction σ) : PolynomialFraction σ :=
  ⟨p * f.numerator, f.denominator⟩

def divPolynomial (f : PolynomialFraction σ) (p : MvPolynomial σ ℚ) : PolynomialFraction σ :=
  ⟨f.numerator, f.denominator * p⟩

def sum : List (PolynomialFraction σ) → PolynomialFraction σ
  | [] => ofPolynomial 0
  | f :: fs => add f (sum fs)

/-- A finite sum in the fixed order of the finite index enumeration. -/
def sumOver [Fintype ι] (f : ι → PolynomialFraction σ) : PolynomialFraction σ :=
  sum (Finset.univ.toList.map f)

@[simp]
theorem value_ofPolynomial (x : σ → ℝ) (p : MvPolynomial σ ℚ) :
    value x (ofPolynomial p) = polynomialValue x p := by
  simp [value, ofPolynomial, polynomialValue]

theorem value_ofPowerFraction (x : σ → ℝ) (L : MvPolynomial σ ℚ) (f : PowerFraction σ) :
    value x (ofPowerFraction L f) = PowerFraction.value (polynomialValue x L) x f := by
  simp [value, ofPowerFraction, PowerFraction.value, polynomialValue]

theorem value_add (x : σ → ℝ) (f g : PolynomialFraction σ)
    (hf : polynomialValue x f.denominator ≠ 0)
    (hg : polynomialValue x g.denominator ≠ 0) :
    value x (add f g) = value x f + value x g := by
  simp only [value, add, polynomialValue, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_add]
  dsimp only [polynomialValue] at hf hg
  field_simp [hf, hg]

theorem value_mulPolynomial (x : σ → ℝ) (p : MvPolynomial σ ℚ) (f : PolynomialFraction σ) :
    value x (mulPolynomial p f) = polynomialValue x p * value x f := by
  simp [value, mulPolynomial, polynomialValue, mul_div_assoc]

theorem value_divPolynomial (x : σ → ℝ) (f : PolynomialFraction σ) (p : MvPolynomial σ ℚ) :
    value x (divPolynomial f p) = value x f / polynomialValue x p := by
  simp [value, divPolynomial, polynomialValue, div_div]

theorem sum_denominator_one_le (x : σ → ℝ) (fs : List (PolynomialFraction σ))
    (hfs : ∀ f ∈ fs, 1 ≤ polynomialValue x f.denominator) :
    1 ≤ polynomialValue x (sum fs).denominator := by
  induction fs with
  | nil => simp [sum, ofPolynomial, polynomialValue]
  | cons f fs ih =>
      change 1 ≤ polynomialValue x (f.denominator * (sum fs).denominator)
      simp only [polynomialValue, MvPolynomial.eval₂_mul]
      exact one_le_mul_of_one_le_of_one_le (hfs f (by simp))
        (ih (fun g hg ↦ hfs g (List.mem_cons_of_mem f hg)))

theorem value_sum (x : σ → ℝ) (fs : List (PolynomialFraction σ))
    (hfs : ∀ f ∈ fs, 1 ≤ polynomialValue x f.denominator) :
    value x (sum fs) = (fs.map (value x)).sum := by
  induction fs with
  | nil => simp [sum, polynomialValue]
  | cons f fs ih =>
      have htail := fun g hg ↦ hfs g (List.mem_cons_of_mem f hg)
      rw [sum, value_add x f (sum fs)
        (ne_of_gt (zero_lt_one.trans_le (hfs f (by simp))))
        (ne_of_gt (zero_lt_one.trans_le (sum_denominator_one_le x fs htail))), ih htail]
      rfl

theorem sumOver_denominator_one_le [Fintype ι] (x : σ → ℝ)
    (f : ι → PolynomialFraction σ) (hf : ∀ i, 1 ≤ polynomialValue x (f i).denominator) :
    1 ≤ polynomialValue x (sumOver f).denominator := by
  apply sum_denominator_one_le
  intro g hg
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
  exact hf i

theorem value_sumOver [Fintype ι] (x : σ → ℝ) (f : ι → PolynomialFraction σ)
    (hf : ∀ i, 1 ≤ polynomialValue x (f i).denominator) :
    value x (sumOver f) = ∑ i, value x (f i) := by
  unfold sumOver
  rw [value_sum x _ (by
    intro g hg
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
    exact hf i), List.map_map]
  simp

end

end PolynomialFraction

end Stability.Simulation
