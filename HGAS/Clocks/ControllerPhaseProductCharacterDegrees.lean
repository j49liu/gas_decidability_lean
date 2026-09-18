import HGAS.Clocks.ControllerPhaseProductCharacterCode
import Mathlib.Tactic

/-!
# Degree bounds for controller-product phase characters

For an integral exponent tuple `a : Fin q → ℤ`, the character compiler
represents a negative phase power by a power of the conjugate coordinate.
Both a phase coordinate and its conjugate are linear, so the polynomial
degree contributed by the `i`-th factor is exactly bounded by
`|aᵢ|`.  The natural degree ledger is therefore

```
                         ∑ i, (a i).natAbs.
```

This file proves that bound directly on the raw sparse syntax.  It also
shows that the compiled character velocity has degree at most one more:
the rational frequency readout is linear and multiplies the character.
No cancellation or semantic unit-circle identity is used.
-/

namespace HGAS.Clocks.ControllerPhaseProductCharacterCode

open HGAS

variable {n q D E : ℕ}

/-- Both real coordinates of a complex-pair code satisfy the same raw
monomial-degree bound. -/
def TermsDegreeLE
    (D : ℕ) (p : ComplexPairCode n) : Prop :=
  PolynomialCode.TermsDegreeLE D p.1 ∧
    PolynomialCode.TermsDegreeLE D p.2

instance termsDegreeLEDecidable
    (D : ℕ) (p : ComplexPairCode n) :
    Decidable (TermsDegreeLE D p) := by
  unfold TermsDegreeLE
  infer_instance

/-- Total unsigned exponent energy of a finite Laurent character. -/
def exponentEnergy
    (exponents : Fin q → ℤ) : ℕ :=
  ∑ i, (exponents i).natAbs

theorem termsDegreeLE_zero (D : ℕ) :
    TermsDegreeLE D (zero : ComplexPairCode n) :=
  ⟨PolynomialCode.termsDegreeLE_zero D,
    PolynomialCode.termsDegreeLE_zero D⟩

theorem termsDegreeLE_one :
    TermsDegreeLE 0 (one : ComplexPairCode n) :=
  ⟨PolynomialCode.termsDegreeLE_one,
    PolynomialCode.termsDegreeLE_zero 0⟩

theorem termsDegreeLE_neg
    {p : ComplexPairCode n}
    (hp : TermsDegreeLE D p) :
    TermsDegreeLE D (neg p) :=
  ⟨PolynomialCode.termsDegreeLE_neg hp.1,
    PolynomialCode.termsDegreeLE_neg hp.2⟩

/-- Conjugation changes coefficients but not raw monomial degrees. -/
theorem termsDegreeLE_conj
    {p : ComplexPairCode n}
    (hp : TermsDegreeLE D p) :
    TermsDegreeLE D (conj p) :=
  ⟨hp.1, PolynomialCode.termsDegreeLE_neg hp.2⟩

/-- Literal complex multiplication adds the two componentwise raw degree
bounds. -/
theorem termsDegreeLE_mul
    {p r : ComplexPairCode n}
    (hp : TermsDegreeLE D p)
    (hr : TermsDegreeLE E r) :
    TermsDegreeLE (D + E) (mul p r) := by
  constructor
  · exact
      PolynomialCode.termsDegreeLE_sub
        (PolynomialCode.termsDegreeLE_mul hp.1 hr.1)
        (PolynomialCode.termsDegreeLE_mul hp.2 hr.2)
  · exact
      PolynomialCode.termsDegreeLE_add
        (PolynomialCode.termsDegreeLE_mul hp.1 hr.2)
        (PolynomialCode.termsDegreeLE_mul hp.2 hr.1)

/-- A natural power multiplies the raw degree bound by its exponent. -/
theorem termsDegreeLE_pow
    {p : ComplexPairCode n}
    (hp : TermsDegreeLE D p) :
    ∀ k, TermsDegreeLE (D * k) (pow p k)
  | 0 => by
      simpa using (termsDegreeLE_one (n := n))
  | k + 1 => by
      have hmul :=
        termsDegreeLE_mul hp (termsDegreeLE_pow hp k)
      simpa [pow, Nat.mul_succ, Nat.add_comm] using hmul

/-- A product indexed by a list has degree bounded by the sum of the
individual bounds.  This formulation is reusable for other finite
complex-pair products. -/
theorem product_map_termsDegreeLE
    {α : Type*}
    (xs : List α)
    (f : α → ComplexPairCode n)
    (degree : α → ℕ)
    (hf : ∀ x ∈ xs, TermsDegreeLE (degree x) (f x)) :
    TermsDegreeLE (xs.map degree).sum
      (product (xs.map f)) := by
  induction xs with
  | nil =>
      simpa [product] using
        (termsDegreeLE_one (n := n))
  | cons x xs ih =>
      have hx : TermsDegreeLE (degree x) (f x) :=
        hf x (by simp)
      have hxs :
          ∀ y ∈ xs, TermsDegreeLE (degree y) (f y) :=
        fun y hy ↦ hf y (by simp [hy])
      simpa [product] using
        termsDegreeLE_mul hx (ih hxs)

/-- Each real phase coordinate is linear. -/
theorem phaseCode_termsDegreeLE
    (i : Fin q) :
    TermsDegreeLE 1 (phaseCode i) := by
  exact
    ⟨PolynomialCode.termsDegreeLE_varCode _,
      PolynomialCode.termsDegreeLE_varCode _⟩

/-- One signed phase power has degree bounded by the unsigned exponent. -/
theorem signedPowerCode_termsDegreeLE
    (i : Fin q) (e : ℤ) :
    TermsDegreeLE e.natAbs (signedPowerCode i e) := by
  by_cases he : e < 0
  · simpa [signedPowerCode, he] using
      termsDegreeLE_pow
        (termsDegreeLE_conj
          (phaseCode_termsDegreeLE i)) e.natAbs
  · simpa [signedPowerCode, he] using
      termsDegreeLE_pow
        (phaseCode_termsDegreeLE i) e.natAbs

/-- **Character degree ledger.**

The real and imaginary codes of a Laurent character have raw degree at
most the sum of the absolute values of its integral exponents. -/
theorem characterCode_termsDegreeLE
    (exponents : Fin q → ℤ) :
    TermsDegreeLE (exponentEnergy exponents)
      (characterCode exponents) := by
  let indices : List (Fin q) :=
    List.ofFn fun i : Fin q ↦ i
  have h :=
    product_map_termsDegreeLE indices
      (fun i ↦ signedPowerCode i (exponents i))
      (fun i ↦ (exponents i).natAbs)
      (fun i _ ↦ signedPowerCode_termsDegreeLE i (exponents i))
  simpa [characterCode, indices, exponentEnergy,
    List.map_ofFn, List.sum_ofFn] using h

/-- The rational character-frequency readout is linear. -/
theorem frequencyCode_termsDegreeLE
    (parameters : Fin q → RationalCode)
    (exponents : Fin q → ℤ) :
    PolynomialCode.TermsDegreeLE 1
      (frequencyCode parameters exponents) :=
  ControllerPhaseProductLinearFrequencyCode.code_termsDegreeLE _ _

/-- **Character derivative degree ledger.**

Multiplication by the linear frequency readout increases the character
degree bound by one. -/
theorem derivativeCode_termsDegreeLE
    (parameters : Fin q → RationalCode)
    (exponents : Fin q → ℤ) :
    TermsDegreeLE (exponentEnergy exponents + 1)
      (derivativeCode parameters exponents) := by
  have hcharacter :=
    characterCode_termsDegreeLE exponents
  have him :
      PolynomialCode.TermsDegreeLE
        (1 + exponentEnergy exponents)
        (PolynomialCode.mul
          (frequencyCode parameters exponents)
          (characterCode exponents).2) :=
    PolynomialCode.termsDegreeLE_mul
      (frequencyCode_termsDegreeLE parameters exponents)
      hcharacter.2
  have hre :
      PolynomialCode.TermsDegreeLE
        (1 + exponentEnergy exponents)
        (PolynomialCode.mul
          (frequencyCode parameters exponents)
          (characterCode exponents).1) :=
    PolynomialCode.termsDegreeLE_mul
      (frequencyCode_termsDegreeLE parameters exponents)
      hcharacter.1
  constructor
  · simpa [derivativeCode, Nat.add_comm] using
      PolynomialCode.termsDegreeLE_neg him
  · simpa [derivativeCode, Nat.add_comm] using hre

end HGAS.Clocks.ControllerPhaseProductCharacterCode
