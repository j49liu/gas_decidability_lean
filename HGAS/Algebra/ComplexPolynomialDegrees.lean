import HGAS.Algebra.ComplexPolynomialCode
import HGAS.Accumulator.PolynomialDegrees
import Mathlib.Tactic

/-!
# Raw degree calculus for complex polynomial codes

Degree control in the HGAS compiler is deliberately syntactic: it bounds
every monomial in the raw sparse list, before normalization or
cancellation.  This file lifts that robust notion componentwise to
complex polynomial codes.

The important algebraic rule is the expected one:

```
deg (p * q) ≤ deg p + deg q.
```

It holds simultaneously for the real and imaginary output lists, even
though each output contains two real products.  Natural powers and
multiplication by rational Gaussian constants then have their usual
bounds.  Finally, the bounds pass unchanged through realification of a
complex vector field.
-/

namespace HGAS

namespace ComplexPolynomialCode

variable {n : ℕ}

/-- Both raw real polynomial lists have monomial degree at most `D`. -/
def TermsDegreeLE (D : ℕ) (p : ComplexPolynomialCode n) : Prop :=
  PolynomialCode.TermsDegreeLE D p.1 ∧
    PolynomialCode.TermsDegreeLE D p.2

/-- Componentwise raw degree is constructively decidable. -/
instance termsDegreeLEDecidable
    (D : ℕ) (p : ComplexPolynomialCode n) :
    Decidable (TermsDegreeLE D p) := by
  unfold TermsDegreeLE
  infer_instance

theorem termsDegreeLE_zero (D : ℕ) :
    TermsDegreeLE D (zero : ComplexPolynomialCode n) :=
  ⟨PolynomialCode.termsDegreeLE_zero D,
    PolynomialCode.termsDegreeLE_zero D⟩

theorem termsDegreeLE_one :
    TermsDegreeLE 0 (one : ComplexPolynomialCode n) :=
  ⟨PolynomialCode.termsDegreeLE_one,
    PolynomialCode.termsDegreeLE_zero 0⟩

theorem termsDegreeLE_rationalConstant (q : RationalCode) :
    TermsDegreeLE 0
      (rationalConstant q : ComplexPolynomialCode n) := by
  constructor
  · intro t ht
    exact (PolynomialCode.termsParityEligible_constant q t ht).1
  · exact PolynomialCode.termsDegreeLE_zero 0

theorem termsDegreeLE_gaussianConstant
    (q : GaussianRationalCode) :
    TermsDegreeLE 0
      (gaussianConstant q : ComplexPolynomialCode n) := by
  constructor
  · intro t ht
    exact (PolynomialCode.termsParityEligible_constant q.1 t ht).1
  · intro t ht
    exact (PolynomialCode.termsParityEligible_constant q.2 t ht).1

theorem termsDegreeLE_var (i : Fin n) :
    TermsDegreeLE 1 (var i) :=
  ⟨PolynomialCode.termsDegreeLE_varCode _,
    PolynomialCode.termsDegreeLE_varCode _⟩

theorem termsDegreeLE_add
    {D : ℕ} {p q : ComplexPolynomialCode n}
    (hp : TermsDegreeLE D p)
    (hq : TermsDegreeLE D q) :
    TermsDegreeLE D (add p q) :=
  ⟨PolynomialCode.termsDegreeLE_add hp.1 hq.1,
    PolynomialCode.termsDegreeLE_add hp.2 hq.2⟩

theorem termsDegreeLE_neg
    {D : ℕ} {p : ComplexPolynomialCode n}
    (hp : TermsDegreeLE D p) :
    TermsDegreeLE D (neg p) :=
  ⟨PolynomialCode.termsDegreeLE_neg hp.1,
    PolynomialCode.termsDegreeLE_neg hp.2⟩

theorem termsDegreeLE_sub
    {D : ℕ} {p q : ComplexPolynomialCode n}
    (hp : TermsDegreeLE D p)
    (hq : TermsDegreeLE D q) :
    TermsDegreeLE D (sub p q) :=
  ⟨PolynomialCode.termsDegreeLE_sub hp.1 hq.1,
    PolynomialCode.termsDegreeLE_sub hp.2 hq.2⟩

/-- Raw degree of complex multiplication is at most the sum of the input
bounds. -/
theorem termsDegreeLE_mul
    {D E : ℕ} {p q : ComplexPolynomialCode n}
    (hp : TermsDegreeLE D p)
    (hq : TermsDegreeLE E q) :
    TermsDegreeLE (D + E) (mul p q) := by
  constructor
  · exact PolynomialCode.termsDegreeLE_sub
      (PolynomialCode.termsDegreeLE_mul hp.1 hq.1)
      (PolynomialCode.termsDegreeLE_mul hp.2 hq.2)
  · exact PolynomialCode.termsDegreeLE_add
      (PolynomialCode.termsDegreeLE_mul hp.1 hq.2)
      (PolynomialCode.termsDegreeLE_mul hp.2 hq.1)

/-- Raw degree of the `k`-th power is at most `k` times the input
bound. -/
theorem termsDegreeLE_pow
    {D : ℕ} {p : ComplexPolynomialCode n}
    (hp : TermsDegreeLE D p) :
    ∀ k, TermsDegreeLE (D * k) (pow p k)
  | 0 => by
      simpa using (termsDegreeLE_one (n := n))
  | k + 1 => by
      rw [pow]
      have hmul :=
        termsDegreeLE_mul hp (termsDegreeLE_pow hp k)
      simpa [Nat.mul_succ, Nat.add_comm] using hmul

theorem termsDegreeLE_mulI
    {D : ℕ} {p : ComplexPolynomialCode n}
    (hp : TermsDegreeLE D p) :
    TermsDegreeLE D (mulI p) :=
  ⟨PolynomialCode.termsDegreeLE_neg hp.2, hp.1⟩

theorem termsDegreeLE_mulGaussian
    {D : ℕ} (q : GaussianRationalCode)
    {p : ComplexPolynomialCode n}
    (hp : TermsDegreeLE D p) :
    TermsDegreeLE D (mulGaussian q p) := by
  have hmul :=
    termsDegreeLE_mul
      (termsDegreeLE_gaussianConstant (n := n) q) hp
  simpa [mulGaussian] using hmul

/-- Monotonicity of the componentwise degree bound. -/
theorem TermsDegreeLE.promote
    {D E : ℕ} {p : ComplexPolynomialCode n}
    (hp : TermsDegreeLE D p) (hDE : D ≤ E) :
    TermsDegreeLE E p :=
  ⟨hp.1.promote hDE, hp.2.promote hDE⟩

end ComplexPolynomialCode

namespace ComplexPolynomialFieldCode

variable {n : ℕ}

/-- Uniform raw degree bound for a complex polynomial field. -/
def TermsDegreeLE
    (D : ℕ) (F : ComplexPolynomialFieldCode n) : Prop :=
  ∀ i, ComplexPolynomialCode.TermsDegreeLE D (F i)

/-- A uniform degree bound on a fixed finite-dimensional complex field is
constructively decidable. -/
instance termsDegreeLEDecidable
    (D : ℕ) (F : ComplexPolynomialFieldCode n) :
    Decidable (TermsDegreeLE D F) := by
  unfold TermsDegreeLE
  infer_instance

/-- Realification preserves the uniform raw degree bound exactly. -/
theorem realify_termsDegreeLE
    {D : ℕ} {F : ComplexPolynomialFieldCode n}
    (hF : TermsDegreeLE D F) :
    ∀ q,
      PolynomialCode.TermsDegreeLE D (realify F q) := by
  intro q
  cases hq : finSumFinEquiv.symm q with
  | inl i =>
      simpa [realify, hq] using (hF i).1
  | inr i =>
      simpa [realify, hq] using (hF i).2

end ComplexPolynomialFieldCode

end HGAS
