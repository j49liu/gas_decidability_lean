import HGAS.Wrapper.TwoSheetPolynomialCode
import HGAS.Wrapper.ParityHomogenization
import Mathlib.Tactic

/-!
# Executable parity homogenization of sparse codes

`ParityHomogenization` gives the semantic construction for a list of
already bundled homogeneous pieces.  An effective wrapper needs the
corresponding operation on raw finite syntax.

For a coded monomial of degree `ℓ`, this file multiplies it by

```
ρ^((E-ℓ)/2),   ρ = ∑ᵢ Xᵢ².
```

When `ℓ ≤ E` and `ℓ ≡ E (mod 2)`, the result is homogeneous of degree
`E`.  On the Euclidean unit sphere `ρ=1`, it has exactly the same value
as the original monomial.  Applying this independently to the raw list
therefore gives an executable parity homogenizer whose decoding is
homogeneous and agrees with the input polynomial on the unit sphere.
-/

namespace HGAS

open _root_.MvPolynomial

namespace PolynomialCode

variable {n : ℕ}

/-- One raw monomial is eligible for parity homogenization to degree `E`. -/
def TermParityEligible (E : ℕ)
    (t : ExponentCode n × RationalCode) : Prop :=
  ExponentCode.totalDegree t.1 ≤ E ∧
    ExponentCode.totalDegree t.1 % 2 = E % 2

/-- Every raw monomial in a sparse code is eligible. -/
def TermsParityEligible (E : ℕ) (p : PolynomialCode n) : Prop :=
  ∀ t ∈ p, TermParityEligible E t

theorem termsParityEligible_cons_iff
    (E : ℕ) (t : ExponentCode n × RationalCode)
    (p : PolynomialCode n) :
    TermsParityEligible E (t :: p) ↔
      TermParityEligible E t ∧ TermsParityEligible E p := by
  simp [TermsParityEligible]

/-- Homogenize one coded monomial using a power of the squared norm. -/
def parityHomogenizeTerm (E : ℕ)
    (t : ExponentCode n × RationalCode) : PolynomialCode n :=
  mul
    (pow (rhoCode n)
      ((E - ExponentCode.totalDegree t.1) / 2))
    [t]

/-- Homogenize every raw monomial and concatenate the resulting sparse
codes. -/
def parityHomogenizeCode (E : ℕ)
    (p : PolynomialCode n) : PolynomialCode n :=
  sumCodes (p.map (parityHomogenizeTerm E))

@[simp]
theorem decode_parityHomogenizeTerm
    (E : ℕ) (t : ExponentCode n × RationalCode) :
    decode (parityHomogenizeTerm E t) =
      rhoPolynomial ^
          ((E - ExponentCode.totalDegree t.1) / 2) *
        decodeTerm t := by
  simp [parityHomogenizeTerm]

@[simp]
theorem decode_parityHomogenizeCode
    (E : ℕ) (p : PolynomialCode n) :
    decode (parityHomogenizeCode E p) =
      (p.map fun t ↦
        rhoPolynomial ^
            ((E - ExponentCode.totalDegree t.1) / 2) *
          decodeTerm t).sum := by
  simp [parityHomogenizeCode, Function.comp_def]

/-- The elementary degree arithmetic behind parity homogenization. -/
theorem parity_degree_arithmetic
    {E degree : ℕ} (hle : degree ≤ E)
    (hparity : degree % 2 = E % 2) :
    2 * ((E - degree) / 2) + degree = E := by
  have hmod : (E - degree) % 2 = 0 := by omega
  have hdivision := Nat.mod_add_div (E - degree) 2
  omega

/-- One eligible raw monomial homogenizes to degree `E`. -/
theorem decode_parityHomogenizeTerm_isHomogeneous
    (E : ℕ) (t : ExponentCode n × RationalCode)
    (ht : TermParityEligible E t) :
    (decode (parityHomogenizeTerm E t)).IsHomogeneous E := by
  rw [decode_parityHomogenizeTerm]
  have hrho :
      (rhoPolynomial (n := n) ^
        ((E - ExponentCode.totalDegree t.1) / 2)).IsHomogeneous
          (2 * ((E - ExponentCode.totalDegree t.1) / 2)) := by
    exact rhoPolynomial_isHomogeneous.pow _
  have hterm :
      (decodeTerm t).IsHomogeneous
        (ExponentCode.totalDegree t.1) := by
    apply isHomogeneous_monomial
    exact ExponentCode.degree_decode t.1
  convert hrho.mul hterm using 1
  exact (parity_degree_arithmetic ht.1 ht.2).symm

/-- The complete executable parity homogenization is homogeneous. -/
theorem decode_parityHomogenizeCode_isHomogeneous
    (E : ℕ) (p : PolynomialCode n)
    (hp : TermsParityEligible E p) :
    (decode (parityHomogenizeCode E p)).IsHomogeneous E := by
  induction p with
  | nil =>
      simpa [parityHomogenizeCode] using
        (isHomogeneous_zero (Fin n) ℚ E)
  | cons t p ih =>
      rw [termsParityEligible_cons_iff] at hp
      change
        (decode
          (add (parityHomogenizeTerm E t)
            (parityHomogenizeCode E p))).IsHomogeneous E
      rw [decode_add_code]
      exact
        (decode_parityHomogenizeTerm_isHomogeneous E t hp.1).add
          (ih hp.2)

/-- One parity-homogenized term is unchanged on the unit sphere. -/
theorem eval₂Hom_parityHomogenizeTerm_of_normSq_one
    (E : ℕ) (t : ExponentCode n × RationalCode)
    (x : Fin n → ℝ) (hx : normSq x = 1) :
    eval₂Hom (algebraMap ℚ ℝ) x
        (decode (parityHomogenizeTerm E t)) =
      eval₂Hom (algebraMap ℚ ℝ) x (decodeTerm t) := by
  simp only [decode_parityHomogenizeTerm, map_mul, map_pow,
    eval₂Hom_rhoPolynomial, hx, one_pow, one_mul]

/-- The executable parity homogenizer agrees with its input polynomial on
the Euclidean unit sphere. -/
theorem eval₂Hom_parityHomogenizeCode_of_normSq_one
    (E : ℕ) (p : PolynomialCode n)
    (x : Fin n → ℝ) (hx : normSq x = 1) :
    eval₂Hom (algebraMap ℚ ℝ) x
        (decode (parityHomogenizeCode E p)) =
      eval₂Hom (algebraMap ℚ ℝ) x (decode p) := by
  induction p with
  | nil => simp [parityHomogenizeCode]
  | cons t p ih =>
      change
        eval₂Hom (algebraMap ℚ ℝ) x
            (decode
              (add (parityHomogenizeTerm E t)
                (parityHomogenizeCode E p))) =
          eval₂Hom (algebraMap ℚ ℝ) x
            (decodeTerm t + decode p)
      rw [decode_add_code, map_add, map_add]
      rw [eval₂Hom_parityHomogenizeTerm_of_normSq_one E t x hx]
      rw [ih]

/-! ## Effectivity -/

theorem parityHomogenizeTerm_primrec {n : ℕ} :
    Primrec₂ (parityHomogenizeTerm :
      ℕ → (ExponentCode n × RationalCode) → PolynomialCode n) := by
  change
    Primrec
      (fun q : ℕ × (ExponentCode n × RationalCode) ↦
        parityHomogenizeTerm q.1 q.2)
  have hdegree :
      Primrec
        (fun q : ℕ × (ExponentCode n × RationalCode) ↦
          ExponentCode.totalDegree q.2.1) :=
    ExponentCode.totalDegree_primrec.comp
      (Primrec.fst.comp Primrec.snd)
  have hexponent :
      Primrec
        (fun q : ℕ × (ExponentCode n × RationalCode) ↦
          (q.1 - ExponentCode.totalDegree q.2.1) / 2) :=
    Primrec.nat_div.comp
      (Primrec.nat_sub.comp Primrec.fst hdegree)
      (Primrec.const 2)
  have hrhoPower :
      Primrec
        (fun q : ℕ × (ExponentCode n × RationalCode) ↦
          pow (rhoCode n)
            ((q.1 - ExponentCode.totalDegree q.2.1) / 2)) :=
    pow_primrec.comp
      (Primrec.const (rhoCode n)) hexponent
  have hsingleton :
      Primrec
        (fun q : ℕ × (ExponentCode n × RationalCode) ↦
          [q.2]) :=
    Primrec.list_cons.comp Primrec.snd (Primrec.const [])
  exact
    (mul_primrec.comp hrhoPower hsingleton).of_eq
      fun _ ↦ rfl

theorem parityHomogenizeCode_primrec {n : ℕ} :
    Primrec₂ (parityHomogenizeCode :
      ℕ → PolynomialCode n → PolynomialCode n) := by
  change
    Primrec
      (fun q : ℕ × PolynomialCode n ↦
        parityHomogenizeCode q.1 q.2)
  have hterm :
      Primrec₂
        (fun (q : ℕ × PolynomialCode n)
          (t : ExponentCode n × RationalCode) ↦
            parityHomogenizeTerm q.1 t) :=
    parityHomogenizeTerm_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.left)
      Primrec₂.right
  exact
    (sumCodes_primrec.comp
      (Primrec.list_map Primrec.snd hterm)).of_eq
        fun _ ↦ rfl

/-- The code-level parity homogenizer is a total computable function. -/
theorem parityHomogenizeCode_computable {n : ℕ} :
    Computable₂ (parityHomogenizeCode :
      ℕ → PolynomialCode n → PolynomialCode n) :=
  parityHomogenizeCode_primrec.to_comp

end PolynomialCode

end HGAS
