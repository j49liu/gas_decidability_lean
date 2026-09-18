import HGAS.Algebra.ComplexPolynomialComputability
import HGAS.Algebra.ComplexPolynomialDegrees
import Mathlib.Tactic

/-!
# Realification of finite complex polynomial families

`ComplexPolynomialFieldCode.realify` handles the special case in which the
number of complex outputs equals the number of complex variables.  Validity
residuals usually have a different number of outputs.  This file provides the
corresponding reusable operation for an arbitrary finite family

```
                 H : Fin m → ComplexPolynomialCode n.
```

The realified family has `2m` scalar outputs in `2n` real variables.  Its
first block consists of real parts and its second block of imaginary parts.
We prove exact evaluation semantics, equivalence of simultaneous real and
complex vanishing, preservation of raw degree, and primitive recursiveness.
-/

namespace HGAS

/-- A finite family of `m` complex polynomial outputs in `n` complex
variables. -/
abbrev ComplexPolynomialFamilyCode (m n : ℕ) :=
  Fin m → ComplexPolynomialCode n

namespace ComplexPolynomialFamilyCode

variable {m n : ℕ}

/-- Split a finite complex polynomial family into its real and imaginary
scalar output families. -/
def realify
    (H : ComplexPolynomialFamilyCode m n) :
    Fin (m + m) → PolynomialCode (n + n) :=
  fun q ↦
    match finSumFinEquiv.symm q with
    | Sum.inl i => (H i).1
    | Sum.inr i => (H i).2

@[simp]
theorem realify_realIndex
    (H : ComplexPolynomialFamilyCode m n) (i : Fin m) :
    realify H (ComplexCoordinates.realIndex i) = (H i).1 := by
  simp [realify]

@[simp]
theorem realify_imagIndex
    (H : ComplexPolynomialFamilyCode m n) (i : Fin m) :
    realify H (ComplexCoordinates.imagIndex i) = (H i).2 := by
  simp [realify]

/-- Evaluating a real output in the realified complex coordinates gives the
real part of complex evaluation. -/
@[simp]
theorem eval_realIndex
    (H : ComplexPolynomialFamilyCode m n)
    (z : Fin n → ℂ) (i : Fin m) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (ComplexCoordinates.realifyPoint z)
        (PolynomialCode.decode
          (realify H (ComplexCoordinates.realIndex i))) =
      (ComplexPolynomialCode.eval (H i) z).re := by
  simp [ComplexPolynomialCode.eval,
    ComplexPolynomialCode.evalReal]

/-- Evaluating an imaginary output gives the imaginary part of complex
evaluation. -/
@[simp]
theorem eval_imagIndex
    (H : ComplexPolynomialFamilyCode m n)
    (z : Fin n → ℂ) (i : Fin m) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (ComplexCoordinates.realifyPoint z)
        (PolynomialCode.decode
          (realify H (ComplexCoordinates.imagIndex i))) =
      (ComplexPolynomialCode.eval (H i) z).im := by
  simp [ComplexPolynomialCode.eval,
    ComplexPolynomialCode.evalReal]

/-- Reassembling all scalar output evaluations recovers simultaneous complex
evaluation of the original family. -/
@[simp]
theorem complexifyPoint_eval_realify
    (H : ComplexPolynomialFamilyCode m n)
    (z : Fin n → ℂ) :
    ComplexCoordinates.complexifyPoint
        (fun q ↦
          MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
            (ComplexCoordinates.realifyPoint z)
            (PolynomialCode.decode (realify H q))) =
      fun i ↦ ComplexPolynomialCode.eval (H i) z := by
  funext i
  apply Complex.ext
  · exact eval_realIndex H z i
  · exact eval_imagIndex H z i

/-- All `2m` real scalar residuals vanish exactly when all `m` complex
residuals vanish. -/
theorem forall_eval_realify_eq_zero_iff
    (H : ComplexPolynomialFamilyCode m n)
    (z : Fin n → ℂ) :
    (∀ q,
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (ComplexCoordinates.realifyPoint z)
        (PolynomialCode.decode (realify H q)) = 0) ↔
      ∀ i, ComplexPolynomialCode.eval (H i) z = 0 := by
  constructor
  · intro h i
    apply Complex.ext
    · simpa using h (ComplexCoordinates.realIndex i)
    · simpa using h (ComplexCoordinates.imagIndex i)
  · intro h q
    obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective q
    · rw [show finSumFinEquiv (Sum.inl i) =
        ComplexCoordinates.realIndex i by rfl]
      rw [eval_realIndex]
      simp [h i]
    · rw [show finSumFinEquiv (Sum.inr i) =
        ComplexCoordinates.imagIndex i by rfl]
      rw [eval_imagIndex]
      simp [h i]

/-- Uniform complex raw degree passes unchanged to every real scalar
output. -/
theorem realify_termsDegreeLE
    {D : ℕ} {H : ComplexPolynomialFamilyCode m n}
    (hH : ∀ i, ComplexPolynomialCode.TermsDegreeLE D (H i)) :
    ∀ q, PolynomialCode.TermsDegreeLE D (realify H q) := by
  intro q
  cases hq : finSumFinEquiv.symm q with
  | inl i =>
      simpa [realify, hq] using (hH i).1
  | inr i =>
      simpa [realify, hq] using (hH i).2

/-- Realification of an arbitrary finite complex family is primitive
recursive for fixed dimensions. -/
theorem realify_primrec :
    Primrec (realify :
      ComplexPolynomialFamilyCode m n →
        (Fin (m + m) → PolynomialCode (n + n))) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro q
  cases hq : finSumFinEquiv.symm q with
  | inl i =>
      exact
        ((Primrec.fst.comp
          (Primrec.fin_app.comp Primrec.id
            (Primrec.const i))).of_eq fun H ↦ by
              simp [realify, hq])
  | inr i =>
      exact
        ((Primrec.snd.comp
          (Primrec.fin_app.comp Primrec.id
            (Primrec.const i))).of_eq fun H ↦ by
              simp [realify, hq])

theorem realify_computable :
    Computable (realify :
      ComplexPolynomialFamilyCode m n →
        (Fin (m + m) → PolynomialCode (n + n))) :=
  realify_primrec.to_comp

end ComplexPolynomialFamilyCode

end HGAS
