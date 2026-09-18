import HGAS.Algebra.ComplexPolynomialCode
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Effectivity of complex polynomial syntax

The complex-polynomial layer is not merely a convenient semantic
notation.  Every constructor is primitive recursive on the underlying
finite sparse codes.  In particular, complex multiplication and
realification of an entire finite-dimensional complex vector field are
effective list transformations.

The `Computable` corollaries are recorded explicitly because downstream
compiler interfaces generally ask only for computability, whereas the
stronger `Primrec` statements are useful when composing encodings.
-/

namespace HGAS

namespace ComplexPolynomialCode

variable {n : ℕ}

theorem zero_primrec :
    Primrec (fun _ : Unit ↦ (zero : ComplexPolynomialCode n)) :=
  Primrec.const _

theorem one_primrec :
    Primrec (fun _ : Unit ↦ (one : ComplexPolynomialCode n)) :=
  Primrec.const _

/-- Formation of a real rational constant is primitive recursive. -/
theorem rationalConstant_primrec :
    Primrec (rationalConstant :
      RationalCode → ComplexPolynomialCode n) := by
  exact Primrec.pair
    PolynomialCode.constant_primrec
    (Primrec.const PolynomialCode.zero)

/-- Formation of a Gaussian-rational constant is primitive recursive. -/
theorem gaussianConstant_primrec :
    Primrec (gaussianConstant :
      GaussianRationalCode → ComplexPolynomialCode n) := by
  exact Primrec.pair
    (PolynomialCode.constant_primrec.comp Primrec.fst)
    (PolynomialCode.constant_primrec.comp Primrec.snd)

/-- The finite family of complex coordinate codes is primitive
recursive. -/
theorem var_primrec :
    Primrec (var : Fin n → ComplexPolynomialCode n) :=
  Primrec.dom_finite _

theorem add_primrec :
    Primrec₂ (add :
      ComplexPolynomialCode n → ComplexPolynomialCode n →
        ComplexPolynomialCode n) := by
  exact Primrec.pair
    (PolynomialCode.add_primrec.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd))
    (PolynomialCode.add_primrec.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd))

theorem neg_primrec :
    Primrec (neg :
      ComplexPolynomialCode n → ComplexPolynomialCode n) := by
  exact Primrec.pair
    (PolynomialCode.neg_primrec.comp Primrec.fst)
    (PolynomialCode.neg_primrec.comp Primrec.snd)

theorem sub_primrec :
    Primrec₂ (sub :
      ComplexPolynomialCode n → ComplexPolynomialCode n →
        ComplexPolynomialCode n) := by
  exact Primrec.pair
    (PolynomialCode.sub_primrec.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd))
    (PolynomialCode.sub_primrec.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd))

/-- Complex multiplication is primitive recursive.  The proof exposes
the four real products `ac`, `bd`, `ad`, and `bc`, mirroring the algebraic
definition. -/
theorem mul_primrec :
    Primrec₂ (mul :
      ComplexPolynomialCode n → ComplexPolynomialCode n →
        ComplexPolynomialCode n) := by
  let hac :
      Primrec
        (fun r :
          ComplexPolynomialCode n × ComplexPolynomialCode n ↦
            PolynomialCode.mul r.1.1 r.2.1) :=
    PolynomialCode.mul_primrec.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
  let hbd :
      Primrec
        (fun r :
          ComplexPolynomialCode n × ComplexPolynomialCode n ↦
            PolynomialCode.mul r.1.2 r.2.2) :=
    PolynomialCode.mul_primrec.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  let had :
      Primrec
        (fun r :
          ComplexPolynomialCode n × ComplexPolynomialCode n ↦
            PolynomialCode.mul r.1.1 r.2.2) :=
    PolynomialCode.mul_primrec.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  let hbc :
      Primrec
        (fun r :
          ComplexPolynomialCode n × ComplexPolynomialCode n ↦
            PolynomialCode.mul r.1.2 r.2.1) :=
    PolynomialCode.mul_primrec.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
  exact Primrec.pair
    (PolynomialCode.sub_primrec.comp hac hbd)
    (PolynomialCode.add_primrec.comp had hbc)

/-- Natural powers are primitive recursive jointly in the code and the
exponent. -/
theorem pow_primrec :
    Primrec₂ (pow :
      ComplexPolynomialCode n → ℕ → ComplexPolynomialCode n) := by
  have hstep :
      Primrec₂
        (fun (p : ComplexPolynomialCode n)
          (r : ℕ × ComplexPolynomialCode n) ↦
            mul p r.2) :=
    mul_primrec.comp₂ Primrec₂.left
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.nat_rec
      (Primrec.const (one : ComplexPolynomialCode n)) hstep).of_eq
      fun p k ↦ by
        induction k with
        | zero => rfl
        | succ k ih =>
            simp only [pow]
            rw [ih]

theorem mulI_primrec :
    Primrec (mulI :
      ComplexPolynomialCode n → ComplexPolynomialCode n) := by
  exact Primrec.pair
    (PolynomialCode.neg_primrec.comp Primrec.snd)
    Primrec.fst

theorem mulGaussian_primrec :
    Primrec₂ (mulGaussian :
      GaussianRationalCode → ComplexPolynomialCode n →
        ComplexPolynomialCode n) := by
  exact mul_primrec.comp
    (gaussianConstant_primrec.comp Primrec.fst)
    Primrec.snd

theorem zero_computable :
    Computable (fun _ : Unit ↦
      (zero : ComplexPolynomialCode n)) :=
  zero_primrec.to_comp

theorem one_computable :
    Computable (fun _ : Unit ↦
      (one : ComplexPolynomialCode n)) :=
  one_primrec.to_comp

theorem rationalConstant_computable :
    Computable (rationalConstant :
      RationalCode → ComplexPolynomialCode n) :=
  rationalConstant_primrec.to_comp

theorem gaussianConstant_computable :
    Computable (gaussianConstant :
      GaussianRationalCode → ComplexPolynomialCode n) :=
  gaussianConstant_primrec.to_comp

theorem var_computable :
    Computable (var : Fin n → ComplexPolynomialCode n) :=
  var_primrec.to_comp

theorem add_computable :
    Computable₂ (add :
      ComplexPolynomialCode n → ComplexPolynomialCode n →
        ComplexPolynomialCode n) :=
  add_primrec.to_comp

theorem neg_computable :
    Computable (neg :
      ComplexPolynomialCode n → ComplexPolynomialCode n) :=
  neg_primrec.to_comp

theorem sub_computable :
    Computable₂ (sub :
      ComplexPolynomialCode n → ComplexPolynomialCode n →
        ComplexPolynomialCode n) :=
  sub_primrec.to_comp

theorem mul_computable :
    Computable₂ (mul :
      ComplexPolynomialCode n → ComplexPolynomialCode n →
        ComplexPolynomialCode n) :=
  mul_primrec.to_comp

theorem pow_computable :
    Computable₂ (pow :
      ComplexPolynomialCode n → ℕ → ComplexPolynomialCode n) :=
  pow_primrec.to_comp

theorem mulI_computable :
    Computable (mulI :
      ComplexPolynomialCode n → ComplexPolynomialCode n) :=
  mulI_primrec.to_comp

theorem mulGaussian_computable :
    Computable₂ (mulGaussian :
      GaussianRationalCode → ComplexPolynomialCode n →
        ComplexPolynomialCode n) :=
  mulGaussian_primrec.to_comp

end ComplexPolynomialCode

namespace ComplexPolynomialFieldCode

variable {n : ℕ}

/-- Realification of a complex polynomial vector field is primitive
recursive for every fixed dimension. -/
theorem realify_primrec :
    Primrec (realify :
      ComplexPolynomialFieldCode n →
        PolynomialFieldCode (n + n)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro q
  cases hq : finSumFinEquiv.symm q with
  | inl i =>
      exact
        ((Primrec.fst.comp
          (Primrec.fin_app.comp Primrec.id
            (Primrec.const i))).of_eq fun F ↦ by
              simp [realify, hq])
  | inr i =>
      exact
        ((Primrec.snd.comp
          (Primrec.fin_app.comp Primrec.id
            (Primrec.const i))).of_eq fun F ↦ by
              simp [realify, hq])

theorem realify_computable :
    Computable (realify :
      ComplexPolynomialFieldCode n →
        PolynomialFieldCode (n + n)) :=
  realify_primrec.to_comp

end ComplexPolynomialFieldCode

end HGAS
