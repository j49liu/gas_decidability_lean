import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-!
# Absolutely convergent series over finite integer lattices

Many Fourier constructions begin with one absolutely summable series for
each member of a finite family and then multiply those series.  The
coefficient of the product is naturally indexed by a function
`Fin n → ℤ`.

This file records the two reusable facts needed for that passage:

* the product coefficients are absolutely summable; and
* the product of the one-dimensional sums is the sum over the finite
  integer lattice.

The statements are deliberately independent of theta functions and of the
HGAS detector.
-/

noncomputable section

open scoped BigOperators

namespace HGAS.Analysis

/-- Absolute summability is preserved when finitely many series with a
common index type are assembled coordinatewise into product
coefficients. -/
theorem summable_norm_finProductComplex
    (f : Fin n → ι → ℂ)
    (hf : ∀ i, Summable (fun z ↦ ‖f i z‖)) :
    Summable
      (fun x : Fin n → ι ↦
        ‖∏ i : Fin n, f i (x i)‖) := by
  induction n with
  | zero =>
      exact Summable.of_finite
  | succ n ih =>
      let e : ι × (Fin n → ι) ≃ (Fin (n + 1) → ι) :=
        Fin.consEquiv fun _ ↦ ι
      have htail :
          Summable
            (fun x : Fin n → ι ↦
              ‖∏ i : Fin n, f i.succ (x i)‖) :=
        ih (fun i ↦ f i.succ) (fun i ↦ hf i.succ)
      have hproduct :
          Summable
            (fun p : ι × (Fin n → ι) ↦
              ‖f 0 p.1‖ *
                ‖∏ i : Fin n, f i.succ (p.2 i)‖) :=
        (hf 0).mul_of_nonneg htail
          (fun _ ↦ norm_nonneg _)
          (fun _ ↦ norm_nonneg _)
      apply e.summable_iff.mp
      convert hproduct using 1
      funext p
      simp only [e, Fin.consEquiv, Function.comp_apply]
      rw [Fin.prod_univ_succ, norm_mul]
      simp

/-- The product of finitely many absolutely convergent complex series with
a common index type is the absolutely convergent series of coordinatewise
product coefficients. -/
theorem prod_tsum_eq_tsum_finProduct
    (f : Fin n → ι → ℂ)
    (hf : ∀ i, Summable (fun z ↦ ‖f i z‖)) :
    (∏ i : Fin n, ∑' z : ι, f i z) =
      ∑' x : Fin n → ι,
        ∏ i : Fin n, f i (x i) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      let tail : Fin n → ι → ℂ :=
        fun i ↦ f i.succ
      let e : ι × (Fin n → ι) ≃ (Fin (n + 1) → ι) :=
        Fin.consEquiv fun _ ↦ ι
      rw [Fin.prod_univ_succ]
      rw [ih tail (fun i ↦ hf i.succ)]
      rw [tsum_mul_tsum_of_summable_norm
        (hf 0)
        (summable_norm_finProductComplex
          tail (fun i ↦ hf i.succ))]
      rw [← e.tsum_eq]
      apply tsum_congr
      intro p
      simp only [e, tail, Fin.consEquiv]
      rw [Fin.prod_univ_succ]
      simp

/-- Integer-indexed specialization of
`summable_norm_finProductComplex`. -/
theorem summable_norm_finIntegerProductComplex
    (f : Fin n → ℤ → ℂ)
    (hf : ∀ i, Summable (fun z ↦ ‖f i z‖)) :
    Summable
      (fun x : Fin n → ℤ ↦
        ‖∏ i : Fin n, f i (x i)‖) :=
  summable_norm_finProductComplex f hf

/-- Integer-indexed specialization of
`prod_tsum_eq_tsum_finProduct`. -/
theorem prod_tsum_eq_tsum_finIntegerProduct
    (f : Fin n → ℤ → ℂ)
    (hf : ∀ i, Summable (fun z ↦ ‖f i z‖)) :
    (∏ i : Fin n, ∑' z : ℤ, f i z) =
      ∑' x : Fin n → ℤ,
        ∏ i : Fin n, f i (x i) :=
  prod_tsum_eq_tsum_finProduct f hf

end HGAS.Analysis
