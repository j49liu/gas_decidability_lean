import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Tactic

/-!
# Cancelling a holomorphic power in differential identities

Pointwise division by a holomorphic function is often inconvenient because
the function may have isolated zeros.  On the connected upper half-plane,
the ring of holomorphic functions is an integral domain: a product of two
holomorphic functions is identically zero only when one factor is
identically zero.

The main theorem below packages the cancellation needed for theta
constants.  It recovers a first-order identity for `f` from the
corresponding identity for `f⁴`, assuming only that `f` is not the zero
function.  No pointwise zero-free theorem is needed.
-/

namespace HGAS.Analysis

open UpperHalfPlane hiding I
open Complex
open Filter Topology
open scoped Manifold

noncomputable section

local notation "Dₘ" => Derivative.normalizedDerivOfComplex

/-- A function tending to a nonzero value along a nontrivial filter is not
identically zero. -/
theorem function_ne_zero_of_tendsto
    {α E : Type*} [TopologicalSpace E] [T2Space E]
    [Zero E] {l : Filter α} [l.NeBot]
    {f : α → E} {c : E}
    (hf : Filter.Tendsto f l (𝓝 c)) (hc : c ≠ 0) :
    f ≠ 0 := by
  intro hzero
  have hzeroLimit :
      Filter.Tendsto f l (𝓝 0) := by
    rw [hzero]
    exact tendsto_const_nhds
  exact hc (tendsto_nhds_unique hf hzeroLimit)

/-- **Holomorphic fourth-power cancellation.**  If

```
        Dₘ(f⁴) = 4 f³ g,
```

then `Dₘf=g`, provided `f` is not identically zero.  Isolated zeros of
`f` cause no difficulty. -/
theorem normalizedDeriv_eq_of_fourthPower
    (f g : ℍ → ℂ)
    (hf : MDiff f) (hg : MDiff g)
    (hfne : f ≠ 0)
    (hfour :
      Dₘ (f ^ 4) =
        fun z ↦ 4 * f z ^ 3 * g z) :
    Dₘ f = g := by
  have hproduct :
      f ^ 3 * (Dₘ f - g) = 0 := by
    ext z
    have hLeibniz :=
      congrFun
        (Derivative.normalizedDerivOfComplex_pow
          f 4 hf) z
    have hgiven := congrFun hfour z
    simp only [Pi.pow_apply, Pi.mul_apply,
      Pi.sub_apply, Pi.zero_apply] at hLeibniz hgiven ⊢
    have heq :
        4 * f z ^ 3 * Dₘ f z =
          4 * f z ^ 3 * g z :=
      hLeibniz.symm.trans hgiven
    linear_combination (1 / 4 : ℂ) * heq
  have hfPowNe : f ^ 3 ≠ 0 := by
    intro hpow
    apply hfne
    ext z
    have hz := congrFun hpow z
    simp only [Pi.pow_apply, Pi.zero_apply] at hz
    exact (pow_eq_zero_iff (by norm_num : 3 ≠ 0)).mp hz
  have hresidual :
      Dₘ f - g = 0 :=
    (UpperHalfPlane.mul_eq_zero_iff
      (fun z ↦ (hf z).pow 3)
      ((Derivative.normalizedDerivOfComplex_mdifferentiable
        hf).sub hg)).mp hproduct
      |>.resolve_left hfPowNe
  exact sub_eq_zero.mp hresidual

end

end HGAS.Analysis
