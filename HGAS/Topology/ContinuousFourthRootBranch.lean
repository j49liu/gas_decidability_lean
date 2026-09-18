import Mathlib.Topology.Algebra.Field
import Mathlib.Analysis.Complex.Basic

/-!
# Constant fourth-root branches over a connected parameter space

This small module records the topological fact needed when a polynomial
construction leaves a finite square-root ambiguity.

Suppose two continuous complex-valued functions `f` and `g` satisfy

```
                         f(x)^2 = g(x)^2
```

on a connected set, and `g` never vanishes there.  Pointwise, one only
knows `f(x) = g(x)` or `f(x) = -g(x)`.  Continuity prevents the sign from
jumping: one of these two alternatives holds on the entire connected
set.  Equivalently, there is one *constant* fourth root of unity `d`,
which may be chosen to be either `1` or `i`, such that

```
                         g(x) d^2 = f(x)
```

throughout the set.

The formulation below is independent of the modular/Jacobi application
and can be reused for any finite-cover sign selection.
-/

namespace HGAS.Topology

open Complex Set

noncomputable section

/-- A continuous pointwise square-sign ambiguity on a preconnected set is
resolved by one constant fourth root of unity on the whole set.

The witness produced by the proof is `1` in the positive branch and `I`
in the negative branch. -/
theorem exists_constant_complex_fourthRoot_branch_on
    {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : IsPreconnected s)
    (f g : X → ℂ)
    (hf : ContinuousOn f s)
    (hg : ContinuousOn g s)
    (hsquare : ∀ x ∈ s, f x ^ 2 = g x ^ 2)
    (hg_ne_zero : ∀ x ∈ s, g x ≠ 0) :
    ∃ d : ℂ,
      d ≠ 0 ∧ d ^ 4 = 1 ∧
      ∀ x ∈ s, g x * d ^ 2 = f x := by
  have hsquare' : Set.EqOn (f ^ 2) (g ^ 2) s := by
    intro x hx
    exact hsquare x hx
  rcases
      hs.eq_or_eq_neg_of_sq_eq hf hg hsquare'
        (fun hx ↦ hg_ne_zero _ hx) with
    hpositive | hnegative
  · refine ⟨1, one_ne_zero, by norm_num, ?_⟩
    intro x hx
    simpa using (hpositive hx).symm
  · refine ⟨I, I_ne_zero, ?_, ?_⟩
    · rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, I_sq]
      norm_num
    · intro x hx
      rw [I_sq]
      simpa using (hnegative hx).symm

/-- Global-space specialization of
`exists_constant_complex_fourthRoot_branch_on`. -/
theorem exists_constant_complex_fourthRoot_branch
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (f g : X → ℂ)
    (hf : Continuous f)
    (hg : Continuous g)
    (hsquare : ∀ x, f x ^ 2 = g x ^ 2)
    (hg_ne_zero : ∀ x, g x ≠ 0) :
    ∃ d : ℂ,
      d ≠ 0 ∧ d ^ 4 = 1 ∧
      ∀ x, g x * d ^ 2 = f x := by
  rcases
      exists_constant_complex_fourthRoot_branch_on
        isPreconnected_univ f g hf.continuousOn hg.continuousOn
        (fun x _ ↦ hsquare x) (fun x _ ↦ hg_ne_zero x) with
    ⟨d, hdzero, hdfour, hd⟩
  exact ⟨d, hdzero, hdfour, fun x ↦ hd x (Set.mem_univ x)⟩

end

end HGAS.Topology
