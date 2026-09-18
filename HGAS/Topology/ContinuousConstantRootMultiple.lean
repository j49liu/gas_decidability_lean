import HGAS.Topology.ContinuousFourthRootBranch
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Continuous roots of a fixed nonzero multiple

The elementary sign-rigidity theorem in
`ContinuousFourthRootBranch` compares two functions whose squares are
equal.  In applications one often first knows

```text
                       f(x)^n = q g(x)^n
```

for a fixed nonzero complex number `q`.  Over a connected parameter
space this still says that `f` is one constant nonzero multiple of `g`.

This file records the cases `n = 2` and `n = 4`.  The proofs choose one
algebraic root of `q` and then use connectedness to prevent the remaining
finite root-of-unity ambiguity from changing with `x`.  No branch of the
complex logarithm is chosen.
-/

namespace HGAS.Topology

open Complex

noncomputable section

/-- A continuous square root of a fixed nonzero multiple differs from
the reference root by one constant nonzero scalar. -/
theorem exists_constant_complex_multiple_of_sq_eq
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (f g : X → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hsquare : ∀ x, f x ^ 2 = q * g x ^ 2)
    (hg_ne_zero : ∀ x, g x ≠ 0)
    (hq : q ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ x, f x = c * g x := by
  obtain ⟨a, ha⟩ :=
    IsAlgClosed.exists_pow_nat_eq q
      (by norm_num : 0 < (2 : ℕ))
  have ha_ne : a ≠ 0 := by
    intro hzero
    apply hq
    rw [← ha, hzero]
    norm_num
  have hbase :
      Continuous (fun x ↦ a * g x) :=
    continuous_const.mul hg
  have heq :
      ∀ x, f x ^ 2 = (a * g x) ^ 2 := by
    intro x
    rw [hsquare x, ← ha]
    ring
  have hbase_ne :
      ∀ x, a * g x ≠ 0 :=
    fun x ↦ mul_ne_zero ha_ne (hg_ne_zero x)
  obtain ⟨d, hd_ne, _hd_fourth, hd⟩ :=
    exists_constant_complex_fourthRoot_branch
      f (fun x ↦ a * g x) hf hbase heq hbase_ne
  refine ⟨a * d ^ 2, mul_ne_zero ha_ne (pow_ne_zero 2 hd_ne), ?_⟩
  intro x
  rw [← hd x]
  ring

/-- A continuous fourth root of a fixed nonzero multiple differs from
the reference root by one constant nonzero scalar. -/
theorem exists_constant_complex_multiple_of_fourth_eq
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (f g : X → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hfourth : ∀ x, f x ^ 4 = q * g x ^ 4)
    (hg_ne_zero : ∀ x, g x ≠ 0)
    (hq : q ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ x, f x = c * g x := by
  obtain ⟨a, ha⟩ :=
    IsAlgClosed.exists_pow_nat_eq q
      (by norm_num : 0 < (4 : ℕ))
  have ha_ne : a ≠ 0 := by
    intro hzero
    apply hq
    rw [← ha, hzero]
    norm_num
  let F : X → ℂ := fun x ↦ f x ^ 2
  let G : X → ℂ := fun x ↦ (a * g x) ^ 2
  have hF : Continuous F := hf.pow 2
  have hG : Continuous G :=
    (continuous_const.mul hg).pow 2
  have hFG : ∀ x, F x ^ 2 = G x ^ 2 := by
    intro x
    dsimp only [F, G]
    rw [show (f x ^ 2) ^ 2 = f x ^ 4 by ring,
      hfourth x, ← ha]
    ring
  have hG_ne : ∀ x, G x ≠ 0 := by
    intro x
    exact pow_ne_zero 2 (mul_ne_zero ha_ne (hg_ne_zero x))
  obtain ⟨d, hd_ne, _hd_fourth, hd⟩ :=
    exists_constant_complex_fourthRoot_branch
      F G hF hG hFG hG_ne
  let h : X → ℂ := fun x ↦ a * g x * d
  have hh : Continuous h :=
    (continuous_const.mul hg).mul continuous_const
  have hh_ne : ∀ x, h x ≠ 0 :=
    fun x ↦
      mul_ne_zero (mul_ne_zero ha_ne (hg_ne_zero x)) hd_ne
  have hfh : ∀ x, f x ^ 2 = h x ^ 2 := by
    intro x
    have hx := hd x
    dsimp only [F, G] at hx
    dsimp only [h]
    rw [← hx]
    ring
  obtain ⟨e, he_ne, _he_fourth, he⟩ :=
    exists_constant_complex_fourthRoot_branch
      f h hf hh hfh hh_ne
  refine
    ⟨a * d * e ^ 2,
      mul_ne_zero (mul_ne_zero ha_ne hd_ne)
        (pow_ne_zero 2 he_ne), ?_⟩
  intro x
  rw [← he x]
  dsimp only [h]
  ring

end

end HGAS.Topology
