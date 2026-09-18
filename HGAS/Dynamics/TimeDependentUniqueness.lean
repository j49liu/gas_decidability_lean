import HGAS.Dynamics.StateTimeChange
import Mathlib.Tactic

/-!
# Compact-interval uniqueness for nonautonomous `C¹` ODEs

The compact-interval uniqueness theorem in `StateTimeChange` is stated for
an autonomous equation

```
x' = F x.
```

For time changes and polar-coordinate constructions we instead encounter

```
x' = v t x.
```

There is no new analytic issue.  Adjoin time as one more state coordinate:

```
(t, x)' = (1, v t x).
```

The augmented field is autonomous and `C¹` whenever the uncurried field
`(t,x) ↦ v t x` is `C¹`.  The theorem below carries out this reduction and
then invokes the already proved compact-interval Grönwall uniqueness
theorem.  It is useful independently of the homogeneous-GAS application.
-/

namespace HGAS

open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [ProperSpace E]

/-- Two solutions of a jointly `C¹` time-dependent ODE which agree at the
left endpoint agree on the whole compact interval. -/
theorem timeDependent_ode_solution_unique_Icc_right_of_contDiff
    (v : ℝ → E → E)
    (hv : ContDiff ℝ 1 (Function.uncurry v))
    {γ η : ℝ → E} {a b : ℝ}
    (hγc : ContinuousOn γ (Icc a b))
    (hγd : ∀ t ∈ Ico a b,
      HasDerivWithinAt γ (v t (γ t)) (Ici t) t)
    (hηc : ContinuousOn η (Icc a b))
    (hηd : ∀ t ∈ Ico a b,
      HasDerivWithinAt η (v t (η t)) (Ici t) t)
    (heq : γ a = η a) :
    EqOn γ η (Icc a b) := by
  let V : ℝ × E → ℝ × E :=
    fun p ↦ (1, v p.1 p.2)
  let Γ : ℝ → ℝ × E := fun t ↦ (t, γ t)
  let H : ℝ → ℝ × E := fun t ↦ (t, η t)
  have hV : ContDiff ℝ 1 V := by
    exact contDiff_const.prodMk hv
  have hΓc : ContinuousOn Γ (Icc a b) := by
    exact continuous_id.continuousOn.prodMk hγc
  have hHc : ContinuousOn H (Icc a b) := by
    exact continuous_id.continuousOn.prodMk hηc
  have hΓd : ∀ t ∈ Ico a b,
      HasDerivWithinAt Γ (V (Γ t)) (Ici t) t := by
    intro t ht
    exact (hasDerivAt_id t).hasDerivWithinAt.prodMk
      (hγd t ht)
  have hHd : ∀ t ∈ Ico a b,
      HasDerivWithinAt H (V (H t)) (Ici t) t := by
    intro t ht
    exact (hasDerivAt_id t).hasDerivWithinAt.prodMk
      (hηd t ht)
  have haugmented :
      EqOn Γ H (Icc a b) :=
    ode_solution_unique_Icc_right_of_contDiff
      hV hΓc hΓd hHc hHd
      (by simp only [Γ, H, heq])
  intro t ht
  exact congrArg Prod.snd (haugmented ht)

end

end HGAS
