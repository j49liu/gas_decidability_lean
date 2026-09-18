import HGAS.Modular.LevelOneLowWeightVanishing
import HGAS.Modular.ThetaAsymptotics
import HGAS.Modular.ThetaHolomorphy
import HGAS.Modular.ThetaTransformations

/-!
# Jacobi's quartic theta identity

We prove

```
                         H₂ + H₄ = H₃,
```

that is, `θ₂⁴ + θ₄⁴ = θ₃⁴`.

The proof is the classical short modular-form argument, but every step is
made explicit.  The difference `g = H₂ + H₄ - H₃` changes sign under both
`S` and `T`; hence `f=g²` is invariant of weight four.  It is holomorphic
and tends to zero at the cusp, so it is a level-one weight-four cusp form.
Mathlib's low-weight dimension theorem forces `f=0`, and pointwise
reducedness of `ℂ` then gives `g=0`.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real Filter Topology
open ModularForm ModularGroup SlashAction
open scoped Manifold MatrixGroups ModularForm

noncomputable section

/-- The difference in Jacobi's quartic identity. -/
def jacobiDifference : ℍ → ℂ :=
  H₂ + H₄ - H₃

/-- The square of the Jacobi difference. -/
def jacobiDifferenceSq : ℍ → ℂ :=
  jacobiDifference ^ 2

/-- The Jacobi difference changes sign under `S`. -/
theorem jacobiDifference_S_action :
    (jacobiDifference ∣[(2 : ℤ)] S) =
      -jacobiDifference := by
  change
    ((H₂ + H₄ - H₃) ∣[(2 : ℤ)] S) =
      -(H₂ + H₄ - H₃)
  simp only [sub_eq_add_neg, SlashAction.add_slash,
    SlashAction.neg_slash, H₂_S_action,
    H₃_S_action, H₄_S_action]
  ext z
  simp only [Pi.add_apply, Pi.neg_apply]
  ring

/-- The Jacobi difference changes sign under `T`. -/
theorem jacobiDifference_T_action :
    (jacobiDifference ∣[(2 : ℤ)] T) =
      -jacobiDifference := by
  change
    ((H₂ + H₄ - H₃) ∣[(2 : ℤ)] T) =
      -(H₂ + H₄ - H₃)
  simp only [sub_eq_add_neg, SlashAction.add_slash,
    SlashAction.neg_slash, H₂_T_action,
    H₃_T_action, H₄_T_action]
  ext z
  simp only [Pi.add_apply, Pi.neg_apply]
  ring

/-- The squared difference is the pointwise product `g*g`. -/
theorem jacobiDifferenceSq_eq_mul :
    jacobiDifferenceSq =
      jacobiDifference * jacobiDifference := by
  ext z
  simp [jacobiDifferenceSq, pow_two]

/-- The squared difference is invariant under `S` at weight four. -/
theorem jacobiDifferenceSq_S_action :
    (jacobiDifferenceSq ∣[(4 : ℤ)] S) =
      jacobiDifferenceSq := by
  simp only [jacobiDifferenceSq_eq_mul,
    show (4 : ℤ) = 2 + 2 by norm_num,
    ModularForm.mul_slash_SL2 2 2 S _ _,
    jacobiDifference_S_action, neg_mul_neg]

/-- The squared difference is invariant under `T` at weight four. -/
theorem jacobiDifferenceSq_T_action :
    (jacobiDifferenceSq ∣[(4 : ℤ)] T) =
      jacobiDifferenceSq := by
  simp only [jacobiDifferenceSq_eq_mul,
    show (4 : ℤ) = 2 + 2 by norm_num,
    ModularForm.mul_slash_SL2 2 2 T _ _,
    jacobiDifference_T_action, neg_mul_neg]

/-- Holomorphy of the Jacobi difference. -/
theorem jacobiDifference_mdifferentiable :
    MDiff jacobiDifference := by
  intro z
  exact
    ((H₂_mdifferentiable z).add
      (H₄_mdifferentiable z)).sub
        (H₃_mdifferentiable z)

/-- Holomorphy of the squared difference. -/
theorem jacobiDifferenceSq_mdifferentiable :
    MDiff jacobiDifferenceSq := by
  intro z
  exact (jacobiDifference_mdifferentiable z).pow 2

/-- The Jacobi difference tends to zero at the cusp. -/
theorem jacobiDifference_tendsto_atImInfty :
    Tendsto jacobiDifference atImInfty (𝓝 0) := by
  change Tendsto
    (fun z ↦ H₂ z + H₄ z - H₃ z)
    atImInfty (𝓝 0)
  simpa using
    H₂_tendsto_atImInfty.add
      H₄_tendsto_atImInfty
      |>.sub H₃_tendsto_atImInfty

/-- The squared Jacobi difference tends to zero at the cusp. -/
theorem jacobiDifferenceSq_tendsto_atImInfty :
    Tendsto jacobiDifferenceSq atImInfty (𝓝 0) := by
  change Tendsto
    (fun z ↦ jacobiDifference z ^ 2)
    atImInfty (𝓝 0)
  simpa using
    jacobiDifference_tendsto_atImInfty.pow 2

/-- The squared difference vanishes identically by low-weight cusp-form
vanishing. -/
theorem jacobiDifferenceSq_eq_zero :
    jacobiDifferenceSq = 0 :=
  eq_zero_of_ST_invariant_tendsto_zero
    (by norm_num) jacobiDifferenceSq
    jacobiDifferenceSq_S_action
    jacobiDifferenceSq_T_action
    jacobiDifferenceSq_mdifferentiable
    jacobiDifferenceSq_tendsto_atImInfty

/-- The unsquared Jacobi difference vanishes identically. -/
theorem jacobiDifference_eq_zero :
    jacobiDifference = 0 := by
  ext z
  have hz := congrFun jacobiDifferenceSq_eq_zero z
  simpa [jacobiDifferenceSq] using hz

/-- **Jacobi's quartic identity:** `θ₂⁴ + θ₄⁴ = θ₃⁴`. -/
theorem jacobi_quartic_identity :
    H₂ + H₄ = H₃ := by
  ext z
  have hz := congrFun jacobiDifference_eq_zero z
  simpa [jacobiDifference, sub_eq_zero] using hz

end

end HGAS.Modular
