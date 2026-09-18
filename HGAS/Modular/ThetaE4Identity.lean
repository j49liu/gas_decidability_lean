import HGAS.Modular.RamanujanIdentities
import HGAS.Modular.ThetaJacobiIdentity

/-!
# The Eisenstein series `E₄` in theta coordinates

This file proves the classical identity

```
                E₄ = H₂² + H₂ H₄ + H₄².
```

Both sides are holomorphic weight-four level-one modular forms normalized
to have cusp limit one.  We verify the right-hand side under the generators
`S,T`; their difference is then a low-weight cusp form and vanishes.

This direct difference argument avoids bundling the individual theta
constants as level-two modular forms and keeps the dependency on the
external Sphere-Packing development completely out of the trusted project.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real Filter Topology
open ModularForm ModularGroup SlashAction
open scoped Manifold MatrixGroups ModularForm

noncomputable section

/-- The degree-two theta polynomial representing `E₄`. -/
def thetaE4Polynomial : ℍ → ℂ :=
  fun z ↦ H₂ z ^ 2 + H₂ z * H₄ z + H₄ z ^ 2

/-- Product form of the theta polynomial, convenient for slash actions. -/
theorem thetaE4Polynomial_eq_products :
    thetaE4Polynomial =
      H₂ * H₂ + H₂ * H₄ + H₄ * H₄ := by
  ext z
  simp [thetaE4Polynomial, pow_two]

/-- The theta polynomial is invariant under `S` at weight four. -/
theorem thetaE4Polynomial_S_action :
    (thetaE4Polynomial ∣[(4 : ℤ)] S) =
      thetaE4Polynomial := by
  simp only [thetaE4Polynomial_eq_products,
    show (4 : ℤ) = 2 + 2 by norm_num,
    SlashAction.add_slash,
    ModularForm.mul_slash_SL2 2 2 S _ _,
    H₂_S_action, H₄_S_action]
  ext z
  simp only [Pi.mul_apply, Pi.add_apply,
    Pi.neg_apply]
  ring

/-- The theta polynomial is invariant under `T` at weight four. -/
theorem thetaE4Polynomial_T_action :
    (thetaE4Polynomial ∣[(4 : ℤ)] T) =
      thetaE4Polynomial := by
  simp only [thetaE4Polynomial_eq_products,
    show (4 : ℤ) = 2 + 2 by norm_num,
    SlashAction.add_slash,
    ModularForm.mul_slash_SL2 2 2 T _ _,
    H₂_T_action, H₄_T_action,
    ← jacobi_quartic_identity]
  ext z
  simp only [Pi.mul_apply, Pi.add_apply,
    Pi.neg_apply]
  ring

/-- Holomorphy of the theta polynomial. -/
theorem thetaE4Polynomial_mdifferentiable :
    MDiff thetaE4Polynomial := by
  intro z
  exact
    (((H₂_mdifferentiable z).pow 2).add
      ((H₂_mdifferentiable z).mul
        (H₄_mdifferentiable z))).add
          ((H₄_mdifferentiable z).pow 2)

/-- The theta polynomial has cusp limit one. -/
theorem thetaE4Polynomial_tendsto_one :
    Tendsto thetaE4Polynomial atImInfty (𝓝 1) := by
  change Tendsto
    (fun z ↦ H₂ z ^ 2 + H₂ z * H₄ z + H₄ z ^ 2)
    atImInfty (𝓝 1)
  have h :=
    (H₂_tendsto_atImInfty.pow 2).add
      (H₂_tendsto_atImInfty.mul
        H₄_tendsto_atImInfty)
      |>.add (H₄_tendsto_atImInfty.pow 2)
  simpa using h

/-- Difference between the normalized Eisenstein series and its theta
polynomial. -/
def E4ThetaDifference : ℍ → ℂ :=
  (ModularForm.E₄ : ℍ → ℂ) - thetaE4Polynomial

/-- The difference is `S`-invariant. -/
theorem E4ThetaDifference_S_action :
    (E4ThetaDifference ∣[(4 : ℤ)] S) =
      E4ThetaDifference := by
  change
    (((ModularForm.E₄ : ℍ → ℂ) -
        thetaE4Polynomial) ∣[(4 : ℤ)] S) =
      (ModularForm.E₄ : ℍ → ℂ) -
        thetaE4Polynomial
  simp only [sub_eq_add_neg,
    SlashAction.add_slash, SlashAction.neg_slash,
    levelOne_slash_eq_self ModularForm.E₄ S,
    thetaE4Polynomial_S_action]

/-- The difference is `T`-invariant. -/
theorem E4ThetaDifference_T_action :
    (E4ThetaDifference ∣[(4 : ℤ)] T) =
      E4ThetaDifference := by
  change
    (((ModularForm.E₄ : ℍ → ℂ) -
        thetaE4Polynomial) ∣[(4 : ℤ)] T) =
      (ModularForm.E₄ : ℍ → ℂ) -
        thetaE4Polynomial
  simp only [sub_eq_add_neg,
    SlashAction.add_slash, SlashAction.neg_slash,
    levelOne_slash_eq_self ModularForm.E₄ T,
    thetaE4Polynomial_T_action]

/-- Holomorphy of the difference. -/
theorem E4ThetaDifference_mdifferentiable :
    MDiff E4ThetaDifference := by
  intro z
  exact ModularForm.E₄.holo' z
    |>.sub (thetaE4Polynomial_mdifferentiable z)

/-- The difference tends to zero at the cusp. -/
theorem E4ThetaDifference_tendsto_zero :
    Tendsto E4ThetaDifference atImInfty (𝓝 0) := by
  change Tendsto
    (fun z ↦ ModularForm.E₄ z -
      thetaE4Polynomial z)
    atImInfty (𝓝 0)
  have hE4 :
      Tendsto (ModularForm.E₄ : ℍ → ℂ)
        atImInfty (𝓝 1) :=
    eisensteinSeries_tendsto_one_atImInfty
      (by norm_num) ⟨2, rfl⟩
  simpa using
    hE4.sub thetaE4Polynomial_tendsto_one

/-- The Eisenstein-theta difference vanishes identically. -/
theorem E4ThetaDifference_eq_zero :
    E4ThetaDifference = 0 :=
  eq_zero_of_ST_invariant_tendsto_zero
    (by norm_num) E4ThetaDifference
    E4ThetaDifference_S_action
    E4ThetaDifference_T_action
    E4ThetaDifference_mdifferentiable
    E4ThetaDifference_tendsto_zero

/-- **Theta realization of `E₄`.** -/
theorem E4_eq_thetaE4Polynomial :
    (ModularForm.E₄ : ℍ → ℂ) =
      thetaE4Polynomial := by
  ext z
  have hz := congrFun E4ThetaDifference_eq_zero z
  simpa [E4ThetaDifference, sub_eq_zero] using hz

/-- Pointwise expanded form of the `E₄` theta identity. -/
theorem E4_apply_eq_theta (z : ℍ) :
    ModularForm.E₄ z =
      H₂ z ^ 2 + H₂ z * H₄ z + H₄ z ^ 2 := by
  exact congrFun E4_eq_thetaE4Polynomial z

end

end HGAS.Modular
