import HGAS.Modular.CanonicalUnaryTheta

/-!
# Canonical square-root theta state

The selector uses, in addition to the fourth-power state, the signed
square-root coordinates

```
 p₂ = θ₂²,   p₃ = θ₃²,   p₄ = θ₄²,   H = E₂/12.
```

This module assembles those functions into `UnaryRootState` and verifies
all four polynomial links from the paper, including the signed link
`p₃=Y²`.  These are literal polynomial identities, independent of the
later recurrence and moment arguments.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Filter Topology
open scoped Manifold

noncomputable section

/-- The canonical theta square-root extension of
`canonicalUnaryTheta`. -/
def canonicalUnaryRoots (τ : ℍ) :
    UnaryRootState ℂ where
  toUnaryModularState := canonicalUnaryTheta τ
  p2 := theta₂ τ ^ 2
  p3 := theta₃ τ ^ 2
  p4 := theta₄ τ ^ 2
  H := EisensteinSeries.E2 τ / 12

@[simp] theorem canonicalUnaryRoots_toUnaryModularState
    (τ : ℍ) :
    (canonicalUnaryRoots τ).toUnaryModularState =
      canonicalUnaryTheta τ := rfl

@[simp] theorem canonicalUnaryRoots_p2 (τ : ℍ) :
    (canonicalUnaryRoots τ).p2 = theta₂ τ ^ 2 := rfl

@[simp] theorem canonicalUnaryRoots_p3 (τ : ℍ) :
    (canonicalUnaryRoots τ).p3 = theta₃ τ ^ 2 := rfl

@[simp] theorem canonicalUnaryRoots_p4 (τ : ℍ) :
    (canonicalUnaryRoots τ).p4 = theta₄ τ ^ 2 := rfl

@[simp] theorem canonicalUnaryRoots_H (τ : ℍ) :
    (canonicalUnaryRoots τ).H =
      EisensteinSeries.E2 τ / 12 := rfl

/-- The unsigned link `p₂²=A`. -/
theorem canonicalUnaryRoots_link2_eq_zero
    (τ : ℍ) :
    UnaryRootState.link2 (canonicalUnaryRoots τ) = 0 := by
  simp [UnaryRootState.link2, canonicalUnaryRoots,
    canonicalUnaryTheta, H₂]
  ring

/-- The unsigned link `p₄²=C`. -/
theorem canonicalUnaryRoots_link4_eq_zero
    (τ : ℍ) :
    UnaryRootState.link4 (canonicalUnaryRoots τ) = 0 := by
  simp [UnaryRootState.link4, canonicalUnaryRoots,
    canonicalUnaryTheta, H₄]
  ring

/-- The rescaling link `12H=E`. -/
theorem canonicalUnaryRoots_linkH_eq_zero
    (τ : ℍ) :
    UnaryRootState.linkH (canonicalUnaryRoots τ) = 0 := by
  simp [UnaryRootState.linkH, canonicalUnaryRoots,
    canonicalUnaryTheta]
  ring

/-- The signed link `p₃=Y²`, which removes the independent sign
ambiguity in the third square root. -/
theorem canonicalUnaryRoots_signedLink3_eq_zero
    (τ : ℍ) :
    UnaryRootState.signedLink3
      (canonicalUnaryRoots τ) = 0 := by
  simp [UnaryRootState.signedLink3,
    canonicalUnaryRoots, canonicalUnaryTheta]

/-- The square-root Jacobi relation `p₃²=p₂²+p₄²`. -/
theorem canonicalUnaryRoots_p3_sq_eq
    (τ : ℍ) :
    (canonicalUnaryRoots τ).p3 ^ 2 =
      (canonicalUnaryRoots τ).p2 ^ 2 +
        (canonicalUnaryRoots τ).p4 ^ 2 := by
  have hJacobi := congrFun jacobi_quartic_identity τ
  simp only [canonicalUnaryRoots_p2,
    canonicalUnaryRoots_p3, canonicalUnaryRoots_p4,
    H₂, H₃, H₄, Pi.add_apply] at hJacobi ⊢
  ring_nf at hJacobi ⊢
  exact hJacobi.symm

/-- Holomorphy of the `p₂` coordinate. -/
theorem canonicalUnaryRoots_p2_mdifferentiable :
    MDiff (fun τ ↦ (canonicalUnaryRoots τ).p2) :=
  fun τ ↦ (theta₂_mdifferentiable τ).pow 2

/-- Holomorphy of the `p₃` coordinate. -/
theorem canonicalUnaryRoots_p3_mdifferentiable :
    MDiff (fun τ ↦ (canonicalUnaryRoots τ).p3) :=
  fun τ ↦ (theta₃_mdifferentiable τ).pow 2

/-- Holomorphy of the `p₄` coordinate. -/
theorem canonicalUnaryRoots_p4_mdifferentiable :
    MDiff (fun τ ↦ (canonicalUnaryRoots τ).p4) :=
  fun τ ↦ (theta₄_mdifferentiable τ).pow 2

/-- Holomorphy of the rescaled `E₂` coordinate. -/
theorem canonicalUnaryRoots_H_mdifferentiable :
    MDiff (fun τ ↦ (canonicalUnaryRoots τ).H) := by
  change MDiff
    (fun τ : ℍ ↦ EisensteinSeries.E2 τ / 12)
  simpa [div_eq_mul_inv] using
    E2_mdifferentiable.mul
      (mdifferentiable_const :
        MDiff (fun _ : ℍ ↦ (12 : ℂ)⁻¹))

/-- The canonical `p₂` coordinate tends to zero at the cusp. -/
theorem canonicalUnaryRoots_p2_tendsto :
    Tendsto (fun τ ↦ (canonicalUnaryRoots τ).p2)
      atImInfty (𝓝 0) := by
  simpa using theta₂_tendsto_atImInfty.pow 2

/-- The canonical `p₃` coordinate tends to one at the cusp. -/
theorem canonicalUnaryRoots_p3_tendsto :
    Tendsto (fun τ ↦ (canonicalUnaryRoots τ).p3)
      atImInfty (𝓝 1) := by
  simpa using theta₃_tendsto_atImInfty.pow 2

/-- The canonical `p₄` coordinate tends to one at the cusp. -/
theorem canonicalUnaryRoots_p4_tendsto :
    Tendsto (fun τ ↦ (canonicalUnaryRoots τ).p4)
      atImInfty (𝓝 1) := by
  simpa using theta₄_tendsto_atImInfty.pow 2

/-- The canonical `H=E₂/12` coordinate tends to `1/12`. -/
theorem canonicalUnaryRoots_H_tendsto :
    Tendsto (fun τ ↦ (canonicalUnaryRoots τ).H)
      atImInfty (𝓝 (1 / 12 : ℂ)) := by
  convert e2_tendsto_one_atImInfty.div_const 12 using 1

end

end HGAS.Modular
