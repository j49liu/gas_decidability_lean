import HGAS.Modular.LevelOneSlashGenerators
import Mathlib.Geometry.Manifold.Notation
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# Low-weight vanishing from `S`- and `T`-invariance

This file packages the standard level-one modular-form argument used by
the theta-constant identities.  A holomorphic function on the upper
half-plane which

* is fixed by the weight-`k` slash actions of `S` and `T`, and
* tends to zero at the infinite cusp

defines a level-one cusp form of weight `k`.  Mathlib proves that every
level-one cusp form of weight strictly below `12` vanishes, so the
original function is identically zero.

The constructor is deliberately independent of theta functions.  It can
be reused whenever an explicit formula is checked only on the two
standard generators.
-/

namespace HGAS.Modular

open UpperHalfPlane Filter Topology
open ModularForm ModularGroup SlashAction
open scoped Manifold MatrixGroups ModularForm

noncomputable section

/-- Build a level-one cusp form from `S`- and `T`-invariance,
holomorphy, and vanishing at the infinite cusp. -/
def cuspFormOfSTTendstoZero
    {k : ℤ} (f : ℍ → ℂ)
    (hS : f ∣[k] S = f)
    (hT : f ∣[k] T = f)
    (hhol : MDiff f)
    (hzero : Tendsto f atImInfty (𝓝 0)) :
    CuspForm 𝒮ℒ k where
  toFun := f
  slash_action_eq' :=
    slashInvariantOnLevelOne_of_S_T f k hS hT
  holo' := hhol
  zero_at_cusps' := fun {c} hc => by
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [slashInvariant_of_S_T f k hS hT γ]
    exact hzero

@[simp]
theorem cuspFormOfSTTendstoZero_apply
    {k : ℤ} (f : ℍ → ℂ)
    (hS : f ∣[k] S = f)
    (hT : f ∣[k] T = f)
    (hhol : MDiff f)
    (hzero : Tendsto f atImInfty (𝓝 0))
    (z : ℍ) :
    cuspFormOfSTTendstoZero f hS hT hhol hzero z = f z :=
  rfl

/-- A holomorphic weight-`k` function fixed by `S` and `T` and
vanishing at the infinite cusp is identically zero when `k < 12`. -/
theorem eq_zero_of_ST_invariant_tendsto_zero
    {k : ℤ} (hk : k < 12) (f : ℍ → ℂ)
    (hS : f ∣[k] S = f)
    (hT : f ∣[k] T = f)
    (hhol : MDiff f)
    (hzero : Tendsto f atImInfty (𝓝 0)) :
    f = 0 := by
  let F : CuspForm 𝒮ℒ k :=
    cuspFormOfSTTendstoZero f hS hT hhol hzero
  have hF : F = 0 :=
    rank_zero_iff_forall_zero.mp
      (CuspForm.rank_eq_zero_of_weight_lt_twelve hk) F
  exact congrArg DFunLike.coe hF

end

end HGAS.Modular
