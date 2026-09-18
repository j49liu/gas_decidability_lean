import HGAS.Modular.CanonicalLambdaQuotient
import HGAS.Modular.CanonicalLambdaSurjectivity
import HGAS.Modular.UnaryLambdaDynamics
import Mathlib.Tactic

/-!
# Every generic unary modular trajectory has a global canonical-lambda lift

For a unary modular state, set

```
                  B = A + C,       ℓ = A / B.
```

On the generic locus `A C B ≠ 0`, the coordinate `ℓ` avoids `0` and `1`.
Its trajectory is differentiable by the polynomial ODE.  The now-formalized
global covering theorem for canonical lambda therefore lifts `ℓ` to a
differentiable curve `T : ℝ → ℍ`.

This file is the unconditional bridge from the algebraic unary system to
the Riccati and horocycle reconstruction modules.  No lift, modular
uniformization theorem, or differentiability statement remains as an
external hypothesis.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex

noncomputable section

/-- The generic unary lambda coordinate as a point of the twice-punctured
plane. -/
def genericUnaryLambdaPunctured
    (z : UnaryModularState ℂ)
    (hA : z.A ≠ 0)
    (hC : z.C ≠ 0)
    (hB : UnaryModularState.B z ≠ 0) :
    LambdaPuncturedPlane :=
  ⟨UnaryModularState.lambdaCoordinate z,
    div_ne_zero hA hB,
    by
      intro hOne
      apply hC
      unfold UnaryModularState.lambdaCoordinate at hOne
      rw [div_eq_one_iff_eq hB] at hOne
      simp only [UnaryModularState.B] at hOne
      have hadd :
          z.A + z.C = z.A + 0 := by
        simpa using hOne.symm
      exact add_left_cancel hadd⟩

@[simp]
theorem genericUnaryLambdaPunctured_coe
    (z : UnaryModularState ℂ)
    (hA : z.A ≠ 0)
    (hC : z.C ≠ 0)
    (hB : UnaryModularState.B z ≠ 0) :
    (genericUnaryLambdaPunctured z hA hC hB : ℂ) =
      UnaryModularState.lambdaCoordinate z :=
  rfl

/-- Bundle the lambda coordinate of a generic unary trajectory as a
continuous map into the punctured plane. -/
def genericUnaryLambdaCurve
    {κ : ℂ} {z : ℝ → UnaryModularState ℂ}
    (hz : IsScaledUnaryModularTrajectory κ z)
    (hA : ∀ t, (z t).A ≠ 0)
    (hC : ∀ t, (z t).C ≠ 0)
    (hB : ∀ t, UnaryModularState.B (z t) ≠ 0) :
    C(ℝ, LambdaPuncturedPlane) where
  toFun t :=
    genericUnaryLambdaPunctured
      (z t) (hA t) (hC t) (hB t)
  continuous_toFun := by
    exact
      (hz.continuous_A.div
        (hz.continuous_A.add hz.continuous_C)
        hB).subtype_mk _

@[simp]
theorem genericUnaryLambdaCurve_coe
    {κ : ℂ} {z : ℝ → UnaryModularState ℂ}
    (hz : IsScaledUnaryModularTrajectory κ z)
    (hA : ∀ t, (z t).A ≠ 0)
    (hC : ∀ t, (z t).C ≠ 0)
    (hB : ∀ t, UnaryModularState.B (z t) ≠ 0)
    (t : ℝ) :
    (genericUnaryLambdaCurve hz hA hC hB t : ℂ) =
      UnaryModularState.lambdaCoordinate (z t) :=
  rfl

/-- **Global generic lift.**  Every generic unary trajectory has a
continuous differentiable lift through canonical lambda. -/
theorem exists_differentiable_canonicalLambdaLift_of_generic
    {κ : ℂ} {z : ℝ → UnaryModularState ℂ}
    (hz : IsScaledUnaryModularTrajectory κ z)
    (hA : ∀ t, (z t).A ≠ 0)
    (hC : ∀ t, (z t).C ≠ 0)
    (hB : ∀ t, UnaryModularState.B (z t) ≠ 0) :
    ∃ T : ℝ → ℍ,
      Continuous T ∧
      (∀ t,
        UnaryModularState.lambdaCoordinate (z t) =
          canonicalLambda (T t)) ∧
      ∀ t, ∃ v : ℂ,
        HasDerivAt (fun s : ℝ ↦ (T s : ℂ)) v t := by
  let ell : C(ℝ, LambdaPuncturedPlane) :=
    genericUnaryLambdaCurve hz hA hC hB
  obtain ⟨z₀, hz₀⟩ :=
    canonicalLambdaPunctured_surjective (ell 0)
  have hell :
      ∀ t, ∃ v : ℂ,
        HasDerivAt
          (fun s : ℝ ↦ (ell s : ℂ)) v t := by
    intro t
    refine
      ⟨κ * UnaryModularState.B (z t) *
          UnaryModularState.lambdaCoordinate (z t) *
          (1 -
            UnaryModularState.lambdaCoordinate (z t)),
        ?_⟩
    simpa only [ell, genericUnaryLambdaCurve_coe] using
      hz.lambdaCoordinate_hasDerivAt t (hB t)
  obtain ⟨T, hTcont, -, hTlift, hTdiff⟩ :=
    canonicalLambdaPunctured_exists_lift_with_derivatives_global
      ell hell 0 z₀ hz₀
  refine ⟨T, hTcont, ?_, hTdiff⟩
  intro t
  have heq := congrArg Subtype.val (hTlift t)
  simpa only [canonicalLambdaPunctured_coe,
    ell, genericUnaryLambdaCurve_coe] using heq.symm

end

end HGAS.Modular
