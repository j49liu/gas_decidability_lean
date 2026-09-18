import HGAS.Analysis.C1ParametricIntervalIntegral
import HGAS.Dynamics.CocycleLyapunovProfile
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# `C¹` regularity of the finite-time cocycle profile

This file supplies the differentiability input needed to turn the
orbitwise identity for `quadraticCocycleProfile` into a Fréchet derivative
identity.

The main device is elementary but useful beyond flows.  A moving-endpoint
integral is rewritten over the fixed interval `[0,1]`:

```
∫ s in 0..t, F x s = t * ∫ u in 0..1, F x (t * u).
```

Consequently, joint `C¹` regularity of `F` implies joint `C¹` regularity of
the left-hand side by the finite-dimensional parametric-integral theorem
in `HGAS.Analysis.C1ParametricIntervalIntegral`.

We package a continuously differentiable ODE flow in `C1ODEFlow`.  Its
generator equation is included even though profile regularity itself only
uses the joint `C¹` action; later modules use the equation to identify the
orbit derivative with the Lie derivative.
-/

noncomputable section

open Function MeasureTheory
open scoped BoundedContinuousFunction Interval

namespace HGAS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A convenient corollary of
`contDiff_one_intervalIntegral_of_continuous_fderiv`: a jointly `C¹`
scalar integrand has a `C¹` finite parametric integral. -/
theorem contDiff_one_intervalIntegral_of_contDiff_uncurry
    (F : E → ℝ → ℝ)
    (hF : ContDiff ℝ 1 (Function.uncurry F))
    (a b : ℝ) :
    ContDiff ℝ 1 (fun x : E ↦ ∫ t in a..b, F x t) := by
  let F' : E → ℝ → E →L[ℝ] ℝ :=
    fun x t ↦ fderiv ℝ (fun y : E ↦ F y t) x
  apply contDiff_one_intervalIntegral_of_continuous_fderiv F F'
  · exact hF.continuous
  · let G : (E × ℝ) → E → ℝ :=
      fun p y ↦ F y p.2
    have hG : ContDiff ℝ 1 (Function.uncurry G) := by
      have hstate :
          ContDiff ℝ 1 (fun q : (E × ℝ) × E ↦ q.2) :=
        contDiff_snd
      have htime :
          ContDiff ℝ 1 (fun q : (E × ℝ) × E ↦ q.1.2) :=
        contDiff_snd.comp contDiff_fst
      exact hF.comp (hstate.prodMk htime)
    have hGfderiv :
        Continuous
          (fun p : E × ℝ ↦
            fderiv ℝ (fun y : E ↦ F y p.2) p.1) := by
      simpa only [G] using
        Continuous.fderiv_one hG continuous_fst
    simpa only [F', Function.uncurry_apply_pair] using hGfderiv
  · intro x t
    have hslice : ContDiff ℝ 1 (fun y : E ↦ F y t) := by
      exact hF.comp (contDiff_id.prodMk contDiff_const)
    exact (hslice.differentiable one_ne_zero x).hasFDerivAt

/-- The fixed-interval normalization of a moving-endpoint integral. -/
def normalizedMovingIntegral
    (F : E → ℝ → ℝ) (p : E × ℝ) : ℝ :=
  p.2 * ∫ u in (0 : ℝ)..1, F p.1 (p.2 * u)

/-- The normalized moving integral is jointly `C¹`. -/
theorem contDiff_one_normalizedMovingIntegral
    (F : E → ℝ → ℝ)
    (hF : ContDiff ℝ 1 (Function.uncurry F)) :
    ContDiff ℝ 1 (normalizedMovingIntegral F) := by
  let G : (E × ℝ) → ℝ → ℝ :=
    fun p u ↦ F p.1 (p.2 * u)
  have hG : ContDiff ℝ 1 (Function.uncurry G) := by
    have hstate :
        ContDiff ℝ 1 (fun q : (E × ℝ) × ℝ ↦ q.1.1) :=
      contDiff_fst.comp contDiff_fst
    have htime :
        ContDiff ℝ 1 (fun q : (E × ℝ) × ℝ ↦ q.1.2 * q.2) :=
      (contDiff_snd.comp contDiff_fst).mul contDiff_snd
    exact hF.comp (hstate.prodMk htime)
  have hintegral :
      ContDiff ℝ 1
        (fun p : E × ℝ ↦ ∫ u in (0 : ℝ)..1, G p u) :=
    contDiff_one_intervalIntegral_of_contDiff_uncurry G hG 0 1
  exact contDiff_snd.mul hintegral

omit [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] in
/-- The normalized expression is exactly the oriented integral from
zero to the moving endpoint. -/
theorem normalizedMovingIntegral_eq
    (F : E → ℝ → ℝ) (x : E) (t : ℝ) :
    normalizedMovingIntegral F (x, t) =
      ∫ s in (0 : ℝ)..t, F x s := by
  simpa [normalizedMovingIntegral] using
    (intervalIntegral.smul_integral_comp_mul_left
      (fun s : ℝ ↦ F x s) (a := (0 : ℝ)) (b := 1) t)

/-- Joint `C¹` regularity of a moving-endpoint integral. -/
theorem contDiff_one_movingIntervalIntegral
    (F : E → ℝ → ℝ)
    (hF : ContDiff ℝ 1 (Function.uncurry F)) :
    ContDiff ℝ 1
      (fun p : E × ℝ ↦ ∫ s in (0 : ℝ)..p.2, F p.1 s) := by
  have hnormalized :=
    contDiff_one_normalizedMovingIntegral F hF
  rw [show
    (fun p : E × ℝ ↦ ∫ s in (0 : ℝ)..p.2, F p.1 s) =
      normalizedMovingIntegral F by
        funext p
        exact (normalizedMovingIntegral_eq F p.1 p.2).symm]
  exact hnormalized

namespace Dynamics

/-- A global real flow with a jointly `C¹` action and an autonomous
generator equation.

The order in `jointContDiff` agrees with `Flow`: the uncurried action maps
`(t,x)` to `flow t x`. -/
structure C1ODEFlow (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] where
  flow : Flow ℝ E
  generator : E → E
  jointContDiff : ContDiff ℝ 1 (Function.uncurry flow)
  generatorODE :
    ∀ x t,
      HasDerivAt (fun s : ℝ ↦ flow s x)
        (generator (flow t x)) t

instance : Coe (C1ODEFlow E) (Flow ℝ E) :=
  ⟨C1ODEFlow.flow⟩

omit [FiniteDimensional ℝ E] in
@[simp]
theorem C1ODEFlow.coe_flow (Φ : C1ODEFlow E) :
    (Φ : Flow ℝ E) = Φ.flow :=
  rfl

omit [FiniteDimensional ℝ E] in
/-- A fixed initial condition follows the packaged generator equation. -/
theorem C1ODEFlow.hasDerivAt_orbit
    (Φ : C1ODEFlow E) (x : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ Φ.flow s x)
      (Φ.generator (Φ.flow t x)) t :=
  Φ.generatorODE x t

omit [FiniteDimensional ℝ E] in
/-- The observable evaluated along a `C¹` flow is jointly `C¹` in initial
condition and time (with the state variable ordered first). -/
theorem C1ODEFlow.contDiff_orbitObservable
    (Φ : C1ODEFlow E) (a : E →ᵇ ℝ)
    (ha : ContDiff ℝ 1 (a : E → ℝ)) :
    ContDiff ℝ 1
      (Function.uncurry fun x t ↦ a (Φ.flow t x)) := by
  exact ha.comp
    (Φ.jointContDiff.comp (contDiff_snd.prodMk contDiff_fst))

/-- The additive orbit cocycle is jointly `C¹` in state and terminal
time. -/
theorem C1ODEFlow.contDiff_orbitIntegral
    (Φ : C1ODEFlow E) (a : E →ᵇ ℝ)
    (ha : ContDiff ℝ 1 (a : E → ℝ)) :
    ContDiff ℝ 1
      (Function.uncurry fun x t ↦ orbitIntegral Φ.flow a t x) := by
  let F : E → ℝ → ℝ :=
    fun x t ↦ a (Φ.flow t x)
  have hF : ContDiff ℝ 1 (Function.uncurry F) := by
    simpa only [F] using Φ.contDiff_orbitObservable a ha
  simpa only [orbitIntegral, F] using
    contDiff_one_movingIntervalIntegral F hF

/-- The exponential quadratic cocycle weight is jointly `C¹` in state and
time. -/
theorem C1ODEFlow.contDiff_quadraticCocycleWeight
    (Φ : C1ODEFlow E) (a : E →ᵇ ℝ)
    (ha : ContDiff ℝ 1 (a : E → ℝ)) :
    ContDiff ℝ 1
      (Function.uncurry fun x t ↦
        quadraticCocycleWeight Φ.flow a t x) := by
  have hA := Φ.contDiff_orbitIntegral a ha
  simpa only [quadraticCocycleWeight] using
    Real.contDiff_exp.comp (contDiff_const.mul hA)

/-- **`C¹` regularity of the finite-time quadratic cocycle profile.**

No sign assumption on `T` is needed: interval integrals are oriented. -/
theorem C1ODEFlow.contDiff_quadraticCocycleProfile
    (Φ : C1ODEFlow E) (a : E →ᵇ ℝ)
    (ha : ContDiff ℝ 1 (a : E → ℝ))
    (T : ℝ) :
    ContDiff ℝ 1
      (quadraticCocycleProfile Φ.flow a T) := by
  let W : E → ℝ → ℝ :=
    fun x t ↦ quadraticCocycleWeight Φ.flow a t x
  have hW : ContDiff ℝ 1 (Function.uncurry W) := by
    simpa only [W] using
      Φ.contDiff_quadraticCocycleWeight a ha
  simpa only [quadraticCocycleProfile, W] using
    contDiff_one_intervalIntegral_of_contDiff_uncurry W hW 0 T

/-- The packaged ODE identity and profile regularity turn the orbitwise
cocycle calculation into the exact Fréchet directional derivative formula.

This is the form used in the finite-time Lyapunov construction. -/
theorem C1ODEFlow.fderiv_quadraticCocycleProfile_generator
    (Φ : C1ODEFlow E) (a : E →ᵇ ℝ)
    (ha : ContDiff ℝ 1 (a : E → ℝ))
    (T : ℝ) (x : E) :
    fderiv ℝ (quadraticCocycleProfile Φ.flow a T) x
        (Φ.generator x) =
      quadraticCocycleWeight Φ.flow a T x - 1 -
        2 * a x * quadraticCocycleProfile Φ.flow a T x := by
  apply
    HGAS.Dynamics.fderiv_quadraticCocycleProfile_generator
      Φ.flow a Φ.generator T x
  · simpa only [Φ.flow.map_zero_apply] using
      Φ.generatorODE x 0
  · exact
      (Φ.contDiff_quadraticCocycleProfile a ha T).differentiable
        one_ne_zero x

end Dynamics

end HGAS
