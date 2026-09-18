import HGAS.Dynamics.C1FlowProfileRegularity
import HGAS.Dynamics.CompactlySupportedFlow
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Tactic

/-!
# Joint `C¹` regularity for compactly supported ODE flows

`CompactlySupportedFlow` constructs the global continuous flow of a compactly
supported `C¹` vector field.  This file proves differentiable dependence on
the initial condition for compactly supported `C²` fields and packages the
result as a `C1ODEFlow`.

The argument is split into reusable layers.  First,
`jointContDiff_of_spatialVariationalData` says that the following two
one-variable facts imply joint `C¹` regularity:

* every orbit is differentiable in time and has derivative given by the vector
  field;
* every fixed-time map is Fréchet differentiable in the initial state, and
  these spatial derivatives vary continuously in `(t,x)`.

The proof is not a mere appeal to a product calculus heuristic.  We use
`hasStrictFDerivAt_uncurry_coprod`, Mathlib's theorem that continuous partial
Fréchet derivatives assemble to a strict Fréchet derivative on a product.
Thus the derivative of `(t,x) ↦ Φ t x` is the expected map

```
(τ,h) ↦ τ • f (Φ t x) + DₓΦ(t,x) h.
```

Second, the Peano--Baker series constructs the fundamental solution

```
J'(t,x) = Df(Φ(t,x)) ∘ J(t,x),    J(0,x) = id.
```

Factorial bounds prove convergence and joint continuity of the series.
A quantitative Grönwall estimate then shows that

```
Φ(t,y) - Φ(t,x) - J(t,x)(y-x) = O(‖y-x‖²),
```

so `J(t,x)` really is the spatial Fréchet derivative.  Negative times are
handled by applying the forward estimate to the reversed flow.

Finally, compact support provides global bounds for `Df`, a global Lipschitz
constant for `Df`, and a global Lipschitz estimate for the flow.  The
unconditional endpoint is `c1ODEFlowOfCompactSupportC2`.

The intermediate structures `SpatialVariationalData` and
`VariationalEquationData` remain useful independently of compact support:
other flow constructions can supply either layer and reuse the assembly
theorems.
-/

noncomputable section

open Function
open MeasureTheory
open scoped Interval NNReal Topology

namespace HGAS.Dynamics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuously varying spatial Fréchet derivatives for a real flow.

`spatialDerivative t x` is intended to be the fundamental solution of the
variational equation along the orbit through `x`.  Keeping the derivative
equation itself out of this minimal interface makes the assembly theorem
applicable whenever differentiable dependence has been established by any
method (Picard iteration, a variational equation, or an implicit-function
argument). -/
structure SpatialVariationalData (Φ : Flow ℝ E) where
  spatialDerivative : ℝ → E → E →L[ℝ] E
  hasFDerivAt_spatial :
    ∀ t x, HasFDerivAt (fun y : E ↦ Φ t y) (spatialDerivative t x) x
  continuous_spatialDerivative :
    Continuous (Function.uncurry spatialDerivative)

/-- The candidate joint derivative formed from the time generator and the
spatial variational derivative. -/
def jointFlowDerivative
    (Φ : Flow ℝ E) (f : E → E)
    (J : ℝ → E → E →L[ℝ] E) (p : ℝ × E) :
    (ℝ × E) →L[ℝ] E :=
  (ContinuousLinearMap.toSpanSingleton ℝ (f (Φ p.1 p.2))).coprod
    (J p.1 p.2)

@[simp]
theorem jointFlowDerivative_apply
    (Φ : Flow ℝ E) (f : E → E)
    (J : ℝ → E → E →L[ℝ] E)
    (p : ℝ × E) (v : ℝ × E) :
    jointFlowDerivative Φ f J p v =
      v.1 • f (Φ p.1 p.2) + J p.1 p.2 v.2 :=
  rfl

/-- The candidate joint derivative is continuous when the flow, generator,
and spatial variational derivative are continuous. -/
theorem continuous_jointFlowDerivative
    (Φ : Flow ℝ E) (f : E → E) (hf : Continuous f)
    (J : ℝ → E → E →L[ℝ] E)
    (hJ : Continuous (Function.uncurry J)) :
    Continuous (jointFlowDerivative Φ f J) := by
  apply Continuous.continuousLinearMapCoprod
  · exact
      (ContinuousLinearMap.toSpanSingletonCLE
        (𝕜 := ℝ) (E := E)).continuous.comp
        (hf.comp Φ.cont')
  · exact hJ

/-- Continuous partial derivatives of a flow assemble to its strict joint
Fréchet derivative.

This is the precise product-calculus step needed in the ODE application.
The theorem is stated for an arbitrary continuous generator and arbitrary
flow; no compactness or finite-dimensionality is used here. -/
theorem hasStrictFDerivAt_uncurry_flow
    (Φ : Flow ℝ E) (f : E → E) (hf : Continuous f)
    (horbit :
      ∀ x t, HasDerivAt (fun s : ℝ ↦ Φ s x) (f (Φ t x)) t)
    (data : SpatialVariationalData Φ) (p : ℝ × E) :
    HasStrictFDerivAt (Function.uncurry Φ)
      (jointFlowDerivative Φ f data.spatialDerivative p) p := by
  let timeDerivative : ℝ → E → ℝ →L[ℝ] E :=
    fun t x ↦ ContinuousLinearMap.toSpanSingleton ℝ (f (Φ t x))
  have htime :
      Continuous (Function.uncurry timeDerivative) := by
    exact
      (ContinuousLinearMap.toSpanSingletonCLE
        (𝕜 := ℝ) (E := E)).continuous.comp
        (hf.comp Φ.cont')
  have hstrict :
      HasStrictFDerivAt (Function.uncurry Φ)
        ((timeDerivative p.1 p.2).coprod
          (data.spatialDerivative p.1 p.2)) p := by
    refine hasStrictFDerivAt_uncurry_coprod
      (𝕜 := ℝ) (u := p)
      (f := fun t x ↦ Φ t x)
      (f₁ := timeDerivative)
      (f₂ := data.spatialDerivative) ?_ ?_ ?_ ?_
    · filter_upwards with q
      simpa only [timeDerivative, Function.uncurry_apply_pair] using
        (horbit q.2 q.1).hasFDerivAt
    · filter_upwards with q
      exact data.hasFDerivAt_spatial q.1 q.2
    · exact htime.continuousAt
    · exact data.continuous_spatialDerivative.continuousAt
  simpa only [jointFlowDerivative, timeDerivative] using hstrict

/-- A continuously varying spatial derivative and the orbit ODE imply joint
`C¹` regularity of the flow action. -/
theorem jointContDiff_of_spatialVariationalData
    (Φ : Flow ℝ E) (f : E → E) (hf : Continuous f)
    (horbit :
      ∀ x t, HasDerivAt (fun s : ℝ ↦ Φ s x) (f (Φ t x)) t)
    (data : SpatialVariationalData Φ) :
    ContDiff ℝ 1 (Function.uncurry Φ) := by
  rw [contDiff_one_iff_hasFDerivAt]
  refine
    ⟨jointFlowDerivative Φ f data.spatialDerivative,
      continuous_jointFlowDerivative Φ f hf data.spatialDerivative
        data.continuous_spatialDerivative, ?_⟩
  intro p
  exact (hasStrictFDerivAt_uncurry_flow Φ f hf horbit data p).hasFDerivAt

/-- Joint `C¹` regularity canonically supplies spatial variational data by
restricting the joint Fréchet derivative to the state summand. -/
noncomputable def spatialVariationalDataOfJointContDiff
    (Φ : Flow ℝ E)
    (hΦ : ContDiff ℝ 1 (Function.uncurry Φ)) :
    SpatialVariationalData Φ where
  spatialDerivative t x :=
    (fderiv ℝ (Function.uncurry Φ) (t, x)).comp
      (ContinuousLinearMap.inr ℝ ℝ E)
  hasFDerivAt_spatial t x := by
    have hjoint :
        HasFDerivAt (Function.uncurry Φ)
          (fderiv ℝ (Function.uncurry Φ) (t, x)) (t, x) :=
      (hΦ.differentiable one_ne_zero (t, x)).hasFDerivAt
    have hslice :=
      hjoint.comp x (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
    simpa only [Function.comp_apply, Function.uncurry_apply_pair] using
      hslice
  continuous_spatialDerivative := by
    exact
      (hΦ.continuous_fderiv one_ne_zero).clm_comp continuous_const

/-- With the orbit ODE fixed, continuously differentiable dependence on
initial state is exactly the missing datum for a jointly `C¹` flow. -/
theorem jointContDiff_iff_nonempty_spatialVariationalData
    (Φ : Flow ℝ E) (f : E → E) (hf : Continuous f)
    (horbit :
      ∀ x t, HasDerivAt (fun s : ℝ ↦ Φ s x) (f (Φ t x)) t) :
    ContDiff ℝ 1 (Function.uncurry Φ) ↔
      Nonempty (SpatialVariationalData Φ) := by
  constructor
  · intro hΦ
    exact ⟨spatialVariationalDataOfJointContDiff Φ hΦ⟩
  · rintro ⟨data⟩
    exact jointContDiff_of_spatialVariationalData Φ f hf horbit data

/-- At time zero the spatial derivative is the identity. -/
theorem SpatialVariationalData.spatialDerivative_zero
    (Φ : Flow ℝ E) (data : SpatialVariationalData Φ) (x : E) :
    data.spatialDerivative 0 x = ContinuousLinearMap.id ℝ E := by
  have hdata := data.hasFDerivAt_spatial 0 x
  have hid : HasFDerivAt (fun y : E ↦ y)
      (ContinuousLinearMap.id ℝ E) x :=
    hasFDerivAt_id x
  have heq : (fun y : E ↦ Φ 0 y) = fun y : E ↦ y := by
    funext y
    exact Φ.map_zero' y
  rw [heq] at hdata
  exact hdata.unique hid

/-- The spatial derivatives inherit the multiplicative cocycle law from the
flow law. -/
theorem SpatialVariationalData.spatialDerivative_add
    (Φ : Flow ℝ E) (data : SpatialVariationalData Φ)
    (t s : ℝ) (x : E) :
    data.spatialDerivative (t + s) x =
      (data.spatialDerivative t (Φ s x)).comp
        (data.spatialDerivative s x) := by
  have hleft :=
    data.hasFDerivAt_spatial (t + s) x
  have hright :=
    (data.hasFDerivAt_spatial t (Φ s x)).comp
      x (data.hasFDerivAt_spatial s x)
  have heq :
      (fun y : E ↦ Φ (t + s) y) =
        (fun y : E ↦ Φ t (Φ s y)) := by
    funext y
    exact Φ.map_add t s y
  rw [heq] at hleft
  exact hleft.unique hright

/-- A globally Lipschitz derivative gives a quadratic first-order remainder.

The constant is deliberately `K` rather than the sharper `K/2`; this form
follows directly from the convex-set mean-value inequality and is exactly
what the variational error estimate needs. -/
theorem norm_sub_fderiv_le_quadratic
    {f : E → E} (hf : Differentiable ℝ f) {K : ℝ≥0}
    (hK : LipschitzWith K (fderiv ℝ f)) (x y : E) :
    ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤
      (K : ℝ) * ‖y - x‖ ^ 2 := by
  have hbound :
      ∀ z ∈ segment ℝ x y,
        ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤
          (K : ℝ) * ‖y - x‖ := by
    intro z hz
    calc
      ‖fderiv ℝ f z - fderiv ℝ f x‖
          = dist (fderiv ℝ f z) (fderiv ℝ f x) := by
              rw [dist_eq_norm]
      _ ≤ (K : ℝ) * dist z x := hK.dist_le_mul z x
      _ = (K : ℝ) * ‖z - x‖ := by rw [dist_eq_norm]
      _ ≤ (K : ℝ) * ‖y - x‖ := by
        gcongr
        exact norm_sub_le_of_mem_segment hz
  have hmean :=
    (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (f := f)
      (f' := fun z ↦ fderiv ℝ f z)
      (φ := fderiv ℝ f x)
      (C := (K : ℝ) * ‖y - x‖)
      (fun z _ ↦ (hf z).hasFDerivAt.hasFDerivWithinAt)
      hbound
      (left_mem_segment ℝ x y)
      (right_mem_segment ℝ x y)
  simpa [pow_two, mul_assoc] using hmean

section PeanoBaker

variable {P V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
/-- A jointly continuous Banach-valued integrand has a continuous
fixed-interval parameter integral. -/
theorem continuous_intervalIntegral_of_continuous_uncurry_vector
    (F : P → ℝ → V)
    (hF : Continuous (Function.uncurry F))
    (a b : ℝ) :
    Continuous (fun p : P ↦ ∫ s in a..b, F p s) := by
  rw [continuous_iff_continuousAt]
  intro p₀
  let C : Set (P × ℝ) :=
    Metric.closedBall p₀ 1 ×ˢ Set.uIcc a b
  have hCcompact : IsCompact C := by
    exact (isCompact_closedBall p₀ 1).prod isCompact_uIcc
  obtain ⟨B₀, hB₀⟩ :=
    hCcompact.bddAbove_image hF.norm.continuousOn
  let B : ℝ := max B₀ 0 + 1
  have hbound :
      ∀ p ∈ Metric.closedBall p₀ 1, ∀ s ∈ Set.uIcc a b,
        ‖F p s‖ ≤ B := by
    intro p hp s hs
    have hle : ‖F p s‖ ≤ B₀ := by
      apply hB₀
      exact ⟨(p, s), ⟨hp, hs⟩, rfl⟩
    exact hle.trans
      ((le_max_left B₀ 0).trans (le_add_of_nonneg_right zero_le_one))
  have hmeas :
      ∀ᶠ p in 𝓝 p₀,
        AEStronglyMeasurable (F p)
          (MeasureTheory.volume.restrict (Ι a b)) := by
    filter_upwards [] with p
    have hslice : Continuous (F p) := by
      simpa [Function.comp_def, Function.uncurry_apply_pair] using
        hF.comp (continuous_const.prodMk continuous_id)
    exact hslice.aestronglyMeasurable
  have hbound_ae :
      ∀ᶠ p in 𝓝 p₀,
        ∀ᵐ s ∂MeasureTheory.volume,
          s ∈ Ι a b → ‖F p s‖ ≤ B := by
    filter_upwards [Metric.closedBall_mem_nhds p₀ zero_lt_one] with p hp
    filter_upwards [] with s hs
    exact hbound p hp s (Set.uIoc_subset_uIcc hs)
  have hB_integrable :
      IntervalIntegrable (fun _ : ℝ ↦ B) MeasureTheory.volume a b :=
    intervalIntegrable_const
  have hpoint :
      ∀ᵐ s ∂MeasureTheory.volume,
        s ∈ Ι a b →
          ContinuousAt (fun p : P ↦ F p s) p₀ := by
    filter_upwards [] with s _hs
    exact
      (hF.comp (continuous_id.prodMk continuous_const)).continuousAt
  exact intervalIntegral.continuousAt_of_dominated_interval
    hmeas hbound_ae hB_integrable hpoint

omit [CompleteSpace V] in
/-- Joint continuity of a moving-endpoint Banach-valued integral. -/
theorem continuous_movingIntervalIntegral_of_continuous_uncurry_vector
    (F : P → ℝ → V)
    (hF : Continuous (Function.uncurry F)) :
    Continuous
      (fun p : P × ℝ ↦ ∫ s in (0 : ℝ)..p.2, F p.1 s) := by
  let G : (P × ℝ) → ℝ → V :=
    fun p u ↦ F p.1 (p.2 * u)
  have hG : Continuous (Function.uncurry G) := by
    exact hF.comp
      ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).mul continuous_snd))
  have hint :
      Continuous
        (fun p : P × ℝ ↦ ∫ u in (0 : ℝ)..1, G p u) :=
    continuous_intervalIntegral_of_continuous_uncurry_vector
      G hG 0 1
  have hnormalized :
      Continuous
        (fun p : P × ℝ ↦
          p.2 • ∫ u in (0 : ℝ)..1, G p u) :=
    continuous_snd.smul hint
  convert hnormalized using 1
  funext p
  simpa only [G, mul_zero, mul_one] using
    (intervalIntegral.smul_integral_comp_mul_left
      (fun s : ℝ ↦ F p.1 s) (a := (0 : ℝ)) (b := 1) p.2).symm

/-- The iterated Volterra terms in the Peano--Baker series. -/
noncomputable def peanoBakerTerm
    (A : P → ℝ → V →L[ℝ] V) :
    ℕ → P → ℝ → V →L[ℝ] V
  | 0, _p, _t => ContinuousLinearMap.id ℝ V
  | n + 1, p, t =>
      ∫ s in (0 : ℝ)..t,
        (A p s).comp (peanoBakerTerm A n p s)

omit [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [CompleteSpace V] in
@[simp]
theorem peanoBakerTerm_zero
    (A : P → ℝ → V →L[ℝ] V) (p : P) (t : ℝ) :
    peanoBakerTerm A 0 p t = ContinuousLinearMap.id ℝ V :=
  rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [CompleteSpace V] in
@[simp]
theorem peanoBakerTerm_succ
    (A : P → ℝ → V →L[ℝ] V)
    (n : ℕ) (p : P) (t : ℝ) :
    peanoBakerTerm A (n + 1) p t =
      ∫ s in (0 : ℝ)..t,
        (A p s).comp (peanoBakerTerm A n p s) :=
  rfl

omit [CompleteSpace V] in
/-- Every Peano--Baker term is jointly continuous in parameter and time. -/
theorem continuous_uncurry_peanoBakerTerm
    (A : P → ℝ → V →L[ℝ] V)
    (hA : Continuous (Function.uncurry A)) :
    ∀ n,
      Continuous (Function.uncurry (peanoBakerTerm A n)) := by
  intro n
  induction n with
  | zero =>
      exact continuous_const
  | succ n ih =>
      let G : P → ℝ → V →L[ℝ] V :=
        fun p s ↦
          (A p s).comp (peanoBakerTerm A n p s)
      have hG : Continuous (Function.uncurry G) := by
        exact hA.clm_comp ih
      change Continuous
        (fun p : P × ℝ ↦
          ∫ s in (0 : ℝ)..p.2,
            (A p.1 s).comp (peanoBakerTerm A n p.1 s))
      exact
        continuous_movingIntervalIntegral_of_continuous_uncurry_vector
          G hG

/-- The derivative in time of a positive-order Peano--Baker term. -/
theorem hasDerivAt_peanoBakerTerm_succ
    (A : P → ℝ → V →L[ℝ] V)
    (hA : Continuous (Function.uncurry A))
    (n : ℕ) (p : P) (t : ℝ) :
    HasDerivAt (fun s ↦ peanoBakerTerm A (n + 1) p s)
      ((A p t).comp (peanoBakerTerm A n p t)) t := by
  have hintegrand :
      Continuous
        (fun s : ℝ ↦
          (A p s).comp (peanoBakerTerm A n p s)) := by
    have hinput : Continuous (fun s : ℝ ↦ (p, s)) :=
      continuous_const.prodMk continuous_id
    exact (hA.comp hinput).clm_comp
      ((continuous_uncurry_peanoBakerTerm A hA n).comp hinput)
  change HasDerivAt
    (fun u : ℝ ↦
      ∫ s in (0 : ℝ)..u,
        (A p s).comp (peanoBakerTerm A n p s))
      ((A p t).comp (peanoBakerTerm A n p t)) t
  exact (hintegrand.integral_hasStrictDerivAt 0 t).hasDerivAt

omit [CompleteSpace V] in
/-- Factorial bound for the Peano--Baker terms. -/
theorem norm_peanoBakerTerm_le
    (A : P → ℝ → V →L[ℝ] V)
    (hAcont : Continuous (Function.uncurry A))
    (M : ℝ≥0) (hA : ∀ p t, ‖A p t‖ ≤ M) :
    ∀ n p t,
      ‖peanoBakerTerm A n p t‖ ≤
        ((M : ℝ) * |t|) ^ n / Nat.factorial n := by
  intro n
  induction n with
  | zero =>
      intro p t
      simpa only [peanoBakerTerm_zero, pow_zero, Nat.factorial_zero,
        Nat.cast_one, div_one] using
        (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := V))
  | succ n ih =>
      intro p t
      have hintegrand :
          Continuous
            (fun s : ℝ ↦
              (A p s).comp (peanoBakerTerm A n p s)) := by
        have hinput : Continuous (fun s : ℝ ↦ (p, s)) :=
          continuous_const.prodMk continuous_id
        exact (hAcont.comp hinput).clm_comp
          ((continuous_uncurry_peanoBakerTerm A hAcont n).comp hinput)
      rw [peanoBakerTerm_succ]
      calc
        ‖∫ s in (0 : ℝ)..t,
            (A p s).comp (peanoBakerTerm A n p s)‖
            ≤ ∫ s in Ι (0 : ℝ) t,
                ‖(A p s).comp (peanoBakerTerm A n p s)‖ :=
          intervalIntegral.norm_integral_le_integral_norm_uIoc
        _ ≤ ∫ s in Ι (0 : ℝ) t,
              (M : ℝ) ^ (n + 1) * |s| ^ n / Nat.factorial n := by
          apply MeasureTheory.setIntegral_mono_on
            hintegrand.norm.integrableOn_uIoc
            (Continuous.integrableOn_uIoc (by fun_prop))
            measurableSet_uIoc
          intro s hs
          calc
            ‖(A p s).comp (peanoBakerTerm A n p s)‖
                ≤ ‖A p s‖ * ‖peanoBakerTerm A n p s‖ :=
              (A p s).opNorm_comp_le _
            _ ≤ (M : ℝ) *
                (((M : ℝ) * |s|) ^ n / Nat.factorial n) := by
              gcongr
              · exact hA p s
              · exact ih p s
            _ = (M : ℝ) ^ (n + 1) * |s| ^ n / Nat.factorial n := by
              rw [mul_pow]
              ring
        _ = ((M : ℝ) * |t|) ^ (n + 1) /
            Nat.factorial (n + 1) := by
          have hpow :
              (∫ a in Ι (0 : ℝ) t, |a| ^ n) =
                |t| ^ (n + 1) / (n + 1) := by
            simpa only [sub_zero] using
              (integral_pow_abs_sub_uIoc
                (a := (0 : ℝ)) (b := t) (n := n))
          rw [MeasureTheory.integral_div,
            MeasureTheory.integral_const_mul,
            hpow]
          simp only [Nat.cast_add, Nat.cast_one,
            Nat.factorial_succ, Nat.cast_mul]
          rw [mul_pow]
          field_simp

/-- The Peano--Baker series converges absolutely at every parameter and
time. -/
theorem summable_peanoBakerTerm
    (A : P → ℝ → V →L[ℝ] V)
    (hAcont : Continuous (Function.uncurry A))
    (M : ℝ≥0) (hA : ∀ p t, ‖A p t‖ ≤ M)
    (p : P) (t : ℝ) :
    Summable (fun n ↦ peanoBakerTerm A n p t) := by
  exact
    (Real.summable_pow_div_factorial ((M : ℝ) * |t|)).of_norm_bounded
      (fun n ↦ norm_peanoBakerTerm_le A hAcont M hA n p t)

/-- The fundamental solution obtained by summing the Peano--Baker series. -/
noncomputable def peanoBakerFundamental
    (A : P → ℝ → V →L[ℝ] V)
    (p : P) (t : ℝ) : V →L[ℝ] V :=
  ∑' n, peanoBakerTerm A n p t

omit [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [CompleteSpace V] in
/-- The Peano--Baker fundamental solution starts at the identity. -/
@[simp]
theorem peanoBakerFundamental_zero
    (A : P → ℝ → V →L[ℝ] V) (p : P) :
    peanoBakerFundamental A p 0 = ContinuousLinearMap.id ℝ V := by
  have htail :
      (fun n : ℕ ↦ peanoBakerTerm A (n + 1) p 0) =
        fun _ ↦ (0 : V →L[ℝ] V) := by
    funext n
    simp only [peanoBakerTerm_succ,
      intervalIntegral.integral_same]
  have hs_tail :
      Summable (fun n : ℕ ↦ peanoBakerTerm A (n + 1) p 0) := by
    rw [htail]
    exact summable_zero
  have hs :
      Summable (fun n : ℕ ↦ peanoBakerTerm A n p 0) :=
    (summable_nat_add_iff 1).mp hs_tail
  rw [peanoBakerFundamental, hs.tsum_eq_zero_add]
  simp only [peanoBakerTerm_zero, peanoBakerTerm_succ,
    intervalIntegral.integral_same, tsum_zero, add_zero]

/-- The Peano--Baker fundamental solution is jointly continuous in its
parameter and time.  The proof uses the factorial estimate on a local time
strip, hence is valid on the whole (noncompact) time axis. -/
theorem continuous_uncurry_peanoBakerFundamental
    (A : P → ℝ → V →L[ℝ] V)
    (hAcont : Continuous (Function.uncurry A))
    (M : ℝ≥0) (hA : ∀ p t, ‖A p t‖ ≤ M) :
    Continuous (Function.uncurry (peanoBakerFundamental A)) := by
  rw [continuous_iff_continuousAt]
  intro q₀
  let T : ℝ := |q₀.2| + 1
  let S : Set (P × ℝ) := {q | |q.2| ≤ T}
  have hT : 0 ≤ T := by
    dsimp only [T]
    positivity
  have hS : S ∈ 𝓝 q₀ := by
    have hlt : |q₀.2| < T := by
      dsimp only [T]
      linarith
    filter_upwards [
      (continuousAt_snd.abs.eventually_lt continuousAt_const hlt)] with q hq
    exact le_of_lt hq
  have hseries :
      Summable
        (fun n : ℕ ↦ ((M : ℝ) * T) ^ n / Nat.factorial n) :=
    Real.summable_pow_div_factorial ((M : ℝ) * T)
  have hcontinuousOn :
      ContinuousOn
        (fun q : P × ℝ ↦
          ∑' n, peanoBakerTerm A n q.1 q.2) S := by
    apply continuousOn_tsum
      (fun n ↦ (continuous_uncurry_peanoBakerTerm A hAcont n).continuousOn)
      hseries
    intro n q hq
    calc
      ‖peanoBakerTerm A n q.1 q.2‖
          ≤ ((M : ℝ) * |q.2|) ^ n / Nat.factorial n :=
        norm_peanoBakerTerm_le A hAcont M hA n q.1 q.2
      _ ≤ ((M : ℝ) * T) ^ n / Nat.factorial n := by
        gcongr
        exact hq
  exact hcontinuousOn.continuousAt hS

/-- The Peano--Baker fundamental solution solves the nonautonomous linear
equation `J' = A J`. -/
theorem hasDerivAt_peanoBakerFundamental
    (A : P → ℝ → V →L[ℝ] V)
    (hAcont : Continuous (Function.uncurry A))
    (M : ℝ≥0) (hA : ∀ p t, ‖A p t‖ ≤ M)
    (p : P) (t : ℝ) :
    HasDerivAt (fun s ↦ peanoBakerFundamental A p s)
      ((A p t).comp (peanoBakerFundamental A p t)) t := by
  let T : ℝ := |t| + 1
  let g : ℕ → ℝ → V →L[ℝ] V :=
    fun n s ↦ peanoBakerTerm A n p s
  let g' : ℕ → ℝ → V →L[ℝ] V :=
    fun n s ↦
      match n with
      | 0 => 0
      | k + 1 => (A p s).comp (peanoBakerTerm A k p s)
  let u : ℕ → ℝ :=
    fun n ↦
      match n with
      | 0 => 0
      | k + 1 =>
          (M : ℝ) * (((M : ℝ) * T) ^ k / Nat.factorial k)
  have hT : 0 < T := by
    dsimp only [T]
    positivity
  have hu_tail : Summable (fun n ↦ u (n + 1)) := by
    simpa only [u] using
      (Real.summable_pow_div_factorial ((M : ℝ) * T)).mul_left
        (M : ℝ)
  have hu : Summable u :=
    (summable_nat_add_iff 1).mp hu_tail
  have hg :
      ∀ n s, s ∈ Set.Ioo (-T) T →
        HasDerivAt (g n) (g' n s) s := by
    intro n s _hs
    cases n with
    | zero =>
        simpa only [g, g'] using
          (hasDerivAt_const s (ContinuousLinearMap.id ℝ V))
    | succ n =>
        simpa only [g, g'] using
          hasDerivAt_peanoBakerTerm_succ A hAcont n p s
  have hg_bound :
      ∀ n s, s ∈ Set.Ioo (-T) T → ‖g' n s‖ ≤ u n := by
    intro n s hs
    cases n with
    | zero =>
        simp only [g', u, norm_zero, le_refl]
    | succ n =>
        have habs : |s| ≤ T :=
          (abs_lt.mpr hs).le
        dsimp only [g', u]
        calc
          ‖(A p s).comp (peanoBakerTerm A n p s)‖
              ≤ ‖A p s‖ * ‖peanoBakerTerm A n p s‖ :=
            (A p s).opNorm_comp_le _
          _ ≤ (M : ℝ) *
              (((M : ℝ) * |s|) ^ n / Nat.factorial n) := by
            gcongr
            · exact hA p s
            · exact norm_peanoBakerTerm_le
                A hAcont M hA n p s
          _ ≤ (M : ℝ) *
              (((M : ℝ) * T) ^ n / Nat.factorial n) := by
            gcongr
  have hzero_mem : (0 : ℝ) ∈ Set.Ioo (-T) T := by
    exact ⟨neg_neg_of_pos hT, hT⟩
  have ht_mem : t ∈ Set.Ioo (-T) T := by
    exact abs_lt.mp (by
      dsimp only [T]
      linarith [abs_nonneg t])
  have hsumAtZero : Summable (fun n ↦ g n 0) := by
    simpa only [g] using
      summable_peanoBakerTerm A hAcont M hA p 0
  have hderiv :=
    hasDerivAt_tsum_of_isPreconnected
      (u := u) (t := Set.Ioo (-T) T)
      (g := g) (g' := g') (y₀ := 0) (y := t)
      hu isOpen_Ioo isPreconnected_Ioo hg hg_bound
      hzero_mem hsumAtZero ht_mem
  have hg'_summable : Summable (fun n ↦ g' n t) :=
    hu.of_norm_bounded (fun n ↦ hg_bound n t ht_mem)
  have hderivativeSeries :
      (∑' n, g' n t) =
        ∑' n, (A p t).comp (peanoBakerTerm A n p t) := by
    rw [hg'_summable.tsum_eq_zero_add]
    simp only [g', zero_add]
  have hmap :
      (A p t).comp (∑' n, peanoBakerTerm A n p t) =
        ∑' n, (A p t).comp (peanoBakerTerm A n p t) := by
    simpa only [ContinuousLinearMap.compL_apply] using
      ((ContinuousLinearMap.compL ℝ V V V) (A p t)).map_tsum
        (summable_peanoBakerTerm A hAcont M hA p t)
  rw [hderivativeSeries, ← hmap] at hderiv
  simpa only [g, peanoBakerFundamental] using hderiv

end PeanoBaker

/-- A continuously varying solution of the first variational equation along
a flow. -/
structure VariationalEquationData
    (Φ : Flow ℝ E) (f : E → E) where
  fundamentalSolution : ℝ → E → E →L[ℝ] E
  continuous_fundamentalSolution :
    Continuous (Function.uncurry fundamentalSolution)
  fundamentalSolution_zero :
    ∀ x, fundamentalSolution 0 x = ContinuousLinearMap.id ℝ E
  hasDerivAt_fundamentalSolution :
    ∀ x t,
      HasDerivAt (fun s : ℝ ↦ fundamentalSolution s x)
        ((fderiv ℝ f (Φ t x)).comp (fundamentalSolution t x)) t

/-- The Peano--Baker construction gives a continuous solution of the first
variational equation whenever the derivative of the vector field is
continuous and globally bounded. -/
noncomputable def peanoBakerVariationalEquationData
    [FiniteDimensional ℝ E]
    (Φ : Flow ℝ E) (f : E → E)
    (hf : ContDiff ℝ 1 f)
    (M : ℝ≥0) (hM : ∀ x, ‖fderiv ℝ f x‖ ≤ M) :
    VariationalEquationData Φ f := by
  let A : E → ℝ → E →L[ℝ] E :=
    fun x t ↦ fderiv ℝ f (Φ t x)
  have hA : Continuous (Function.uncurry A) := by
    exact (hf.continuous_fderiv one_ne_zero).comp
      (Φ.cont'.comp (continuous_snd.prodMk continuous_fst))
  have hAbound : ∀ x t, ‖A x t‖ ≤ M := by
    intro x t
    exact hM (Φ t x)
  exact
    { fundamentalSolution :=
        fun t x ↦ peanoBakerFundamental A x t
      continuous_fundamentalSolution := by
        exact
          (continuous_uncurry_peanoBakerFundamental A hA M hAbound).comp
            (continuous_snd.prodMk continuous_fst)
      fundamentalSolution_zero := by
        intro x
        exact peanoBakerFundamental_zero A x
      hasDerivAt_fundamentalSolution := by
        intro x t
        exact
          hasDerivAt_peanoBakerFundamental A hA M hAbound x t }

/-- `gronwallBound` is homogeneous in its inhomogeneous-error parameter
when the initial error is zero. -/
theorem gronwallBound_zero_mul (M c r t : ℝ) :
    gronwallBound 0 M (c * r) t =
      gronwallBound 0 M c t * r := by
  by_cases hM : M = 0
  · subst M
    simp [gronwallBound_K0]
    ring
  · simp [gronwallBound_of_K_ne_0 hM]
    ring

/-- Quantitative forward-time error estimate for a solution of the
variational equation.

The estimate is global in the perturbed initial state `y`.  Its right-hand
side is quadratic in `‖y-x‖`, which is the crucial fact for extracting a
Fréchet derivative. -/
theorem VariationalEquationData.spatial_remainder_bound_of_nonneg
    (Φ : Flow ℝ E) (f : E → E)
    (horbit :
      ∀ x t, HasDerivAt (fun s : ℝ ↦ Φ s x) (f (Φ t x)) t)
    (data : VariationalEquationData Φ f)
    (hf : Differentiable ℝ f)
    {K : ℝ≥0} (hK : LipschitzWith K (fderiv ℝ f))
    {L : ℝ≥0}
    (hflow :
      ∀ x y t,
        dist (Φ t x) (Φ t y) ≤
          dist x y * Real.exp ((L : ℝ) * |t|))
    {M : ℝ} (hM : ∀ z, ‖fderiv ℝ f z‖ ≤ M)
    (x y : E) {t : ℝ} (ht : 0 ≤ t) :
    ‖Φ t y - Φ t x -
        data.fundamentalSolution t x (y - x)‖ ≤
      gronwallBound 0 M
          ((K : ℝ) * Real.exp ((L : ℝ) * t) ^ 2) t *
        ‖y - x‖ ^ 2 := by
  let h : E := y - x
  let r : ℝ → E := fun s ↦
    Φ s y - Φ s x - data.fundamentalSolution s x h
  let r' : ℝ → E := fun s ↦
    f (Φ s y) - f (Φ s x) -
      ((fderiv ℝ f (Φ s x)).comp
        (data.fundamentalSolution s x)) h
  have hr_continuous : Continuous r := by
    have hflow_y : Continuous (fun s : ℝ ↦ Φ s y) :=
      Φ.cont'.comp (continuous_id.prodMk continuous_const)
    have hflow_x : Continuous (fun s : ℝ ↦ Φ s x) :=
      Φ.cont'.comp (continuous_id.prodMk continuous_const)
    have hJ : Continuous
        (fun s : ℝ ↦ data.fundamentalSolution s x) :=
      data.continuous_fundamentalSolution.comp
        (continuous_id.prodMk continuous_const)
    exact (hflow_y.sub hflow_x).sub
      (hJ.clm_apply continuous_const)
  have hr_deriv : ∀ s, HasDerivAt r (r' s) s := by
    intro s
    have hlinear :=
      (data.hasDerivAt_fundamentalSolution x s).clm_apply
        (hasDerivAt_const s h)
    simpa only [r, r', zero_add, map_zero, add_zero] using
      ((horbit y s).sub (horbit x s)).sub hlinear
  have hr_zero : r 0 = 0 := by
    simp only [r, data.fundamentalSolution_zero,
      ContinuousLinearMap.id_apply, Φ.map_zero_apply, h]
    abel
  let c : ℝ := (K : ℝ) * Real.exp ((L : ℝ) * t) ^ 2
  have hc_nonneg : 0 ≤ c := by
    dsimp only [c]
    positivity
  have hr'_bound :
      ∀ s ∈ Set.Ico (0 : ℝ) t,
        ‖r' s‖ ≤ M * ‖r s‖ + c * ‖h‖ ^ 2 := by
    intro s hs
    let d : E := Φ s y - Φ s x
    let A : E →L[ℝ] E := fderiv ℝ f (Φ s x)
    let q : E := f (Φ s y) - f (Φ s x) - A d
    have hr'_eq : r' s = A (r s) + q := by
      dsimp only [r', r, d, A, q]
      simp only [ContinuousLinearMap.comp_apply, map_sub]
      abel
    have hq :
        ‖q‖ ≤ (K : ℝ) * ‖d‖ ^ 2 := by
      exact norm_sub_fderiv_le_quadratic hf hK (Φ s x) (Φ s y)
    have hs_nonneg : 0 ≤ s := hs.1
    have hs_le : s ≤ t := hs.2.le
    have hd :
        ‖d‖ ≤ ‖h‖ * Real.exp ((L : ℝ) * t) := by
      calc
        ‖d‖ = dist (Φ s y) (Φ s x) := by
          rw [dist_eq_norm]
        _ ≤ dist y x * Real.exp ((L : ℝ) * |s|) :=
          hflow y x s
        _ = ‖h‖ * Real.exp ((L : ℝ) * s) := by
          rw [dist_eq_norm, abs_of_nonneg hs_nonneg]
        _ ≤ ‖h‖ * Real.exp ((L : ℝ) * t) := by
          gcongr
    rw [hr'_eq]
    calc
      ‖A (r s) + q‖ ≤ ‖A (r s)‖ + ‖q‖ := norm_add_le _ _
      _ ≤ ‖A‖ * ‖r s‖ + (K : ℝ) * ‖d‖ ^ 2 := by
        gcongr
        exact ContinuousLinearMap.le_opNorm A (r s)
      _ ≤ M * ‖r s‖ +
          (K : ℝ) * (‖h‖ * Real.exp ((L : ℝ) * t)) ^ 2 := by
        gcongr
        · exact hM (Φ s x)
      _ = M * ‖r s‖ + c * ‖h‖ ^ 2 := by
        dsimp only [c]
        ring
  have hgronwall :
      ‖r t‖ ≤ gronwallBound 0 M (c * ‖h‖ ^ 2) t := by
    have hg :=
      norm_le_gronwallBound_of_norm_deriv_right_le
        (f := r) (f' := r') (δ := 0) (K := M)
        (ε := c * ‖h‖ ^ 2) (a := 0) (b := t)
        hr_continuous.continuousOn
        (fun s hs ↦ (hr_deriv s).hasDerivWithinAt)
        (by simp [hr_zero])
        hr'_bound
        t
        ⟨ht, le_rfl⟩
    simpa only [sub_zero] using hg
  rw [gronwallBound_zero_mul] at hgronwall
  simpa only [r, h, c] using hgronwall

/-- On nonnegative time slices, a solution of the variational equation is
the spatial Fréchet derivative of the flow. -/
theorem VariationalEquationData.hasFDerivAt_spatial_of_nonneg
    (Φ : Flow ℝ E) (f : E → E)
    (horbit :
      ∀ x t, HasDerivAt (fun s : ℝ ↦ Φ s x) (f (Φ t x)) t)
    (data : VariationalEquationData Φ f)
    (hf : Differentiable ℝ f)
    {K : ℝ≥0} (hK : LipschitzWith K (fderiv ℝ f))
    {L : ℝ≥0}
    (hflow :
      ∀ x y t,
        dist (Φ t x) (Φ t y) ≤
          dist x y * Real.exp ((L : ℝ) * |t|))
    {M : ℝ} (hM : ∀ z, ‖fderiv ℝ f z‖ ≤ M)
    (x : E) {t : ℝ} (ht : 0 ≤ t) :
    HasFDerivAt (fun y : E ↦ Φ t y)
      (data.fundamentalSolution t x) x := by
  let C : ℝ :=
    gronwallBound 0 M
      ((K : ℝ) * Real.exp ((L : ℝ) * t) ^ 2) t
  have hquadratic :
      (fun y : E ↦
        Φ t y - Φ t x -
          data.fundamentalSolution t x (y - x)) =O[𝓝 x]
        (fun y : E ↦ ‖y - x‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards with y
    simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using
      data.spatial_remainder_bound_of_nonneg
        Φ f horbit hf hK hflow hM x y ht
  rw [hasFDerivAt_iff_isLittleO]
  exact hquadratic.trans_isLittleO
    (Asymptotics.isLittleO_pow_sub_sub x one_lt_two)

/-- Reverse both a flow and its first variational equation. -/
noncomputable def VariationalEquationData.reverse
    (Φ : Flow ℝ E) (f : E → E)
    (data : VariationalEquationData Φ f) :
    VariationalEquationData Φ.reverse (-f) where
  fundamentalSolution t x := data.fundamentalSolution (-t) x
  continuous_fundamentalSolution := by
    exact data.continuous_fundamentalSolution.comp
      (continuous_fst.neg.prodMk continuous_snd)
  fundamentalSolution_zero := by
    intro x
    simpa only [neg_zero] using data.fundamentalSolution_zero x
  hasDerivAt_fundamentalSolution := by
    intro x t
    have h :=
      (data.hasDerivAt_fundamentalSolution x (-t)).scomp
        t (hasDerivAt_neg t)
    simpa only [Function.comp_def, one_mul, Flow.reverse,
      fderiv_neg, ContinuousLinearMap.neg_comp,
      ContinuousLinearMap.neg_apply, neg_one_smul] using h

/-- The variational solution is the spatial derivative also on negative
time slices.  This is the forward theorem applied to the reversed flow and
the negated vector field. -/
theorem VariationalEquationData.hasFDerivAt_spatial_of_nonpos
    (Φ : Flow ℝ E) (f : E → E)
    (horbit :
      ∀ x t, HasDerivAt (fun s : ℝ ↦ Φ s x) (f (Φ t x)) t)
    (data : VariationalEquationData Φ f)
    (hf : Differentiable ℝ f)
    {K : ℝ≥0} (hK : LipschitzWith K (fderiv ℝ f))
    {L : ℝ≥0}
    (hflow :
      ∀ x y t,
        dist (Φ t x) (Φ t y) ≤
          dist x y * Real.exp ((L : ℝ) * |t|))
    {M : ℝ} (hM : ∀ z, ‖fderiv ℝ f z‖ ≤ M)
    (x : E) {t : ℝ} (ht : t ≤ 0) :
    HasFDerivAt (fun y : E ↦ Φ t y)
      (data.fundamentalSolution t x) x := by
  let Ψ : Flow ℝ E := Φ.reverse
  let g : E → E := -f
  let revData : VariationalEquationData Ψ g :=
    data.reverse Φ f
  have hgorbit :
      ∀ z s, HasDerivAt (fun u : ℝ ↦ Ψ u z) (g (Ψ s z)) s := by
    intro z s
    have h := (horbit z (-s)).scomp s (hasDerivAt_neg s)
    simpa only [Ψ, g, Flow.reverse, Function.comp_def, one_mul,
      neg_one_smul, Pi.neg_apply] using h
  have hgdiff : Differentiable ℝ g := by
    simpa only [g] using hf.neg
  have hgK : LipschitzWith K (fderiv ℝ g) := by
    change LipschitzWith K (fderiv ℝ (-f))
    rw [show fderiv ℝ (-f) = -fderiv ℝ f by
      funext z
      exact fderiv_neg]
    exact hK.neg
  have hΨflow :
      ∀ z w s,
        dist (Ψ s z) (Ψ s w) ≤
          dist z w * Real.exp ((L : ℝ) * |s|) := by
    intro z w s
    simpa only [Ψ, Flow.reverse, abs_neg] using hflow z w (-s)
  have hgM : ∀ z, ‖fderiv ℝ g z‖ ≤ M := by
    intro z
    change ‖fderiv ℝ (-f) z‖ ≤ M
    simpa only [fderiv_neg, norm_neg] using hM z
  have hforward :=
    revData.hasFDerivAt_spatial_of_nonneg
      Ψ g hgorbit hgdiff hgK hΨflow hgM x (t := -t)
      (neg_nonneg.mpr ht)
  simpa only [Ψ, g, revData, VariationalEquationData.reverse,
    Flow.reverse, neg_neg] using hforward

/-- A continuous solution of the variational equation is the spatial
Fréchet derivative on every time slice. -/
theorem VariationalEquationData.hasFDerivAt_spatial
    (Φ : Flow ℝ E) (f : E → E)
    (horbit :
      ∀ x t, HasDerivAt (fun s : ℝ ↦ Φ s x) (f (Φ t x)) t)
    (data : VariationalEquationData Φ f)
    (hf : Differentiable ℝ f)
    {K : ℝ≥0} (hK : LipschitzWith K (fderiv ℝ f))
    {L : ℝ≥0}
    (hflow :
      ∀ x y t,
        dist (Φ t x) (Φ t y) ≤
          dist x y * Real.exp ((L : ℝ) * |t|))
    {M : ℝ} (hM : ∀ z, ‖fderiv ℝ f z‖ ≤ M)
    (t : ℝ) (x : E) :
    HasFDerivAt (fun y : E ↦ Φ t y)
      (data.fundamentalSolution t x) x := by
  rcases le_total 0 t with ht | ht
  · exact data.hasFDerivAt_spatial_of_nonneg
      Φ f horbit hf hK hflow hM x ht
  · exact data.hasFDerivAt_spatial_of_nonpos
      Φ f horbit hf hK hflow hM x ht

/-- A continuous variational-equation solution produces the minimal spatial
data expected by the joint-regularity assembly theorem. -/
noncomputable def VariationalEquationData.toSpatialVariationalData
    (Φ : Flow ℝ E) (f : E → E)
    (horbit :
      ∀ x t, HasDerivAt (fun s : ℝ ↦ Φ s x) (f (Φ t x)) t)
    (data : VariationalEquationData Φ f)
    (hf : Differentiable ℝ f)
    {K : ℝ≥0} (hK : LipschitzWith K (fderiv ℝ f))
    {L : ℝ≥0}
    (hflow :
      ∀ x y t,
        dist (Φ t x) (Φ t y) ≤
          dist x y * Real.exp ((L : ℝ) * |t|))
    {M : ℝ} (hM : ∀ z, ‖fderiv ℝ f z‖ ≤ M) :
    SpatialVariationalData Φ where
  spatialDerivative := data.fundamentalSolution
  hasFDerivAt_spatial :=
    data.hasFDerivAt_spatial Φ f horbit hf hK hflow hM
  continuous_spatialDerivative :=
    data.continuous_fundamentalSolution

/-- Package a flow with spatial variational data as a `C1ODEFlow`. -/
noncomputable def C1ODEFlow.ofSpatialVariationalData
    (Φ : Flow ℝ E) (f : E → E) (hf : Continuous f)
    (horbit :
      ∀ x t, HasDerivAt (fun s : ℝ ↦ Φ s x) (f (Φ t x)) t)
    (data : SpatialVariationalData Φ) :
    C1ODEFlow E where
  flow := Φ
  generator := f
  jointContDiff :=
    jointContDiff_of_spatialVariationalData Φ f hf horbit data
  generatorODE := horbit

section CompactSupport

variable [FiniteDimensional ℝ E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- The derivative of a compactly supported `C¹` map is globally bounded.

This quantitative lemma is one of the two inputs in the standard
variational-equation proof of smooth dependence. -/
theorem exists_global_fderiv_bound_of_compactSupport
    (f : E → E) (hf : ContDiff ℝ 1 f)
    (hsupport : HasCompactSupport f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ f x‖ ≤ M := by
  have hderivContinuous : Continuous (fderiv ℝ f) :=
    hf.continuous_fderiv one_ne_zero
  obtain ⟨B, hB⟩ :=
    (hsupport.fderiv ℝ).exists_bound_of_continuous
      hderivContinuous
  refine ⟨max B 0, le_max_right B 0, ?_⟩
  intro x
  exact (hB x).trans (le_max_left B 0)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- A compactly supported `C²` map has a globally Lipschitz derivative.

Together with `exists_global_fderiv_bound_of_compactSupport`, this controls
both the homogeneous and inhomogeneous terms in the difference-quotient
error equation. -/
theorem exists_lipschitzWith_fderiv_of_compactSupport
    (f : E → E) (hf : ContDiff ℝ 2 f)
    (hsupport : HasCompactSupport f) :
    ∃ K : ℝ≥0, LipschitzWith K (fderiv ℝ f) := by
  have hderiv : ContDiff ℝ 1 (fderiv ℝ f) := by
    exact hf.fderiv_right (m := 1) (by norm_num)
  exact
    hderiv.lipschitzWith_of_hasCompactSupport
      (hsupport.fderiv ℝ) one_ne_zero

omit [FiniteDimensional ℝ E] in
/-- The compactly supported flow satisfies the required time derivative
equation at every time and initial state. -/
theorem compactlySupportedContDiffFlow_hasDerivAt_orbit
    (f : E → E) (hf : ContDiff ℝ 1 f)
    (hsupport : HasCompactSupport f) (x : E) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ HGAS.compactlySupportedContDiffFlow f hf hsupport s x)
      (f (HGAS.compactlySupportedContDiffFlow f hf hsupport t x)) t :=
  HGAS.compactlySupportedContDiffFlow_isIntegralCurve
    f hf hsupport x t

/-- Once differentiable dependence on initial data is supplied, the existing
compactly supported flow becomes an actual `C1ODEFlow`.

The only non-structural input is `data`.  In a complete smooth-dependence
development it is obtained by solving the variational equation

```
J' = Df(Φ(t,x)) ∘ J,    J(0,x) = id,
```

and proving that `J` is the spatial Fréchet derivative of `Φ`. -/
noncomputable def c1ODEFlowOfCompactSupport
    (f : E → E) (hf : ContDiff ℝ 1 f)
    (hsupport : HasCompactSupport f)
    (data :
      SpatialVariationalData
        (HGAS.compactlySupportedContDiffFlow f hf hsupport)) :
    C1ODEFlow E :=
  C1ODEFlow.ofSpatialVariationalData
    (HGAS.compactlySupportedContDiffFlow f hf hsupport)
    f hf.continuous
    (compactlySupportedContDiffFlow_hasDerivAt_orbit f hf hsupport)
    data

/-- A continuous solution of the first variational equation is enough to
upgrade a compactly supported `C²` vector field to a `C1ODEFlow`.

This intermediate assembly theorem extracts all quantitative constants from
compact support.  The following Peano--Baker specialization supplies its
`data` argument unconditionally. -/
noncomputable def c1ODEFlowOfCompactSupportOfVariationalEquation
    (f : E → E) (hf : ContDiff ℝ 2 f)
    (hsupport : HasCompactSupport f)
    (data :
      VariationalEquationData
        (HGAS.compactlySupportedContDiffFlow f
          (hf.of_le (by norm_num)) hsupport) f) :
    C1ODEFlow E := by
  let hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  let Φ : Flow ℝ E :=
    HGAS.compactlySupportedContDiffFlow f hf1 hsupport
  let derivativeLipschitz :=
    exists_lipschitzWith_fderiv_of_compactSupport f hf hsupport
  let K : ℝ≥0 := Classical.choose derivativeLipschitz
  have hK : LipschitzWith K (fderiv ℝ f) :=
    Classical.choose_spec derivativeLipschitz
  let derivativeBound :=
    exists_global_fderiv_bound_of_compactSupport f hf1 hsupport
  let M : ℝ := Classical.choose derivativeBound
  have hM : ∀ z, ‖fderiv ℝ f z‖ ≤ M :=
    (Classical.choose_spec derivativeBound).2
  let flowData :=
    HGAS.boundedLipschitzDataOfCompactSupport f hf1 hsupport
  let L : ℝ≥0 := flowData.lipschitzConstant
  have hflow :
      ∀ x y t,
        dist (Φ t x) (Φ t y) ≤
          dist x y * Real.exp ((L : ℝ) * |t|) := by
    intro x y t
    exact
      HGAS.globalCurve_dist_le f flowData.lipschitz
        flowData.norm_le x y t
  have horbit :
      ∀ x t, HasDerivAt (fun s : ℝ ↦ Φ s x) (f (Φ t x)) t :=
    compactlySupportedContDiffFlow_hasDerivAt_orbit
      f hf1 hsupport
  let spatial : SpatialVariationalData Φ :=
    data.toSpatialVariationalData
      Φ f horbit hf1.differentiable_one hK hflow hM
  exact c1ODEFlowOfCompactSupport f hf1 hsupport spatial

/-- Every compactly supported `C²` vector field on a finite-dimensional real
normed space generates a global jointly `C¹` ODE flow.

This is the unconditional smooth-dependence theorem assembled in this file.
The Peano--Baker series constructs the first variational equation, the
quadratic remainder estimate identifies that series with the derivative in
the initial state, and the partial-derivative theorem then gives joint
regularity in time and state. -/
noncomputable def c1ODEFlowOfCompactSupportC2
    (f : E → E) (hf : ContDiff ℝ 2 f)
    (hsupport : HasCompactSupport f) :
    C1ODEFlow E :=
  let hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  let derivativeBound :=
    exists_global_fderiv_bound_of_compactSupport f hf1 hsupport
  let B : ℝ := Classical.choose derivativeBound
  let M : ℝ≥0 :=
    ⟨B, (Classical.choose_spec derivativeBound).1⟩
  let Φ : Flow ℝ E :=
    HGAS.compactlySupportedContDiffFlow f hf1 hsupport
  let data : VariationalEquationData Φ f :=
    peanoBakerVariationalEquationData
      Φ f hf1 M (Classical.choose_spec derivativeBound).2
  c1ODEFlowOfCompactSupportOfVariationalEquation
    f hf hsupport data

@[simp]
theorem c1ODEFlowOfCompactSupportC2_flow
    (f : E → E) (hf : ContDiff ℝ 2 f)
    (hsupport : HasCompactSupport f) :
    (c1ODEFlowOfCompactSupportC2 f hf hsupport).flow =
      HGAS.compactlySupportedContDiffFlow f
        (hf.of_le (by norm_num)) hsupport :=
  rfl

@[simp]
theorem c1ODEFlowOfCompactSupportC2_generator
    (f : E → E) (hf : ContDiff ℝ 2 f)
    (hsupport : HasCompactSupport f) :
    (c1ODEFlowOfCompactSupportC2 f hf hsupport).generator = f :=
  rfl

omit [FiniteDimensional ℝ E] in
@[simp]
theorem c1ODEFlowOfCompactSupport_flow
    (f : E → E) (hf : ContDiff ℝ 1 f)
    (hsupport : HasCompactSupport f)
    (data :
      SpatialVariationalData
        (HGAS.compactlySupportedContDiffFlow f hf hsupport)) :
    (c1ODEFlowOfCompactSupport f hf hsupport data).flow =
      HGAS.compactlySupportedContDiffFlow f hf hsupport :=
  rfl

omit [FiniteDimensional ℝ E] in
@[simp]
theorem c1ODEFlowOfCompactSupport_generator
    (f : E → E) (hf : ContDiff ℝ 1 f)
    (hsupport : HasCompactSupport f)
    (data :
      SpatialVariationalData
        (HGAS.compactlySupportedContDiffFlow f hf hsupport)) :
    (c1ODEFlowOfCompactSupport f hf hsupport data).generator = f :=
  rfl

end CompactSupport

end HGAS.Dynamics
