import HGAS.Modular.CanonicalLambdaLocal
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# The canonical lambda map as a local covering coordinate

This file packages the precise topological consequence of the local
differential theory of `canonicalLambda`.

The natural target of the modular lambda function is the twice-punctured
plane

```
                         ℂ ∖ {0, 1}.
```

The theta zero-free theorem proves that lambda really takes values in this
space.  The derivative formula from `CanonicalLambdaLocal` proves that its
complex derivative is nowhere zero.  The complex inverse-function theorem
therefore gives a local homeomorphism

```
                    ℍ  →  ℂ ∖ {0, 1}.
```

This is the complete *local* input for path lifting.  A global covering
theorem additionally requires the classical uniformization statement that
lambda identifies the quotient of `ℍ` by `Γ(2)` with the twice-punctured
plane.  That global statement is deliberately not smuggled into this module:
the final section instead records exactly what follows from it, once supplied
as an `IsCoveringMap` hypothesis.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Filter Topology TopologicalSpace
open scoped Manifold Topology

noncomputable section

/-- The natural codomain of the modular lambda function. -/
abbrev LambdaPuncturedPlane :=
  {z : ℂ // z ≠ 0 ∧ z ≠ 1}

/-- The twice-punctured plane is an open subset of `ℂ`. -/
theorem isOpen_lambdaPuncturedPlane :
    IsOpen {z : ℂ | z ≠ 0 ∧ z ≠ 1} := by
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
    (isClosed_singleton.isOpen_compl.inter
      isClosed_singleton.isOpen_compl :
        IsOpen (({0} : Set ℂ)ᶜ ∩ ({1} : Set ℂ)ᶜ))

/-- The canonical lambda function, with its honest punctured codomain. -/
def canonicalLambdaPunctured (z : ℍ) : LambdaPuncturedPlane :=
  ⟨canonicalLambda z,
    canonicalLambda_ne_zero z,
    canonicalLambda_ne_one z⟩

@[simp]
theorem canonicalLambdaPunctured_coe (z : ℍ) :
    (canonicalLambdaPunctured z : ℂ) = canonicalLambda z :=
  rfl

/-- A total ambient representative used to apply the Banach-space inverse
function theorem.  Only its germ at points of `ℍ` is relevant. -/
def canonicalLambdaRaw (z : ℂ) : ℂ :=
  canonicalLambda (ofComplex z)

@[simp]
theorem canonicalLambdaRaw_coe (z : ℍ) :
    canonicalLambdaRaw z = canonicalLambda z := by
  simp [canonicalLambdaRaw]

/-- The ambient representative is analytic at every point of the upper
half-plane. -/
theorem canonicalLambdaRaw_analyticAt (z : ℍ) :
    AnalyticAt ℂ canonicalLambdaRaw z := by
  have hdiff :
      DifferentiableOn ℂ canonicalLambdaRaw
        {w : ℂ | 0 < w.im} := by
    simpa only [canonicalLambdaRaw] using
      (UpperHalfPlane.mdifferentiable_iff.mp
        canonicalLambda_mdifferentiable)
  exact
    (hdiff.analyticOnNhd isOpen_upperHalfPlaneSet)
      z z.im_pos

/-- The ordinary complex derivative of the ambient representative is
nonzero at every point of `ℍ`. -/
theorem deriv_canonicalLambdaRaw_ne_zero (z : ℍ) :
    deriv canonicalLambdaRaw z ≠ 0 := by
  intro hzero
  apply normalizedDeriv_canonicalLambda_ne_zero z
  unfold Derivative.normalizedDerivOfComplex
  change (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    deriv canonicalLambdaRaw z = 0
  rw [hzero, mul_zero]

/-- The ambient representative has a strict nondegenerate derivative at
every upper-half-plane point. -/
theorem canonicalLambdaRaw_hasStrictDerivAt (z : ℍ) :
    HasStrictDerivAt canonicalLambdaRaw
      (deriv canonicalLambdaRaw z) z :=
  (canonicalLambdaRaw_analyticAt z).hasStrictDerivAt

/-- The twice-punctured plane regarded as an open set, for use with
`OpenPartialHomeomorph.subtypeRestr`. -/
def lambdaPuncturedOpens : Opens ℂ :=
  ⟨{z : ℂ | z ≠ 0 ∧ z ≠ 1},
    isOpen_lambdaPuncturedPlane⟩

/-- The punctured target is nonempty. -/
theorem lambdaPuncturedPlane_nonempty :
    Nonempty lambdaPuncturedOpens :=
  ⟨⟨canonicalLambda UpperHalfPlane.I,
    canonicalLambda_ne_zero UpperHalfPlane.I,
    canonicalLambda_ne_one UpperHalfPlane.I⟩⟩

/-- The canonical lambda map into the twice-punctured plane is a local
homeomorphism.

The proof applies the complex inverse-function theorem to an ambient
representative, composes with the standard upper-half-plane chart, and
then restricts the target to `ℂ ∖ {0,1}`. -/
theorem canonicalLambdaPunctured_isLocalHomeomorph :
    IsLocalHomeomorph canonicalLambdaPunctured := by
  apply IsLocalHomeomorph.mk
  intro z
  let hstrict :=
    canonicalLambdaRaw_hasStrictDerivAt z
  let hne :=
    deriv_canonicalLambdaRaw_ne_zero z
  let eC : OpenPartialHomeomorph ℂ ℂ :=
    HasStrictFDerivAt.toOpenPartialHomeomorph
      canonicalLambdaRaw
      (hstrict.hasStrictFDerivAt_equiv hne)
  have hzC : (z : ℂ) ∈ eC.source := by
    change (z : ℂ) ∈
      (HasStrictFDerivAt.toOpenPartialHomeomorph
        canonicalLambdaRaw
        (hstrict.hasStrictFDerivAt_equiv hne)).source
    exact
      HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source
        (hstrict.hasStrictFDerivAt_equiv hne)
  let eH : OpenPartialHomeomorph ℍ ℂ :=
    UpperHalfPlane.ofComplex.symm.trans eC
  have hzH : z ∈ eH.source := by
    exact ⟨by simp [UpperHalfPlane.ofComplex], hzC⟩
  have hvalue :
      eH z = canonicalLambda z := by
    change canonicalLambda
      (UpperHalfPlane.ofComplex (z : ℂ)) =
        canonicalLambda z
    rw [UpperHalfPlane.ofComplex_apply]
  have htarget :
      canonicalLambda z ∈ eH.target := by
    rw [← hvalue]
    exact eH.map_source hzH
  let eT : OpenPartialHomeomorph
      lambdaPuncturedOpens ℍ :=
    eH.symm.subtypeRestr
      lambdaPuncturedPlane_nonempty
  let e : OpenPartialHomeomorph ℍ
      lambdaPuncturedOpens :=
    eT.symm
  have hz : z ∈ e.source := by
    change z ∈ eT.target
    have hmap :
        eH.symm
            (canonicalLambdaPunctured z : ℂ) ∈
          eT.target := by
      exact eH.symm.map_subtype_source
        lambdaPuncturedPlane_nonempty htarget
    convert hmap using 1
    change z = eH.symm (canonicalLambda z)
    rw [← hvalue]
    exact (eH.left_inv hzH).symm
  refine ⟨e, hz, ?_⟩
  intro w hw
  apply Subtype.ext
  change canonicalLambda w = ((eT.symm w :
    lambdaPuncturedOpens) : ℂ)
  have heq :=
    eH.symm.subtypeRestr_symm_apply
      lambdaPuncturedPlane_nonempty hw
  change ((eT.symm w : lambdaPuncturedOpens) : ℂ) =
    eH w at heq
  rw [heq]
  change canonicalLambda w =
    canonicalLambda
      (UpperHalfPlane.ofComplex (w : ℂ))
  rw [UpperHalfPlane.ofComplex_apply]

/-- The punctured lambda map is continuous. -/
theorem canonicalLambdaPunctured_continuous :
    Continuous canonicalLambdaPunctured :=
  canonicalLambdaPunctured_isLocalHomeomorph.continuous

/-- The punctured lambda map is open. -/
theorem canonicalLambdaPunctured_isOpenMap :
    IsOpenMap canonicalLambdaPunctured :=
  canonicalLambdaPunctured_isLocalHomeomorph.isOpenMap

/-- Continuous lifts through canonical lambda are unique on a connected
parameter space after fixing one value.  This uses only the local
homeomorphism theorem, not a global covering theorem. -/
theorem canonicalLambdaPunctured_lift_unique
    {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    {T₁ T₂ : A → ℍ}
    (hT₁ : Continuous T₁)
    (hT₂ : Continuous T₂)
    (hlift :
      canonicalLambdaPunctured ∘ T₁ =
        canonicalLambdaPunctured ∘ T₂)
    (a : A) (ha : T₁ a = T₂ a) :
    T₁ = T₂ :=
  IsSeparatedMap.eq_of_comp_eq
      (T2Space.isSeparatedMap canonicalLambdaPunctured)
      canonicalLambdaPunctured_isLocalHomeomorph.isLocallyInjective
      hT₁ hT₂ hlift a ha

/-- Differentiating a continuous lift needs no global covering theorem.
If `ell = canonicalLambdaPunctured ∘ T` and `ell` is differentiable at
`t`, then the lift is differentiable there, with the derivative supplied
by the ordinary inverse-function formula. -/
theorem canonicalLambdaPunctured_lift_hasDerivAt
    {ell : ℝ → LambdaPuncturedPlane}
    {T : ℝ → ℍ} {t : ℝ} {v : ℂ}
    (hT : Continuous T)
    (hlift : ∀ s,
      canonicalLambdaPunctured (T s) = ell s)
    (hell :
      HasDerivAt (fun s : ℝ ↦ (ell s : ℂ)) v t) :
    HasDerivAt
      (fun s : ℝ ↦ (T s : ℂ))
      (v / deriv canonicalLambdaRaw (T t)) t := by
  let d : ℂ := deriv canonicalLambdaRaw (T t)
  have hd : d ≠ 0 :=
    deriv_canonicalLambdaRaw_ne_zero (T t)
  let eR : ℂ ≃L[ℝ] ℂ :=
    ContinuousLinearEquiv.smulLeft
      (R₁ := ℝ) (Units.mk0 d hd)
  have hfR :
      HasFDerivAt canonicalLambdaRaw
        (eR : ℂ →L[ℝ] ℂ) (T t : ℂ) := by
    have hfC :=
      HasStrictDerivAt.hasStrictFDerivAt_equiv
        (canonicalLambdaRaw_hasStrictDerivAt (T t)) hd
    have hfR' := hfC.restrictScalars ℝ
    apply HasStrictFDerivAt.hasFDerivAt
    convert hfR' using 1
    ext x
    simp only [ContinuousLinearEquiv.coe_coe,
      ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearEquiv.unitsEquivAut_apply,
      Units.val_mk0]
    exact mul_comm _ _
  have hcomp :
      canonicalLambdaRaw ∘
          (fun s : ℝ ↦ (T s : ℂ)) =ᶠ[𝓝 t]
        (fun s : ℝ ↦ (ell s : ℂ)) := by
    filter_upwards [] with s
    simp only [Function.comp_apply]
    rw [canonicalLambdaRaw_coe]
    exact congrArg Subtype.val (hlift s)
  have hg :=
    hfR.of_comp_of_leftInverse
      (f'symm := (eR.symm : ℂ →L[ℝ] ℂ))
      ((UpperHalfPlane.continuous_coe.comp hT).continuousAt)
      hell.hasFDerivAt hcomp eR.symm_apply_apply
  rw [hasFDerivAt_iff_hasDerivAt] at hg
  convert hg using 1
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply_one]
  change v / d = eR.symm v
  rw [div_eq_inv_mul]
  apply eR.injective
  simp [eR, hd]

/-- The global covering statement isolated as a named proposition.

No theorem in this file assumes this proposition implicitly.  It is the
remaining classical uniformization input: proving it amounts to showing
that lambda identifies `ℍ / Γ(2)` with `ℂ ∖ {0,1}`. -/
def CanonicalLambdaIsCovering : Prop :=
  IsCoveringMap canonicalLambdaPunctured

/-- Once the global covering statement is available, every continuous
real trajectory in the twice-punctured plane has a unique continuous
lambda lift after an initial value is fixed. -/
theorem canonicalLambdaPunctured_existsUnique_continuous_lift
    (hcover : CanonicalLambdaIsCovering)
    (ell : C(ℝ, LambdaPuncturedPlane))
    (t₀ : ℝ) (z₀ : ℍ)
    (hinitial :
      canonicalLambdaPunctured z₀ = ell t₀) :
    ∃! T : C(ℝ, ℍ),
      T t₀ = z₀ ∧
        canonicalLambdaPunctured ∘ T = ell := by
  exact
    hcover.existsUnique_continuousMap_lifts
      ell t₀ z₀ hinitial

/-- Conditional global lift package in the exact form needed by the
trajectory reconstruction: the lift is continuous, has the prescribed
initial value, lifts lambda pointwise, and is differentiable wherever the
base trajectory is differentiable. -/
theorem canonicalLambdaPunctured_exists_lift_with_derivatives
    (hcover : CanonicalLambdaIsCovering)
    (ell : C(ℝ, LambdaPuncturedPlane))
    (hell : ∀ t, ∃ v : ℂ,
      HasDerivAt (fun s : ℝ ↦ (ell s : ℂ)) v t)
    (t₀ : ℝ) (z₀ : ℍ)
    (hinitial :
      canonicalLambdaPunctured z₀ = ell t₀) :
    ∃ T : ℝ → ℍ,
      Continuous T ∧
      T t₀ = z₀ ∧
      (∀ t,
        canonicalLambdaPunctured (T t) = ell t) ∧
      ∀ t, ∃ v : ℂ,
        HasDerivAt (fun s : ℝ ↦ (T s : ℂ)) v t := by
  obtain ⟨T, hT, -⟩ :=
    canonicalLambdaPunctured_existsUnique_continuous_lift
      hcover ell t₀ z₀ hinitial
  refine ⟨T, T.continuous, hT.1, ?_, ?_⟩
  · intro t
    exact congrFun hT.2 t
  · intro t
    obtain ⟨v, hv⟩ := hell t
    exact
      ⟨v / deriv canonicalLambdaRaw (T t),
        canonicalLambdaPunctured_lift_hasDerivAt
          T.continuous (fun s ↦ congrFun hT.2 s) hv⟩

end

end HGAS.Modular
