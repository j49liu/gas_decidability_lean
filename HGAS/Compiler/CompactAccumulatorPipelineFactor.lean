import HGAS.Compiler.CompactAccumulatorPipelineInterior
import HGAS.Compactification.StereographicDynamics
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# The compact base factor and the finite accumulator chart

The complete source produced by `CompactAccumulatorPipelineCode.fieldCode`
has two geometrically different parts:

* the mixed-central compactification of the original source;
* one final sphere carrying the stereographic accumulator.

This file separates them again, without choosing coordinates on any
mixed-central sphere.  The coordinate projection to the first part is a
continuous factor of the complete flow.  On the invariant finite interior,
the last sphere gives a continuous map to `FiniteAccumulatorChart`.

The proofs are deliberately global.  In particular, the base-factor
semiconjugacy is obtained from uniqueness for the two polynomial ODE
solutions, not by dividing by a central chart weight.
-/

namespace HGAS

open _root_.MvPolynomial
open Function Metric Set
open scoped BoundedContinuousFunction

noncomputable section

namespace CompactAccumulatorPipelineCode

variable {n k l m : ℕ}

/-- Compact mixed-central base, before adjoining the accumulator sphere. -/
abbrev BaseSpace
    (layout : Fin n → Fin k ⊕ Fin l) :=
  UnitSpherePolynomialWrapper.SourceProductSphere
    (MixedCentralPolynomialCode.targetBlock layout)

/-- The raw base coordinates of a complete source point lie on the
mixed-central product of spheres. -/
theorem sourceBasePoint_onSourceProductSpheres
    (layout : Fin n → Fin k ⊕ Fin l)
    (v :
      UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout)) :
    UnitSpherePolynomialWrapper.OnSourceProductSpheres
      (MixedCentralPolynomialCode.targetBlock layout)
      (sourceBasePoint v) := by
  let u : Fin m → ℝ := fun i ↦ sourceAccumulatorU v i
  let W : ℝ := sourceAccumulatorW v
  have hv :
      AccumulatorPolynomialCode.combinedPoint
          (sourceBasePoint v) u W =
        v.1 := by
    exact combinedPoint_decompose v.1
  have hspheres :
      UnitSpherePolynomialWrapper.OnSourceProductSpheres
        (sourceBlock (m := m) layout)
        (AccumulatorPolynomialCode.combinedPoint
          (sourceBasePoint v) u W) := by
    rw [hv]
    exact v.2
  exact
    (AccumulatorPolynomialCode.onSourceProductSpheres_productSphereBlock_iff
        (MixedCentralPolynomialCode.targetBlock layout)
        (sourceBasePoint v) u W).mp hspheres |>.1

/-- Continuous projection from the complete compact source to its base. -/
def baseProjection
    (layout : Fin n → Fin k ⊕ Fin l) :
    UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout) →
      BaseSpace layout :=
  fun v ↦
    ⟨sourceBasePoint v,
      sourceBasePoint_onSourceProductSpheres layout v⟩

theorem continuous_sourceBasePoint
    (layout : Fin n → Fin k ⊕ Fin l) :
    Continuous
      (sourceBasePoint :
        UnitSpherePolynomialWrapper.SourceProductSphere
            (sourceBlock (m := m) layout) →
          Fin (n + k) → ℝ) := by
  unfold sourceBasePoint
  apply continuous_pi
  intro q
  exact
    (continuous_apply
      (AccumulatorPolynomialCode.baseIndex
        (m := m) q)).comp continuous_subtype_val

theorem continuous_baseProjection
    (layout : Fin n → Fin k ⊕ Fin l) :
    Continuous (baseProjection (m := m) layout) :=
  (continuous_sourceBasePoint (m := m) layout).subtype_mk _

/-- The last coordinates of a complete source point lie on the
accumulator unit sphere. -/
theorem sourceAccumulator_mem_sphere
    (layout : Fin n → Fin k ⊕ Fin l)
    (v :
      UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout)) :
    normSq (sourceAccumulatorU v) +
        sourceAccumulatorW v ^ 2 = 1 := by
  have hv :
      AccumulatorPolynomialCode.combinedPoint
          (sourceBasePoint v)
          (sourceAccumulatorU v)
          (sourceAccumulatorW v) =
        v.1 := by
    exact combinedPoint_decompose v.1
  have hspheres :
      UnitSpherePolynomialWrapper.OnSourceProductSpheres
        (sourceBlock (m := m) layout)
        (AccumulatorPolynomialCode.combinedPoint
          (sourceBasePoint v)
          (sourceAccumulatorU v)
          (sourceAccumulatorW v)) := by
    rw [hv]
    exact v.2
  exact
    (AccumulatorPolynomialCode.onSourceProductSpheres_productSphereBlock_iff
        (MixedCentralPolynomialCode.targetBlock layout)
        (sourceBasePoint v)
        (sourceAccumulatorU v)
        (sourceAccumulatorW v)).mp hspheres |>.2

/-- Projection of the final sphere to the algebraic accumulator sphere. -/
def accumulatorProjection
    (layout : Fin n → Fin k ⊕ Fin l)
    (v :
      UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout)) :
    AccumulatorSphere m :=
  ⟨(sourceAccumulatorU v, sourceAccumulatorW v),
    sourceAccumulator_mem_sphere layout v⟩

theorem continuous_sourceAccumulatorU
    (layout : Fin n → Fin k ⊕ Fin l) :
    Continuous
      (sourceAccumulatorU :
        UnitSpherePolynomialWrapper.SourceProductSphere
            (sourceBlock (m := m) layout) →
          Fin m → ℝ) := by
  unfold sourceAccumulatorU
  apply continuous_pi
  intro i
  exact
    (continuous_apply
      (AccumulatorPolynomialCode.uIndex
        (n := n + k) i)).comp continuous_subtype_val

theorem continuous_accumulatorProjection
    (layout : Fin n → Fin k ⊕ Fin l) :
    Continuous (accumulatorProjection (m := m) layout) := by
  apply Continuous.subtype_mk
  exact
    (continuous_sourceAccumulatorU (m := m) layout).prodMk
      (continuous_sourceAccumulatorW (m := m) layout)

/-- On the finite interior the accumulator projection avoids its unique
point at infinity. -/
def finiteAccumulatorProjection
    (layout : Fin n → Fin k ⊕ Fin l) :
    sourceFiniteInteriorSet (m := m) layout →
      FiniteAccumulatorChart m :=
  fun v ↦
    ⟨accumulatorProjection layout v.1,
      (sourceFiniteInteriorSet_iff layout v.1).mp v.2 |>.2⟩

theorem continuous_finiteAccumulatorProjection
    (layout : Fin n → Fin k ⊕ Fin l) :
    Continuous (finiteAccumulatorProjection (m := m) layout) := by
  apply Continuous.subtype_mk
  exact
    (continuous_accumulatorProjection (m := m) layout).comp
      continuous_subtype_val

/-! ## The autonomous compact base flow -/

/-- Global tangency of the mixed-central base field.  Only the already
compact blocks require a source-specific premise; the new affine
compactification spheres are tangent by construction. -/
theorem baseFieldCode_sourceTangentAt
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (P : PolynomialFieldCode n)
    (hcompactBase :
      ∀ y : BaseSpace layout,
        let x : Fin n → ℝ :=
          fun j ↦
            y.1 (MixedCentralPolynomialCode.xIndex
              (k := k) j)
        ∀ c, MixedCentralPolynomialCode.compactBlockDot layout x
          (MixedCentralPolynomialCode.clearedSourceVelocity
            layout M P y.1) c = 0)
    (y : BaseSpace layout) :
    UnitSpherePolynomialWrapper.SourceTangentAt
      (MixedCentralPolynomialCode.targetBlock layout) y.1
      (PolynomialFieldCode.realize
        (baseFieldCode layout M P) y.1) := by
  let x : Fin n → ℝ :=
    fun j ↦
      y.1 (MixedCentralPolynomialCode.xIndex
        (k := k) j)
  let w : Fin k → ℝ :=
    fun b ↦
      y.1 (MixedCentralPolynomialCode.wIndex
        (n := n) b)
  have hy :
      MixedCentralPolynomialCode.chartPoint x w = y.1 :=
    MixedCentralPolynomialCode.chartPoint_decompose y.1
  have hyspheres := y.property
  rw [← hy] at hyspheres ⊢
  apply
    MixedCentralPolynomialCode.fieldCode_sourceTangentAt_chartPoint
      layout M P x w hyspheres
  simpa only [hy] using hcompactBase y

/-- The compactified base field fits under the same uniform odd degree
used for the complete source wrapper. -/
theorem baseFieldCode_termsDegreeLE_wrapperDegree
    (layout : Fin n → Fin k ⊕ Fin l)
    (E M : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j)) :
    ∀ q,
      PolynomialCode.TermsDegreeLE
        (wrapperDegree E k M)
        (baseFieldCode layout M P q) := by
  intro q
  exact
    (MixedCentralPolynomialCode.fieldCode_termsDegreeLE
      layout M P hP q).promote (by
        unfold wrapperDegree
        omega)

/-- Canonical autonomous flow of the compactified base.  The zero reward
is used only to instantiate the reusable positive-sheet construction; it
does not alter the source ODE. -/
def baseFlow
    (layout : Fin n → Fin k ⊕ Fin l)
    (E M : ℕ) (P : PolynomialFieldCode n) :
    Flow ℝ (BaseSpace layout) :=
  UnitSpherePolynomialWrapper.positiveSourceFlow
    (MixedCentralPolynomialCode.targetBlock layout)
    (wrapperDegree E k M)
    (baseFieldCode layout M P)
    PolynomialCode.zero

/-- Every trajectory of the canonical base flow solves the literal
mixed-central polynomial ODE. -/
theorem baseFlow_integralCurve
    (layout : Fin n → Fin k ⊕ Fin l)
    (E M : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
    (hcompactBase :
      ∀ y : BaseSpace layout,
        let x : Fin n → ℝ :=
          fun j ↦
            y.1 (MixedCentralPolynomialCode.xIndex
              (k := k) j)
        ∀ c, MixedCentralPolynomialCode.compactBlockDot layout x
          (MixedCentralPolynomialCode.clearedSourceVelocity
            layout M P y.1) c = 0)
    (y : BaseSpace layout) :
    IsIntegralCurve
      (fun t ↦ (baseFlow layout E M P t y).1)
      (fun _ x ↦
        PolynomialFieldCode.realize
          (baseFieldCode layout M P) x) := by
  exact
    UnitSpherePolynomialWrapper.positiveSourceFlow_isIntegralCurve_sourceField
        (MixedCentralPolynomialCode.targetBlock layout)
        (wrapperDegree E k M)
        (wrapperDegree_odd E k M)
        (baseFieldCode layout M P)
        (baseFieldCode_termsDegreeLE_wrapperDegree
          layout E M P hP)
        PolynomialCode.zero
        (baseFieldCode_sourceTangentAt
          layout M P hcompactBase)
        y

/-! ## Exact factor equation -/

/-- The base coordinates of the complete polynomial field are literally
the mixed-central base field. -/
theorem realize_fieldCode_baseIndex
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (h : Fin m → PolynomialCode n)
    (v :
      UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout))
    (q : Fin (n + k)) :
    PolynomialFieldCode.realize
        (fieldCode layout M κ P h) v.1
        (AccumulatorPolynomialCode.baseIndex
          (m := m) q) =
      PolynomialFieldCode.realize
        (baseFieldCode layout M P)
        (sourceBasePoint v) q := by
  let u : Fin m → ℝ := fun i ↦ sourceAccumulatorU v i
  let W : ℝ := sourceAccumulatorW v
  have hv :
      AccumulatorPolynomialCode.combinedPoint
          (sourceBasePoint v) u W =
        v.1 := by
    exact combinedPoint_decompose v.1
  rw [← hv]
  rw [PolynomialFieldCode.realize_apply,
    fieldCode,
    AccumulatorPolynomialCode.eval₂Hom_fieldCode_base]
  rfl

/-- Projecting any complete source trajectory gives an integral curve of
the autonomous base field. -/
theorem sourceBasePoint_isIntegralCurve
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (h : Fin m → PolynomialCode n)
    (ϕ :
      Flow ℝ
        (UnitSpherePolynomialWrapper.SourceProductSphere
          (sourceBlock (m := m) layout)))
    (hcurve :
      ∀ v,
        IsIntegralCurve
          (fun t ↦ (ϕ t v).1)
          (fun _ x ↦
            PolynomialFieldCode.realize
              (fieldCode layout M κ P h) x))
    (v :
      UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout)) :
    IsIntegralCurve
      (fun t ↦ sourceBasePoint (ϕ t v))
      (fun _ x ↦
        PolynomialFieldCode.realize
          (baseFieldCode layout M P) x) := by
  intro t
  rw [hasDerivAt_pi]
  intro q
  have hcoord :=
    (hasDerivAt_pi.mp (hcurve v t))
      (AccumulatorPolynomialCode.baseIndex
        (m := m) q)
  dsimp only at hcoord
  rw [realize_fieldCode_baseIndex] at hcoord
  simpa only [sourceBasePoint] using hcoord

/-- ODE uniqueness identifies the projected complete trajectory with the
canonical base trajectory. -/
theorem baseProjection_flow_eq
    (layout : Fin n → Fin k ⊕ Fin l)
    (E M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
    (h : Fin m → PolynomialCode n)
    (ϕ :
      Flow ℝ
        (UnitSpherePolynomialWrapper.SourceProductSphere
          (sourceBlock (m := m) layout)))
    (hcurve :
      ∀ v,
        IsIntegralCurve
          (fun t ↦ (ϕ t v).1)
          (fun _ x ↦
            PolynomialFieldCode.realize
              (fieldCode layout M κ P h) x))
    (hcompactBase :
      ∀ y : BaseSpace layout,
        let x : Fin n → ℝ :=
          fun j ↦
            y.1 (MixedCentralPolynomialCode.xIndex
              (k := k) j)
        ∀ c, MixedCentralPolynomialCode.compactBlockDot layout x
          (MixedCentralPolynomialCode.clearedSourceVelocity
            layout M P y.1) c = 0)
    (v :
      UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout))
    (t : ℝ) :
    baseProjection layout (ϕ t v) =
      baseFlow layout E M P t (baseProjection layout v) := by
  apply Subtype.ext
  let gammaOne : ℝ → Fin (n + k) → ℝ :=
    fun s ↦ sourceBasePoint (ϕ s v)
  let gammaTwo : ℝ → Fin (n + k) → ℝ :=
    fun s ↦
      (baseFlow layout E M P s
        (baseProjection layout v)).1
  have hgammaOne :
      IsIntegralCurve gammaOne
        (fun _ x ↦
          PolynomialFieldCode.realize
            (baseFieldCode layout M P) x) := by
    simpa only [gammaOne] using
      sourceBasePoint_isIntegralCurve
        layout M κ P h ϕ hcurve v
  have hgammaTwo :
      IsIntegralCurve gammaTwo
        (fun _ x ↦
          PolynomialFieldCode.realize
            (baseFieldCode layout M P) x) := by
    simpa only [gammaTwo] using
      baseFlow_integralCurve
        layout E M P hP hcompactBase
          (baseProjection layout v)
  have hC1 :
      ContDiff ℝ 1
        (PolynomialFieldCode.realize
          (baseFieldCode layout M P)) :=
    (UnitSpherePolynomialWrapper.contDiff_realize_sourcePolynomialFieldCode
        (baseFieldCode layout M P)).of_le (by norm_num)
  obtain ⟨K, hK⟩ :=
    hC1.contDiffOn.exists_lipschitzOnWith
      one_ne_zero
      (convex_closedBall (0 : Fin (n + k) → ℝ) 1)
      (isCompact_closedBall (0 : Fin (n + k) → ℝ) 1)
  have hOneMem :
      ∀ s,
        gammaOne s ∈
          closedBall (0 : Fin (n + k) → ℝ) 1 := by
    intro s
    have hnorm :=
      UnitSpherePolynomialWrapper.source_norm_le_one_of_onSourceProductSpheres
          (MixedCentralPolynomialCode.targetBlock layout)
          (gammaOne s)
          (baseProjection layout (ϕ s v)).property
    simpa only [Metric.mem_closedBall, dist_zero_right]
      using hnorm
  have hTwoMem :
      ∀ s,
        gammaTwo s ∈
          closedBall (0 : Fin (n + k) → ℝ) 1 := by
    intro s
    have hnorm :=
      UnitSpherePolynomialWrapper.source_norm_le_one_of_onSourceProductSpheres
          (MixedCentralPolynomialCode.targetBlock layout)
          (gammaTwo s)
          (baseFlow layout E M P s
            (baseProjection layout v)).property
    simpa only [Metric.mem_closedBall, dist_zero_right]
      using hnorm
  have heq : gammaOne = gammaTwo := by
    apply ODE_solution_unique_univ
      (v := fun _ : ℝ ↦
        PolynomialFieldCode.realize
          (baseFieldCode layout M P))
      (s := fun _ ↦
        closedBall (0 : Fin (n + k) → ℝ) 1)
      (K := K) (t₀ := 0)
    · intro _
      exact hK
    · intro s
      exact ⟨hgammaOne s, hOneMem s⟩
    · intro s
      exact ⟨hgammaTwo s, hTwoMem s⟩
    · simp [gammaOne, gammaTwo, baseProjection,
        Flow.map_zero_apply]
  exact congrFun heq t

/-- The base projection is a factor map from any complete source flow
solving the emitted ODE to the canonical compact base flow. -/
theorem baseProjection_semiconj
    (layout : Fin n → Fin k ⊕ Fin l)
    (E M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
    (h : Fin m → PolynomialCode n)
    (ϕ :
      Flow ℝ
        (UnitSpherePolynomialWrapper.SourceProductSphere
          (sourceBlock (m := m) layout)))
    (hcurve :
      ∀ v,
        IsIntegralCurve
          (fun t ↦ (ϕ t v).1)
          (fun _ x ↦
            PolynomialFieldCode.realize
              (fieldCode layout M κ P h) x))
    (hcompactBase :
      ∀ y : BaseSpace layout,
        let x : Fin n → ℝ :=
          fun j ↦
            y.1 (MixedCentralPolynomialCode.xIndex
              (k := k) j)
        ∀ c, MixedCentralPolynomialCode.compactBlockDot layout x
          (MixedCentralPolynomialCode.clearedSourceVelocity
            layout M P y.1) c = 0)
    (t : ℝ) :
    Semiconj
      (baseProjection layout)
      (ϕ t)
      (baseFlow layout E M P t) := by
  intro v
  exact
    baseProjection_flow_eq
      layout E M κ P hP h ϕ hcurve hcompactBase v t

/-! ## Restriction to the finite interior -/

/-- Base projection on the invariant finite interior. -/
def restrictedBaseProjection
    (layout : Fin n → Fin k ⊕ Fin l) :
    sourceFiniteInteriorSet (m := m) layout →
      BaseSpace layout :=
  fun v ↦ baseProjection layout v.1

theorem continuous_restrictedBaseProjection
    (layout : Fin n → Fin k ⊕ Fin l) :
    Continuous (restrictedBaseProjection (m := m) layout) :=
  (continuous_baseProjection (m := m) layout).comp
    continuous_subtype_val

/-- The base factor equation remains exact after restricting a complete
flow to the invariant finite interior. -/
theorem restrictedBaseProjection_semiconj
    (layout : Fin n → Fin k ⊕ Fin l)
    (E M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
    (h : Fin m → PolynomialCode n)
    (ϕ :
      Flow ℝ
        (UnitSpherePolynomialWrapper.SourceProductSphere
          (sourceBlock (m := m) layout)))
    (hcurve :
      ∀ v,
        IsIntegralCurve
          (fun t ↦ (ϕ t v).1)
          (fun _ x ↦
            PolynomialFieldCode.realize
              (fieldCode layout M κ P h) x))
    (hcompactBase :
      ∀ y : BaseSpace layout,
        let x : Fin n → ℝ :=
          fun j ↦
            y.1 (MixedCentralPolynomialCode.xIndex
              (k := k) j)
        ∀ c, MixedCentralPolynomialCode.compactBlockDot layout x
          (MixedCentralPolynomialCode.clearedSourceVelocity
            layout M P y.1) c = 0)
    (hinv :
      IsInvariant ϕ
        (sourceFiniteInteriorSet (m := m) layout))
    (t : ℝ) :
    Semiconj
      (restrictedBaseProjection layout)
      ((ϕ.restrict hinv) t)
      (baseFlow layout E M P t) := by
  intro v
  exact
    baseProjection_semiconj
      layout E M κ P hP h ϕ hcurve hcompactBase t v.1

/-! ## The bounded drift observable on the compact base -/

/-- The denominator-cleared, scaled drift observable on the compact base.
Compactness makes this continuous polynomial map automatically bounded. -/
def baseDriftBCF
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (κ : RationalCode)
    (h : Fin m → PolynomialCode n) :
    BaseSpace layout →ᵇ FinVector m ℝ := by
  let f : BaseSpace layout → FinVector m ℝ :=
    fun y i ↦
      eval₂Hom (algebraMap ℚ ℝ) y.1
        (PolynomialCode.decode
          (slowedDriftCode layout M κ h i))
  have hf : Continuous f := by
    apply continuous_pi
    intro i
    have hpoly :=
      MvPolynomial.continuous_eval
        (MvPolynomial.map (algebraMap ℚ ℝ)
          (PolynomialCode.decode
            (slowedDriftCode layout M κ h i)))
    have hcomp := hpoly.comp
      (continuous_subtype_val :
        Continuous
          (fun y : BaseSpace layout ↦ y.1))
    simpa only [MvPolynomial.eval_map, f] using hcomp
  exact BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩

@[simp]
theorem baseDriftBCF_apply
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (κ : RationalCode)
    (h : Fin m → PolynomialCode n)
    (y : BaseSpace layout) (i : Fin m) :
    baseDriftBCF layout M κ h y i =
      eval₂Hom (algebraMap ℚ ℝ) y.1
        (PolynomialCode.decode
          (slowedDriftCode layout M κ h i)) :=
  rfl

/-- Literal accumulator-vector equation at an arbitrary compact source
point, expressed using the base drift observable. -/
theorem realize_fieldCode_accumulatorU
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (h : Fin m → PolynomialCode n)
    (v :
      UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout))
    (i : Fin m) :
    PolynomialFieldCode.realize
        (fieldCode layout M κ P h) v.1
        (AccumulatorPolynomialCode.uIndex
          (n := n + k) i) =
      accumulatorUField
        (sourceAccumulatorU v)
        (sourceAccumulatorW v)
        (baseDriftBCF layout M κ h
          (baseProjection layout v)) i := by
  have hv :
      AccumulatorPolynomialCode.combinedPoint
          (sourceBasePoint v)
          (sourceAccumulatorU v)
          (sourceAccumulatorW v) =
        v.1 := by
    exact combinedPoint_decompose v.1
  rw [← hv]
  rw [PolynomialFieldCode.realize_apply,
    fieldCode,
    AccumulatorPolynomialCode.eval₂Hom_fieldCode_u]
  rfl

/-- Literal accumulator-scalar equation at an arbitrary compact source
point, in the same base-factor form. -/
theorem realize_fieldCode_accumulatorW_factor
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (h : Fin m → PolynomialCode n)
    (v :
      UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout)) :
    PolynomialFieldCode.realize
        (fieldCode layout M κ P h) v.1
        (AccumulatorPolynomialCode.wIndex (n + k) m) =
      accumulatorWField
        (sourceAccumulatorU v)
        (sourceAccumulatorW v)
        (baseDriftBCF layout M κ h
          (baseProjection layout v)) := by
  have hv :
      AccumulatorPolynomialCode.combinedPoint
          (sourceBasePoint v)
          (sourceAccumulatorU v)
          (sourceAccumulatorW v) =
        v.1 := by
    exact combinedPoint_decompose v.1
  rw [← hv]
  rw [PolynomialFieldCode.realize_apply,
    fieldCode,
    AccumulatorPolynomialCode.eval₂Hom_fieldCode_w]
  rfl

/-- Accumulator-vector coordinate derivative along any complete source
flow solving the emitted polynomial ODE. -/
theorem sourceAccumulatorU_hasDerivAt
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (h : Fin m → PolynomialCode n)
    (ϕ :
      Flow ℝ
        (UnitSpherePolynomialWrapper.SourceProductSphere
          (sourceBlock (m := m) layout)))
    (hcurve :
      ∀ v,
        IsIntegralCurve
          (fun t ↦ (ϕ t v).1)
          (fun _ x ↦
            PolynomialFieldCode.realize
              (fieldCode layout M κ P h) x))
    (v :
      UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout))
    (i : Fin m) (t : ℝ) :
    HasDerivAt
      (fun s ↦ sourceAccumulatorU (ϕ s v) i)
      (accumulatorUField
        (sourceAccumulatorU (ϕ t v))
        (sourceAccumulatorW (ϕ t v))
        (baseDriftBCF layout M κ h
          (baseProjection layout (ϕ t v))) i) t := by
  have hcoord :=
    (hasDerivAt_pi.mp (hcurve v t))
      (AccumulatorPolynomialCode.uIndex
        (n := n + k) i)
  dsimp only at hcoord
  rw [realize_fieldCode_accumulatorU] at hcoord
  simpa only [sourceAccumulatorU] using hcoord

/-- Accumulator-scalar coordinate derivative along any complete source
flow solving the emitted polynomial ODE. -/
theorem sourceAccumulatorW_hasDerivAt
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (h : Fin m → PolynomialCode n)
    (ϕ :
      Flow ℝ
        (UnitSpherePolynomialWrapper.SourceProductSphere
          (sourceBlock (m := m) layout)))
    (hcurve :
      ∀ v,
        IsIntegralCurve
          (fun t ↦ (ϕ t v).1)
          (fun _ x ↦
            PolynomialFieldCode.realize
              (fieldCode layout M κ P h) x))
    (v :
      UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout))
    (t : ℝ) :
    HasDerivAt
      (fun s ↦ sourceAccumulatorW (ϕ s v))
      (accumulatorWField
        (sourceAccumulatorU (ϕ t v))
        (sourceAccumulatorW (ϕ t v))
        (baseDriftBCF layout M κ h
          (baseProjection layout (ϕ t v)))) t := by
  have hcoord :=
    (hasDerivAt_pi.mp (hcurve v t))
      (AccumulatorPolynomialCode.wIndex (n + k) m)
  dsimp only at hcoord
  rw [realize_fieldCode_accumulatorW_factor] at hcoord
  simpa only [sourceAccumulatorW] using hcoord

/-- The restricted finite-chart projection satisfies the exact
compactified accumulator-vector equation required by the measure
obstruction. -/
theorem finiteAccumulatorProjection_u_hasDerivAt
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (h : Fin m → PolynomialCode n)
    (ϕ :
      Flow ℝ
        (UnitSpherePolynomialWrapper.SourceProductSphere
          (sourceBlock (m := m) layout)))
    (hcurve :
      ∀ v,
        IsIntegralCurve
          (fun t ↦ (ϕ t v).1)
          (fun _ x ↦
            PolynomialFieldCode.realize
              (fieldCode layout M κ P h) x))
    (hinv :
      IsInvariant ϕ
        (sourceFiniteInteriorSet (m := m) layout))
    (x : sourceFiniteInteriorSet (m := m) layout)
    (i : Fin m) (t : ℝ) :
    HasDerivAt
      (fun r ↦
        (finiteAccumulatorProjection layout
          ((ϕ.restrict hinv) r x)).1.1.1 i)
      (accumulatorUField
        (finiteAccumulatorProjection layout
          ((ϕ.restrict hinv) t x)).1.1.1
        (finiteAccumulatorProjection layout
          ((ϕ.restrict hinv) t x)).1.1.2
        (baseDriftBCF layout M κ h
          (restrictedBaseProjection layout
            ((ϕ.restrict hinv) t x))) i) t := by
  simpa only [finiteAccumulatorProjection,
    accumulatorProjection, restrictedBaseProjection,
    Flow.coe_restrict_apply] using
      sourceAccumulatorU_hasDerivAt
        layout M κ P h ϕ hcurve x.1 i t

/-- The restricted finite-chart projection satisfies the matching
compactified accumulator-scalar equation. -/
theorem finiteAccumulatorProjection_w_hasDerivAt
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (h : Fin m → PolynomialCode n)
    (ϕ :
      Flow ℝ
        (UnitSpherePolynomialWrapper.SourceProductSphere
          (sourceBlock (m := m) layout)))
    (hcurve :
      ∀ v,
        IsIntegralCurve
          (fun t ↦ (ϕ t v).1)
          (fun _ x ↦
            PolynomialFieldCode.realize
              (fieldCode layout M κ P h) x))
    (hinv :
      IsInvariant ϕ
        (sourceFiniteInteriorSet (m := m) layout))
    (x : sourceFiniteInteriorSet (m := m) layout)
    (t : ℝ) :
    HasDerivAt
      (fun r ↦
        (finiteAccumulatorProjection layout
          ((ϕ.restrict hinv) r x)).1.1.2)
      (accumulatorWField
        (finiteAccumulatorProjection layout
          ((ϕ.restrict hinv) t x)).1.1.1
        (finiteAccumulatorProjection layout
          ((ϕ.restrict hinv) t x)).1.1.2
        (baseDriftBCF layout M κ h
          (restrictedBaseProjection layout
            ((ϕ.restrict hinv) t x)))) t := by
  simpa only [finiteAccumulatorProjection,
    accumulatorProjection, restrictedBaseProjection,
    Flow.coe_restrict_apply] using
      sourceAccumulatorW_hasDerivAt
        layout M κ P h ϕ hcurve x.1 t

/-- Tangency premise for the complete compiler, derived solely from
global tangency of the compact base blocks. -/
theorem fullCompactTangencyHypothesis_of_base
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (P : PolynomialFieldCode n)
    (hcompactBase :
      ∀ y : BaseSpace layout,
        let x : Fin n → ℝ :=
          fun j ↦
            y.1 (MixedCentralPolynomialCode.xIndex
              (k := k) j)
        ∀ c, MixedCentralPolynomialCode.compactBlockDot layout x
          (MixedCentralPolynomialCode.clearedSourceVelocity
            layout M P y.1) c = 0) :
    ∀ v :
        UnitSpherePolynomialWrapper.SourceProductSphere
          (sourceBlock (m := m) layout),
      let y : Fin (n + k) → ℝ :=
        fun q ↦
          v.1 (AccumulatorPolynomialCode.baseIndex
            (m := m) q)
      let x : Fin n → ℝ :=
        fun j ↦ y (MixedCentralPolynomialCode.xIndex
          (k := k) j)
      ∀ c, MixedCentralPolynomialCode.compactBlockDot layout x
        (MixedCentralPolynomialCode.clearedSourceVelocity
          layout M P y) c = 0 := by
  intro v
  exact hcompactBase (baseProjection layout v)

/-! ## Canonical structural data for the compact-sign theorem -/

/-- The finite interior is invariant under the canonical complete source
flow.  Every premise is finite-syntax or base tangency data. -/
def canonicalFiniteInteriorInvariant
    (layout : Fin n → Fin k ⊕ Fin l)
    (E M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
    (h : Fin m → PolynomialCode n)
    (hh : ∀ i, PolynomialCode.TermsDegreeLE E (h i))
    (ε : RationalCode)
    (hcompactBase :
      ∀ y : BaseSpace layout,
        let x : Fin n → ℝ :=
          fun j ↦
            y.1 (MixedCentralPolynomialCode.xIndex
              (k := k) j)
        ∀ c, MixedCentralPolynomialCode.compactBlockDot layout x
          (MixedCentralPolynomialCode.clearedSourceVelocity
            layout M P y.1) c = 0) :
    IsInvariant
      (sourceFlow layout E M κ P h ε)
      (sourceFiniteInteriorSet (m := m) layout) :=
  isInvariant_sourceFiniteInteriorSet
    layout M κ P h
    (sourceFlow layout E M κ P h ε)
    (sourceFlow_integralCurve
      layout E M κ P hP h hh ε
      (fullCompactTangencyHypothesis_of_base
        layout M P hcompactBase))

/-- Canonical finite-interior base factor equation. -/
theorem canonicalRestrictedBaseProjection_semiconj
    (layout : Fin n → Fin k ⊕ Fin l)
    (E M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
    (h : Fin m → PolynomialCode n)
    (hh : ∀ i, PolynomialCode.TermsDegreeLE E (h i))
    (ε : RationalCode)
    (hcompactBase :
      ∀ y : BaseSpace layout,
        let x : Fin n → ℝ :=
          fun j ↦
            y.1 (MixedCentralPolynomialCode.xIndex
              (k := k) j)
        ∀ c, MixedCentralPolynomialCode.compactBlockDot layout x
          (MixedCentralPolynomialCode.clearedSourceVelocity
            layout M P y.1) c = 0)
    (t : ℝ) :
    Semiconj
      (restrictedBaseProjection layout)
      (((sourceFlow layout E M κ P h ε).restrict
        (canonicalFiniteInteriorInvariant
          layout E M κ P hP h hh ε hcompactBase)) t)
      (baseFlow layout E M P t) := by
  apply
    restrictedBaseProjection_semiconj
      layout E M κ P hP h
      (sourceFlow layout E M κ P h ε)
  · exact
      sourceFlow_integralCurve
        layout E M κ P hP h hh ε
        (fullCompactTangencyHypothesis_of_base
          layout M P hcompactBase)
  · exact hcompactBase

/-- Canonical finite-interior accumulator-vector equation. -/
theorem canonicalFiniteAccumulator_u_hasDerivAt
    (layout : Fin n → Fin k ⊕ Fin l)
    (E M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
    (h : Fin m → PolynomialCode n)
    (hh : ∀ i, PolynomialCode.TermsDegreeLE E (h i))
    (ε : RationalCode)
    (hcompactBase :
      ∀ y : BaseSpace layout,
        let x : Fin n → ℝ :=
          fun j ↦
            y.1 (MixedCentralPolynomialCode.xIndex
              (k := k) j)
        ∀ c, MixedCentralPolynomialCode.compactBlockDot layout x
          (MixedCentralPolynomialCode.clearedSourceVelocity
            layout M P y.1) c = 0)
    (x : sourceFiniteInteriorSet (m := m) layout)
    (i : Fin m) (t : ℝ) :
    HasDerivAt
      (fun r ↦
        (finiteAccumulatorProjection layout
          (((sourceFlow layout E M κ P h ε).restrict
            (canonicalFiniteInteriorInvariant
              layout E M κ P hP h hh ε hcompactBase))
            r x)).1.1.1 i)
      (accumulatorUField
        (finiteAccumulatorProjection layout
          (((sourceFlow layout E M κ P h ε).restrict
            (canonicalFiniteInteriorInvariant
              layout E M κ P hP h hh ε hcompactBase))
            t x)).1.1.1
        (finiteAccumulatorProjection layout
          (((sourceFlow layout E M κ P h ε).restrict
            (canonicalFiniteInteriorInvariant
              layout E M κ P hP h hh ε hcompactBase))
            t x)).1.1.2
        (baseDriftBCF layout M κ h
          (restrictedBaseProjection layout
            (((sourceFlow layout E M κ P h ε).restrict
              (canonicalFiniteInteriorInvariant
                layout E M κ P hP h hh ε hcompactBase))
              t x))) i) t := by
  apply finiteAccumulatorProjection_u_hasDerivAt
  exact
    sourceFlow_integralCurve
      layout E M κ P hP h hh ε
      (fullCompactTangencyHypothesis_of_base
        layout M P hcompactBase)

/-- Canonical finite-interior accumulator-scalar equation. -/
theorem canonicalFiniteAccumulator_w_hasDerivAt
    (layout : Fin n → Fin k ⊕ Fin l)
    (E M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
    (h : Fin m → PolynomialCode n)
    (hh : ∀ i, PolynomialCode.TermsDegreeLE E (h i))
    (ε : RationalCode)
    (hcompactBase :
      ∀ y : BaseSpace layout,
        let x : Fin n → ℝ :=
          fun j ↦
            y.1 (MixedCentralPolynomialCode.xIndex
              (k := k) j)
        ∀ c, MixedCentralPolynomialCode.compactBlockDot layout x
          (MixedCentralPolynomialCode.clearedSourceVelocity
            layout M P y.1) c = 0)
    (x : sourceFiniteInteriorSet (m := m) layout)
    (t : ℝ) :
    HasDerivAt
      (fun r ↦
        (finiteAccumulatorProjection layout
          (((sourceFlow layout E M κ P h ε).restrict
            (canonicalFiniteInteriorInvariant
              layout E M κ P hP h hh ε hcompactBase))
            r x)).1.1.2)
      (accumulatorWField
        (finiteAccumulatorProjection layout
          (((sourceFlow layout E M κ P h ε).restrict
            (canonicalFiniteInteriorInvariant
              layout E M κ P hP h hh ε hcompactBase))
            t x)).1.1.1
        (finiteAccumulatorProjection layout
          (((sourceFlow layout E M κ P h ε).restrict
            (canonicalFiniteInteriorInvariant
              layout E M κ P hP h hh ε hcompactBase))
            t x)).1.1.2
        (baseDriftBCF layout M κ h
          (restrictedBaseProjection layout
            (((sourceFlow layout E M κ P h ε).restrict
              (canonicalFiniteInteriorInvariant
                layout E M κ P hP h hh ε hcompactBase))
              t x)))) t := by
  apply finiteAccumulatorProjection_w_hasDerivAt
  exact
    sourceFlow_integralCurve
      layout E M κ P hP h hh ε
      (fullCompactTangencyHypothesis_of_base
        layout M P hcompactBase)

end CompactAccumulatorPipelineCode

end

end HGAS
