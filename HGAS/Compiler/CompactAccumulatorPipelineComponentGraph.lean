import HGAS.Compiler.CompactAccumulatorPipelineFiniteGraph
import Mathlib.Tactic

/-!
# Finite accumulator graphs over an invariant base component

The global finite-graph interface in
`CompactAccumulatorPipelineFiniteGraph` asks for a primitive and a positive
central-weight bound on the whole compact base.  That is intentionally
stronger than the no-instance construction in the reduction: the canonical
primitive exists only on one invariant modular/Jacobi component, and other
components may meet a central equator.

This module gives the component-restricted interface.  A
`BaseInvariantComponent` records a measurable invariant set `C` in the
compact base.  A continuous primitive

```
z : C -> FinVector m ℝ
```

whose derivative along the restricted base flow is the compiled drift
defines an inverse-stereographic graph from `C` to the complete source.
The graph is equivariant, so every invariant probability of the restricted
flow pushes to an invariant probability of the complete source.

Both pointwise and almost-everywhere quantitative hypotheses are supported.
In particular, no positive lower bound for the central-weight product is
required away from `C`.
-/

namespace HGAS

open _root_.MvPolynomial
open Function MeasureTheory Metric Set
open scoped BoundedContinuousFunction

noncomputable section

namespace CompactAccumulatorPipelineCode

variable {n k l m : ℕ}

/-- A measurable invariant component of the canonical compact base flow. -/
structure BaseInvariantComponent
    (layout : Fin n → Fin k ⊕ Fin l)
    (E M : ℕ) (P : PolynomialFieldCode n) where
  carrier : Set (BaseSpace layout)
  measurableSet_carrier : MeasurableSet carrier
  invariant : IsInvariant (baseFlow layout E M P) carrier

namespace BaseInvariantComponent

variable
    {layout : Fin n → Fin k ⊕ Fin l}
    {E M : ℕ} {P : PolynomialFieldCode n}

/-- The component as a phase type. -/
abbrev Space
    (C : BaseInvariantComponent layout E M P) :=
  C.carrier

/-- The canonical base flow restricted to the selected component. -/
def flow
    (C : BaseInvariantComponent layout E M P) :
    Flow ℝ C.Space :=
  (baseFlow layout E M P).restrict C.invariant

@[simp]
theorem coe_flow_apply
    (C : BaseInvariantComponent layout E M P)
    (t : ℝ) (b : C.Space) :
    (C.flow t b : BaseSpace layout) =
      baseFlow layout E M P t b :=
  rfl

end BaseInvariantComponent

/-- The inverse-stereographic finite graph, defined only over the chosen
invariant base component. -/
def componentFiniteGraphPoint
    (layout : Fin n → Fin k ⊕ Fin l)
    {E M : ℕ} {P : PolynomialFieldCode n}
    (C : BaseInvariantComponent layout E M P)
    (z : C.Space → FinVector m ℝ)
    (b : C.Space) :
    UnitSpherePolynomialWrapper.SourceProductSphere
      (sourceBlock (m := m) layout) :=
  ⟨AccumulatorPolynomialCode.combinedPoint
      b.1.1 (stereoU (z b)) (stereoW (z b)),
    (AccumulatorPolynomialCode.onSourceProductSpheres_productSphereBlock_iff
        (MixedCentralPolynomialCode.targetBlock layout)
        b.1.1 (stereoU (z b)) (stereoW (z b))).2
      ⟨b.1.2, stereo_mem_sphere (z b)⟩⟩

@[simp]
theorem sourceBasePoint_componentFiniteGraphPoint
    (layout : Fin n → Fin k ⊕ Fin l)
    {E M : ℕ} {P : PolynomialFieldCode n}
    (C : BaseInvariantComponent layout E M P)
    (z : C.Space → FinVector m ℝ)
    (b : C.Space) :
    sourceBasePoint (componentFiniteGraphPoint layout C z b) =
      b.1.1 := by
  funext q
  simp [sourceBasePoint, componentFiniteGraphPoint]

@[simp]
theorem sourceAccumulatorU_componentFiniteGraphPoint
    (layout : Fin n → Fin k ⊕ Fin l)
    {E M : ℕ} {P : PolynomialFieldCode n}
    (C : BaseInvariantComponent layout E M P)
    (z : C.Space → FinVector m ℝ)
    (b : C.Space) :
    sourceAccumulatorU (componentFiniteGraphPoint layout C z b) =
      stereoU (z b) := by
  funext i
  simp [sourceAccumulatorU, componentFiniteGraphPoint]

@[simp]
theorem sourceAccumulatorW_componentFiniteGraphPoint
    (layout : Fin n → Fin k ⊕ Fin l)
    {E M : ℕ} {P : PolynomialFieldCode n}
    (C : BaseInvariantComponent layout E M P)
    (z : C.Space → FinVector m ℝ)
    (b : C.Space) :
    sourceAccumulatorW (componentFiniteGraphPoint layout C z b) =
      stereoW (z b) := by
  simp [sourceAccumulatorW, componentFiniteGraphPoint]

@[simp]
theorem baseProjection_componentFiniteGraphPoint
    (layout : Fin n → Fin k ⊕ Fin l)
    {E M : ℕ} {P : PolynomialFieldCode n}
    (C : BaseInvariantComponent layout E M P)
    (z : C.Space → FinVector m ℝ)
    (b : C.Space) :
    baseProjection layout (componentFiniteGraphPoint layout C z b) =
      b.1 := by
  apply Subtype.ext
  exact sourceBasePoint_componentFiniteGraphPoint layout C z b

/-- Continuity of a component primitive gives continuity of its finite
graph into the complete source. -/
theorem continuous_componentFiniteGraphPoint
    (layout : Fin n → Fin k ⊕ Fin l)
    {E M : ℕ} {P : PolynomialFieldCode n}
    (C : BaseInvariantComponent layout E M P)
    (z : C.Space → FinVector m ℝ)
    (hz : Continuous z) :
    Continuous (componentFiniteGraphPoint layout C z) := by
  have hbase :
      Continuous (fun b : C.Space ↦ b.1.1) :=
    continuous_subtype_val.comp continuous_subtype_val
  apply Continuous.subtype_mk
  apply continuous_pi
  intro q
  obtain ⟨j | r, rfl⟩ := finSumFinEquiv.surjective q
  · have hj :
        Continuous (fun b : C.Space ↦ b.1.1 j) :=
      (continuous_apply j).comp hbase
    simpa [componentFiniteGraphPoint,
      AccumulatorPolynomialCode.combinedPoint] using hj
  · obtain ⟨i | e, rfl⟩ := finSumFinEquiv.surjective r
    · have hi :
          Continuous (fun b ↦ stereoU (z b) i) :=
        (continuous_apply i).comp
          (continuous_stereoU.comp hz)
      simpa [componentFiniteGraphPoint,
        AccumulatorPolynomialCode.combinedPoint] using hi
    · fin_cases e
      have hW : Continuous (fun b ↦ stereoW (z b)) :=
        continuous_stereoW.comp hz
      simpa [componentFiniteGraphPoint,
        AccumulatorPolynomialCode.combinedPoint] using hW

/-! ## The component graph solves the complete polynomial ODE -/

/-- If the component primitive differentiates to the compiled drift along
the restricted base flow, its inverse-stereographic graph is an integral
curve of the complete source field. -/
theorem componentFiniteGraphPoint_isIntegralCurve
    (layout : Fin n → Fin k ⊕ Fin l)
    (E M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
    (h : Fin m → PolynomialCode n)
    (hcompactBase :
      ∀ y : BaseSpace layout,
        let x : Fin n → ℝ :=
          fun j ↦
            y.1 (MixedCentralPolynomialCode.xIndex
              (k := k) j)
        ∀ c, MixedCentralPolynomialCode.compactBlockDot layout x
          (MixedCentralPolynomialCode.clearedSourceVelocity
            layout M P y.1) c = 0)
    (C : BaseInvariantComponent layout E M P)
    (z : C.Space → FinVector m ℝ)
    (hz :
      ∀ b i t,
        HasDerivAt
          (fun s ↦ z (C.flow s b) i)
          (baseDriftBCF layout M κ h (C.flow t b).1 i) t)
    (b : C.Space) :
    IsIntegralCurve
      (fun t ↦
        (componentFiniteGraphPoint layout C z
          (C.flow t b)).1)
      (fun _ x ↦
        PolynomialFieldCode.realize
          (fieldCode layout M κ P h) x) := by
  intro t
  rw [hasDerivAt_pi]
  intro q
  cases hq : finSumFinEquiv.symm q with
  | inl j =>
      have hq' :
          q =
            AccumulatorPolynomialCode.baseIndex
              (m := m) j := by
        rw [AccumulatorPolynomialCode.baseIndex,
          DegreePaddingCode.baseIndex, ← hq]
        simp
      rw [hq']
      have hb :=
        (hasDerivAt_pi.mp
          (baseFlow_integralCurve
            layout E M P hP hcompactBase b.1 t)) j
      convert hb using 1
      · funext s
        simp [componentFiniteGraphPoint,
          BaseInvariantComponent.coe_flow_apply]
      · dsimp only
        rw [realize_fieldCode_baseIndex,
          sourceBasePoint_componentFiniteGraphPoint]
        rfl
  | inr r =>
      cases hr : finSumFinEquiv.symm r with
      | inl i =>
          have hq' :
              q =
                AccumulatorPolynomialCode.uIndex
                  (n := n + k) i := by
            have hr' :
                r =
                  AccumulatorPolynomialCode.uAuxIndex i := by
              calc
                r = finSumFinEquiv
                    (finSumFinEquiv.symm r) :=
                  (finSumFinEquiv.apply_symm_apply r).symm
                _ = finSumFinEquiv (Sum.inl i) :=
                  congrArg finSumFinEquiv hr
                _ =
                    AccumulatorPolynomialCode.uAuxIndex i := rfl
            calc
              q = finSumFinEquiv
                    (finSumFinEquiv.symm q) :=
                (finSumFinEquiv.apply_symm_apply q).symm
              _ = finSumFinEquiv (Sum.inr r) :=
                congrArg finSumFinEquiv hq
              _ =
                  AccumulatorPolynomialCode.uIndex
                    (n := n + k) i := by
                rw [hr']
                rfl
          rw [hq']
          have hu :=
            stereoU_hasDerivAt
              (fun s ↦ z (C.flow s b))
              (fun s ↦
                baseDriftBCF layout M κ h (C.flow s b).1)
              t (fun j ↦ hz b j t) i
          convert hu using 1
          · funext s
            simp [componentFiniteGraphPoint]
          · dsimp only
            rw [realize_fieldCode_accumulatorU,
              sourceAccumulatorU_componentFiniteGraphPoint,
              sourceAccumulatorW_componentFiniteGraphPoint,
              baseProjection_componentFiniteGraphPoint]
      | inr e =>
          fin_cases e
          have hq' :
              q =
                AccumulatorPolynomialCode.wIndex
                  (n + k) m := by
            have hr' :
                r =
                  AccumulatorPolynomialCode.wAuxIndex m := by
              calc
                r = finSumFinEquiv
                    (finSumFinEquiv.symm r) :=
                  (finSumFinEquiv.apply_symm_apply r).symm
                _ = finSumFinEquiv
                    (Sum.inr (0 : Fin 1)) :=
                  congrArg finSumFinEquiv hr
                _ =
                    AccumulatorPolynomialCode.wAuxIndex m := rfl
            calc
              q = finSumFinEquiv
                    (finSumFinEquiv.symm q) :=
                (finSumFinEquiv.apply_symm_apply q).symm
              _ = finSumFinEquiv (Sum.inr r) :=
                congrArg finSumFinEquiv hq
              _ =
                  AccumulatorPolynomialCode.wIndex
                    (n + k) m := by
                rw [hr']
                rfl
          rw [hq']
          have hW :=
            stereoW_hasDerivAt
              (fun s ↦ z (C.flow s b))
              (fun s ↦
                baseDriftBCF layout M κ h (C.flow s b).1)
              t (fun j ↦ hz b j t)
          convert hW using 1
          · funext s
            simp [componentFiniteGraphPoint]
          · dsimp only
            rw [realize_fieldCode_accumulatorW_factor,
              sourceAccumulatorU_componentFiniteGraphPoint,
              sourceAccumulatorW_componentFiniteGraphPoint,
              baseProjection_componentFiniteGraphPoint]

/-! ## Equivariance and component graph measures -/

/-- ODE uniqueness identifies the differentiated component graph with the
canonical complete source flow. -/
theorem componentFiniteGraphPoint_flow_eq
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
    (C : BaseInvariantComponent layout E M P)
    (z : C.Space → FinVector m ℝ)
    (hz :
      ∀ b i t,
        HasDerivAt
          (fun s ↦ z (C.flow s b) i)
          (baseDriftBCF layout M κ h (C.flow t b).1 i) t)
    (b : C.Space) (t : ℝ) :
    componentFiniteGraphPoint layout C z (C.flow t b) =
      sourceFlow layout E M κ P h ε t
        (componentFiniteGraphPoint layout C z b) := by
  apply Subtype.ext
  let gammaOne :
      ℝ → Fin ((n + k) + (m + 1)) → ℝ :=
    fun s ↦
      (componentFiniteGraphPoint layout C z (C.flow s b)).1
  let gammaTwo :
      ℝ → Fin ((n + k) + (m + 1)) → ℝ :=
    fun s ↦
      (sourceFlow layout E M κ P h ε s
        (componentFiniteGraphPoint layout C z b)).1
  have hgammaOne :
      IsIntegralCurve gammaOne
        (fun _ x ↦
          PolynomialFieldCode.realize
            (fieldCode layout M κ P h) x) := by
    simpa only [gammaOne] using
      componentFiniteGraphPoint_isIntegralCurve
        layout E M κ P hP h hcompactBase C z hz b
  have hgammaTwo :
      IsIntegralCurve gammaTwo
        (fun _ x ↦
          PolynomialFieldCode.realize
            (fieldCode layout M κ P h) x) := by
    simpa only [gammaTwo] using
      sourceFlow_integralCurve
        layout E M κ P hP h hh ε
        (fullCompactTangencyHypothesis_of_base
          layout M P hcompactBase)
        (componentFiniteGraphPoint layout C z b)
  have hC1 :
      ContDiff ℝ 1
        (PolynomialFieldCode.realize
          (fieldCode layout M κ P h)) :=
    (UnitSpherePolynomialWrapper.contDiff_realize_sourcePolynomialFieldCode
        (fieldCode layout M κ P h)).of_le (by norm_num)
  obtain ⟨K, hK⟩ :=
    hC1.contDiffOn.exists_lipschitzOnWith
      one_ne_zero
      (convex_closedBall
        (0 : Fin ((n + k) + (m + 1)) → ℝ) 1)
      (isCompact_closedBall
        (0 : Fin ((n + k) + (m + 1)) → ℝ) 1)
  have hOneMem :
      ∀ s,
        gammaOne s ∈
          closedBall
            (0 : Fin ((n + k) + (m + 1)) → ℝ) 1 := by
    intro s
    have hnorm :=
      UnitSpherePolynomialWrapper.source_norm_le_one_of_onSourceProductSpheres
          (sourceBlock (m := m) layout)
          (gammaOne s)
          (componentFiniteGraphPoint layout C z
            (C.flow s b)).property
    simpa only [Metric.mem_closedBall, dist_zero_right]
      using hnorm
  have hTwoMem :
      ∀ s,
        gammaTwo s ∈
          closedBall
            (0 : Fin ((n + k) + (m + 1)) → ℝ) 1 := by
    intro s
    have hnorm :=
      UnitSpherePolynomialWrapper.source_norm_le_one_of_onSourceProductSpheres
          (sourceBlock (m := m) layout)
          (gammaTwo s)
          (sourceFlow layout E M κ P h ε s
            (componentFiniteGraphPoint layout C z b)).property
    simpa only [Metric.mem_closedBall, dist_zero_right]
      using hnorm
  have heq : gammaOne = gammaTwo := by
    apply ODE_solution_unique_univ
      (v := fun _ : ℝ ↦
        PolynomialFieldCode.realize
          (fieldCode layout M κ P h))
      (s := fun _ ↦
        closedBall
          (0 : Fin ((n + k) + (m + 1)) → ℝ) 1)
      (K := K) (t₀ := 0)
    · intro _
      exact hK
    · intro s
      exact ⟨hgammaOne s, hOneMem s⟩
    · intro s
      exact ⟨hgammaTwo s, hTwoMem s⟩
    · simp [gammaOne, gammaTwo, Flow.map_zero_apply]
  exact congrFun heq t

/-- The component graph semiconjugates the restricted compact-base flow to
the canonical complete source flow. -/
theorem componentFiniteGraphPoint_semiconj
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
    (C : BaseInvariantComponent layout E M P)
    (z : C.Space → FinVector m ℝ)
    (hz :
      ∀ b i t,
        HasDerivAt
          (fun s ↦ z (C.flow s b) i)
          (baseDriftBCF layout M κ h (C.flow t b).1 i) t)
    (t : ℝ) :
    Semiconj
      (componentFiniteGraphPoint layout C z)
      (C.flow t)
      (sourceFlow layout E M κ P h ε t) := by
  intro b
  exact
    componentFiniteGraphPoint_flow_eq
      layout E M κ P hP h hh ε hcompactBase C z hz b t

/-- Push an invariant probability on the selected base component to an
invariant probability of the complete compact source. -/
def componentFiniteGraphInvariantProbability
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
    (C : BaseInvariantComponent layout E M P)
    (z : C.Space → FinVector m ℝ)
    (hzcont : Continuous z)
    (hz :
      ∀ b i t,
        HasDerivAt
          (fun s ↦ z (C.flow s b) i)
          (baseDriftBCF layout M κ h (C.flow t b).1 i) t)
    (η : Dynamics.InvariantProbabilityMeasure C.flow) :
    Dynamics.InvariantProbabilityMeasure
      (sourceFlow layout E M κ P h ε) :=
  η.mapEquivariant
    (componentFiniteGraphPoint layout C z)
    (continuous_componentFiniteGraphPoint layout C z hzcont)
    (componentFiniteGraphPoint_semiconj
      layout E M κ P hP h hh ε hcompactBase C z hz)

/-! ## Quantitative reward on one invariant component -/

/-- Pointwise reward lower bound at one component graph point.  Both
quantitative assumptions concern only that point of the selected
component. -/
theorem componentFiniteGraph_reward_lower_of_point
    (layout : Fin n → Fin k ⊕ Fin l)
    {E M : ℕ} {P : PolynomialFieldCode n}
    (C : BaseInvariantComponent layout E M P)
    (ε : RationalCode)
    (z : C.Space → FinVector m ℝ)
    (wStar : ℝ)
    (b : C.Space)
    (hnorm : normSq (z b) ≤ wStar / 4)
    (hweight :
      wStar ≤ baseCentralWeightProduct layout b.1) :
    3 * wStar / 2 - (ε.decode : ℝ) ≤
      UnitSpherePolynomialWrapper.sourceRewardBCF
        (sourceBlock (m := m) layout)
        (rewardCode (n := n) (k := k) (m := m) ε)
        (componentFiniteGraphPoint layout C z b) := by
  let x : Fin n → ℝ :=
    fun j ↦
      b.1.1 (MixedCentralPolynomialCode.xIndex
        (k := k) j)
  let w : Fin k → ℝ :=
    fun c ↦
      b.1.1 (MixedCentralPolynomialCode.wIndex
        (n := n) c)
  have hb :
      MixedCentralPolynomialCode.chartPoint x w = b.1.1 :=
    MixedCentralPolynomialCode.chartPoint_decompose b.1.1
  rw [UnitSpherePolynomialWrapper.sourceRewardBCF_apply]
  change
    3 * wStar / 2 - (ε.decode : ℝ) ≤
      eval₂Hom (algebraMap ℚ ℝ)
        (AccumulatorPolynomialCode.combinedPoint
          b.1.1 (stereoU (z b)) (stereoW (z b)))
        (PolynomialCode.decode
          (rewardCode (n := n) (k := k) (m := m) ε))
  rw [← hb]
  apply finiteGraphGap_le_eval₂Hom_rewardCode
  · simpa only [stereoW] using
      stereoW_lower_bound_of_scaled_norm
        (normSq_nonneg (z b)) hnorm
  · simpa only [baseCentralWeightProduct, w] using hweight

/-- Pointwise-on-component hypotheses give a uniform reward bound on the
component graph.  No assertion is made on the rest of `BaseSpace`. -/
theorem componentFiniteGraph_reward_lower
    (layout : Fin n → Fin k ⊕ Fin l)
    {E M : ℕ} {P : PolynomialFieldCode n}
    (C : BaseInvariantComponent layout E M P)
    (ε : RationalCode)
    (z : C.Space → FinVector m ℝ)
    (wStar : ℝ)
    (hnorm :
      ∀ b, normSq (z b) ≤ wStar / 4)
    (hweight :
      ∀ b : C.Space,
        wStar ≤ baseCentralWeightProduct layout b.1)
    (b : C.Space) :
    3 * wStar / 2 - (ε.decode : ℝ) ≤
      UnitSpherePolynomialWrapper.sourceRewardBCF
        (sourceBlock (m := m) layout)
        (rewardCode (n := n) (k := k) (m := m) ε)
        (componentFiniteGraphPoint layout C z b) :=
  componentFiniteGraph_reward_lower_of_point
    layout C ε z wStar b (hnorm b) (hweight b)

/-- Almost-everywhere norm and central-weight bounds under the chosen
component probability suffice for the same lower bound after pushing the
probability to the complete source. -/
theorem componentFiniteGraphInvariantProbability_reward_lower_ae
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
    (C : BaseInvariantComponent layout E M P)
    (z : C.Space → FinVector m ℝ)
    (hzcont : Continuous z)
    (hz :
      ∀ b i t,
        HasDerivAt
          (fun s ↦ z (C.flow s b) i)
          (baseDriftBCF layout M κ h (C.flow t b).1 i) t)
    (η : Dynamics.InvariantProbabilityMeasure C.flow)
    (wStar : ℝ)
    (hnorm :
      ∀ᵐ b ∂(η.measure : Measure C.Space),
        normSq (z b) ≤ wStar / 4)
    (hweight :
      ∀ᵐ b ∂(η.measure : Measure C.Space),
        wStar ≤ baseCentralWeightProduct layout b.1) :
    3 * wStar / 2 - (ε.decode : ℝ) ≤
      Dynamics.observableAverage
        (UnitSpherePolynomialWrapper.sourceRewardBCF
          (sourceBlock (m := m) layout)
          (rewardCode (n := n) (k := k) (m := m) ε))
        ((componentFiniteGraphInvariantProbability
          layout E M κ P hP h hh ε hcompactBase
          C z hzcont hz η).measure) := by
  let reward :=
    UnitSpherePolynomialWrapper.sourceRewardBCF
      (sourceBlock (m := m) layout)
      (rewardCode (n := n) (k := k) (m := m) ε)
  let graph := componentFiniteGraphPoint layout C z
  let hgraph :=
    continuous_componentFiniteGraphPoint layout C z hzcont
  let hequiv :=
    componentFiniteGraphPoint_semiconj
      layout E M κ P hP h hh ε hcompactBase C z hz
  change
    3 * wStar / 2 - (ε.decode : ℝ) ≤
      Dynamics.observableAverage reward
        ((η.mapEquivariant graph hgraph hequiv).measure)
  rw [Dynamics.observableAverage_mapEquivariant]
  unfold Dynamics.observableAverage
  have hpoint :
      ∀ᵐ b ∂(η.measure : Measure C.Space),
        3 * wStar / 2 - (ε.decode : ℝ) ≤
          (reward.compContinuous ⟨graph, hgraph⟩) b := by
    filter_upwards [hnorm, hweight] with b hbNorm hbWeight
    exact
      componentFiniteGraph_reward_lower_of_point
        layout C ε z wStar b hbNorm hbWeight
  calc
    3 * wStar / 2 - (ε.decode : ℝ) =
        ∫ _b : C.Space,
          (3 * wStar / 2 - (ε.decode : ℝ))
          ∂(η.measure : Measure C.Space) := by
            simp
    _ ≤
        ∫ b,
          (reward.compContinuous ⟨graph, hgraph⟩) b
          ∂(η.measure : Measure C.Space) := by
      exact integral_mono_ae
        (integrable_const _)
        ((reward.compContinuous ⟨graph, hgraph⟩).integrable _)
        hpoint

/-- Uniform bounds on the selected component are a convenient special case
of the almost-everywhere reward theorem. -/
theorem componentFiniteGraphInvariantProbability_reward_lower
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
    (C : BaseInvariantComponent layout E M P)
    (z : C.Space → FinVector m ℝ)
    (hzcont : Continuous z)
    (hz :
      ∀ b i t,
        HasDerivAt
          (fun s ↦ z (C.flow s b) i)
          (baseDriftBCF layout M κ h (C.flow t b).1 i) t)
    (η : Dynamics.InvariantProbabilityMeasure C.flow)
    (wStar : ℝ)
    (hnorm :
      ∀ b, normSq (z b) ≤ wStar / 4)
    (hweight :
      ∀ b : C.Space,
        wStar ≤ baseCentralWeightProduct layout b.1) :
    3 * wStar / 2 - (ε.decode : ℝ) ≤
      Dynamics.observableAverage
        (UnitSpherePolynomialWrapper.sourceRewardBCF
          (sourceBlock (m := m) layout)
          (rewardCode (n := n) (k := k) (m := m) ε))
        ((componentFiniteGraphInvariantProbability
          layout E M κ P hP h hh ε hcompactBase
          C z hzcont hz η).measure) := by
  apply
    componentFiniteGraphInvariantProbability_reward_lower_ae
      layout E M κ P hP h hh ε hcompactBase
      C z hzcont hz η wStar
  · filter_upwards with b
    exact hnorm b
  · filter_upwards with b
    exact hweight b

/-- Existence form matching the `finite_graph` field of the compact-gap
certificate. -/
theorem exists_componentFiniteGraphInvariantProbability_reward_lower_ae
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
    (C : BaseInvariantComponent layout E M P)
    (z : C.Space → FinVector m ℝ)
    (hzcont : Continuous z)
    (hz :
      ∀ b i t,
        HasDerivAt
          (fun s ↦ z (C.flow s b) i)
          (baseDriftBCF layout M κ h (C.flow t b).1 i) t)
    (η : Dynamics.InvariantProbabilityMeasure C.flow)
    (wStar : ℝ)
    (hnorm :
      ∀ᵐ b ∂(η.measure : Measure C.Space),
        normSq (z b) ≤ wStar / 4)
    (hweight :
      ∀ᵐ b ∂(η.measure : Measure C.Space),
        wStar ≤ baseCentralWeightProduct layout b.1) :
    ∃ μ :
        Dynamics.InvariantProbabilityMeasure
          (sourceFlow layout E M κ P h ε),
      3 * wStar / 2 - (ε.decode : ℝ) ≤
        Dynamics.observableAverage
          (UnitSpherePolynomialWrapper.sourceRewardBCF
            (sourceBlock (m := m) layout)
            (rewardCode (n := n) (k := k) (m := m) ε))
          μ.measure := by
  let μ :=
    componentFiniteGraphInvariantProbability
      layout E M κ P hP h hh ε hcompactBase
      C z hzcont hz η
  refine ⟨μ, ?_⟩
  exact
    componentFiniteGraphInvariantProbability_reward_lower_ae
      layout E M κ P hP h hh ε hcompactBase
      C z hzcont hz η wStar hnorm hweight

/-! ## Packaged upstream interface -/

/-- Reusable data carried by one finite invariant graph over a selected
base component.  It contains no global quantitative assertion on the
ambient compact base. -/
structure ComponentFiniteGraphCertificate
    (layout : Fin n → Fin k ⊕ Fin l)
    (E M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (h : Fin m → PolynomialCode n) where
  component : BaseInvariantComponent layout E M P
  primitive : component.Space → FinVector m ℝ
  primitive_continuous : Continuous primitive
  primitive_derivative :
    ∀ b i t,
      HasDerivAt
        (fun s ↦ primitive (component.flow s b) i)
        (baseDriftBCF layout M κ h
          (component.flow t b).1 i) t
  probability :
    Dynamics.InvariantProbabilityMeasure component.flow
  wStar : ℝ
  primitive_norm_ae :
    ∀ᵐ b ∂(probability.measure : Measure component.Space),
      normSq (primitive b) ≤ wStar / 4
  centralWeight_ae :
    ∀ᵐ b ∂(probability.measure : Measure component.Space),
      wStar ≤ baseCentralWeightProduct layout b.1

namespace ComponentFiniteGraphCertificate

variable
    {layout : Fin n → Fin k ⊕ Fin l}
    {E M : ℕ} {κ : RationalCode}
    {P : PolynomialFieldCode n}
    {h : Fin m → PolynomialCode n}

/-- The invariant probability on the complete source carried by a packaged
component graph certificate. -/
def sourceProbability
    (G : ComponentFiniteGraphCertificate layout E M κ P h)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
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
    Dynamics.InvariantProbabilityMeasure
      (sourceFlow layout E M κ P h ε) :=
  componentFiniteGraphInvariantProbability
    layout E M κ P hP h hh ε hcompactBase
    G.component G.primitive G.primitive_continuous
    G.primitive_derivative G.probability

/-- Quantitative reward lower bound supplied by a packaged component graph
certificate. -/
theorem sourceProbability_reward_lower
    (G : ComponentFiniteGraphCertificate layout E M κ P h)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
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
    3 * G.wStar / 2 - (ε.decode : ℝ) ≤
      Dynamics.observableAverage
        (UnitSpherePolynomialWrapper.sourceRewardBCF
          (sourceBlock (m := m) layout)
          (rewardCode (n := n) (k := k) (m := m) ε))
        ((G.sourceProbability hP hh ε hcompactBase).measure) := by
  exact
    componentFiniteGraphInvariantProbability_reward_lower_ae
      layout E M κ P hP h hh ε hcompactBase
      G.component G.primitive G.primitive_continuous
      G.primitive_derivative G.probability G.wStar
      G.primitive_norm_ae G.centralWeight_ae

/-- Existence form of the packaged certificate, ready for the
`CanonicalCompactAccumulatorGap.finite_graph` field. -/
theorem exists_sourceProbability_reward_lower
    (G : ComponentFiniteGraphCertificate layout E M κ P h)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
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
    ∃ μ :
        Dynamics.InvariantProbabilityMeasure
          (sourceFlow layout E M κ P h ε),
      3 * G.wStar / 2 - (ε.decode : ℝ) ≤
        Dynamics.observableAverage
          (UnitSpherePolynomialWrapper.sourceRewardBCF
            (sourceBlock (m := m) layout)
            (rewardCode (n := n) (k := k) (m := m) ε))
          μ.measure :=
  ⟨G.sourceProbability hP hh ε hcompactBase,
    G.sourceProbability_reward_lower hP hh ε hcompactBase⟩

end ComponentFiniteGraphCertificate

end CompactAccumulatorPipelineCode

end

end HGAS
