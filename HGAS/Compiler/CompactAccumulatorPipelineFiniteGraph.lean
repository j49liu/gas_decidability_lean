import HGAS.Compiler.CompactAccumulatorPipelineFactor
import HGAS.Compactification.StereographicTrajectory
import HGAS.Dynamics.InvariantComponentAverage
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Finite invariant graphs for the compiled accumulator

Suppose a continuous vector-valued function `z` on the compact base solves
the cohomological equation

```
 d/dt z(baseFlow t b) = baseDrift(baseFlow t b).
```

Inverse stereographic projection turns `z` into a graph in the complete
compact source.  This file proves that the graph is equivariant for the
literal compiled polynomial flow and therefore pushes every invariant
base probability to an invariant source probability.

This is the reusable dynamical core of the no-instance construction.  The
arithmetic source is responsible only for constructing a bounded primitive
and proving its quantitative central-weight lower bound.

The present interface is the **global-base** version: `z`, its
cohomological equation, and the quantitative bounds below are required on
all of `BaseSpace`.  A canonical no-instance graph which is defined only
over a proper invariant base component instead requires the corresponding
component-restricted version.  In particular, a positive global lower
bound for the central-weight product cannot hold when `BaseSpace` contains
a central equator.
-/

namespace HGAS

open _root_.MvPolynomial
open Function MeasureTheory Metric Set
open scoped BoundedContinuousFunction

noncomputable section

namespace CompactAccumulatorPipelineCode

variable {n k l m : ℕ}

/-- The inverse-stereographic graph of a vector function on the compact
base, valued in the complete product-sphere source. -/
def finiteGraphPoint
    (layout : Fin n → Fin k ⊕ Fin l)
    (z : BaseSpace layout → FinVector m ℝ)
    (b : BaseSpace layout) :
    UnitSpherePolynomialWrapper.SourceProductSphere
      (sourceBlock (m := m) layout) :=
  ⟨AccumulatorPolynomialCode.combinedPoint
      b.1 (stereoU (z b)) (stereoW (z b)),
    (AccumulatorPolynomialCode.onSourceProductSpheres_productSphereBlock_iff
        (MixedCentralPolynomialCode.targetBlock layout)
        b.1 (stereoU (z b)) (stereoW (z b))).2
      ⟨b.2, stereo_mem_sphere (z b)⟩⟩

@[simp]
theorem sourceBasePoint_finiteGraphPoint
    (layout : Fin n → Fin k ⊕ Fin l)
    (z : BaseSpace layout → FinVector m ℝ)
    (b : BaseSpace layout) :
    sourceBasePoint (finiteGraphPoint layout z b) = b.1 := by
  funext q
  simp [sourceBasePoint, finiteGraphPoint]

@[simp]
theorem sourceAccumulatorU_finiteGraphPoint
    (layout : Fin n → Fin k ⊕ Fin l)
    (z : BaseSpace layout → FinVector m ℝ)
    (b : BaseSpace layout) :
    sourceAccumulatorU (finiteGraphPoint layout z b) =
      stereoU (z b) := by
  funext i
  simp [sourceAccumulatorU, finiteGraphPoint]

@[simp]
theorem sourceAccumulatorW_finiteGraphPoint
    (layout : Fin n → Fin k ⊕ Fin l)
    (z : BaseSpace layout → FinVector m ℝ)
    (b : BaseSpace layout) :
    sourceAccumulatorW (finiteGraphPoint layout z b) =
      stereoW (z b) := by
  simp [sourceAccumulatorW, finiteGraphPoint]

@[simp]
theorem baseProjection_finiteGraphPoint
    (layout : Fin n → Fin k ⊕ Fin l)
    (z : BaseSpace layout → FinVector m ℝ)
    (b : BaseSpace layout) :
    baseProjection layout (finiteGraphPoint layout z b) = b := by
  apply Subtype.ext
  exact sourceBasePoint_finiteGraphPoint layout z b

/-- Continuity of the vector coordinate of inverse stereographic
projection. -/
theorem continuous_stereoU :
    Continuous (stereoU : FinVector m ℝ → FinVector m ℝ) := by
  have hnorm :
      Continuous (normSq : FinVector m ℝ → ℝ) := by
    unfold normSq dot
    fun_prop
  apply continuous_pi
  intro i
  unfold stereoU
  apply Continuous.div
  · exact continuous_const.mul (continuous_apply i)
  · exact continuous_const.add hnorm
  · intro z
    exact ne_of_gt (stereo_denominator_pos z)

/-- Continuity of the scalar coordinate of inverse stereographic
projection. -/
theorem continuous_stereoW :
    Continuous (stereoW : FinVector m ℝ → ℝ) := by
  have hnorm :
      Continuous (normSq : FinVector m ℝ → ℝ) := by
    unfold normSq dot
    fun_prop
  unfold stereoW
  apply Continuous.div
  · exact continuous_const.sub hnorm
  · exact continuous_const.add hnorm
  · intro z
    exact ne_of_gt (stereo_denominator_pos z)

/-- A continuous affine primitive gives a continuous graph in the compact
source. -/
theorem continuous_finiteGraphPoint
    (layout : Fin n → Fin k ⊕ Fin l)
    (z : BaseSpace layout → FinVector m ℝ)
    (hz : Continuous z) :
    Continuous (finiteGraphPoint layout z) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro q
  obtain ⟨j | r, rfl⟩ := finSumFinEquiv.surjective q
  · have hj :
        Continuous (fun b : BaseSpace layout ↦ b.1 j) :=
      (continuous_apply j).comp continuous_subtype_val
    simpa [finiteGraphPoint,
      AccumulatorPolynomialCode.combinedPoint] using hj
  · obtain ⟨i | e, rfl⟩ := finSumFinEquiv.surjective r
    · have hi : Continuous (fun b ↦ stereoU (z b) i) :=
        (continuous_apply i).comp
          (continuous_stereoU.comp hz)
      simpa [finiteGraphPoint,
        AccumulatorPolynomialCode.combinedPoint] using hi
    · fin_cases e
      have hW : Continuous (fun b ↦ stereoW (z b)) :=
        continuous_stereoW.comp hz
      simpa [finiteGraphPoint,
        AccumulatorPolynomialCode.combinedPoint] using hW

/-! ## The graph solves the compiled source ODE -/

/-- If `z` differentiates to the compact-base drift along every base
trajectory, then its inverse-stereographic graph is an integral curve of
the complete compiled polynomial field. -/
theorem finiteGraphPoint_isIntegralCurve
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
    (z : BaseSpace layout → FinVector m ℝ)
    (hz :
      ∀ b i t,
        HasDerivAt
          (fun s ↦ z (baseFlow layout E M P s b) i)
          (baseDriftBCF layout M κ h
            (baseFlow layout E M P t b) i) t)
    (b : BaseSpace layout) :
    IsIntegralCurve
      (fun t ↦
        (finiteGraphPoint layout z
          (baseFlow layout E M P t b)).1)
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
            layout E M P hP hcompactBase b t)) j
      convert hb using 1
      · funext s
        simp [finiteGraphPoint]
      · dsimp only
        rw [realize_fieldCode_baseIndex,
          sourceBasePoint_finiteGraphPoint]
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
              (fun s ↦
                z (baseFlow layout E M P s b))
              (fun s ↦
                baseDriftBCF layout M κ h
                  (baseFlow layout E M P s b))
              t (fun j ↦ hz b j t) i
          convert hu using 1
          · funext s
            simp [finiteGraphPoint]
          · dsimp only
            rw [realize_fieldCode_accumulatorU,
              sourceAccumulatorU_finiteGraphPoint,
              sourceAccumulatorW_finiteGraphPoint,
              baseProjection_finiteGraphPoint]
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
              (fun s ↦
                z (baseFlow layout E M P s b))
              (fun s ↦
                baseDriftBCF layout M κ h
                  (baseFlow layout E M P s b))
              t (fun j ↦ hz b j t)
          convert hW using 1
          · funext s
            simp [finiteGraphPoint]
          · dsimp only
            rw [realize_fieldCode_accumulatorW_factor,
              sourceAccumulatorU_finiteGraphPoint,
              sourceAccumulatorW_finiteGraphPoint,
              baseProjection_finiteGraphPoint]

/-! ## Equivariance and invariant graph measures -/

/-- ODE uniqueness identifies the explicitly differentiated finite graph
trajectory with the canonical complete source flow. -/
theorem finiteGraphPoint_flow_eq
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
    (z : BaseSpace layout → FinVector m ℝ)
    (hz :
      ∀ b i t,
        HasDerivAt
          (fun s ↦ z (baseFlow layout E M P s b) i)
          (baseDriftBCF layout M κ h
            (baseFlow layout E M P t b) i) t)
    (b : BaseSpace layout) (t : ℝ) :
    finiteGraphPoint layout z
        (baseFlow layout E M P t b) =
      sourceFlow layout E M κ P h ε t
        (finiteGraphPoint layout z b) := by
  apply Subtype.ext
  let gammaOne :
      ℝ → Fin ((n + k) + (m + 1)) → ℝ :=
    fun s ↦
      (finiteGraphPoint layout z
        (baseFlow layout E M P s b)).1
  let gammaTwo :
      ℝ → Fin ((n + k) + (m + 1)) → ℝ :=
    fun s ↦
      (sourceFlow layout E M κ P h ε s
        (finiteGraphPoint layout z b)).1
  have hgammaOne :
      IsIntegralCurve gammaOne
        (fun _ x ↦
          PolynomialFieldCode.realize
            (fieldCode layout M κ P h) x) := by
    simpa only [gammaOne] using
      finiteGraphPoint_isIntegralCurve
        layout E M κ P hP h hcompactBase z hz b
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
        (finiteGraphPoint layout z b)
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
          (finiteGraphPoint layout z
            (baseFlow layout E M P s b)).property
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
            (finiteGraphPoint layout z b)).property
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

/-- The explicit finite graph semiconjugates the compact base flow to the
canonical complete source flow. -/
theorem finiteGraphPoint_semiconj
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
    (z : BaseSpace layout → FinVector m ℝ)
    (hz :
      ∀ b i t,
        HasDerivAt
          (fun s ↦ z (baseFlow layout E M P s b) i)
          (baseDriftBCF layout M κ h
            (baseFlow layout E M P t b) i) t)
    (t : ℝ) :
    Semiconj
      (finiteGraphPoint layout z)
      (baseFlow layout E M P t)
      (sourceFlow layout E M κ P h ε t) := by
  intro b
  exact
    finiteGraphPoint_flow_eq
      layout E M κ P hP h hh ε hcompactBase z hz b t

/-- Push an invariant compact-base probability to the complete source
along a proved finite graph. -/
def finiteGraphInvariantProbability
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
    (z : BaseSpace layout → FinVector m ℝ)
    (hzcont : Continuous z)
    (hz :
      ∀ b i t,
        HasDerivAt
          (fun s ↦ z (baseFlow layout E M P s b) i)
          (baseDriftBCF layout M κ h
            (baseFlow layout E M P t b) i) t)
    (η :
      Dynamics.InvariantProbabilityMeasure
        (baseFlow layout E M P)) :
    Dynamics.InvariantProbabilityMeasure
      (sourceFlow layout E M κ P h ε) :=
  η.mapEquivariant
    (finiteGraphPoint layout z)
    (continuous_finiteGraphPoint layout z hzcont)
    (finiteGraphPoint_semiconj
      layout E M κ P hP h hh ε hcompactBase z hz)

/-! ## Quantitative reward on the finite graph -/

/-- Product of the squared mixed-central chart weights on the compact
base. -/
def baseCentralWeightProduct
    (layout : Fin n → Fin k ⊕ Fin l)
    (b : BaseSpace layout) : ℝ :=
  ∏ c : Fin k,
    b.1 (MixedCentralPolynomialCode.wIndex
      (n := n) c) ^ 2

/-- A uniform squared-norm bound on the affine graph gives the paper's
lower bound for its inverse-stereographic scalar coordinate. -/
theorem finiteGraph_stereoW_lower
    (layout : Fin n → Fin k ⊕ Fin l)
    (z : BaseSpace layout → FinVector m ℝ)
    (wStar : ℝ)
    (hnorm :
      ∀ b, normSq (z b) ≤ wStar / 4)
    (b : BaseSpace layout) :
    1 - wStar / 2 ≤ stereoW (z b) := by
  simpa only [stereoW] using
    stereoW_lower_bound_of_scaled_norm
      (normSq_nonneg (z b)) (hnorm b)

/-- Pointwise reward lower bound on a finite graph. -/
theorem finiteGraph_reward_lower
    (layout : Fin n → Fin k ⊕ Fin l)
    (ε : RationalCode)
    (z : BaseSpace layout → FinVector m ℝ)
    (wStar : ℝ)
    (hnorm :
      ∀ b, normSq (z b) ≤ wStar / 4)
    (hweight :
      ∀ b, wStar ≤ baseCentralWeightProduct layout b)
    (b : BaseSpace layout) :
    3 * wStar / 2 - (ε.decode : ℝ) ≤
      UnitSpherePolynomialWrapper.sourceRewardBCF
        (sourceBlock (m := m) layout)
        (rewardCode (n := n) (k := k) (m := m) ε)
        (finiteGraphPoint layout z b) := by
  let x : Fin n → ℝ :=
    fun j ↦
      b.1 (MixedCentralPolynomialCode.xIndex
        (k := k) j)
  let w : Fin k → ℝ :=
    fun c ↦
      b.1 (MixedCentralPolynomialCode.wIndex
        (n := n) c)
  have hb :
      MixedCentralPolynomialCode.chartPoint x w = b.1 :=
    MixedCentralPolynomialCode.chartPoint_decompose b.1
  rw [UnitSpherePolynomialWrapper.sourceRewardBCF_apply]
  change
    3 * wStar / 2 - (ε.decode : ℝ) ≤
      eval₂Hom (algebraMap ℚ ℝ)
        (AccumulatorPolynomialCode.combinedPoint
          b.1 (stereoU (z b)) (stereoW (z b)))
        (PolynomialCode.decode
          (rewardCode (n := n) (k := k) (m := m) ε))
  rw [← hb]
  apply finiteGraphGap_le_eval₂Hom_rewardCode
  · exact finiteGraph_stereoW_lower
      layout z wStar hnorm b
  · simpa only [baseCentralWeightProduct, w] using
      hweight b

/-- The invariant probability carried by a quantitatively bounded finite
graph has at least the same reward gap. -/
theorem finiteGraphInvariantProbability_reward_lower
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
    (z : BaseSpace layout → FinVector m ℝ)
    (hzcont : Continuous z)
    (hz :
      ∀ b i t,
        HasDerivAt
          (fun s ↦ z (baseFlow layout E M P s b) i)
          (baseDriftBCF layout M κ h
            (baseFlow layout E M P t b) i) t)
    (η :
      Dynamics.InvariantProbabilityMeasure
        (baseFlow layout E M P))
    (wStar : ℝ)
    (hnorm :
      ∀ b, normSq (z b) ≤ wStar / 4)
    (hweight :
      ∀ b, wStar ≤ baseCentralWeightProduct layout b) :
    3 * wStar / 2 - (ε.decode : ℝ) ≤
      Dynamics.observableAverage
        (UnitSpherePolynomialWrapper.sourceRewardBCF
          (sourceBlock (m := m) layout)
          (rewardCode (n := n) (k := k) (m := m) ε))
        ((finiteGraphInvariantProbability
          layout E M κ P hP h hh ε hcompactBase
          z hzcont hz η).measure) := by
  let reward :=
    UnitSpherePolynomialWrapper.sourceRewardBCF
      (sourceBlock (m := m) layout)
      (rewardCode (n := n) (k := k) (m := m) ε)
  let graph := finiteGraphPoint layout z
  let hgraph := continuous_finiteGraphPoint layout z hzcont
  let hequiv :=
    finiteGraphPoint_semiconj
      layout E M κ P hP h hh ε hcompactBase z hz
  change
    3 * wStar / 2 - (ε.decode : ℝ) ≤
      Dynamics.observableAverage reward
        ((η.mapEquivariant graph hgraph hequiv).measure)
  rw [Dynamics.observableAverage_mapEquivariant]
  unfold Dynamics.observableAverage
  have hpoint :
      ∀ᵐ b ∂(η.measure : Measure (BaseSpace layout)),
        3 * wStar / 2 - (ε.decode : ℝ) ≤
          (reward.compContinuous ⟨graph, hgraph⟩) b := by
    filter_upwards with b
    exact finiteGraph_reward_lower
      layout ε z wStar hnorm hweight b
  calc
    3 * wStar / 2 - (ε.decode : ℝ) =
        ∫ _b : BaseSpace layout,
          (3 * wStar / 2 - (ε.decode : ℝ))
          ∂(η.measure : Measure (BaseSpace layout)) := by
            simp
    _ ≤
        ∫ b,
          (reward.compContinuous ⟨graph, hgraph⟩) b
          ∂(η.measure : Measure (BaseSpace layout)) := by
      exact integral_mono_ae
        (integrable_const _)
        ((reward.compContinuous ⟨graph, hgraph⟩).integrable _)
        hpoint

end CompactAccumulatorPipelineCode

end

end HGAS
