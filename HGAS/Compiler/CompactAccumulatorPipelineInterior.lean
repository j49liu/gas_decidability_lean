import HGAS.Analysis.LinearODEZero
import HGAS.Compiler.CompactAccumulatorPipelineCertificate
import HGAS.Dynamics.InvariantRestriction
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic

/-!
# Invariance of the finite interior chart

For the complete compact source there are two kinds of boundary:

* a central compactification equator `w_b = 0`;
* the unique accumulator point at infinity, characterized on the
  accumulator sphere by `W = -1`.

The emitted equations contain the exact factors

```
        w_b' = (-w_b D_b) w_b,
        (1+W)' = (-(U·g)) (1+W).
```

Scalar uniqueness therefore propagates either zero for all time.  This
module proves that every boundary face, their union, and the complementary
finite interior chart are invariant under any flow solving the literal
pipeline ODE.  It also proves measurability of the interior chart, providing
the set required by the compact-accumulator measure argument.
-/

namespace HGAS

open _root_.MvPolynomial
open Function Set

noncomputable section

namespace CompactAccumulatorPipelineCode

variable {n k l m : ℕ}

/-- Raw centrally compactified base coordinates. -/
def sourceBasePoint
    {layout : Fin n → Fin k ⊕ Fin l}
    (v :
      UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout)) :
    Fin (n + k) → ℝ :=
  fun q ↦
    v.1 (AccumulatorPolynomialCode.baseIndex
      (m := m) q)

/-- Old mixed-central coordinates extracted from the compact base. -/
def sourceOldPoint
    {layout : Fin n → Fin k ⊕ Fin l}
    (v :
      UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout)) :
    Fin n → ℝ :=
  fun j ↦
    sourceBasePoint v
      (MixedCentralPolynomialCode.xIndex (k := k) j)

/-- One central chart coordinate `w_b`. -/
def sourceChartWeight
    {layout : Fin n → Fin k ⊕ Fin l}
    (v :
      UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout))
    (b : Fin k) : ℝ :=
  sourceBasePoint v
    (MixedCentralPolynomialCode.wIndex (n := n) b)

/-- One accumulator vector coordinate. -/
def sourceAccumulatorU
    {layout : Fin n → Fin k ⊕ Fin l}
    (v :
      UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout))
    (i : Fin m) : ℝ :=
  v.1 (AccumulatorPolynomialCode.uIndex
    (n := n + k) i)

/-- The stereographic scalar coordinate `W`. -/
def sourceAccumulatorW
    {layout : Fin n → Fin k ⊕ Fin l}
    (v :
      UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout)) : ℝ :=
  v.1 (AccumulatorPolynomialCode.wIndex (n + k) m)

/-- Value of the cleared affine-block dot polynomial `D_b`. -/
def sourceAffineDotValue
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (P : PolynomialFieldCode n)
    (v :
      UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout))
    (b : Fin k) : ℝ :=
  eval₂Hom (algebraMap ℚ ℝ) (sourceBasePoint v)
    (PolynomialCode.decode
      (MixedCentralPolynomialCode.affineBlockDotCode
        layout M P b))

/-- Value of the complete accumulator dot polynomial `U·g`. -/
def sourceAccumulatorDotValue
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (κ : RationalCode)
    (h : Fin m → PolynomialCode n)
    (v :
      UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout)) : ℝ :=
  eval₂Hom (algebraMap ℚ ℝ) v.1
    (PolynomialCode.decode
      (AccumulatorPolynomialCode.dotCode
        (slowedDriftCode layout M κ h)))

/-- Evaluation of a rational polynomial is continuous on the source
product sphere. -/
private theorem continuous_eval₂Hom_source
    {N K : ℕ} {block : Fin N → Fin K}
    (p : MvPolynomial (Fin N) ℚ) :
    Continuous
      (fun v :
          UnitSpherePolynomialWrapper.SourceProductSphere block ↦
        eval₂Hom (algebraMap ℚ ℝ) v.1 p) := by
  have h :=
    MvPolynomial.continuous_eval
      (MvPolynomial.map (algebraMap ℚ ℝ) p)
  have h' := h.comp
    (continuous_subtype_val :
      Continuous
        (fun v :
          UnitSpherePolynomialWrapper.SourceProductSphere block ↦
            v.1))
  simpa only [MvPolynomial.eval_map] using h'

theorem continuous_sourceChartWeight
    (layout : Fin n → Fin k ⊕ Fin l)
    (b : Fin k) :
    Continuous
      (fun v :
          UnitSpherePolynomialWrapper.SourceProductSphere
            (sourceBlock (m := m) layout) ↦
        sourceChartWeight v b) := by
  unfold sourceChartWeight sourceBasePoint
  exact
    (continuous_apply
      (AccumulatorPolynomialCode.baseIndex
        (m := m)
        (MixedCentralPolynomialCode.wIndex
          (n := n) b))).comp continuous_subtype_val

theorem continuous_sourceAccumulatorW
    (layout : Fin n → Fin k ⊕ Fin l) :
    Continuous
      (sourceAccumulatorW :
        UnitSpherePolynomialWrapper.SourceProductSphere
          (sourceBlock (m := m) layout) → ℝ) := by
  unfold sourceAccumulatorW
  exact
    (continuous_apply
      (AccumulatorPolynomialCode.wIndex (n + k) m)).comp
        continuous_subtype_val

theorem continuous_sourceAffineDotValue
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (P : PolynomialFieldCode n)
    (b : Fin k) :
    Continuous
      (sourceAffineDotValue (m := m) layout M P · b) := by
  have hpoly :=
    MvPolynomial.continuous_eval
      (MvPolynomial.map (algebraMap ℚ ℝ)
        (PolynomialCode.decode
          (MixedCentralPolynomialCode.affineBlockDotCode
            layout M P b)))
  have hbase :
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
  have h := hpoly.comp hbase
  simpa only [MvPolynomial.eval_map,
    sourceAffineDotValue] using h

theorem continuous_sourceAccumulatorDotValue
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (κ : RationalCode)
    (h : Fin m → PolynomialCode n) :
    Continuous
      (sourceAccumulatorDotValue layout M κ h) := by
  exact
    continuous_eval₂Hom_source
      (PolynomialCode.decode
        (AccumulatorPolynomialCode.dotCode
          (slowedDriftCode layout M κ h)))

/-- The literal source-chart equation factors as
`w_b' = (-w_b D_b) w_b` at every compact source point. -/
theorem realize_fieldCode_chartWeight
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (h : Fin m → PolynomialCode n)
    (v :
      UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout))
    (b : Fin k) :
    PolynomialFieldCode.realize
        (fieldCode layout M κ P h) v.1
        (AccumulatorPolynomialCode.baseIndex
          (m := m)
          (MixedCentralPolynomialCode.wIndex
            (n := n) b)) =
      (-sourceChartWeight v b *
          sourceAffineDotValue layout M P v b) *
        sourceChartWeight v b := by
  let y := sourceBasePoint v
  let u : Fin m → ℝ := fun i ↦ sourceAccumulatorU v i
  let W : ℝ := sourceAccumulatorW v
  have hv :
      AccumulatorPolynomialCode.combinedPoint y u W = v.1 := by
    exact combinedPoint_decompose v.1
  rw [← hv]
  rw [PolynomialFieldCode.realize_apply, fieldCode,
    AccumulatorPolynomialCode.eval₂Hom_fieldCode_base]
  simp only [baseFieldCode,
    MixedCentralPolynomialCode.fieldCode,
    MixedCentralPolynomialCode.finSumFinEquiv_symm_wIndex,
    MixedCentralPolynomialCode.wFieldCode,
    PolynomialCode.decode_neg_code,
    PolynomialCode.decode_mul_code,
    PolynomialCode.decode_pow_code,
    PolynomialCode.decode_varCode,
    map_neg, map_mul, map_pow, eval₂Hom_X']
  change
    -(y (MixedCentralPolynomialCode.wIndex (n := n) b) ^ 2 *
        sourceAffineDotValue layout M P v b) =
      (-sourceChartWeight v b *
          sourceAffineDotValue layout M P v b) *
        sourceChartWeight v b
  dsimp only [sourceChartWeight, sourceBasePoint, y]
  ring

/-- The literal accumulator scalar equation factors as
`W' = -(U·g)(1+W)`. -/
theorem realize_fieldCode_accumulatorW
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
      -sourceAccumulatorDotValue layout M κ h v *
        (1 + sourceAccumulatorW v) := by
  let y := sourceBasePoint v
  let u : Fin m → ℝ := fun i ↦ sourceAccumulatorU v i
  let W : ℝ := sourceAccumulatorW v
  have hv :
      AccumulatorPolynomialCode.combinedPoint y u W = v.1 := by
    exact combinedPoint_decompose v.1
  rw [← hv]
  rw [PolynomialFieldCode.realize_apply, fieldCode,
    AccumulatorPolynomialCode.eval₂Hom_fieldCode_w]
  unfold accumulatorWField
  unfold dot
  rw [← AccumulatorPolynomialCode.eval₂Hom_dotCode]
  change
    -(1 + W) *
        eval₂Hom (algebraMap ℚ ℝ)
          (AccumulatorPolynomialCode.combinedPoint y u W)
          (PolynomialCode.decode
            (AccumulatorPolynomialCode.dotCode
              (slowedDriftCode layout M κ h))) =
      -sourceAccumulatorDotValue layout M κ h v *
        (1 + sourceAccumulatorW v)
  rw [hv]
  dsimp only [sourceAccumulatorDotValue,
    sourceAccumulatorW, W]
  ring

/-- Along any flow solving the pipeline ODE, a central chart coordinate
satisfies its scalar homogeneous equation. -/
theorem sourceChartWeight_hasDerivAt
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
    (b : Fin k) (t : ℝ) :
    HasDerivAt
      (fun s ↦ sourceChartWeight (ϕ s v) b)
      ((-sourceChartWeight (ϕ t v) b *
          sourceAffineDotValue layout M P (ϕ t v) b) *
        sourceChartWeight (ϕ t v) b) t := by
  have hcoord :=
    (hasDerivAt_pi.mp (hcurve v t))
      (AccumulatorPolynomialCode.baseIndex
        (m := m)
        (MixedCentralPolynomialCode.wIndex
          (n := n) b))
  dsimp only at hcoord
  rw [realize_fieldCode_chartWeight] at hcoord
  simpa only [sourceChartWeight, sourceBasePoint] using hcoord

/-- The shifted scalar coordinate `1+W` also satisfies a scalar
homogeneous equation. -/
theorem one_add_sourceAccumulatorW_hasDerivAt
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
      (fun s ↦ 1 + sourceAccumulatorW (ϕ s v))
      ((-sourceAccumulatorDotValue layout M κ h (ϕ t v)) *
        (1 + sourceAccumulatorW (ϕ t v))) t := by
  have hcoord :=
    (hasDerivAt_pi.mp (hcurve v t))
      (AccumulatorPolynomialCode.wIndex (n + k) m)
  dsimp only at hcoord
  rw [realize_fieldCode_accumulatorW] at hcoord
  simpa only [sourceAccumulatorW] using hcoord.const_add 1

/-- One central equator. -/
def sourceEquatorSet
    (layout : Fin n → Fin k ⊕ Fin l)
    (b : Fin k) :
    Set
      (UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout)) :=
  {v | sourceChartWeight v b = 0}

/-- The unique accumulator-infinity stratum. -/
def accumulatorInfinitySet
    (layout : Fin n → Fin k ⊕ Fin l) :
    Set
      (UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout)) :=
  {v | sourceAccumulatorW v = -1}

/-- Union of all source equators and accumulator infinity. -/
def sourceBoundarySet
    (layout : Fin n → Fin k ⊕ Fin l) :
    Set
      (UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout)) :=
  {v | (∃ b, sourceChartWeight v b = 0) ∨
    sourceAccumulatorW v = -1}

/-- Complementary finite interior chart. -/
def sourceFiniteInteriorSet
    (layout : Fin n → Fin k ⊕ Fin l) :
    Set
      (UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout)) :=
  (sourceBoundarySet (m := m) layout)ᶜ

theorem sourceFiniteInteriorSet_iff
    (layout : Fin n → Fin k ⊕ Fin l)
    (v :
      UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout)) :
    v ∈ sourceFiniteInteriorSet (m := m) layout ↔
      (∀ b, sourceChartWeight v b ≠ 0) ∧
      sourceAccumulatorW v ≠ -1 := by
  simp [sourceFiniteInteriorSet, sourceBoundarySet]

theorem measurableSet_sourceBoundarySet
    (layout : Fin n → Fin k ⊕ Fin l) :
    MeasurableSet (sourceBoundarySet (m := m) layout) := by
  have hequator :
      MeasurableSet
        {v :
          UnitSpherePolynomialWrapper.SourceProductSphere
            (sourceBlock (m := m) layout) |
          ∃ b, sourceChartWeight v b = 0} := by
    rw [show
        {v :
          UnitSpherePolynomialWrapper.SourceProductSphere
            (sourceBlock (m := m) layout) |
          ∃ b, sourceChartWeight v b = 0} =
          ⋃ b : Fin k, sourceEquatorSet (m := m) layout b by
      ext v
      simp [sourceEquatorSet]]
    exact MeasurableSet.iUnion fun b ↦
      (isClosed_eq
        (continuous_sourceChartWeight (m := m) layout b)
        continuous_const).measurableSet
  have hinfinity :
      MeasurableSet
        (accumulatorInfinitySet (m := m) layout) :=
    (isClosed_eq
      (continuous_sourceAccumulatorW (m := m) layout)
      continuous_const).measurableSet
  change
    MeasurableSet
      ({v |
          ∃ b, sourceChartWeight v b = 0} ∪
        accumulatorInfinitySet (m := m) layout)
  exact hequator.union hinfinity

theorem measurableSet_sourceFiniteInteriorSet
    (layout : Fin n → Fin k ⊕ Fin l) :
    MeasurableSet (sourceFiniteInteriorSet (m := m) layout) :=
  (measurableSet_sourceBoundarySet (m := m) layout).compl

/-- The literal source reward is uniformly at most `-ε` off the finite
interior chart.  This combines the source-face and accumulator-infinity
estimates without any dynamical hypothesis. -/
theorem sourceRewardBCF_le_neg_epsilon_of_not_mem_finiteInterior
    (layout : Fin n → Fin k ⊕ Fin l)
    (ε : RationalCode)
    (v :
      UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := m) layout))
    (hvnot :
      v ∉ sourceFiniteInteriorSet (m := m) layout) :
    UnitSpherePolynomialWrapper.sourceRewardBCF
        (sourceBlock (m := m) layout)
        (rewardCode (n := n) (k := k) (m := m) ε) v ≤
      -(ε.decode : ℝ) := by
  let y : Fin (n + k) → ℝ := sourceBasePoint v
  let x : Fin n → ℝ := sourceOldPoint v
  let w : Fin k → ℝ := fun b ↦ sourceChartWeight v b
  let u : Fin m → ℝ := fun i ↦ sourceAccumulatorU v i
  let W : ℝ := sourceAccumulatorW v
  have hy :
      MixedCentralPolynomialCode.chartPoint x w = y := by
    exact
      MixedCentralPolynomialCode.chartPoint_decompose y
  have hv :
      AccumulatorPolynomialCode.combinedPoint y u W = v.1 := by
    exact combinedPoint_decompose v.1
  have hspheres :
      UnitSpherePolynomialWrapper.OnSourceProductSpheres
        (sourceBlock (m := m) layout)
        (AccumulatorPolynomialCode.combinedPoint y u W) := by
    rw [hv]
    exact v.2
  have hsplit :=
    (AccumulatorPolynomialCode.onSourceProductSpheres_productSphereBlock_iff
      (MixedCentralPolynomialCode.targetBlock layout) y u W).mp
      hspheres
  have hvboundary :
      v ∈ sourceBoundarySet (m := m) layout := by
    simpa only [sourceFiniteInteriorSet, Set.mem_compl_iff,
      not_not] using hvnot
  rw [UnitSpherePolynomialWrapper.sourceRewardBCF_apply]
  rw [← hv, ← hy]
  rcases hvboundary with ⟨b, hb⟩ | hinfinity
  · apply eval₂Hom_rewardCode_le_neg_epsilon_on_sourceFace
      ε x w u W hsplit.2
    exact ⟨b, hb⟩
  · apply eval₂Hom_rewardCode_le_neg_epsilon_at_infinity
      ε layout x w u W
    · simpa only [hy] using hsplit.1
    · exact hinfinity

/-- Every central equator is invariant. -/
theorem isInvariant_sourceEquatorSet
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
    (b : Fin k) :
    IsInvariant ϕ (sourceEquatorSet (m := m) layout b) := by
  intro t v hv
  let r : ℝ → ℝ :=
    fun s ↦ sourceChartWeight (ϕ s v) b
  let a : ℝ → ℝ :=
    fun s ↦
      -sourceChartWeight (ϕ s v) b *
        sourceAffineDotValue layout M P (ϕ s v) b
  have htrajectory :
      Continuous
        (fun s : ℝ ↦ ϕ s v) :=
    ϕ.continuous continuous_id continuous_const
  have ha : Continuous a := by
    exact
      ((continuous_sourceChartWeight (m := m) layout b).comp
        htrajectory).neg.mul
          ((continuous_sourceAffineDotValue
            (m := m) layout M P b).comp htrajectory)
  have hr : ∀ s, HasDerivAt r (a s * r s) s := by
    intro s
    exact
      sourceChartWeight_hasDerivAt
        layout M κ P h ϕ hcurve v b s
  have hr0 : r 0 = 0 := by
    simpa [r, sourceEquatorSet] using hv
  have hzero :=
    real_eq_zero_of_hasDerivAt_eq_mul a r ha hr hr0
  change sourceChartWeight (ϕ t v) b = 0
  simpa only [r] using congrFun hzero t

/-- Accumulator infinity is invariant. -/
theorem isInvariant_accumulatorInfinitySet
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
              (fieldCode layout M κ P h) x)) :
    IsInvariant ϕ (accumulatorInfinitySet (m := m) layout) := by
  intro t v hv
  let r : ℝ → ℝ :=
    fun s ↦ 1 + sourceAccumulatorW (ϕ s v)
  let a : ℝ → ℝ :=
    fun s ↦
      -sourceAccumulatorDotValue layout M κ h (ϕ s v)
  have htrajectory :
      Continuous
        (fun s : ℝ ↦ ϕ s v) :=
    ϕ.continuous continuous_id continuous_const
  have ha : Continuous a :=
    ((continuous_sourceAccumulatorDotValue
      layout M κ h).comp htrajectory).neg
  have hr : ∀ s, HasDerivAt r (a s * r s) s := by
    intro s
    exact
      one_add_sourceAccumulatorW_hasDerivAt
        layout M κ P h ϕ hcurve v s
  have hr0 : r 0 = 0 := by
    change 1 + sourceAccumulatorW (ϕ 0 v) = 0
    rw [ϕ.map_zero_apply]
    change sourceAccumulatorW v = -1 at hv
    linarith
  have hzero :=
    real_eq_zero_of_hasDerivAt_eq_mul a r ha hr hr0
  change sourceAccumulatorW (ϕ t v) = -1
  have ht := congrFun hzero t
  dsimp only [r] at ht
  linarith

/-- The full boundary union is invariant. -/
theorem isInvariant_sourceBoundarySet
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
              (fieldCode layout M κ P h) x)) :
    IsInvariant ϕ (sourceBoundarySet (m := m) layout) := by
  intro t v hv
  rcases hv with ⟨b, hb⟩ | hinfinity
  · left
    exact
      ⟨b,
        isInvariant_sourceEquatorSet
          layout M κ P h ϕ hcurve b t hb⟩
  · right
    exact
      isInvariant_accumulatorInfinitySet
        layout M κ P h ϕ hcurve t hinfinity

/-- The finite interior chart is invariant under the two-sided flow. -/
theorem isInvariant_sourceFiniteInteriorSet
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
              (fieldCode layout M κ P h) x)) :
    IsInvariant ϕ (sourceFiniteInteriorSet (m := m) layout) := by
  exact
    Dynamics.isInvariant_compl_of_flow ϕ
      (isInvariant_sourceBoundarySet
        layout M κ P h ϕ hcurve)

end CompactAccumulatorPipelineCode

end

end HGAS
