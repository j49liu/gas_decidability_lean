import HGAS.Compiler.CompactAccumulatorPipelineCode
import HGAS.Compactification.MixedCentralPolynomialGlobalTangency
import HGAS.Accumulator.ProductSphereTangency
import Mathlib.Tactic

/-!
# Product-sphere tangency of the compact source/accumulator pipeline

This module joins the two global tangency ledgers:

1. mixed central compactification turns `k` affine blocks and `l` already
   compact blocks into `k+l` sphere blocks;
2. the stereographic vector accumulator adds one further sphere.

The result is a single block assignment for the exact finite polynomial
field emitted by `CompactAccumulatorPipelineCode.fieldCode`.  The proof is
global: it includes equators, multiple projective corners, and accumulator
infinity.  No division by a chart coordinate occurs.
-/

namespace HGAS

open _root_.MvPolynomial

noncomputable section

namespace CompactAccumulatorPipelineCode

variable {n k l m : ℕ}

/-- Block assignment of the complete compact source and its vector
accumulator. -/
def sourceBlock
    (layout : Fin n → Fin k ⊕ Fin l) :
    Fin ((n + k) + (m + 1)) → Fin ((k + l) + 1) :=
  AccumulatorPolynomialCode.productSphereBlock
    (m := m) (MixedCentralPolynomialCode.targetBlock layout)

/-- Every flattened base-plus-accumulator point is recovered from its three
coordinate projections. -/
theorem combinedPoint_decompose
    {R : Type*}
    (v : Fin ((n + k) + (m + 1)) → R) :
    AccumulatorPolynomialCode.combinedPoint
        (fun q ↦
          v (AccumulatorPolynomialCode.baseIndex
            (m := m) q))
        (fun i ↦
          v (AccumulatorPolynomialCode.uIndex
            (n := n + k) i))
        (v (AccumulatorPolynomialCode.wIndex (n + k) m)) =
      v := by
  funext q
  obtain ⟨j | r, rfl⟩ := finSumFinEquiv.surjective q
  · simp [AccumulatorPolynomialCode.combinedPoint,
      AccumulatorPolynomialCode.baseIndex,
      DegreePaddingCode.baseIndex]
  · obtain ⟨i | e, rfl⟩ := finSumFinEquiv.surjective r
    · simp [AccumulatorPolynomialCode.combinedPoint,
        AccumulatorPolynomialCode.uIndex,
        AccumulatorPolynomialCode.uAuxIndex,
        DegreePaddingCode.sinkIndex]
    · fin_cases e
      simp [AccumulatorPolynomialCode.combinedPoint,
        AccumulatorPolynomialCode.wIndex,
        AccumulatorPolynomialCode.wAuxIndex,
        DegreePaddingCode.sinkIndex]

/-- Tangency at a point already displayed in mixed-central and accumulator
coordinates. -/
theorem fieldCode_sourceTangentAt_chartPoint
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (h : Fin m → PolynomialCode n)
    (x : Fin n → ℝ) (w : Fin k → ℝ)
    (u : Fin m → ℝ) (W : ℝ)
    (hspheres :
      UnitSpherePolynomialWrapper.OnSourceProductSpheres
        (sourceBlock (m := m) layout)
        (AccumulatorPolynomialCode.combinedPoint
          (MixedCentralPolynomialCode.chartPoint x w) u W))
    (hcompact :
      ∀ c, MixedCentralPolynomialCode.compactBlockDot layout x
        (MixedCentralPolynomialCode.clearedSourceVelocity
          layout M P
          (MixedCentralPolynomialCode.chartPoint x w)) c = 0) :
    UnitSpherePolynomialWrapper.SourceTangentAt
        (sourceBlock (m := m) layout)
        (AccumulatorPolynomialCode.combinedPoint
          (MixedCentralPolynomialCode.chartPoint x w) u W)
        (PolynomialFieldCode.realize
          (fieldCode layout M κ P h)
          (AccumulatorPolynomialCode.combinedPoint
            (MixedCentralPolynomialCode.chartPoint x w) u W)) := by
  have hsplit :=
    (AccumulatorPolynomialCode.onSourceProductSpheres_productSphereBlock_iff
        (MixedCentralPolynomialCode.targetBlock layout)
        (MixedCentralPolynomialCode.chartPoint x w) u W).mp
      hspheres
  have hbase :
      UnitSpherePolynomialWrapper.SourceTangentAt
        (MixedCentralPolynomialCode.targetBlock layout)
        (MixedCentralPolynomialCode.chartPoint x w)
        (PolynomialFieldCode.realize
          (baseFieldCode layout M P)
          (MixedCentralPolynomialCode.chartPoint x w)) := by
    exact
      MixedCentralPolynomialCode.fieldCode_sourceTangentAt_chartPoint
        layout M P x w hsplit.1 hcompact
  unfold fieldCode
  exact
    AccumulatorPolynomialCode.fieldCode_sourceTangentAt
      (MixedCentralPolynomialCode.targetBlock layout)
      (baseFieldCode layout M P)
      (slowedDriftCode layout M κ h)
      (MixedCentralPolynomialCode.chartPoint x w) u W
      hbase hsplit.2

/-- Global wrapper-facing tangency theorem for an arbitrary flattened
ambient point.  The sole source-specific premise is tangency of each
already compact source block after denominator clearing. -/
theorem fieldCode_sourceTangentAt
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (h : Fin m → PolynomialCode n)
    (v : Fin ((n + k) + (m + 1)) → ℝ)
    (hspheres :
      UnitSpherePolynomialWrapper.OnSourceProductSpheres
        (sourceBlock (m := m) layout) v)
    (hcompact :
      let y : Fin (n + k) → ℝ :=
        fun q ↦
          v (AccumulatorPolynomialCode.baseIndex
            (m := m) q)
      let x : Fin n → ℝ :=
        fun j ↦ y (MixedCentralPolynomialCode.xIndex
          (k := k) j)
      ∀ c, MixedCentralPolynomialCode.compactBlockDot layout x
        (MixedCentralPolynomialCode.clearedSourceVelocity
          layout M P y) c = 0) :
    UnitSpherePolynomialWrapper.SourceTangentAt
        (sourceBlock (m := m) layout) v
        (PolynomialFieldCode.realize
          (fieldCode layout M κ P h) v) := by
  let y : Fin (n + k) → ℝ :=
    fun q ↦
      v (AccumulatorPolynomialCode.baseIndex
        (m := m) q)
  let x : Fin n → ℝ :=
    fun j ↦ y (MixedCentralPolynomialCode.xIndex
      (k := k) j)
  let w : Fin k → ℝ :=
    fun b ↦ y (MixedCentralPolynomialCode.wIndex
      (n := n) b)
  let u : Fin m → ℝ :=
    fun i ↦
      v (AccumulatorPolynomialCode.uIndex
        (n := n + k) i)
  let W : ℝ :=
    v (AccumulatorPolynomialCode.wIndex (n + k) m)
  have hy :
      MixedCentralPolynomialCode.chartPoint x w = y := by
    exact
      MixedCentralPolynomialCode.chartPoint_decompose y
  have hv :
      AccumulatorPolynomialCode.combinedPoint y u W = v := by
    exact combinedPoint_decompose v
  have hv' :
      AccumulatorPolynomialCode.combinedPoint
          (MixedCentralPolynomialCode.chartPoint x w) u W =
        v := by
    rw [hy, hv]
  rw [← hv'] at hspheres ⊢
  apply fieldCode_sourceTangentAt_chartPoint
    layout M κ P h x w u W hspheres
  simpa only [hy] using hcompact

end CompactAccumulatorPipelineCode

end

end HGAS
