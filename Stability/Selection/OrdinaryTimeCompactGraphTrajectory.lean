import HGAS.Compiler.CompactAccumulatorPipelineFiniteGraph
import HGAS.Compiler.AllAffinePositiveCentralTrajectory

/-!
# Compact accumulator trajectories over a parametrized graph

The base point and accumulator primitive may share a parameter without
the primitive descending to a function of the base point. The chain rule
still gives an actual compact-source trajectory, and ODE uniqueness
identifies it with the canonical complete polynomial flow.
-/

namespace Stability.Selection

noncomputable section

open HGAS HGAS.CompactAccumulatorPipelineCode Function Metric Set

variable {n k l m : ℕ}

/-- A compact base point paired with an affine accumulator point. -/
def compactGraphPoint (layout : Fin n → Fin k ⊕ Fin l)
    (b : BaseSpace layout) (z : Fin m → ℝ) :
    UnitSpherePolynomialWrapper.SourceProductSphere (sourceBlock (m := m) layout) :=
  finiteGraphPoint layout (fun _ ↦ z) b

theorem continuous_compactGraphPoint (layout : Fin n → Fin k ⊕ Fin l) :
    Continuous (fun p : BaseSpace layout × (Fin m → ℝ) ↦ compactGraphPoint layout p.1 p.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro q
  obtain ⟨j | r, rfl⟩ := finSumFinEquiv.surjective q
  · have hc : Continuous (fun p : BaseSpace layout × (Fin m → ℝ) ↦ p.1.val j) :=
      (continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)
    simpa [compactGraphPoint, finiteGraphPoint, AccumulatorPolynomialCode.combinedPoint] using hc
  · obtain ⟨i | e, rfl⟩ := finSumFinEquiv.surjective r
    · have hc : Continuous (fun p : BaseSpace layout × (Fin m → ℝ) ↦ stereoU p.2 i) :=
        (continuous_apply i).comp (continuous_stereoU.comp continuous_snd)
      simpa [compactGraphPoint, finiteGraphPoint, AccumulatorPolynomialCode.combinedPoint] using hc
    · fin_cases e
      have hc : Continuous (fun p : BaseSpace layout × (Fin m → ℝ) ↦ stereoW p.2) :=
        continuous_stereoW.comp continuous_snd
      simpa [compactGraphPoint, finiteGraphPoint, AccumulatorPolynomialCode.combinedPoint] using hc

/-- Differentiating the two chart maps gives the literal compiled field. -/
theorem compactGraphPoint_isIntegralCurve
    (layout : Fin n → Fin k ⊕ Fin l) (M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n) (h : Fin m → PolynomialCode n)
    (b : ℝ → BaseSpace layout) (z : ℝ → Fin m → ℝ)
    (hb : IsIntegralCurve (fun t ↦ (b t).val)
      (fun _ y ↦ PolynomialFieldCode.realize (baseFieldCode layout M P) y))
    (hz : ∀ i t, HasDerivAt (fun s ↦ z s i) (baseDriftBCF layout M κ h (b t) i) t) :
    IsIntegralCurve (fun t ↦ (compactGraphPoint layout (b t) (z t)).val)
      (fun _ y ↦ PolynomialFieldCode.realize (fieldCode layout M κ P h) y) := by
  intro t
  rw [hasDerivAt_pi]
  intro q
  obtain ⟨j | r, rfl⟩ := finSumFinEquiv.surjective q
  · convert hasDerivAt_pi.mp (hb t) j using 1
    · funext s
      simp [compactGraphPoint, finiteGraphPoint, AccumulatorPolynomialCode.combinedPoint]
    · change PolynomialFieldCode.realize (fieldCode layout M κ P h)
        (compactGraphPoint layout (b t) (z t)).val
        (AccumulatorPolynomialCode.baseIndex j) = _
      rw [realize_fieldCode_baseIndex]
      simp [compactGraphPoint]
  · obtain ⟨i | e, rfl⟩ := finSumFinEquiv.surjective r
    · convert stereoU_hasDerivAt z (fun s ↦ baseDriftBCF layout M κ h (b s)) t
        (fun j ↦ hz j t) i using 1
      · funext s
        simp [compactGraphPoint, finiteGraphPoint, AccumulatorPolynomialCode.combinedPoint]
      · change PolynomialFieldCode.realize (fieldCode layout M κ P h)
          (compactGraphPoint layout (b t) (z t)).val
          (AccumulatorPolynomialCode.uIndex i) = _
        rw [realize_fieldCode_accumulatorU]
        simp [compactGraphPoint]
    · fin_cases e
      convert stereoW_hasDerivAt z (fun s ↦ baseDriftBCF layout M κ h (b s)) t
        (fun j ↦ hz j t) using 1
      · funext s
        simp [compactGraphPoint, finiteGraphPoint, AccumulatorPolynomialCode.combinedPoint]
      · change PolynomialFieldCode.realize (fieldCode layout M κ P h)
          (compactGraphPoint layout (b t) (z t)).val
          (AccumulatorPolynomialCode.wIndex (n + k) m) = _
        rw [realize_fieldCode_accumulatorW_factor]
        simp [compactGraphPoint]

/-- A complete compact-source integral curve is the canonical flow orbit. -/
theorem compactSourceIntegralCurve_eq_flow
    (layout : Fin n → Fin k ⊕ Fin l) (E M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n) (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
    (h : Fin m → PolynomialCode n) (hh : ∀ i, PolynomialCode.TermsDegreeLE E (h i))
    (ε : RationalCode)
    (htangent : ∀ y : BaseSpace layout,
      let x : Fin n → ℝ := fun j ↦ y.val (MixedCentralPolynomialCode.xIndex (k := k) j)
      ∀ c, MixedCentralPolynomialCode.compactBlockDot layout x
        (MixedCentralPolynomialCode.clearedSourceVelocity layout M P y.val) c = 0)
    (γ : ℝ → UnitSpherePolynomialWrapper.SourceProductSphere (sourceBlock (m := m) layout))
    (hγ : IsIntegralCurve (fun t ↦ (γ t).val)
      (fun _ y ↦ PolynomialFieldCode.realize (fieldCode layout M κ P h) y)) (t : ℝ) :
    γ t = sourceFlow layout E M κ P h ε t (γ 0) := by
  apply Subtype.ext
  have hflow := sourceFlow_integralCurve layout E M κ P hP h hh ε
    (fullCompactTangencyHypothesis_of_base layout M P htangent) (γ 0)
  have hC1 : ContDiff ℝ 1 (PolynomialFieldCode.realize (fieldCode layout M κ P h)) :=
    (UnitSpherePolynomialWrapper.contDiff_realize_sourcePolynomialFieldCode
      (fieldCode layout M κ P h)).of_le (by norm_num)
  obtain ⟨L, hL⟩ := hC1.contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_closedBall (0 : Fin ((n + k) + (m + 1)) → ℝ) 1)
    (isCompact_closedBall (0 : Fin ((n + k) + (m + 1)) → ℝ) 1)
  have hmem (v : UnitSpherePolynomialWrapper.SourceProductSphere
      (sourceBlock (m := m) layout)) : v.val ∈ closedBall 0 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      UnitSpherePolynomialWrapper.source_norm_le_one_of_onSourceProductSpheres
        (sourceBlock (m := m) layout) v.val v.property
  have heq : (fun t ↦ (γ t).val) =
      (fun t ↦ (sourceFlow layout E M κ P h ε t (γ 0)).val) := by
    apply ODE_solution_unique_univ
      (v := fun _ : ℝ ↦ PolynomialFieldCode.realize (fieldCode layout M κ P h))
      (s := fun _ ↦ closedBall 0 1) (K := L) (t₀ := 0)
    · exact fun _ ↦ hL
    · exact fun s ↦ ⟨hγ s, hmem _⟩
    · exact fun s ↦ ⟨hflow s, hmem _⟩
    · simp only [Flow.map_zero_apply]
  exact congrFun heq t

end

end Stability.Selection
