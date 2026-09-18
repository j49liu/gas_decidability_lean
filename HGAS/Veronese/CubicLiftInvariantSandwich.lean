import HGAS.Veronese.CubicLiftAngularFlow
import HGAS.Dynamics.AngularGAS
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# The invariant-measure sandwich for the stabilized cubic lift

This file proves the measure-theoretic part of the transverse stabilization
argument without assuming a global Lyapunov inequality.

Inside the tube `0 < W < η`, the actual angular derivative of the toric
penalty is strictly negative.  Outside the tube its sign is not controlled.
To isolate precisely the controlled region, choose a nonnegative smooth
bump `β` which is positive exactly on `(0,η)` and zero off that interval,
and let

```
χ(s) = ∫₀ˢ β(r) dr.
```

Along the stabilized angular flow,

```
d/dt χ(W(y(t))) = β(W(y(t))) · Y_H W(y(t)).
```

The right side is nonpositive everywhere and strictly negative precisely
in the punctured tube.  It is also an orbit-integral coboundary.  Every
invariant probability annihilates such a coboundary, so the nonpositive
generator must vanish almost everywhere.  Consequently every invariant
probability gives the punctured tube measure zero and is concentrated on

```
{W=0} ∪ {W≥η}.
```

This smooth-cap proof avoids an unformalized first-exit or barrier argument.
-/

namespace HGAS.Veronese

open Set Filter Function Metric MeasureTheory
open scoped Topology NNReal BigOperators BoundedContinuousFunction Interval

noncomputable section

variable {n k : ℕ} {F : HGAS.PolynomialField n}

/-! ## A smooth cap whose derivative detects exactly the punctured tube -/

/-- A nonnegative smooth function supported in `[0,η]` and positive on
the open interval `(0,η)`. -/
noncomputable def tubeDerivativeBump
    (η : ℝ) (hη : 0 < η) :
    ContDiffBump (η / 2 : ℝ) where
  rIn := η / 4
  rOut := η / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

theorem tubeDerivativeBump_pos
    (η : ℝ) (hη : 0 < η) (s : ℝ)
    (hs0 : 0 < s) (hsη : s < η) :
    0 < tubeDerivativeBump η hη s := by
  apply (tubeDerivativeBump η hη).pos_of_mem_ball
  rw [Metric.mem_ball, Real.dist_eq]
  change |s - η / 2| < η / 2
  rw [abs_lt]
  constructor <;> linarith

theorem tubeDerivativeBump_eq_zero_of_not_between
    (η : ℝ) (hη : 0 < η) (s : ℝ)
    (hs : ¬ (0 < s ∧ s < η)) :
    tubeDerivativeBump η hη s = 0 := by
  apply (tubeDerivativeBump η hη).zero_of_le_dist
  rw [Real.dist_eq]
  change η / 2 ≤ |s - η / 2|
  rw [le_abs]
  rcases not_and_or.mp hs with hs0 | hsη
  · right
    have hs0' : s ≤ 0 := le_of_not_gt hs0
    linarith
  · left
    have hsη' : η ≤ s := le_of_not_gt hsη
    linarith

/-- A smooth cap obtained by integrating `tubeDerivativeBump`. -/
def tubeCap
    (η : ℝ) (hη : 0 < η) (s : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..s, tubeDerivativeBump η hη r

theorem tubeCap_hasDerivAt
    (η : ℝ) (hη : 0 < η) (s : ℝ) :
    HasDerivAt (tubeCap η hη)
      (tubeDerivativeBump η hη s) s := by
  exact
    ((tubeDerivativeBump η hη).continuous.integral_hasStrictDerivAt
      0 s).hasDerivAt

theorem continuous_tubeCap
    (η : ℝ) (hη : 0 < η) :
    Continuous (tubeCap η hη) := by
  rw [continuous_iff_continuousAt]
  intro s
  exact (tubeCap_hasDerivAt η hη s).continuousAt

theorem continuous_penaltyLieDerivative
    {V : RealVeroneseSpace n k → RealVeroneseSpace n k}
    (hV : Continuous V) :
    Continuous (penaltyLieDerivative V) := by
  have hP :
      Continuous
        (penaltyAmbientGradient :
          RealVeroneseSpace n k → RealVeroneseSpace n k) :=
    continuous_penaltyAmbientGradient
  unfold penaltyLieDerivative weightedInner
  fun_prop

/-! ## Bounded observables on the compact weighted sphere -/

/-- The capped penalty as a bounded continuous observable. -/
noncomputable def stabilizedPenaltyCapBCF
    (b : CubicLiftStabilizationBounds F k) :
    weightedUnitSphere n k →ᵇ ℝ := by
  letI : CompactSpace (weightedUnitSphere n k) :=
    isCompact_iff_compactSpace.mp isCompact_weightedUnitSphere
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun y ↦ tubeCap b.η b.η_pos (completeToricEnergy y.1),
      (continuous_tubeCap b.η b.η_pos).comp
        (continuous_completeToricEnergy.comp continuous_subtype_val)⟩

/-- Infinitesimal generator of the capped penalty along the actual
stabilized angular flow. -/
noncomputable def stabilizedPenaltyGeneratorBCF
    (b : CubicLiftStabilizationBounds F k) :
    weightedUnitSphere n k →ᵇ ℝ := by
  letI : CompactSpace (weightedUnitSphere n k) :=
    isCompact_iff_compactSpace.mp isCompact_weightedUnitSphere
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun y ↦
      tubeDerivativeBump b.η b.η_pos (completeToricEnergy y.1) *
        penaltyLieDerivative
          (weightedAngularField
            (evaluatedStabilizedCubicField b)) y.1,
      ((tubeDerivativeBump b.η b.η_pos).continuous.comp
        (continuous_completeToricEnergy.comp continuous_subtype_val)).mul
        ((continuous_penaltyLieDerivative
          (continuous_weightedAngularField
            (contDiff_evaluatedStabilizedCubicField b).continuous)).comp
              continuous_subtype_val)⟩

@[simp]
theorem stabilizedPenaltyCapBCF_apply
    (b : CubicLiftStabilizationBounds F k)
    (y : weightedUnitSphere n k) :
    stabilizedPenaltyCapBCF b y =
      tubeCap b.η b.η_pos (completeToricEnergy y.1) :=
  rfl

@[simp]
theorem stabilizedPenaltyGeneratorBCF_apply
    (b : CubicLiftStabilizationBounds F k)
    (y : weightedUnitSphere n k) :
    stabilizedPenaltyGeneratorBCF b y =
      tubeDerivativeBump b.η b.η_pos (completeToricEnergy y.1) *
        penaltyLieDerivative
          (weightedAngularField
            (evaluatedStabilizedCubicField b)) y.1 :=
  rfl

/-- The capped generator is globally nonpositive.  Outside `(0,η)` the
bump factor is zero; inside, the stabilization estimate is negative. -/
theorem stabilizedPenaltyGenerator_nonpos
    (b : CubicLiftStabilizationBounds F k)
    (y : weightedUnitSphere n k) :
    stabilizedPenaltyGeneratorBCF b y ≤ 0 := by
  let W := completeToricEnergy y.1
  by_cases hbetween : 0 < W ∧ W < b.η
  · have hderiv :
        penaltyLieDerivative
            (weightedAngularField
              (evaluatedStabilizedCubicField b)) y.1 < 0 := by
      have hle :=
        stabilizedCubicAngular_penaltyDerivative_le
          b y.1 y.2 hbetween.2.le
      have hrate := cubicLiftStabilization_decayRate_pos b
      have hprod :
          0 <
            ((b.K : ℝ) * b.c - b.C) * W :=
        mul_pos hrate hbetween.1
      linarith
    change tubeDerivativeBump b.η b.η_pos W * _ ≤ 0
    exact mul_nonpos_of_nonneg_of_nonpos
      (tubeDerivativeBump b.η b.η_pos).nonneg hderiv.le
  · rw [stabilizedPenaltyGeneratorBCF_apply,
      tubeDerivativeBump_eq_zero_of_not_between
        b.η b.η_pos W hbetween, zero_mul]

/-- The capped generator is strictly negative throughout the punctured
stabilization tube. -/
theorem stabilizedPenaltyGenerator_neg
    (b : CubicLiftStabilizationBounds F k)
    (y : weightedUnitSphere n k)
    (hW0 : 0 < completeToricEnergy y.1)
    (hWη : completeToricEnergy y.1 < b.η) :
    stabilizedPenaltyGeneratorBCF b y < 0 := by
  rw [stabilizedPenaltyGeneratorBCF_apply]
  have hderiv :
      penaltyLieDerivative
          (weightedAngularField
            (evaluatedStabilizedCubicField b)) y.1 < 0 := by
    have hle :=
      stabilizedCubicAngular_penaltyDerivative_le
        b y.1 y.2 hWη.le
    have hrate := cubicLiftStabilization_decayRate_pos b
    have hprod :
        0 <
          ((b.K : ℝ) * b.c - b.C) *
            completeToricEnergy y.1 :=
      mul_pos hrate hW0
    linarith
  exact mul_neg_of_pos_of_neg
    (tubeDerivativeBump_pos b.η b.η_pos _ hW0 hWη)
    hderiv

/-! ## The orbit coboundary and invariant-measure exclusion -/

set_option maxHeartbeats 800000 in
-- Unfolding the restricted flow through the FTC chain rule is elaboration-heavy.
/-- The orbit integral of the capped generator is exactly the change in
the capped penalty over one unit of time. -/
theorem stabilizedPenaltyCap_orbit_coboundary
    (b : CubicLiftStabilizationBounds F k)
    (y : weightedUnitSphere n k) :
    HGAS.Dynamics.orbitIntegral
        (stabilizedCubicAngularFlow b)
        (stabilizedPenaltyGeneratorBCF b) 1 y =
      stabilizedPenaltyCapBCF b
          (stabilizedCubicAngularFlow b 1 y) -
        stabilizedPenaltyCapBCF b y := by
  let ϕ := stabilizedCubicAngularFlow b
  let g := stabilizedPenaltyGeneratorBCF b
  let w := stabilizedPenaltyCapBCF b
  have hderiv :
      ∀ t : ℝ,
        HasDerivAt
          (fun s ↦ w (ϕ s y))
          (g (ϕ t y)) t := by
    intro t
    have hcurve :
        HasDerivAt
          (fun s ↦ ((ϕ s y : weightedUnitSphere n k) :
            RealVeroneseSpace n k))
          (weightedAngularField
            (evaluatedStabilizedCubicField b)
            ((ϕ t y : weightedUnitSphere n k) :
              RealVeroneseSpace n k)) t := by
      have hamb :=
        stabilizedCubicAmbientAngularFlow_isIntegralCurve
          b y.1 y.2 t
      simpa [ϕ, stabilizedCubicAngularFlow,
        weightedUnitSphereFlow,
        stabilizedCubicAmbientAngularFlow] using hamb
    have hW :=
      HGAS.Veronese.HasDerivAt.toricPenalty_comp_eq_weightedInner
        hcurve
    have hcap :=
      (tubeCap_hasDerivAt b.η b.η_pos
        (completeToricEnergy
          ((ϕ t y : weightedUnitSphere n k) :
            RealVeroneseSpace n k))).scomp t hW
    simpa [w, g, Function.comp_def, penaltyLieDerivative,
      smul_eq_mul, mul_comm] using hcap
  rw [HGAS.Dynamics.orbitIntegral]
  have hgcont :
      Continuous (fun t : ℝ ↦ g (ϕ t y)) :=
    HGAS.Dynamics.continuous_orbitObservable ϕ g y
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := (1 : ℝ))
      (f := fun t ↦ w (ϕ t y))
      (f' := fun t ↦ g (ϕ t y))
      (fun t _ ↦ hderiv t)
      (hgcont.intervalIntegrable 0 1)
  simpa [ϕ, g, w] using hFTC

/-- Every invariant probability has zero average capped generator. -/
theorem stabilizedPenaltyGenerator_average_eq_zero
    (b : CubicLiftStabilizationBounds F k)
    (μ : HGAS.Dynamics.InvariantProbabilityMeasure
      (stabilizedCubicAngularFlow b)) :
    HGAS.Dynamics.observableAverage
      (stabilizedPenaltyGeneratorBCF b) μ.measure = 0 := by
  letI : CompactSpace (weightedUnitSphere n k) :=
    isCompact_iff_compactSpace.mp isCompact_weightedUnitSphere
  exact
    HGAS.Dynamics.observableAverage_eq_zero_of_orbitIntegral_eq_coboundary
      (stabilizedCubicAngularFlow b)
      (stabilizedPenaltyGeneratorBCF b)
      (stabilizedPenaltyCapBCF b)
      (stabilizedPenaltyCap_orbit_coboundary b)
      μ

/-- The punctured stabilization tube on the weighted unit sphere. -/
def puncturedStabilizationTube
    (b : CubicLiftStabilizationBounds F k) :
    Set (weightedUnitSphere n k) :=
  {y | 0 < completeToricEnergy y.1 ∧
    completeToricEnergy y.1 < b.η}

/-- Every invariant probability gives the punctured tube measure zero. -/
theorem invariantMeasure_puncturedStabilizationTube_eq_zero
    (b : CubicLiftStabilizationBounds F k)
    (μ : HGAS.Dynamics.InvariantProbabilityMeasure
      (stabilizedCubicAngularFlow b)) :
    (μ.measure : Measure (weightedUnitSphere n k))
        (puncturedStabilizationTube b) = 0 := by
  letI : CompactSpace (weightedUnitSphere n k) :=
    isCompact_iff_compactSpace.mp isCompact_weightedUnitSphere
  let g := stabilizedPenaltyGeneratorBCF b
  have havg :
      ∫ x, g x ∂(μ.measure : Measure (weightedUnitSphere n k)) = 0 := by
    simpa [HGAS.Dynamics.observableAverage, g] using
      stabilizedPenaltyGenerator_average_eq_zero b μ
  have hnegint :
      (∫ x, -g x
          ∂(μ.measure : Measure (weightedUnitSphere n k))) = 0 := by
    rw [integral_neg, havg, neg_zero]
  have hnonneg : ∀ x, 0 ≤ -g x := by
    intro x
    exact neg_nonneg.mpr (stabilizedPenaltyGenerator_nonpos b x)
  have hnegIntegrable :
      Integrable (fun x ↦ -g x)
        (μ.measure : Measure (weightedUnitSphere n k)) :=
    (g.integrable _).neg
  have hae :
      (fun x ↦ -g x) =ᵐ[
        (μ.measure : Measure (weightedUnitSphere n k))] 0 :=
    (integral_eq_zero_iff_of_nonneg hnonneg hnegIntegrable).mp
      hnegint
  have hsupport :
      (μ.measure : Measure (weightedUnitSphere n k))
          (Function.support fun x ↦ -g x) = 0 := by
    have hnull := MeasureTheory.ae_iff.mp hae
    simpa [Function.support] using hnull
  apply measure_mono_null (t := Function.support fun x ↦ -g x)
  · intro y hy
    change -g y ≠ 0
    have hstrict :
        g y < 0 := by
      exact stabilizedPenaltyGenerator_neg b y hy.1 hy.2
    exact neg_ne_zero.mpr hstrict.ne
  · exact hsupport

/-! ## The final support sandwich -/

/-- The zero-penalty Veronese core on the weighted unit sphere. -/
def stabilizedConeCore
    (n k : ℕ) :
    Set (weightedUnitSphere n k) :=
  {y | completeToricEnergy y.1 = 0}

/-- The region on or outside the stabilization-tube boundary. -/
def stabilizedOutsideTube
    (b : CubicLiftStabilizationBounds F k) :
    Set (weightedUnitSphere n k) :=
  {y | b.η ≤ completeToricEnergy y.1}

/-- Every invariant probability is concentrated on the union of the
zero-penalty core and the outside-tube region. -/
theorem invariantMeasure_compl_core_union_outside_eq_zero
    (b : CubicLiftStabilizationBounds F k)
    (μ : HGAS.Dynamics.InvariantProbabilityMeasure
      (stabilizedCubicAngularFlow b)) :
    (μ.measure : Measure (weightedUnitSphere n k))
        ((stabilizedConeCore n k ∪
          stabilizedOutsideTube b)ᶜ) = 0 := by
  apply measure_mono_null
    (t := puncturedStabilizationTube b)
  · intro y hy
    have hnotcore :
        completeToricEnergy y.1 ≠ 0 := by
      intro hzero
      exact hy (show
        y ∈ stabilizedConeCore n k ∪
          stabilizedOutsideTube b from Or.inl hzero)
    have hnotoutside :
        ¬ b.η ≤ completeToricEnergy y.1 := by
      intro hout
      exact hy (show
        y ∈ stabilizedConeCore n k ∪
          stabilizedOutsideTube b from Or.inr hout)
    exact
      ⟨lt_of_le_of_ne
          (toricPenalty_nonneg_real y.1) (Ne.symm hnotcore),
        lt_of_not_ge hnotoutside⟩
  · exact invariantMeasure_puncturedStabilizationTube_eq_zero b μ

end

end HGAS.Veronese
