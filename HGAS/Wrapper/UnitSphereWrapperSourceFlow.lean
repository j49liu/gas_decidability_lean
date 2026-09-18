import HGAS.Dynamics.HomeomorphicFlow
import HGAS.Wrapper.UnitSphereWrapperSourceCompact
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# The source flow carried by each normalized wrapper sheet

The positive and negative full sheets are invariant compact phase spaces.
Restricting the concrete wrapper angular flow to either sheet and pulling
it back through the explicit chart homeomorphism gives two flows on the
same source product of spheres.

This file proves, directly from the pointwise chart calculation, that both
pulled-back trajectories solve the source polynomial ODE.  Ordinary ODE
uniqueness on the compact source product then shows that the two flows are
literally equal.  It also identifies the pulled-back chart reward with the
source polynomial reward.

This construction deliberately does not postulate an abstract source flow:
the positive sheet supplies a canonical one, and the generator theorem
below states exactly which polynomial ODE it solves.
-/

namespace HGAS

open Function MeasureTheory Metric Set
open scoped BigOperators BoundedContinuousFunction

noncomputable section

namespace UnitSpherePolynomialWrapper

variable {n k : ℕ}

/-- The concrete angular flow of the compiled Euclidean wrapper field. -/
noncomputable def wrapperUnitFlow
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    Flow ℝ (EuclideanUnitSphere (EuclideanWrapperSpace n)) :=
  euclideanUnitAngularFlow
    (euclideanFinalField sourceBlock D P a)
    ((contDiff_euclideanFinalField
      sourceBlock D P a).of_le (by norm_num))

/-- The wrapper flow restricted to its positive normalized sheet. -/
noncomputable def positiveSheetFlow
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    Flow ℝ (positiveFullSheet sourceBlock D P a) :=
  (wrapperUnitFlow sourceBlock D P a).restrict
    (isInvariant_positiveFullSheet sourceBlock D P a)

/-- The wrapper flow restricted to its negative normalized sheet. -/
noncomputable def negativeSheetFlow
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    Flow ℝ (negativeFullSheet sourceBlock D P a) :=
  (wrapperUnitFlow sourceBlock D P a).restrict
    (isInvariant_negativeFullSheet sourceBlock D P a)

/-- Canonical source flow obtained from the positive wrapper sheet. -/
noncomputable def positiveSourceFlow
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    Flow ℝ (SourceProductSphere sourceBlock) :=
  Flow.pullbackHomeomorph
    (positiveSheetHomeomorph sourceBlock D P a)
    (positiveSheetFlow sourceBlock D P a)

/-- Source flow obtained from the negative wrapper sheet. -/
noncomputable def negativeSourceFlow
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    Flow ℝ (SourceProductSphere sourceBlock) :=
  Flow.pullbackHomeomorph
    (negativeSheetHomeomorph sourceBlock D P a)
    (negativeSheetFlow sourceBlock D P a)

/-- The source polynomial reward bundled on the compact product sphere. -/
noncomputable def sourceRewardBCF
    (sourceBlock : Fin n → Fin k)
    (a : PolynomialCode n) :
    SourceProductSphere sourceBlock →ᵇ ℝ := by
  have hcontinuous :
      Continuous
        (fun y : SourceProductSphere sourceBlock ↦
          MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) y.1
            (PolynomialCode.decode a)) := by
    have h :=
      (contDiff_ratMvPolynomialEval
        (PolynomialCode.decode a)).continuous
    have hval :
        Continuous
          (fun y : SourceProductSphere sourceBlock ↦ y.1) :=
      continuous_subtype_val
    have hcomp := h.comp hval
    convert hcomp using 1
    funext y
    simp [ratMvPolynomialEval, MvPolynomial.eval_map]
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun y ↦
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) y.1
        (PolynomialCode.decode a),
      hcontinuous⟩

@[simp]
theorem sourceRewardBCF_apply
    (sourceBlock : Fin n → Fin k)
    (a : PolynomialCode n)
    (y : SourceProductSphere sourceBlock) :
    sourceRewardBCF sourceBlock a y =
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) y.1
        (PolynomialCode.decode a) :=
  rfl

/-- On the positive sheet, the chart reward pulls back exactly to the
source polynomial reward. -/
theorem pullback_chartRewardBCF_positive
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (hDodd : D % 2 = 1)
    (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (ha : PolynomialCode.TermsDegreeLE (D - 1) a) :
    Dynamics.pullbackObservable
        (positiveSheetHomeomorph sourceBlock D P a)
        ((chartRewardBCF (k := k) D a).compContinuous
          ⟨Subtype.val, continuous_subtype_val⟩) =
      sourceRewardBCF sourceBlock a := by
  ext y
  simp only [Dynamics.pullbackObservable_apply,
    BoundedContinuousFunction.compContinuous_apply,
    ContinuousMap.coe_mk, chartRewardBCF_apply,
    sourceRewardBCF_apply]
  change
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (wrapperEuclideanEquiv.symm
          (normalizedEuclideanChartPoint sourceBlock
            (positiveChartScalar k)
            positiveChartScalar_sheet y).1)
        (PolynomialCode.decode (chartRewardCode k D a)) =
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) y.1
        (PolynomialCode.decode a)
  rw [normalizedEuclideanChartPoint_raw]
  exact eval_chartRewardCode_on_sheet
    D hDodd a ha
    (positiveChartScalar k) positiveChartScalar_sheet y.1

/-- The same reward identity on the negative sheet. -/
theorem pullback_chartRewardBCF_negative
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (hDodd : D % 2 = 1)
    (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (ha : PolynomialCode.TermsDegreeLE (D - 1) a) :
    Dynamics.pullbackObservable
        (negativeSheetHomeomorph sourceBlock D P a)
        ((chartRewardBCF (k := k) D a).compContinuous
          ⟨Subtype.val, continuous_subtype_val⟩) =
      sourceRewardBCF sourceBlock a := by
  ext y
  simp only [Dynamics.pullbackObservable_apply,
    BoundedContinuousFunction.compContinuous_apply,
    ContinuousMap.coe_mk, chartRewardBCF_apply,
    sourceRewardBCF_apply]
  change
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (wrapperEuclideanEquiv.symm
          (normalizedEuclideanChartPoint sourceBlock
            (negativeChartScalar k)
            negativeChartScalar_sheet y).1)
        (PolynomialCode.decode (chartRewardCode k D a)) =
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) y.1
        (PolynomialCode.decode a)
  rw [normalizedEuclideanChartPoint_raw]
  exact eval_chartRewardCode_on_sheet
    D hDodd a ha
    (negativeChartScalar k) negativeChartScalar_sheet y.1

/-! ## The pulled-back trajectories solve the source polynomial ODE -/

/-- Raw-coordinate chart identity along the positive pulled-back flow. -/
theorem positiveSourceFlow_raw_chart_eq
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (y : SourceProductSphere sourceBlock) (t : ℝ) :
    wrapperEuclideanEquiv.symm
        ((wrapperUnitFlow sourceBlock D P a) t
          (sourceToPositiveSheet sourceBlock D P a y).1).1 =
      normalizedRawChartPoint (positiveChartScalar k)
        ((positiveSourceFlow sourceBlock D P a t y).1) := by
  let e := positiveSheetHomeomorph sourceBlock D P a
  let ψs := positiveSheetFlow sourceBlock D P a
  let η := positiveSourceFlow sourceBlock D P a t y
  have heq :
      e η = ψs t (e y) := by
    simp only [η, positiveSourceFlow,
      Flow.pullbackHomeomorph_apply, e, ψs,
      Homeomorph.apply_symm_apply]
  have hraw :=
    congrArg
      (fun u : positiveFullSheet sourceBlock D P a ↦
        wrapperEuclideanEquiv.symm u.1.1) heq
  change
    wrapperEuclideanEquiv.symm
        ((wrapperUnitFlow sourceBlock D P a) t
          (sourceToPositiveSheet sourceBlock D P a y).1).1 =
      normalizedRawChartPoint (positiveChartScalar k) η.1
  rw [← normalizedEuclideanChartPoint_raw
    sourceBlock (positiveChartScalar k)
      positiveChartScalar_sheet η]
  exact hraw.symm

/-- Raw-coordinate chart identity along the negative pulled-back flow. -/
theorem negativeSourceFlow_raw_chart_eq
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (y : SourceProductSphere sourceBlock) (t : ℝ) :
    wrapperEuclideanEquiv.symm
        ((wrapperUnitFlow sourceBlock D P a) t
          (sourceToNegativeSheet sourceBlock D P a y).1).1 =
      normalizedRawChartPoint (negativeChartScalar k)
        ((negativeSourceFlow sourceBlock D P a t y).1) := by
  let e := negativeSheetHomeomorph sourceBlock D P a
  let ψs := negativeSheetFlow sourceBlock D P a
  let η := negativeSourceFlow sourceBlock D P a t y
  have heq :
      e η = ψs t (e y) := by
    simp only [η, negativeSourceFlow,
      Flow.pullbackHomeomorph_apply, e, ψs,
      Homeomorph.apply_symm_apply]
  have hraw :=
    congrArg
      (fun u : negativeFullSheet sourceBlock D P a ↦
        wrapperEuclideanEquiv.symm u.1.1) heq
  change
    wrapperEuclideanEquiv.symm
        ((wrapperUnitFlow sourceBlock D P a) t
          (sourceToNegativeSheet sourceBlock D P a y).1).1 =
      normalizedRawChartPoint (negativeChartScalar k) η.1
  rw [← normalizedEuclideanChartPoint_raw
    sourceBlock (negativeChartScalar k)
      negativeChartScalar_sheet η]
  exact hraw.symm

/-- Every trajectory of the positive pulled-back flow solves the source
polynomial differential equation in ambient source coordinates. -/
theorem positiveSourceFlow_isIntegralCurve_sourceField
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (hDodd : D % 2 = 1)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j))
    (a : PolynomialCode n)
    (htangent :
      ∀ y : SourceProductSphere sourceBlock,
        SourceTangentAt sourceBlock y.1
          (PolynomialFieldCode.realize P y.1))
    (y : SourceProductSphere sourceBlock) :
    IsIntegralCurve
      (fun t ↦
        (positiveSourceFlow sourceBlock D P a t y).1)
      (fun _ x ↦ PolynomialFieldCode.realize P x) := by
  let η : ℝ → Fin n → ℝ :=
    fun t ↦ (positiveSourceFlow sourceBlock D P a t y).1
  let γ : ℝ → RawWrapperSpace n :=
    fun t ↦ wrapperEuclideanEquiv.symm
      ((wrapperUnitFlow sourceBlock D P a) t
        (sourceToPositiveSheet sourceBlock D P a y).1).1
  have hγ :
      IsIntegralCurve γ
        (fun _ x ↦ PolynomialFieldCode.realize
          (rawWrapperFieldCode sourceBlock D P) x) := by
    simpa only [γ, wrapperUnitFlow] using
      euclideanUnitAngularFlow_raw_isIntegralCurve
        sourceBlock D P a
          (sourceToPositiveSheet sourceBlock D P a y).1
  have hchart :
      ∀ t,
        γ t =
          normalizedRawChartPoint (positiveChartScalar k) (η t) := by
    intro t
    simpa only [γ, η] using
      positiveSourceFlow_raw_chart_eq
        sourceBlock D P a y t
  change
    IsIntegralCurve η
      (fun _ x ↦ PolynomialFieldCode.realize P x)
  intro t
  rw [hasDerivAt_pi]
  intro j
  have hcoord :=
    (hasDerivAt_pi.mp (hγ t)) j.succ
  have hdiv :=
    hcoord.div_const (positiveChartScalar k)
  have hηcoord :
      (fun s ↦ η s j) =
        (fun s ↦ γ s j.succ / positiveChartScalar k) := by
    funext s
    have hs := congrFun (hchart s) j.succ
    change
      η s j = γ s j.succ / positiveChartScalar k
    rw [hs]
    simp [normalizedRawChartPoint,
      positiveChartScalar_ne_zero]
  rw [hηcoord]
  apply hdiv.congr_deriv
  have hfield :=
    realize_rawWrapperFieldCode_on_chart
      sourceBlock D hDodd P hP
      (positiveChartScalar k)
      positiveChartScalar_sheet
      (η t)
      (positiveSourceFlow sourceBlock D P a t y).property
      (htangent
        (positiveSourceFlow sourceBlock D P a t y))
  change
    PolynomialFieldCode.realize
        (rawWrapperFieldCode sourceBlock D P) (γ t) j.succ /
        positiveChartScalar k =
      PolynomialFieldCode.realize P (η t) j
  rw [hchart t, normalizedRawChartPoint, hfield]
  simp [positiveChartScalar_ne_zero]

/-- Every trajectory of the negative pulled-back flow solves the same
source polynomial differential equation, with the same time orientation. -/
theorem negativeSourceFlow_isIntegralCurve_sourceField
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (hDodd : D % 2 = 1)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j))
    (a : PolynomialCode n)
    (htangent :
      ∀ y : SourceProductSphere sourceBlock,
        SourceTangentAt sourceBlock y.1
          (PolynomialFieldCode.realize P y.1))
    (y : SourceProductSphere sourceBlock) :
    IsIntegralCurve
      (fun t ↦
        (negativeSourceFlow sourceBlock D P a t y).1)
      (fun _ x ↦ PolynomialFieldCode.realize P x) := by
  let η : ℝ → Fin n → ℝ :=
    fun t ↦ (negativeSourceFlow sourceBlock D P a t y).1
  let γ : ℝ → RawWrapperSpace n :=
    fun t ↦ wrapperEuclideanEquiv.symm
      ((wrapperUnitFlow sourceBlock D P a) t
        (sourceToNegativeSheet sourceBlock D P a y).1).1
  have hγ :
      IsIntegralCurve γ
        (fun _ x ↦ PolynomialFieldCode.realize
          (rawWrapperFieldCode sourceBlock D P) x) := by
    simpa only [γ, wrapperUnitFlow] using
      euclideanUnitAngularFlow_raw_isIntegralCurve
        sourceBlock D P a
          (sourceToNegativeSheet sourceBlock D P a y).1
  have hchart :
      ∀ t,
        γ t =
          normalizedRawChartPoint (negativeChartScalar k) (η t) := by
    intro t
    simpa only [γ, η] using
      negativeSourceFlow_raw_chart_eq
        sourceBlock D P a y t
  change
    IsIntegralCurve η
      (fun _ x ↦ PolynomialFieldCode.realize P x)
  intro t
  rw [hasDerivAt_pi]
  intro j
  have hcoord :=
    (hasDerivAt_pi.mp (hγ t)) j.succ
  have hdiv :=
    hcoord.div_const (negativeChartScalar k)
  have hηcoord :
      (fun s ↦ η s j) =
        (fun s ↦ γ s j.succ / negativeChartScalar k) := by
    funext s
    have hs := congrFun (hchart s) j.succ
    change
      η s j = γ s j.succ / negativeChartScalar k
    rw [hs]
    simp [normalizedRawChartPoint,
      negativeChartScalar_ne_zero]
  rw [hηcoord]
  apply hdiv.congr_deriv
  have hfield :=
    realize_rawWrapperFieldCode_on_chart
      sourceBlock D hDodd P hP
      (negativeChartScalar k)
      negativeChartScalar_sheet
      (η t)
      (negativeSourceFlow sourceBlock D P a t y).property
      (htangent
        (negativeSourceFlow sourceBlock D P a t y))
  change
    PolynomialFieldCode.realize
        (rawWrapperFieldCode sourceBlock D P) (γ t) j.succ /
        negativeChartScalar k =
      PolynomialFieldCode.realize P (η t) j
  rw [hchart t, normalizedRawChartPoint, hfield]
  simp [negativeChartScalar_ne_zero]

/-- A sparse source polynomial field is smooth in its ambient source
coordinates. -/
theorem contDiff_realize_sourcePolynomialFieldCode
    (P : PolynomialFieldCode n) :
    ContDiff ℝ ⊤ (PolynomialFieldCode.realize P) := by
  rw [contDiff_pi]
  intro i
  have hfun :
      (fun y ↦ PolynomialFieldCode.realize P y i) =
        ratMvPolynomialEval (PolynomialCode.decode (P i)) := by
    funext y
    simp only [PolynomialFieldCode.realize_apply]
    simp [ratMvPolynomialEval, MvPolynomial.eval_map]
  rw [hfun]
  exact contDiff_ratMvPolynomialEval _

/-- The positive and negative sheets carry exactly the same source flow.

Both pulled-back curves solve the same smooth polynomial ODE, start at the
same point, and stay in the closed unit ball because every source-product
point has norm at most one. -/
theorem positiveSourceFlow_eq_negativeSourceFlow
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (hDodd : D % 2 = 1)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j))
    (a : PolynomialCode n)
    (htangent :
      ∀ y : SourceProductSphere sourceBlock,
        SourceTangentAt sourceBlock y.1
          (PolynomialFieldCode.realize P y.1)) :
    positiveSourceFlow sourceBlock D P a =
      negativeSourceFlow sourceBlock D P a := by
  apply Flow.ext
  intro t y
  apply Subtype.ext
  let gammaPos : ℝ → Fin n → ℝ :=
    fun s ↦ (positiveSourceFlow sourceBlock D P a s y).1
  let gammaNeg : ℝ → Fin n → ℝ :=
    fun s ↦ (negativeSourceFlow sourceBlock D P a s y).1
  have hgammaPos :
      IsIntegralCurve gammaPos
        (fun _ x ↦ PolynomialFieldCode.realize P x) := by
    simpa only [gammaPos] using
      positiveSourceFlow_isIntegralCurve_sourceField
        sourceBlock D hDodd P hP a htangent y
  have hgammaNeg :
      IsIntegralCurve gammaNeg
        (fun _ x ↦ PolynomialFieldCode.realize P x) := by
    simpa only [gammaNeg] using
      negativeSourceFlow_isIntegralCurve_sourceField
        sourceBlock D hDodd P hP a htangent y
  have hC1 :
      ContDiff ℝ 1 (PolynomialFieldCode.realize P) :=
    (contDiff_realize_sourcePolynomialFieldCode P).of_le
      (by norm_num)
  obtain ⟨K, hK⟩ :=
    hC1.contDiffOn.exists_lipschitzOnWith
      one_ne_zero
      (convex_closedBall (0 : Fin n → ℝ) 1)
      (isCompact_closedBall (0 : Fin n → ℝ) 1)
  have hgammaPosMem :
      ∀ s,
        gammaPos s ∈ closedBall (0 : Fin n → ℝ) 1 := by
    intro s
    have hnorm :=
      source_norm_le_one_of_onSourceProductSpheres
        sourceBlock (gammaPos s)
        (positiveSourceFlow sourceBlock D P a s y).property
    simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hgammaNegMem :
      ∀ s,
        gammaNeg s ∈ closedBall (0 : Fin n → ℝ) 1 := by
    intro s
    have hnorm :=
      source_norm_le_one_of_onSourceProductSpheres
        sourceBlock (gammaNeg s)
        (negativeSourceFlow sourceBlock D P a s y).property
    simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm
  have heq : gammaPos = gammaNeg := by
    apply ODE_solution_unique_univ
      (v := fun _ : ℝ ↦ PolynomialFieldCode.realize P)
      (s := fun _ ↦ closedBall (0 : Fin n → ℝ) 1)
      (K := K) (t₀ := 0)
    · intro _
      exact hK
    · intro s
      exact ⟨hgammaPos s, hgammaPosMem s⟩
    · intro s
      exact ⟨hgammaNeg s, hgammaNegMem s⟩
    · simp [gammaPos, gammaNeg, Flow.map_zero_apply]
  exact congrFun heq t

/-- Uniqueness interface for independently constructed source flows.

Any two flows on the source product sphere whose ambient-coordinate
trajectories solve the same sparse polynomial ODE are equal.  This is the
bridge used by upstream reductions that construct the source flow by a
different compactification or clock mechanism. -/
theorem sourceFlows_eq_of_isIntegralCurve
    (sourceBlock : Fin n → Fin k)
    (P : PolynomialFieldCode n)
    (ψ₁ ψ₂ : Flow ℝ (SourceProductSphere sourceBlock))
    (hψ₁ :
      ∀ y,
        IsIntegralCurve
          (fun t ↦ (ψ₁ t y).1)
          (fun _ x ↦ PolynomialFieldCode.realize P x))
    (hψ₂ :
      ∀ y,
        IsIntegralCurve
          (fun t ↦ (ψ₂ t y).1)
          (fun _ x ↦ PolynomialFieldCode.realize P x)) :
    ψ₁ = ψ₂ := by
  apply Flow.ext
  intro t y
  apply Subtype.ext
  let gammaOne : ℝ → Fin n → ℝ :=
    fun s ↦ (ψ₁ s y).1
  let gammaTwo : ℝ → Fin n → ℝ :=
    fun s ↦ (ψ₂ s y).1
  have hgammaOne :
      IsIntegralCurve gammaOne
        (fun _ x ↦ PolynomialFieldCode.realize P x) := by
    simpa only [gammaOne] using hψ₁ y
  have hgammaTwo :
      IsIntegralCurve gammaTwo
        (fun _ x ↦ PolynomialFieldCode.realize P x) := by
    simpa only [gammaTwo] using hψ₂ y
  have hC1 :
      ContDiff ℝ 1 (PolynomialFieldCode.realize P) :=
    (contDiff_realize_sourcePolynomialFieldCode P).of_le
      (by norm_num)
  obtain ⟨K, hK⟩ :=
    hC1.contDiffOn.exists_lipschitzOnWith
      one_ne_zero
      (convex_closedBall (0 : Fin n → ℝ) 1)
      (isCompact_closedBall (0 : Fin n → ℝ) 1)
  have hOneMem :
      ∀ s,
        gammaOne s ∈ closedBall (0 : Fin n → ℝ) 1 := by
    intro s
    have hnorm :=
      source_norm_le_one_of_onSourceProductSpheres
        sourceBlock (gammaOne s) (ψ₁ s y).property
    simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hTwoMem :
      ∀ s,
        gammaTwo s ∈ closedBall (0 : Fin n → ℝ) 1 := by
    intro s
    have hnorm :=
      source_norm_le_one_of_onSourceProductSpheres
        sourceBlock (gammaTwo s) (ψ₂ s y).property
    simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm
  have heq : gammaOne = gammaTwo := by
    apply ODE_solution_unique_univ
      (v := fun _ : ℝ ↦ PolynomialFieldCode.realize P)
      (s := fun _ ↦ closedBall (0 : Fin n → ℝ) 1)
      (K := K) (t₀ := 0)
    · intro _
      exact hK
    · intro s
      exact ⟨hgammaOne s, hOneMem s⟩
    · intro s
      exact ⟨hgammaTwo s, hTwoMem s⟩
    · simp [gammaOne, gammaTwo, Flow.map_zero_apply]
  exact congrFun heq t

/-- An externally supplied source flow solving the polynomial ODE equals
the canonical flow pulled back from the positive wrapper sheet. -/
theorem sourceFlow_eq_positiveSourceFlow
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (hDodd : D % 2 = 1)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j))
    (a : PolynomialCode n)
    (htangent :
      ∀ y : SourceProductSphere sourceBlock,
        SourceTangentAt sourceBlock y.1
          (PolynomialFieldCode.realize P y.1))
    (ψ : Flow ℝ (SourceProductSphere sourceBlock))
    (hψ :
      ∀ y,
        IsIntegralCurve
          (fun t ↦ (ψ t y).1)
          (fun _ x ↦ PolynomialFieldCode.realize P x)) :
    ψ = positiveSourceFlow sourceBlock D P a :=
  sourceFlows_eq_of_isIntegralCurve sourceBlock P
    ψ (positiveSourceFlow sourceBlock D P a)
    hψ
    (positiveSourceFlow_isIntegralCurve_sourceField
      sourceBlock D hDodd P hP a htangent)

end UnitSpherePolynomialWrapper

end

end HGAS
