import HGAS.Wrapper.UnitSphereWrapperSemanticGAS
import Mathlib.Tactic

/-!
# Invariance of the full product-sphere stratum

The radius certificate shows that every block radius satisfies the closed
finite-dimensional polynomial system

```
sᵢ' = 2 sᵢ (1 - sᵢ - f̄(s)).
```

The all-ones radius vector is an equilibrium.  This file uses ordinary ODE
uniqueness on the compact radius simplex to prove that an orbit starting
with all radii equal to one keeps them equal to one for all positive and
negative times.  It therefore discharges the full-stratum invariance
hypothesis of the concrete semantic GAS theorem without invoking the chart
dynamics.
-/

namespace HGAS

open Function Metric Set
open scoped BigOperators BoundedContinuousFunction RealInnerProductSpace

noncomputable section

namespace UnitSpherePolynomialWrapper

variable {n k : ℕ}

/-- The autonomous radius-cleanup vector field is `C¹`. -/
theorem contDiff_radiusRhs
    (L : ℝ) :
    ContDiff ℝ 1
      (radiusRhs L :
        (Fin (k + 1) → ℝ) → (Fin (k + 1) → ℝ)) := by
  rw [contDiff_pi]
  intro i
  unfold radiusRhs radiusDeviation radiusAverage
  fun_prop

/-- Every scaled block radius is nonnegative. -/
theorem scaledBlockRadius_nonneg
    (sourceBlock : Fin n → Fin k)
    (x : RawWrapperSpace n) (b : Fin (k + 1)) :
    0 ≤ scaledBlockRadius sourceBlock x b := by
  unfold scaledBlockRadius rawBlockNormSq
  positivity

/-- If nonnegative coordinates sum to `L`, their sup norm is at most
`L`. -/
theorem norm_le_of_nonnegative_sum
    (s : Fin (k + 1) → ℝ)
    (hs : ∀ i, 0 ≤ s i)
    (hsum : ∑ i, s i = (k + 1 : ℝ)) :
    ‖s‖ ≤ (k + 1 : ℝ) := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (hs i)]
  calc
    s i ≤ ∑ j, s j :=
      Finset.single_le_sum
        (fun j _ ↦ hs j) (Finset.mem_univ i)
    _ = (k + 1 : ℝ) := hsum

/-- The constant all-ones vector is an equilibrium of the radius system. -/
theorem radiusRhs_one_eq_zero :
    radiusRhs (k + 1 : ℝ)
      (fun _ : Fin (k + 1) ↦ (1 : ℝ)) = 0 := by
  funext i
  simp [radiusRhs, radiusDeviation, radiusAverage]

/-- Along a concrete wrapper angular orbit, the scaled block-radius vector
is an integral curve of the autonomous radius-cleanup system. -/
theorem wrapperOrbitRadii_isIntegralCurve
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (u : EuclideanUnitSphere (EuclideanWrapperSpace n)) :
    IsIntegralCurve
      (fun t b ↦
        scaledBlockRadius sourceBlock
          (wrapperEuclideanEquiv.symm
            ((euclideanUnitAngularFlow
              (euclideanFinalField sourceBlock D P a)
              ((contDiff_euclideanFinalField
                sourceBlock D P a).of_le (by norm_num)))
              t u).1) b)
      (fun _ ↦ radiusRhs (k + 1 : ℝ)) := by
  let γ : ℝ → RawWrapperSpace n :=
    fun t ↦ wrapperEuclideanEquiv.symm
      ((euclideanUnitAngularFlow
        (euclideanFinalField sourceBlock D P a)
        ((contDiff_euclideanFinalField
          sourceBlock D P a).of_le (by norm_num)))
        t u).1
  have hγ :
      IsIntegralCurve γ
        (fun _ x ↦ PolynomialFieldCode.realize
          (rawWrapperFieldCode sourceBlock D P) x) :=
    euclideanUnitAngularFlow_raw_isIntegralCurve
      sourceBlock D P a u
  intro t
  rw [hasDerivAt_pi]
  intro b
  have hb :=
    hasDerivAt_scaledBlockRadius sourceBlock (hγ t) b
  apply hb.congr_deriv
  exact blockRadiusDirectionalDerivative_rawWrapper
    sourceBlock D P (γ t) b

/-- Every radius vector along the restricted sphere flow is nonnegative,
sums to `k+1`, and lies in the corresponding closed sup-norm ball. -/
theorem wrapperOrbitRadii_mem_closedBall
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (u : EuclideanUnitSphere (EuclideanWrapperSpace n))
    (t : ℝ) :
    let s : Fin (k + 1) → ℝ :=
      fun b ↦ scaledBlockRadius sourceBlock
        (wrapperEuclideanEquiv.symm
          ((euclideanUnitAngularFlow
            (euclideanFinalField sourceBlock D P a)
            ((contDiff_euclideanFinalField
              sourceBlock D P a).of_le (by norm_num)))
            t u).1) b
    s ∈ closedBall (0 : Fin (k + 1) → ℝ) (k + 1 : ℝ) := by
  dsimp only
  let v :=
    wrapperEuclideanEquiv.symm
      ((euclideanUnitAngularFlow
        (euclideanFinalField sourceBlock D P a)
        ((contDiff_euclideanFinalField
          sourceBlock D P a).of_le (by norm_num)))
        t u).1
  have hv : normSq v = 1 :=
    normSq_wrapperEuclideanEquiv_symm_sphere
      ((euclideanUnitAngularFlow
        (euclideanFinalField sourceBlock D P a)
        ((contDiff_euclideanFinalField
          sourceBlock D P a).of_le (by norm_num)))
        t u)
  have hsum :
      ∑ b, scaledBlockRadius sourceBlock v b =
        (k + 1 : ℝ) := by
    rw [sum_scaledBlockRadius, hv, mul_one]
  have hnorm :
      ‖fun b ↦ scaledBlockRadius sourceBlock v b‖ ≤
        (k + 1 : ℝ) :=
    norm_le_of_nonnegative_sum
      (fun b ↦ scaledBlockRadius sourceBlock v b)
      (fun b ↦ scaledBlockRadius_nonneg sourceBlock v b)
      hsum
  simpa [Metric.mem_closedBall, dist_zero_right, v] using hnorm

/-- The all-ones radius vector lies in the same compact ball. -/
theorem oneRadius_mem_closedBall :
    (fun _ : Fin (k + 1) ↦ (1 : ℝ)) ∈
      closedBall (0 : Fin (k + 1) → ℝ) (k + 1 : ℝ) := by
  rw [Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  simp

/-- **Full-stratum invariance.**  Every orbit starting with all scaled
block radii equal to one remains on that stratum for all real times. -/
theorem isInvariant_fullStratum
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    IsInvariant
      (euclideanUnitAngularFlow
        (euclideanFinalField sourceBlock D P a)
        ((contDiff_euclideanFinalField
          sourceBlock D P a).of_le (by norm_num)))
      (radiusCleanupFlowCertificate
        sourceBlock D P a).fullStratum := by
  intro t u hu
  let ϕ :=
    euclideanUnitAngularFlow
      (euclideanFinalField sourceBlock D P a)
      ((contDiff_euclideanFinalField
        sourceBlock D P a).of_le (by norm_num))
  let σ : ℝ → Fin (k + 1) → ℝ :=
    fun s b ↦ scaledBlockRadius sourceBlock
      (wrapperEuclideanEquiv.symm ((ϕ s u).1)) b
  let one : ℝ → Fin (k + 1) → ℝ :=
    fun _ _ ↦ 1
  have hσ :
      IsIntegralCurve σ
        (fun _ ↦ radiusRhs (k + 1 : ℝ)) := by
    simpa only [σ, ϕ] using
      wrapperOrbitRadii_isIntegralCurve
        sourceBlock D P a u
  have hone :
      IsIntegralCurve one
        (fun _ ↦ radiusRhs (k + 1 : ℝ)) := by
    exact isIntegralCurve_const (fun _ ↦ radiusRhs_one_eq_zero)
  have hσzero : σ 0 = one 0 := by
    funext b
    have hb := hu b
    change
      (radiusCleanupFlowCertificate
        sourceBlock D P a).radii b u = 1 at hb
    simpa only [σ, one, ϕ, Flow.map_zero_apply,
      radiusCleanupFlowCertificate_radii_apply] using hb
  have hR :
      ContDiff ℝ 1
        (radiusRhs (k + 1 : ℝ) :
          (Fin (k + 1) → ℝ) → (Fin (k + 1) → ℝ)) :=
    contDiff_radiusRhs (k := k) (k + 1 : ℝ)
  obtain ⟨K, hK⟩ :=
    hR.contDiffOn.exists_lipschitzOnWith
      one_ne_zero
      (convex_closedBall
        (0 : Fin (k + 1) → ℝ) (k + 1 : ℝ))
      (isCompact_closedBall
        (0 : Fin (k + 1) → ℝ) (k + 1 : ℝ))
  have heq : σ = one := by
    apply ODE_solution_unique_univ
      (v := fun _ : ℝ ↦ radiusRhs (k + 1 : ℝ))
      (s := fun _ ↦
        closedBall (0 : Fin (k + 1) → ℝ) (k + 1 : ℝ))
      (K := K) (t₀ := 0)
    · intro _
      exact hK
    · intro s
      exact ⟨hσ s, by
        simpa only [σ, ϕ] using
          wrapperOrbitRadii_mem_closedBall
            sourceBlock D P a u s⟩
    · intro s
      exact ⟨hone s, oneRadius_mem_closedBall (k := k)⟩
    · exact hσzero
  intro b
  change
    (radiusCleanupFlowCertificate
      sourceBlock D P a).radii b (ϕ t u) = 1
  rw [radiusCleanupFlowCertificate_radii_apply]
  exact congrFun (congrFun heq t) b

/-- After proving full-stratum invariance, the only remaining semantic
input is the identification of the full-stratum maximal average with the
source value `β`. -/
theorem realize_finalFieldCode_gas_iff_of_sourceMaximum
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (hD : 3 ≤ D) (hDodd : D % 2 = 1)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j))
    (a : PolynomialCode n)
    (ha : PolynomialCode.TermsDegreeLE (D - 1) a)
    (i : Fin k)
    (β : ℝ)
    (hsource :
      (radiusCleanupFlowCertificate sourceBlock D P a).FullStratumMaximum
        (chartRewardBCF (k := k) D a) β) :
    GloballyAsymptoticallyStable
        (PolynomialFieldCode.realize
          (finalFieldCode sourceBlock D P a)) 0 ↔
      β < 0 :=
  realize_finalFieldCode_gas_iff_of_fullStratumMaximum
    sourceBlock D hD hDodd P hP a ha i β
    (isInvariant_fullStratum sourceBlock D P a)
    hsource

end UnitSpherePolynomialWrapper

end

end HGAS
