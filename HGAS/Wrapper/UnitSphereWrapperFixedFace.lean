import HGAS.Wrapper.UnitSphereWrapperRewardCertificate
import Mathlib.Tactic

/-!
# A fixed proper-face point of the concrete wrapper flow

The chart pole has unit norm, every source block is absent there, and the
raw wrapper angular field vanishes.  This file transports that pole to the
genuine Euclidean sphere and proves that it is fixed by the actual cutoff
angular flow.  Hence the auxiliary reward value `-1` is attained by an
invariant Dirac probability, as required by the exact maximal-average
identity.
-/

namespace HGAS

open Function Metric Set
open scoped BoundedContinuousFunction RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-- An equilibrium of a compactly supported `C¹` field is fixed by the
chosen global flow.  This reusable lemma follows from global ODE
uniqueness; it does not depend on how the global solution was selected. -/
theorem compactlySupportedContDiffFlow_fixed_of_eq_zero
    (f : E → E) (hf : ContDiff ℝ 1 f)
    (hsupport : HasCompactSupport f)
    (x : E) (hx : f x = 0) :
    ∀ t : ℝ,
      compactlySupportedContDiffFlow f hf hsupport t x = x := by
  let data := boundedLipschitzDataOfCompactSupport f hf hsupport
  let γ₁ : ℝ → E :=
    fun t ↦ compactlySupportedContDiffFlow f hf hsupport t x
  let γ₂ : ℝ → E := fun _ ↦ x
  have hγ₁ : IsIntegralCurve γ₁ (fun _ ↦ f) := by
    simpa only [γ₁] using
      compactlySupportedContDiffFlow_isIntegralCurve
        f hf hsupport x
  have hγ₂ : IsIntegralCurve γ₂ (fun _ ↦ f) := by
    exact isIntegralCurve_const (fun _ ↦ hx)
  have heq : γ₁ = γ₂ := by
    apply ODE_solution_unique_univ
      (v := fun _ : ℝ ↦ f)
      (s := fun _ ↦ (Set.univ : Set E))
      (K := data.lipschitzConstant) (t₀ := 0)
    · intro _
      exact data.lipschitz.lipschitzOnWith
    · intro t
      exact ⟨hγ₁ t, Set.mem_univ _⟩
    · intro t
      exact ⟨hγ₂ t, Set.mem_univ _⟩
    · simp [γ₁, γ₂]
  intro t
  exact congrFun heq t

/-- If the inner angular field vanishes at a unit vector, that vector is
fixed by the Euclidean cutoff angular flow. -/
theorem euclideanAngularFlow_fixed_of_innerAngularField_eq_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    (F : H → H) (hF : ContDiff ℝ 1 F)
    (x : H) (hx : innerAngularField F x = 0) :
    ∀ t : ℝ, euclideanAngularFlow F hF t x = x := by
  apply compactlySupportedContDiffFlow_fixed_of_eq_zero
  simp [cutoffInnerAngularField, hx]

namespace UnitSpherePolynomialWrapper

variable {n k : ℕ}

/-- The raw chart pole transported to the genuine Euclidean unit sphere. -/
noncomputable def euclideanChartPole :
    EuclideanUnitSphere (EuclideanWrapperSpace n) :=
  ⟨wrapperEuclideanEquiv (chartPole : RawWrapperSpace n), by
    change dist (wrapperEuclideanEquiv
      (chartPole : RawWrapperSpace n)) 0 = 1
    rw [dist_zero_right]
    exact (norm_wrapperEuclideanEquiv_eq_one_iff
      (chartPole : RawWrapperSpace n)).2 normSq_chartPole⟩

@[simp]
theorem euclideanChartPole_raw :
    wrapperEuclideanEquiv.symm
        (euclideanChartPole (n := n)).1 =
      (chartPole : RawWrapperSpace n) := by
  simp [euclideanChartPole]

/-- The Euclidean angular field of the final compiled field vanishes at
the transported chart pole. -/
theorem innerAngularField_euclideanFinalField_chartPole
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j)) :
    innerAngularField
        (euclideanFinalField sourceBlock D P a)
        (euclideanChartPole (n := n)).1 = 0 := by
  let Fraw :=
    PolynomialFieldCode.realize
      (finalFieldCode sourceBlock D P a)
  have hraw :
      angularField Fraw (chartPole : RawWrapperSpace n) = 0 := by
    rw [angularField_finalFieldCode_of_normSq_one
      sourceBlock D P a _ normSq_chartPole]
    exact realize_rawWrapperFieldCode_chartPole sourceBlock D P hP
  have hconj :=
    Veronese.innerAngularField_conjugateField_sourceEuclideanEquiv
      Fraw (chartPole : RawWrapperSpace n)
  simpa only [euclideanFinalField, wrapperEuclideanEquiv,
    euclideanChartPole, Fraw, hraw, map_zero] using hconj

/-- The chart pole belongs to a proper block face as soon as there is at
least one source block. -/
theorem euclideanChartPole_mem_properFace
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (i : Fin k) :
    euclideanChartPole (n := n) ∈
      (radiusCleanupFlowCertificate sourceBlock D P a).properFace := by
  refine ⟨i.succ, ?_⟩
  rw [radiusCleanupFlowCertificate_radii_apply,
    euclideanChartPole_raw,
    scaledBlockRadius_chartPole_succ]

/-- The chart pole is fixed by the actual restricted Euclidean angular
flow. -/
theorem euclideanChartPole_isFlowFixedPoint
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j)) :
    Dynamics.InvariantProbabilityMeasure.IsFlowFixedPoint
      (euclideanUnitAngularFlow
        (euclideanFinalField sourceBlock D P a)
        ((contDiff_euclideanFinalField
          sourceBlock D P a).of_le (by norm_num)))
      (euclideanChartPole (n := n)) := by
  intro t
  apply Subtype.ext
  change
    euclideanAngularFlow
        (euclideanFinalField sourceBlock D P a)
        ((contDiff_euclideanFinalField
          sourceBlock D P a).of_le (by norm_num))
        t (euclideanChartPole (n := n)).1 =
      (euclideanChartPole (n := n)).1
  exact euclideanAngularFlow_fixed_of_innerAngularField_eq_zero
    (euclideanFinalField sourceBlock D P a)
    ((contDiff_euclideanFinalField
      sourceBlock D P a).of_le (by norm_num))
    (euclideanChartPole (n := n)).1
    (innerAngularField_euclideanFinalField_chartPole
      sourceBlock D P a hP) t

/-- Concrete witness for the semantic theorem's attained proper-face
fixed-point hypothesis. -/
theorem exists_properFace_fixedPoint
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j))
    (i : Fin k) :
    ∃ u : EuclideanUnitSphere (EuclideanWrapperSpace n),
      u ∈ (radiusCleanupFlowCertificate
        sourceBlock D P a).properFace ∧
      Dynamics.InvariantProbabilityMeasure.IsFlowFixedPoint
        (euclideanUnitAngularFlow
          (euclideanFinalField sourceBlock D P a)
          ((contDiff_euclideanFinalField
            sourceBlock D P a).of_le (by norm_num))) u :=
  ⟨euclideanChartPole,
    euclideanChartPole_mem_properFace sourceBlock D P a i,
    euclideanChartPole_isFlowFixedPoint sourceBlock D P a hP⟩

end UnitSpherePolynomialWrapper

end

end HGAS
