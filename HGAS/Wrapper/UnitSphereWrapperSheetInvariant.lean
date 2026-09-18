import HGAS.Wrapper.UnitSphereWrapperFullStratumChart
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Invariance of the two normalized chart sheets

The raw wrapper has identically zero chart-coordinate velocity on the full
stratum.  Since the full stratum is invariant, the chart coordinate is
constant along each full-stratum orbit.  The positive and negative sheets
are therefore separately invariant; no orbit can cross from one copy of
the source product sphere to the other.
-/

namespace HGAS

open Function Metric Set
open scoped BigOperators BoundedContinuousFunction RealInnerProductSpace

noncomputable section

namespace UnitSpherePolynomialWrapper

variable {n k : ℕ}

/-- The zeroth raw-wrapper velocity vanishes whenever all scaled radii are
one.  No source tangency hypothesis is needed for this coordinate. -/
theorem rawWrapperField_zero_coordinate_of_all_radii_one
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (x : RawWrapperSpace n)
    (hradii : ∀ b, scaledBlockRadius sourceBlock x b = 1) :
    PolynomialFieldCode.realize
        (rawWrapperFieldCode sourceBlock D P) x 0 = 0 := by
  rw [eval_rawWrapperFieldCode, eval_tangentFieldCode]
  simp only [ambientBlock_zero]
  rw [eval_chartFieldCode_zero,
    blockDotValue_chartField_zero,
    radiusDeviation_eq_zero_of_all_one
      (fun b ↦ scaledBlockRadius sourceBlock x b)
      hradii]
  ring

/-- The raw chart coordinate is constant along every orbit starting in the
full stratum. -/
theorem chartCoordinate_euclideanUnitAngularFlow_eq
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (u : EuclideanUnitSphere (EuclideanWrapperSpace n))
    (hu :
      u ∈ (radiusCleanupFlowCertificate
        sourceBlock D P a).fullStratum) :
    ∀ t : ℝ,
      wrapperEuclideanEquiv.symm
          ((euclideanUnitAngularFlow
            (euclideanFinalField sourceBlock D P a)
            ((contDiff_euclideanFinalField
              sourceBlock D P a).of_le (by norm_num)))
            t u).1 0 =
        wrapperEuclideanEquiv.symm u.1 0 := by
  let ϕ :=
    euclideanUnitAngularFlow
      (euclideanFinalField sourceBlock D P a)
      ((contDiff_euclideanFinalField
        sourceBlock D P a).of_le (by norm_num))
  let γ : ℝ → RawWrapperSpace n :=
    fun t ↦ wrapperEuclideanEquiv.symm ((ϕ t u).1)
  let z : ℝ → ℝ := fun t ↦ γ t 0
  have hγ :
      IsIntegralCurve γ
        (fun _ x ↦ PolynomialFieldCode.realize
          (rawWrapperFieldCode sourceBlock D P) x) := by
    simpa only [γ, ϕ] using
      euclideanUnitAngularFlow_raw_isIntegralCurve
        sourceBlock D P a u
  have hz : ∀ t, HasDerivAt z 0 t := by
    intro t
    have hfull :
        ϕ t u ∈ (radiusCleanupFlowCertificate
          sourceBlock D P a).fullStratum :=
      isInvariant_fullStratum sourceBlock D P a t hu
    have hradii :
        ∀ b, scaledBlockRadius sourceBlock (γ t) b = 1 := by
      intro b
      have hb := hfull b
      simpa only [γ, ϕ,
        radiusCleanupFlowCertificate_radii_apply] using hb
    have hcoord := hasDerivAt_pi.mp (hγ t) 0
    apply hcoord.congr_deriv
    exact rawWrapperField_zero_coordinate_of_all_radii_one
      sourceBlock D P (γ t) hradii
  have hdiff : Differentiable ℝ z :=
    fun t ↦ (hz t).differentiableAt
  intro t
  have hconst :=
    isOpen_univ.is_const_of_deriv_eq_zero
      isPreconnected_univ hdiff.differentiableOn
      (fun s _ ↦ (hz s).deriv)
      (x := t) (y := 0) (mem_univ t) (mem_univ 0)
  simpa only [z, γ, ϕ, Flow.map_zero_apply] using hconst

/-- The positive normalized chart sheet is invariant. -/
theorem isInvariant_positiveFullSheet
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    IsInvariant
      (euclideanUnitAngularFlow
        (euclideanFinalField sourceBlock D P a)
        ((contDiff_euclideanFinalField
          sourceBlock D P a).of_le (by norm_num)))
      (positiveFullSheet sourceBlock D P a) := by
  intro t u hu
  refine ⟨isInvariant_fullStratum sourceBlock D P a t hu.1, ?_⟩
  rw [chartCoordinate_euclideanUnitAngularFlow_eq
    sourceBlock D P a u hu.1 t]
  exact hu.2

/-- The negative normalized chart sheet is invariant. -/
theorem isInvariant_negativeFullSheet
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    IsInvariant
      (euclideanUnitAngularFlow
        (euclideanFinalField sourceBlock D P a)
        ((contDiff_euclideanFinalField
          sourceBlock D P a).of_le (by norm_num)))
      (negativeFullSheet sourceBlock D P a) := by
  intro t u hu
  refine ⟨isInvariant_fullStratum sourceBlock D P a t hu.1, ?_⟩
  rw [chartCoordinate_euclideanUnitAngularFlow_eq
    sourceBlock D P a u hu.1 t]
  exact hu.2

end UnitSpherePolynomialWrapper

end

end HGAS
