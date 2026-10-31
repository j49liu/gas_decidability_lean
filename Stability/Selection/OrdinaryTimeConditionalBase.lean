import Stability.Selection.OrdinaryTimeDetectorExtraction
import HGAS.Compiler.CompactAccumulatorPipelineGapCertificate
import HGAS.Dynamics.ErgodicFactor
import HGAS.Dynamics.ErgodicFullMeasureRestriction

/-!
# The conditional compact base and the nonzero-mean obstruction

Conditioning an ergodic source probability on its finite interior and
projecting to the base preserves ergodicity and gives full mass off the
equator. Section 9's extraction theorem therefore applies to this actual
conditional measure. A nonzero accumulator gain does not alter which
drift coordinates have zero mean.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Dynamics HGAS.CompactAccumulatorPipelineCode
open HGAS.CompactAccumulatorPipelineCode.AllAffineCompactSourceChart (layout SourceSpace)
open HGAS.CompactAccumulatorPipelineCode.AllAffineCompactBaseChartTrajectory
open MeasureTheory

variable {n m : ℕ}

section ConditionalMeasure

variable (E M : ℕ) (κ : RationalCode) (P : PolynomialFieldCode n)
  (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j))
  (h : Fin m → PolynomialCode n) (hh : ∀ q, PolynomialCode.TermsDegreeLE E (h q))
  (ε : RationalCode) (htangent : BaseCompactTangency (layout n) M P)
  (μ : InvariantProbabilityMeasure (sourceFlow (layout n) E M κ P h ε))
  (hpos : (μ.measure : Measure (SourceSpace n m))
    (sourceFiniteInteriorSet (m := m) (layout n)) ≠ 0)

/-- Ergodicity of the actual positive-interior conditional base factor. -/
theorem ordinaryConditionalBase_ergodic
    (hμ : IsErgodicInvariantProbability (sourceFlow (layout n) E M κ P h ε) μ.measure) :
    IsErgodicInvariantProbability (baseFlow (layout n) E M P)
      (conditionalBaseProbability (layout n) E M κ P hP h hh ε htangent μ hpos).measure := by
  exact (hμ.restrictToPositiveInvariant μ
    (measurableSet_sourceFiniteInteriorSet (m := m) (layout n)) hpos
    (canonicalFiniteInteriorInvariant (layout n) E M κ P hP h hh ε htangent)).mapEquivariant
      (restrictedBaseProjection (layout n))
      (continuous_restrictedBaseProjection (layout n))
      (canonicalRestrictedBaseProjection_semiconj (layout n) E M κ P hP h hh ε htangent)

/-- Every point of the conditional source projects into the finite base
chart; consequently the factor probability gives that chart full mass. -/
theorem ordinaryConditionalBase_finiteInterior_full :
    ((conditionalBaseProbability (layout n) E M κ P hP h hh ε htangent μ hpos).measure :
      Measure (BaseSpace (layout n))) finiteInterior = 1 := by
  let ν := μ.restrictToPositiveInvariant
    (measurableSet_sourceFiniteInteriorSet (m := m) (layout n)) hpos
    (canonicalFiniteInteriorInvariant (layout n) E M κ P hP h hh ε htangent)
  change Measure.map (restrictedBaseProjection (m := m) (layout n))
    (ν.measure : Measure (sourceFiniteInteriorSet (m := m) (layout n))) finiteInterior = 1
  rw [Measure.map_apply (continuous_restrictedBaseProjection (layout n)).measurable
    ordinaryBase_finiteInterior_measurable]
  have hpre : (restrictedBaseProjection (m := m) (layout n)) ⁻¹' finiteInterior = Set.univ := by
    ext v
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    change sourceChartWeight v.1 0 ≠ 0
    exact ((sourceFiniteInteriorSet_iff (layout n) v.1).mp v.2).1 0
  rw [hpre]
  exact measure_univ

end ConditionalMeasure

/-- Removing a nonzero constant gain from a zero compact drift mean. -/
theorem compactBase_mean_zero_of_scaled
    (M : ℕ) (κ : RationalCode) (hκ : (κ.decode : ℝ) ≠ 0)
    (h : Fin m → PolynomialCode n) (ν : Measure (BaseSpace (layout n))) (q : Fin m)
    (hzero : (∫ b, baseDriftBCF (layout n) M κ h b q ∂ν) = 0) :
    (∫ b, baseDriftBCF (layout n) M RationalCode.one h b q ∂ν) = 0 := by
  have hscale (b : BaseSpace (layout n)) :
      baseDriftBCF (layout n) M κ h b q =
        (κ.decode : ℝ) * baseDriftBCF (layout n) M RationalCode.one h b q := by
    simp only [baseDriftBCF_apply, slowedDriftCode, PolynomialCode.decode_mul_code,
      PolynomialCode.decode_constant, map_mul, MvPolynomial.eval₂Hom_C,
      RationalCode.decode_one, map_one, one_mul]
    rfl
  simp_rw [hscale] at hzero
  rw [integral_const_mul] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left hκ

end Stability.Selection
