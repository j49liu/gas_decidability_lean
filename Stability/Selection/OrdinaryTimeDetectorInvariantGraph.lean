import Stability.Selection.OrdinaryTimePositiveGraph
import Stability.Selection.OrdinaryTimeDetectorZeroMode
import Stability.Selection.OrdinaryTimeDetectorGainCode

/-!
# An invariant graph probability for the printed detector gain

The literal source graph and the actual Haar-coefficient primitive give
a compact invariant graph for the printed computable gain. The resulting
probability has full mass on that graph and reward at least `5w*/4`.
Neither graph invariance nor existence of a suitable measure is assumed.
-/

namespace Stability.Selection

noncomputable section

open HGAS HGAS.Analysis HGAS.Clocks HGAS.CompactAccumulatorPipelineCode
open ObservedTimeChangedControllerPhaseHaar Set

namespace DetectorInvariantGraph

variable {eqs vars : ℕ}

open NormalizedCorrectedFixedDetectorCompactSourceCode

def graph (I : DQLSystem eqs vars) (p : Fin (vars + eqs) → ℕ)
    (x : UnitAddTorus (Fin (vars + eqs))) :
    AllAffineCompactSourceChart.SourceSpace
      (sourceDimension eqs vars) (driftDimension vars) :=
  positiveCompactGraphPoint
    (intendedSourceGraph I (fun i ↦ ExplicitPositiveControllerEquilibrium.state (p i : ℝ)) x)
    ((detectorGraphGain I p : ℝ) • detectorSourcePrimitive I p x)

/-- This is the raw least-admissible-denominator code, not a replacement
gain chosen solely to make the sign theorem hold. -/
def gainCode (I : DQLSystem eqs vars) (p : Fin (vars + eqs) → ℕ) : RationalCode :=
  rhsGraphGainCode I p I.rhs

def marginCode (eqs vars : ℕ) : RationalCode :=
  RationalCode.encode (detectorGraphMargin eqs vars)

theorem decode_gainCode (I : DQLSystem eqs vars) (p : Fin (vars + eqs) → ℕ) :
    (gainCode I p).decode = detectorGraphGain I p := decode_rhsGraphGainCode I p I.rhs

def flow (I : DQLSystem eqs vars) (p : Fin (vars + eqs) → ℕ) :=
  sourceFlow layout (sourceDegreeBound I) (clearingExponent I)
    (gainCode I p) (sourceFieldCode (primeClockCodes p) I)
    (sourceDriftCode I) (marginCode eqs vars)

def reward (eqs vars : ℕ) :=
  UnitSpherePolynomialWrapper.sourceRewardBCF
    (sourceBlock (m := driftDimension vars) (layout (eqs := eqs) (vars := vars)))
    (rewardCode (n := sourceDimension eqs vars) (k := 1)
      (m := driftDimension vars) (marginCode eqs vars))

theorem reward_graph_lower (I : DQLSystem eqs vars) (p : Fin (vars + eqs) → ℕ)
    (hp : ∀ i, (p i).Prime) (hinjective : Function.Injective p)
    (x : UnitAddTorus (Fin (vars + eqs))) :
    5 * (graphWeightBudget (sourceGraphSizeBudget eqs vars) : ℝ) / 4 ≤
      reward eqs vars (graph I p x) := by
  change _ ≤ UnitSpherePolynomialWrapper.sourceRewardBCF _ _
    (positiveCompactGraphPoint _ _)
  rw [positiveCompactGraphPoint_reward]
  simp only [marginCode, RationalCode.decode_encode]
  exact detectorGraph_reward_lower_bound I p hp hinjective x

/-- Every no-instance has an actual invariant probability carried by the
printed compact graph, with the printed strict positive reward margin. -/
theorem exists_probability (I : DQLSystem eqs vars) (hnot : ¬ I.Solvable)
    (p : Fin (vars + eqs) → ℕ) (hp : ∀ i, (p i).Prime)
    (hinjective : Function.Injective p) :
    ∃ μ : HGAS.Dynamics.InvariantProbabilityMeasure (flow I p),
      (μ.measure : MeasureTheory.Measure (UnitSpherePolynomialWrapper.SourceProductSphere
        (sourceBlock (m := driftDimension vars) (layout (eqs := eqs) (vars := vars)))))
          (range (graph I p)) = 1 ∧
        5 * (graphWeightBudget (sourceGraphSizeBudget eqs vars) : ℝ) / 4 ≤
          HGAS.Dynamics.observableAverage (reward eqs vars) μ.measure := by
  let Γ := intendedSourceGraph I
    (fun i ↦ ExplicitPositiveControllerEquilibrium.state (p i : ℝ))
  let B := fun x ↦ (detectorGraphGain I p : ℝ) • detectorSourcePrimitive I p x
  let φ := RadicalClock.torusTranslationFlow
    (ScaledRadicalClock.scaledSignedPrimeSqrtFrequency
      (1 / (2 * Real.pi)) p (fun _ ↦ 1))
  have hBcont : Continuous B := continuous_const.smul
    (detectorSourcePrimitive_resources I p hp hinjective (sourceRadiusIndex I)
      (sourceRadiusIndex_pos I) (sourceRadiusIndex_bounds I).1 (sourceRadiusIndex_bounds I).2).1
  apply exists_invariantProbability_positiveCompactGraph φ Γ B
    (continuous_intendedSourceGraph _ _) hBcont
    (sourceDegreeBound I) (sourceDegreeBound I)
    (gainCode I p) (marginCode eqs vars) (sourceFieldCode (primeClockCodes p) I)
    (sourceDriftCode I)
    (sourceFieldCode_termsDegreeLE _ I) (sourceDriftCode_termsDegreeLE I)
    (sourceFieldCode_termsAffineBlockDegreeLE _ I)
    (sourceDriftCode_termsAffineBlockDegreeLE I)
    (positivePrimeSourceGraph_isIntegralCurve I p hp) ?_
    (reward eqs vars) _ (reward_graph_lower I p hp hinjective)
  intro x q t
  have hd := (detectorSourcePrimitive_hasDerivAt_of_not_solvable
    I hnot p hp hinjective x t q).const_mul (detectorGraphGain I p : ℝ)
  rw [decode_gainCode]
  change HasDerivAt (fun s ↦ (detectorGraphGain I p : ℝ) *
    detectorSourcePrimitive I p (φ s x) q)
    ((detectorGraphGain I p : ℝ) * MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
      (intendedSourceGraph I _ (φ t x))
      (PolynomialCode.decode (NormalizedCorrectedFixedDetectorDriftCode.driftCode I q))) t
  rw [intendedSourceGraph, NormalizedCorrectedFixedDetectorDriftCode.eval_driftCode]
  exact hd

theorem exists_probability_positive_reward (I : DQLSystem eqs vars) (hnot : ¬ I.Solvable)
    (p : Fin (vars + eqs) → ℕ) (hp : ∀ i, (p i).Prime)
    (hinjective : Function.Injective p) :
    ∃ μ : HGAS.Dynamics.InvariantProbabilityMeasure (flow I p),
      0 < HGAS.Dynamics.observableAverage (reward eqs vars) μ.measure := by
  obtain ⟨μ, _, hμ⟩ := exists_probability I hnot p hp hinjective
  refine ⟨μ, lt_of_lt_of_le ?_ hμ⟩
  have hpos : (0 : ℝ) < (graphWeightBudget (sourceGraphSizeBudget eqs vars) : ℝ) := by
    exact_mod_cast graphWeightBudget_pos (sourceGraphSizeBudget eqs vars)
  positivity

end DetectorInvariantGraph

end

end Stability.Selection
