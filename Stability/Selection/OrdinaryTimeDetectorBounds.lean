import Stability.Selection.OrdinaryTimeDetectorZeroMode

/-!
# Uniform bounds for fixed matrices and arbitrary RHS

Section 9, Lemma `bounds`: the same explicit rational `M₀,K₀`, radius,
and semantic drift degree work for every RHS. The primitive bound is in
the Euclidean norm, and the derivative retains the actual constant mode.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Analysis HGAS.Clocks

variable {eqs vars : ℕ}

/-- All constants before the stated RHS factor depend only on the fixed
matrices and chosen primes. -/
theorem detectorGraph_constants_replace_rhs (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) (rhs : Fin eqs → ℤ) :
    sourceRadiusIndex { I with rhs := rhs } = sourceRadiusIndex I ∧
    detectorDriftDegree { I with rhs := rhs } = detectorDriftDegree I ∧
    detectorPrimitiveBudget { I with rhs := rhs } p
      (sourceRadiusIndex { I with rhs := rhs }) =
      detectorPrimitiveBudget I p (sourceRadiusIndex I) := ⟨rfl, rfl, rfl⟩

/-- The complete resource statement, uniformly in the arithmetic RHS.
It does not require knowing whether that RHS is solvable. -/
theorem detectorGraph_bounds_fixed_matrices
    (I : DQLSystem eqs vars) (p : Fin (vars + eqs) → ℕ)
    (hp : ∀ i, (p i).Prime) (hinjective : Function.Injective p) :
    let M₀ : ℚ := sourceGraphSizeBudget eqs vars
    let K₀ : ℚ := detectorPrimitiveBudget I p (sourceRadiusIndex I)
    let ρ : ℝ := 1 + 1 / (sourceRadiusIndex I : ℝ)
    let D := detectorDriftDegree I
    let controller := fun i ↦ ExplicitPositiveControllerEquilibrium.state (p i : ℝ)
    let ω := ScaledRadicalClock.scaledSignedPrimeSqrtFrequency
      (1 / (2 * Real.pi)) p (fun _ ↦ 1)
    1 ≤ M₀ ∧ 0 < K₀ ∧ 1 < ρ ∧
    ∀ rhs : Fin eqs → ℤ,
      let J : DQLSystem eqs vars := { I with rhs := rhs }
      let K : ℝ := (K₀ : ℝ) * ρ ^ (4 * (D : ℝ) * ∑ row, |(rhs row : ℝ)|)
      Continuous (intendedSourceGraph J controller) ∧
      Continuous (detectorSourcePrimitive J p) ∧
      (∀ x, normSq (intendedSourceGraph J controller x) ≤ (M₀ : ℝ) ∧
        Real.sqrt (normSq (detectorSourcePrimitive J p x)) ≤ K) ∧
      ∀ x t q,
        HasDerivAt (fun s ↦ detectorSourcePrimitive J p
          (RadicalClock.torusTranslationFlow ω s x) q)
          (NormalizedCorrectedFixedDetectorDriftCode.driftValue J
            (intendedSourceStateGraph J controller (RadicalClock.torusTranslationFlow ω t x)) q -
            (UnitAddTorus.mFourierCoeff (fun y ↦
              (NormalizedCorrectedFixedDetectorDriftCode.driftValue J
                (intendedSourceStateGraph J controller y) q : ℂ)) 0).re) t := by
  dsimp only
  refine ⟨?_, detectorPrimitiveBudget_pos _ _ _, ?_, ?_⟩
  · exact_mod_cast Nat.succ_le_iff.mpr (sourceGraphSizeBudget_pos eqs vars)
  · have hm : (0 : ℝ) < sourceRadiusIndex I := by exact_mod_cast sourceRadiusIndex_pos I
    linarith [one_div_pos.mpr hm]
  · intro rhs
    let J : DQLSystem eqs vars := { I with rhs := rhs }
    have hresources := detectorSourcePrimitive_resources J p hp hinjective
      (sourceRadiusIndex J) (sourceRadiusIndex_pos J)
      (sourceRadiusIndex_bounds J).1 (sourceRadiusIndex_bounds J).2
    refine ⟨continuous_intendedSourceGraph _ _, hresources.1, ?_, hresources.2.2⟩
    intro x
    constructor
    · simpa only [Rat.cast_natCast] using
        positiveControllerSourceGraph_normSq_le J (fun i ↦ (p i : ℝ)) x
    · have hK₀ : 0 ≤ (detectorPrimitiveBudget I p (sourceRadiusIndex I) : ℝ) := by
        exact_mod_cast (detectorPrimitiveBudget_pos I p (sourceRadiusIndex I)).le
      apply (Real.sqrt_le_left (mul_nonneg hK₀ (Real.rpow_nonneg (by positivity) _))).2
      exact hresources.2.1 x

/-- The same resource statement supplies an actual skew-product solution
when arithmetic forces the constant mode to vanish. -/
theorem detectorGraph_skew_solution
    (I : DQLSystem eqs vars) (hnot : ¬ I.Solvable)
    (p : Fin (vars + eqs) → ℕ) (hp : ∀ i, (p i).Prime)
    (hinjective : Function.Injective p) (x : UnitAddTorus (Fin (vars + eqs))) :
    let ω := ScaledRadicalClock.scaledSignedPrimeSqrtFrequency
      (1 / (2 * Real.pi)) p (fun _ ↦ 1)
    let controller := fun i ↦ ExplicitPositiveControllerEquilibrium.state (p i : ℝ)
    IsIntegralCurve (fun t ↦ intendedSourceGraph I controller
      (RadicalClock.torusTranslationFlow ω t x))
      (fun _ y ↦ PolynomialFieldCode.realize
        (FixedDetectorPolynomialCode.fieldCode
          (ObservedTimeChangedControllerPhaseHaar.primeClockCodes p) I) y) ∧
    ∀ t q,
      HasDerivAt (fun s ↦ (detectorGraphGain I p : ℝ) *
        detectorSourcePrimitive I p (RadicalClock.torusTranslationFlow ω s x) q)
        ((detectorGraphGain I p : ℝ) *
          NormalizedCorrectedFixedDetectorDriftCode.driftValue I
            (intendedSourceStateGraph I controller
              (RadicalClock.torusTranslationFlow ω t x)) q) t :=
  ⟨positivePrimeSourceGraph_isIntegralCurve I p hp x,
    fun t q ↦ (detectorSourcePrimitive_hasDerivAt_of_not_solvable
      I hnot p hp hinjective x t q).const_mul _⟩

end Stability.Selection
