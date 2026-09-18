import HGAS.Veronese.MorseBottCoercivity
import Mathlib.Tactic

/-!
# Uniform bounds and a rational gain for the stabilized cubic lift

The preceding modules establish the two difficult estimates separately:

* `MorseBottCoercivity` supplies `c W ≤ D` in a small tube;
* `CubicLiftToricFactorization` supplies `|Y_G W| ≤ C W` for the
  angular cubic lift.

This module packages those estimates with the compact radial-reward
bound and chooses one rational stabilization gain `K` satisfying both
strict inequalities required in the paper.  The resulting structure is
reusable: downstream dynamical arguments no longer need to repeat the
compactness or Archimedean choices.
-/

namespace HGAS.Veronese

noncomputable section

variable {n k : ℕ}

/-- The real semantic vector field obtained by evaluating the canonical
rational cubic lift. -/
def evaluatedCubicLift
    (F : HGAS.PolynomialField n) :
    RealVeroneseSpace n k → RealVeroneseSpace n k :=
  fun y ↦ evalCoordinateField (cubicLiftField (k := k) F) y

theorem continuous_evaluatedCubicLift
    (F : HGAS.PolynomialField n) :
    Continuous (evaluatedCubicLift (k := k) F) := by
  exact continuous_evalCoordinateField_real
    (cubicLiftField (k := k) F)

/-- All quantitative data needed by transverse stabilization.

The gain is rational because the stabilized polynomial field must retain
rational coefficients.  The estimates themselves are stated for its
real coercion, which is the value used by the analytic dynamics. -/
structure CubicLiftStabilizationBounds
    (F : HGAS.PolynomialField n) (k : ℕ) where
  c : ℝ
  η : ℝ
  C : ℝ
  A : ℝ
  K : ℚ
  c_pos : 0 < c
  η_pos : 0 < η
  C_nonneg : 0 ≤ C
  A_nonneg : 0 ≤ A
  K_pos : 0 < K
  morseBott :
    ∀ y : RealVeroneseSpace n k,
      Q y = 1 →
        completeToricEnergy y ≤ η →
          c * completeToricEnergy y ≤ penaltyDissipation y
  angularTangency :
    ∀ y : RealVeroneseSpace n k,
      Q y = 1 →
        |penaltyLieDerivative
            (weightedAngularField (evaluatedCubicLift (k := k) F)) y| ≤
          C * completeToricEnergy y
  radialBound :
    ∀ y : RealVeroneseSpace n k,
      Q y = 1 →
        |weightedRadialReward (evaluatedCubicLift (k := k) F) y| ≤ A
  angularGain : C < (K : ℝ) * c
  radialGain : A + 1 ≤ 4 * (K : ℝ) * η

/-- A rational gain satisfying both stabilization inequalities exists.

Choose the Morse--Bott, tangency, and radial constants first.  A natural
number larger than both real thresholds `C/c` and `(A+1)/(4η)` is then
a valid rational gain. -/
theorem exists_cubicLiftStabilizationBounds
    (F : HGAS.PolynomialField n)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k) :
    Nonempty (CubicLiftStabilizationBounds F k) := by
  obtain ⟨c, η, hc, hη, hMorseBott⟩ :=
    exists_positive_morseBott_coercivity_constants
      (n := n) hk
  obtain ⟨C, hC, hTangency⟩ :=
    exists_cubicLift_angularPenaltyLieDerivative_linear_bound
      F hF hk
  obtain ⟨A, hA, hRadial⟩ :=
    exists_radialReward_bound_on_weightedUnitSphere
      (continuous_evaluatedCubicLift (k := k) F)
  let threshold : ℝ :=
    max 0 (max (C / c) ((A + 1) / (4 * η)))
  obtain ⟨N, hN⟩ := exists_nat_gt threshold
  have hN0 : (0 : ℝ) < N :=
    lt_of_le_of_lt (le_max_left _ _) hN
  have hNC : C / c < (N : ℝ) :=
    lt_of_le_of_lt
      (le_trans (le_max_left _ _)
        (le_max_right 0
          (max (C / c) ((A + 1) / (4 * η)))))
      hN
  have hNA : (A + 1) / (4 * η) < (N : ℝ) :=
    lt_of_le_of_lt
      (le_trans (le_max_right _ _)
        (le_max_right 0
          (max (C / c) ((A + 1) / (4 * η)))))
      hN
  have hAngularGain : C < (N : ℝ) * c := by
    exact (div_lt_iff₀ hc).mp hNC
  have hfourEta : 0 < 4 * η := mul_pos (by norm_num) hη
  have hRadialGain : A + 1 ≤ 4 * (N : ℝ) * η := by
    have hstrict : A + 1 < (N : ℝ) * (4 * η) :=
      (div_lt_iff₀ hfourEta).mp hNA
    nlinarith
  let K : ℚ := N
  have hKpos : 0 < K := by
    dsimp only [K]
    exact_mod_cast hN0
  refine ⟨{
    c := c
    η := η
    C := C
    A := A
    K := K
    c_pos := hc
    η_pos := hη
    C_nonneg := hC
    A_nonneg := hA
    K_pos := hKpos
    morseBott := hMorseBott
    angularTangency := hTangency
    radialBound := hRadial
    angularGain := ?_
    radialGain := ?_
  }⟩
  · simpa only [K, Rat.cast_natCast] using hAngularGain
  · simpa only [K, Rat.cast_natCast] using hRadialGain

namespace CubicLiftStabilizationBounds

variable {F : HGAS.PolynomialField n}

/-- Inside the coercivity tube, the stabilized angular field decreases
the penalty at a uniform linear rate. -/
theorem angularPenaltyLieDerivative_le
    (b : CubicLiftStabilizationBounds F k)
    (y : RealVeroneseSpace n k)
    (hQ : Q y = 1) (hTube : completeToricEnergy y ≤ b.η) :
    penaltyLieDerivative
        (weightedAngularField
          (transverseStabilizedField
            (evaluatedCubicLift (k := k) F) (b.K : ℝ))) y ≤
      -((b.K : ℝ) * b.c - b.C) * completeToricEnergy y := by
  exact penaltyLieDerivative_stabilizedAngular_le
    (evaluatedCubicLift (k := k) F)
    (b.K : ℝ) b.c b.C y hQ
    (le_of_lt (Rat.cast_pos.mpr b.K_pos))
    (b.morseBott y hQ hTube)
    (b.angularTangency y hQ)

/-- At every positive-penalty point in the tube, the angular penalty
derivative is strictly negative. -/
theorem angularPenaltyLieDerivative_lt_zero
    (b : CubicLiftStabilizationBounds F k)
    (y : RealVeroneseSpace n k)
    (hQ : Q y = 1) (hTube : completeToricEnergy y ≤ b.η)
    (hW : 0 < completeToricEnergy y) :
    penaltyLieDerivative
        (weightedAngularField
          (transverseStabilizedField
            (evaluatedCubicLift (k := k) F) (b.K : ℝ))) y < 0 := by
  exact penaltyLieDerivative_stabilizedAngular_lt_zero
    (evaluatedCubicLift (k := k) F)
    (b.K : ℝ) b.c b.C y hQ
    (le_of_lt (Rat.cast_pos.mpr b.K_pos))
    b.angularGain hW
    (b.morseBott y hQ hTube)
    (b.angularTangency y hQ)

/-- Outside the tube, stabilization makes the radial reward at most
`-1`. -/
theorem radialReward_le_neg_one
    (b : CubicLiftStabilizationBounds F k)
    (y : RealVeroneseSpace n k)
    (hQ : Q y = 1) (hOutside : b.η ≤ completeToricEnergy y) :
    weightedRadialReward
        (transverseStabilizedField
          (evaluatedCubicLift (k := k) F) (b.K : ℝ)) y ≤ -1 := by
  exact weightedRadialReward_transverse_le_neg_one
    (evaluatedCubicLift (k := k) F)
    (b.K : ℝ) b.A b.η y
    (le_of_lt (Rat.cast_pos.mpr b.K_pos))
    hOutside (b.radialBound y hQ) b.radialGain

/-- The semantic stabilized field is exactly evaluation of the rational
polynomial `stabilizedCubicField`. -/
theorem eval_stabilized_eq
    (b : CubicLiftStabilizationBounds F k)
    (y : RealVeroneseSpace n k) :
    evalCoordinateField
        (stabilizedCubicField (k := k) F b.K) y =
      transverseStabilizedField
        (evaluatedCubicLift (k := k) F) (b.K : ℝ) y := by
  exact eval_stabilizedCubicField_real_eq_transverse F b.K y

/-- Polynomial-evaluation form of the uniform angular decay estimate. -/
theorem evaluatedStabilized_angularPenaltyLieDerivative_le
    (b : CubicLiftStabilizationBounds F k)
    (y : RealVeroneseSpace n k)
    (hQ : Q y = 1) (hTube : completeToricEnergy y ≤ b.η) :
    penaltyLieDerivative
        (weightedAngularField
          (fun z ↦ evalCoordinateField
            (stabilizedCubicField (k := k) F b.K) z)) y ≤
      -((b.K : ℝ) * b.c - b.C) * completeToricEnergy y := by
  have hfield :
      (fun z : RealVeroneseSpace n k ↦
        evalCoordinateField
          (stabilizedCubicField (k := k) F b.K) z) =
        transverseStabilizedField
          (evaluatedCubicLift (k := k) F) (b.K : ℝ) := by
    funext z
    exact b.eval_stabilized_eq z
  rw [hfield]
  exact b.angularPenaltyLieDerivative_le y hQ hTube

/-- Polynomial-evaluation form of the outside-tube radial estimate. -/
theorem evaluatedStabilized_radialReward_le_neg_one
    (b : CubicLiftStabilizationBounds F k)
    (y : RealVeroneseSpace n k)
    (hQ : Q y = 1) (hOutside : b.η ≤ completeToricEnergy y) :
    weightedRadialReward
        (fun z ↦ evalCoordinateField
          (stabilizedCubicField (k := k) F b.K) z) y ≤ -1 := by
  have hfield :
      (fun z : RealVeroneseSpace n k ↦
        evalCoordinateField
          (stabilizedCubicField (k := k) F b.K) z) =
        transverseStabilizedField
          (evaluatedCubicLift (k := k) F) (b.K : ℝ) := by
    funext z
    exact b.eval_stabilized_eq z
  rw [hfield]
  exact b.radialReward_le_neg_one y hQ hOutside

end CubicLiftStabilizationBounds

end

end HGAS.Veronese
