import HGAS.Veronese.CubicLiftFlowConjugacy
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic

/-!
# Preliminaries for exponential shadowing of the stabilized cubic lift

This module collects four analytic ingredients used in the exponential
shadowing argument for the stabilized cubic Veronese lift.

* **Lipschitz bounds (P1).**  On the compact convex region `Q ≤ 1`, the
  angular field and the radial reward of any `C¹` field — in particular
  of the unstabilized cubic lift `G` — are Lipschitz for the weighted
  metric.
* **Penalty-gradient bound (P2).**  On `Q = 1`,
  `‖grad_{S_Q} W‖_Q² ≤ C_W² W`.  The proof is the self-improving
  estimate `D = (grad_{S_Q} W) W ≤ C sqrt W sqrt D`.
* **Tube invariance and exponential decay (P3).**  Every stabilized
  angular orbit starting in the tube `W ≤ η` stays there and obeys
  `W(φ_t y) ≤ W(y) exp(-(K c - C) t)` for `t ≥ 0`.
* **Agreement on the cone (P4).**  For a starting point on the
  zero-penalty core, the unstabilized and stabilized angular flows agree
  for all times, and the common orbit stays in the core.
-/

namespace HGAS.Veronese

open Set Function Metric Filter
open scoped Topology NNReal BigOperators

noncomputable section

variable {n k : ℕ} {F : HGAS.PolynomialField n}

/-! ## Elementary comparisons between the weighted and sup norms -/

/-- A single squared coordinate is at most the weighted norm-square. -/
private theorem sq_apply_le_weightedNormSq
    (h : RealVeroneseSpace n k) (a : MultiIndex n k) :
    h a ^ 2 ≤ weightedNormSq h := by
  rw [weightedNormSq_eq_Q]
  have hterm :
      (multinomialWeight a : ℝ) * h a ^ 2 ≤ Q h := by
    unfold Q
    exact Finset.single_le_sum
      (fun b _ ↦
        mul_nonneg (Nat.cast_nonneg _) (sq_nonneg (h b)))
      (Finset.mem_univ a)
  have hweight : (1 : ℝ) ≤ multinomialWeight a := by
    exact_mod_cast multinomialWeight_pos a
  nlinarith [sq_nonneg (h a)]

private theorem abs_apply_le_sqrt_weightedNormSq
    (h : RealVeroneseSpace n k) (a : MultiIndex n k) :
    |h a| ≤ Real.sqrt (weightedNormSq h) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (sq_apply_le_weightedNormSq h a)

/-- The sup norm is dominated by the weighted norm. -/
private theorem norm_le_sqrt_weightedNormSq
    (h : RealVeroneseSpace n k) :
    ‖h‖ ≤ Real.sqrt (weightedNormSq h) := by
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro a
  rw [Real.norm_eq_abs]
  exact abs_apply_le_sqrt_weightedNormSq h a

/-- Total multinomial mass, shifted by one so that it is at least one. -/
private def shadowWeightMass (n k : ℕ) : ℝ :=
  (∑ a : MultiIndex n k, (multinomialWeight a : ℝ)) + 1

private theorem one_le_shadowWeightMass :
    1 ≤ shadowWeightMass n k := by
  unfold shadowWeightMass
  have : 0 ≤ ∑ a : MultiIndex n k, (multinomialWeight a : ℝ) :=
    Finset.sum_nonneg fun a _ ↦ Nat.cast_nonneg _
  linarith

/-- The weighted norm is dominated by the sup norm. -/
private theorem weightedNormSq_le_mass_mul_norm_sq
    (h : RealVeroneseSpace n k) :
    weightedNormSq h ≤ shadowWeightMass n k * ‖h‖ ^ 2 := by
  rw [weightedNormSq_eq_Q]
  unfold Q shadowWeightMass
  have hsum :
      (∑ a : MultiIndex n k, (multinomialWeight a : ℝ) * h a ^ 2) ≤
        ∑ a : MultiIndex n k, (multinomialWeight a : ℝ) * ‖h‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro a _
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have ha := norm_le_pi_norm h a
    rw [Real.norm_eq_abs] at ha
    rw [← sq_abs (h a)]
    exact pow_le_pow_left₀ (abs_nonneg _) ha 2
  rw [← Finset.sum_mul] at hsum
  nlinarith [sq_nonneg ‖h‖]

/-- `Q ≤ 1` forces every coordinate into `[-1, 1]`. -/
private theorem norm_le_one_of_Q_le_one'
    (y : RealVeroneseSpace n k) (hQ : Q y ≤ 1) :
    ‖y‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro a
  rw [Real.norm_eq_abs]
  have hsq := sq_apply_le_weightedNormSq y a
  rw [weightedNormSq_eq_Q] at hsq
  exact (sq_le_one_iff_abs_le_one (y a)).mp (hsq.trans hQ)

private theorem abs_apply_le_one_of_Q_eq_one'
    (y : RealVeroneseSpace n k) (hQ : Q y = 1) (a : MultiIndex n k) :
    |y a| ≤ 1 := by
  have hn := norm_le_one_of_Q_eq_one y hQ
  have ha := norm_le_pi_norm y a
  rw [Real.norm_eq_abs] at ha
  linarith

/-! ## (P1) Lipschitz bounds on `Q ≤ 1` -/

/-- The evaluated (unstabilized) cubic lift is `C¹`. -/
theorem contDiff_evaluatedCubicLift
    (F : HGAS.PolynomialField n) :
    ContDiff ℝ 1 (evaluatedCubicLift (k := k) F) := by
  exact
    (contDiff_evalCoordinateField_real
      (cubicLiftField (k := k) F)).of_le
      (by norm_num)

/-- For any `C¹` field, the weighted angular field and the radial reward
are Lipschitz on `Q ≤ 1` for the weighted metric. -/
theorem exists_lipschitz_weightedAngular_of_contDiff
    {G : RealVeroneseSpace n k → RealVeroneseSpace n k}
    (hG : ContDiff ℝ 1 G) :
    ∃ L : ℝ, 0 < L ∧
      ∀ y y' : RealVeroneseSpace n k, Q y ≤ 1 → Q y' ≤ 1 →
        weightedNormSq
            (weightedAngularField G y - weightedAngularField G y') ≤
          L ^ 2 * weightedNormSq (y - y') ∧
        |weightedRadialReward G y - weightedRadialReward G y'| ≤
          L * Real.sqrt (weightedNormSq (y - y')) := by
  obtain ⟨K₁, hK₁⟩ :=
    (contDiff_weightedAngularField hG).contDiffOn.exists_lipschitzOnWith
      one_ne_zero
      (convex_closedBall (0 : RealVeroneseSpace n k) 1)
      (isCompact_closedBall (0 : RealVeroneseSpace n k) 1)
  obtain ⟨K₂, hK₂⟩ :=
    (contDiff_weightedRadialReward hG).contDiffOn.exists_lipschitzOnWith
      one_ne_zero
      (convex_closedBall (0 : RealVeroneseSpace n k) 1)
      (isCompact_closedBall (0 : RealVeroneseSpace n k) 1)
  set M := shadowWeightMass n k with hMdef
  have hM : 1 ≤ M := one_le_shadowWeightMass
  have hK₁0 : (0 : ℝ) ≤ K₁ := K₁.2
  have hK₂0 : (0 : ℝ) ≤ K₂ := K₂.2
  refine ⟨M * ((K₁ : ℝ) + K₂ + 1), by positivity, ?_⟩
  intro y y' hy hy'
  have hyb : y ∈ closedBall (0 : RealVeroneseSpace n k) 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using
      norm_le_one_of_Q_le_one' y hy
  have hyb' : y' ∈ closedBall (0 : RealVeroneseSpace n k) 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using
      norm_le_one_of_Q_le_one' y' hy'
  have hdist := norm_le_sqrt_weightedNormSq (y - y')
  have hNnonneg : 0 ≤ weightedNormSq (y - y') := by
    rw [weightedNormSq_eq_Q]
    exact Q_nonneg_real _
  set s := Real.sqrt (weightedNormSq (y - y')) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = weightedNormSq (y - y') := Real.sq_sqrt hNnonneg
  constructor
  · have hlip := hK₁.dist_le_mul y hyb y' hyb'
    rw [dist_eq_norm, dist_eq_norm] at hlip
    have hnormY :
        ‖weightedAngularField G y - weightedAngularField G y'‖ ≤
          K₁ * s :=
      hlip.trans (mul_le_mul_of_nonneg_left hdist hK₁0)
    have hsq :
        ‖weightedAngularField G y - weightedAngularField G y'‖ ^ 2 ≤
          (K₁ * s) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnormY 2
    have hw :=
      weightedNormSq_le_mass_mul_norm_sq
        (weightedAngularField G y - weightedAngularField G y')
    have hK1L : (K₁ : ℝ) ≤ M * ((K₁ : ℝ) + K₂ + 1) := by
      nlinarith
    calc
      weightedNormSq
          (weightedAngularField G y - weightedAngularField G y') ≤
          M * (K₁ * s) ^ 2 :=
        hw.trans (mul_le_mul_of_nonneg_left hsq (by linarith))
      _ = M * K₁ ^ 2 * weightedNormSq (y - y') := by
        rw [← hss]; ring
      _ ≤ (M * ((K₁ : ℝ) + K₂ + 1)) ^ 2 *
            weightedNormSq (y - y') := by
        apply mul_le_mul_of_nonneg_right _ hNnonneg
        have h1 : M * (K₁ : ℝ) ^ 2 ≤ M * (M * (K₁ : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (le_mul_of_one_le_left (sq_nonneg _) hM) (by linarith)
        have h2 : (K₁ : ℝ) ^ 2 ≤ ((K₁ : ℝ) + K₂ + 1) ^ 2 :=
          pow_le_pow_left₀ hK₁0 (by linarith) 2
        calc
          M * (K₁ : ℝ) ^ 2 ≤ M * (M * (K₁ : ℝ) ^ 2) := h1
          _ ≤ M * (M * ((K₁ : ℝ) + K₂ + 1) ^ 2) := by
            gcongr
          _ = (M * ((K₁ : ℝ) + K₂ + 1)) ^ 2 := by ring
  · have hlip := hK₂.dist_le_mul y hyb y' hyb'
    rw [Real.dist_eq, dist_eq_norm] at hlip
    have hK2L : (K₂ : ℝ) ≤ M * ((K₁ : ℝ) + K₂ + 1) := by
      nlinarith
    calc
      |weightedRadialReward G y - weightedRadialReward G y'| ≤
          K₂ * ‖y - y'‖ := hlip
      _ ≤ K₂ * s := mul_le_mul_of_nonneg_left hdist hK₂0
      _ ≤ M * ((K₁ : ℝ) + K₂ + 1) * s :=
        mul_le_mul_of_nonneg_right hK2L hs0

/-- (P1) Lipschitz bounds for the unstabilized cubic lift on `Q ≤ 1`. -/
theorem exists_lipschitz_cubicLift_angular
    (F : HGAS.PolynomialField n) :
    ∃ L : ℝ, 0 < L ∧
      ∀ y y' : RealVeroneseSpace n k, Q y ≤ 1 → Q y' ≤ 1 →
        weightedNormSq
            (weightedAngularField (evaluatedCubicLift (k := k) F) y -
              weightedAngularField (evaluatedCubicLift (k := k) F) y') ≤
          L ^ 2 * weightedNormSq (y - y') ∧
        |weightedRadialReward (evaluatedCubicLift (k := k) F) y -
            weightedRadialReward (evaluatedCubicLift (k := k) F) y'| ≤
          L * Real.sqrt (weightedNormSq (y - y')) :=
  exists_lipschitz_weightedAngular_of_contDiff
    (contDiff_evaluatedCubicLift F)

/-! ## (P2) The tangential penalty gradient is `O(sqrt W)` -/

/-- On `Q = 1`, every relation differential is bounded by four times the
weighted norm of the direction. -/
private theorem abs_toricRelationDifferential_le_of_Q_eq_one
    (r : ToricRelationIndex n k)
    (y h : RealVeroneseSpace n k) (hQ : Q y = 1) :
    |toricRelationDifferential r y h| ≤
      4 * Real.sqrt (weightedNormSq h) := by
  set s := Real.sqrt (weightedNormSq h)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hy := abs_apply_le_one_of_Q_eq_one' y hQ
  have hh := abs_apply_le_sqrt_weightedNormSq h
  have hprod : ∀ a b : MultiIndex n k, |h a * y b| ≤ s := by
    intro a b
    rw [abs_mul]
    calc
      |h a| * |y b| ≤ s * 1 :=
        mul_le_mul (hh a) (hy b) (abs_nonneg _) hs
      _ = s := mul_one s
  have hprod' : ∀ a b : MultiIndex n k, |y a * h b| ≤ s := by
    intro a b
    rw [mul_comm]
    exact hprod b a
  unfold toricRelationDifferential
  have e1 := hprod r.alpha r.beta
  have e2 := hprod' r.alpha r.beta
  have e3 := hprod r.gamma r.delta
  have e4 := hprod' r.gamma r.delta
  rw [abs_le] at e1 e2 e3 e4 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2]

/-- (P2) Penalty-gradient bound: `‖grad_{S_Q} W‖_Q² ≤ C_W² W` on `Q = 1`. -/
theorem exists_penaltySphereGradient_bound :
    ∃ C_W : ℝ, 0 ≤ C_W ∧
      ∀ y : RealVeroneseSpace n k, Q y = 1 →
        weightedNormSq (penaltySphereGradient y) ≤
          C_W ^ 2 * completeToricEnergy y := by
  set R : ℝ := (Fintype.card (ToricRelationIndex n k) : ℝ)
  have hR : 0 ≤ R := Nat.cast_nonneg _
  refine ⟨8 * R, by positivity, ?_⟩
  intro y hQ
  set D := weightedNormSq (penaltySphereGradient y) with hDdef
  have hD0 : 0 ≤ D := by
    rw [hDdef, weightedNormSq_eq_Q]
    exact Q_nonneg_real _
  have hW0 : 0 ≤ completeToricEnergy y := toricPenalty_nonneg_real y
  set sD := Real.sqrt D with hsD
  set sW := Real.sqrt (completeToricEnergy y) with hsW
  have hsD0 : 0 ≤ sD := Real.sqrt_nonneg _
  have hsW0 : 0 ≤ sW := Real.sqrt_nonneg _
  -- `D` is the derivative of `W` along its own tangential gradient.
  have hDdir :
      D = toricPenaltyDirectional y (penaltySphereGradient y) := by
    rw [toricPenaltyDirectional_eq_weightedInner,
      weightedInner_penaltyAmbientGradient_penaltySphereGradient y hQ]
    rfl
  have hsum :
      relationDifferentialAbsSum penaltySphereGradient y ≤ R * (4 * sD) := by
    unfold relationDifferentialAbsSum
    calc
      (∑ r : ToricRelationIndex n k,
          |toricRelationDifferential r y (penaltySphereGradient y)|) ≤
          ∑ _r : ToricRelationIndex n k, 4 * sD := by
        apply Finset.sum_le_sum
        intro r _
        exact abs_toricRelationDifferential_le_of_Q_eq_one r y _ hQ
      _ = R * (4 * sD) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hDle : D ≤ 8 * R * sW * sD := by
    have h1 :=
      abs_toricPenaltyDirectional_le_sqrt_mul_absSum
        penaltySphereGradient y
    rw [← hDdir] at h1
    calc
      D ≤ |D| := le_abs_self D
      _ ≤ 2 * sW * relationDifferentialAbsSum penaltySphereGradient y := h1
      _ ≤ 2 * sW * (R * (4 * sD)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 8 * R * sW * sD := by ring
  have hsDsq : sD ^ 2 = D := Real.sq_sqrt hD0
  have hsWsq : sW ^ 2 = completeToricEnergy y := Real.sq_sqrt hW0
  have hroot : sD ≤ 8 * R * sW := by
    rcases eq_or_lt_of_le hsD0 with h0 | hpos
    · rw [← h0]
      exact mul_nonneg (mul_nonneg (by norm_num) hR) hsW0
    · have : sD * sD ≤ (8 * R * sW) * sD := by
        nlinarith
      exact le_of_mul_le_mul_right this hpos
  calc
    D = sD ^ 2 := hsDsq.symm
    _ ≤ (8 * R * sW) ^ 2 := pow_le_pow_left₀ hsD0 hroot 2
    _ = (8 * R) ^ 2 * completeToricEnergy y := by
      rw [← hsWsq]; ring

/-! ## (P3) Tube invariance and exponential decay -/

/-- (P3a) Forward invariance of the tube `W ≤ η` for the stabilized
angular flow. -/
theorem stabilizedCubicAmbientAngularFlow_energy_le_eta
    (b : CubicLiftStabilizationBounds F k)
    (y : RealVeroneseSpace n k) (hQ : Q y = 1)
    (hTube : completeToricEnergy y ≤ b.η)
    (t : ℝ) (ht : 0 ≤ t) :
    completeToricEnergy (stabilizedCubicAmbientAngularFlow b t y) ≤
      b.η := by
  set w : ℝ → ℝ := fun s ↦
    completeToricEnergy (stabilizedCubicAmbientAngularFlow b s y)
    with hwdef
  set P : ℝ → ℝ := fun s ↦
    penaltyLieDerivative
      (weightedAngularField (evaluatedStabilizedCubicField b))
      (stabilizedCubicAmbientAngularFlow b s y) with hPdef
  have hw : ∀ s, HasDerivAt w (P s) s :=
    stabilizedCubicAmbientAngularFlow_hasDerivAt_penalty b y hQ
  have hrate := cubicLiftStabilization_decayRate_pos b
  have hw0 : w 0 = completeToricEnergy y := by
    simp only [hwdef, Flow.map_zero_apply]
  have key :=
    image_le_of_deriv_right_lt_deriv_boundary
      (f := w) (f' := P) (a := 0) (b := t)
      (B := fun _ ↦ b.η) (B' := fun _ ↦ 0)
      (fun s _ ↦ (hw s).continuousAt.continuousWithinAt)
      (fun s _ ↦ (hw s).hasDerivWithinAt)
      (by rw [hw0]; exact hTube)
      (fun s ↦ hasDerivAt_const s b.η)
      (by
        intro s _ hs
        have hQs :=
          stabilizedCubicAmbientAngularFlow_preserves_Q b y hQ s
        have hle :=
          stabilizedCubicAngular_penaltyDerivative_le b
            (stabilizedCubicAmbientAngularFlow b s y) hQs
            (le_of_eq hs)
        have hs' :
            completeToricEnergy
                (stabilizedCubicAmbientAngularFlow b s y) = b.η := hs
        rw [hs'] at hle
        have hprod :
            0 < ((b.K : ℝ) * b.c - b.C) * b.η :=
          mul_pos hrate b.η_pos
        change P s < 0
        simp only [hPdef]
        linarith)
  exact key ⟨ht, le_rfl⟩

/-- (P3b) Exponential decay of the penalty along stabilized angular
orbits starting in the tube. -/
theorem stabilizedCubicAmbientAngularFlow_energy_le_exp
    (b : CubicLiftStabilizationBounds F k)
    (y : RealVeroneseSpace n k) (hQ : Q y = 1)
    (hTube : completeToricEnergy y ≤ b.η)
    (t : ℝ) (ht : 0 ≤ t) :
    completeToricEnergy (stabilizedCubicAmbientAngularFlow b t y) ≤
      completeToricEnergy y *
        Real.exp (-(((b.K : ℝ) * b.c - b.C)) * t) := by
  set w : ℝ → ℝ := fun s ↦
    completeToricEnergy (stabilizedCubicAmbientAngularFlow b s y)
    with hwdef
  set P : ℝ → ℝ := fun s ↦
    penaltyLieDerivative
      (weightedAngularField (evaluatedStabilizedCubicField b))
      (stabilizedCubicAmbientAngularFlow b s y) with hPdef
  have hw : ∀ s, HasDerivAt w (P s) s :=
    stabilizedCubicAmbientAngularFlow_hasDerivAt_penalty b y hQ
  have hw0 : w 0 = completeToricEnergy y := by
    simp only [hwdef, Flow.map_zero_apply]
  have key :=
    le_gronwallBound_of_liminf_deriv_right_le
      (f := w) (f' := P) (δ := completeToricEnergy y)
      (K := -(((b.K : ℝ) * b.c - b.C))) (ε := 0)
      (a := 0) (b := t)
      (fun s _ ↦ (hw s).continuousAt.continuousWithinAt)
      (fun s _ r hr ↦ (hw s).hasDerivWithinAt.liminf_right_slope_le hr)
      (le_of_eq hw0)
      (by
        intro s hs
        have hQs :=
          stabilizedCubicAmbientAngularFlow_preserves_Q b y hQ s
        have hTs :=
          stabilizedCubicAmbientAngularFlow_energy_le_eta
            b y hQ hTube s hs.1
        have hle :=
          stabilizedCubicAngular_penaltyDerivative_le b
            (stabilizedCubicAmbientAngularFlow b s y) hQs hTs
        simp only [hPdef, hwdef]
        linarith)
      t ⟨ht, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero] at key
  exact key

/-! ## (P4) The stabilized and unstabilized flows agree on the cone -/

/-- A stabilized angular orbit starting on the zero-penalty core stays in
the real toric zero set for all times. -/
theorem stabilizedCubicAmbientAngularFlow_mem_toricZeroSet_of_cone
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k)
    (y : RealVeroneseSpace n k) (hQ : Q y = 1)
    (hW : completeToricEnergy y = 0) (t : ℝ) :
    stabilizedCubicAmbientAngularFlow b t y ∈
      toricZeroSet (R := ℝ) n k := by
  obtain ⟨u, hu, hy | hy⟩ :=
    (completeToricEnergy_eq_zero_on_weightedUnitSphere_iff
      hk y hQ).mp hW
  · rw [hy, ← positive_veronese_ambient_flow_conjugacy b hF hk u hu t]
    exact veronese_mem_toricZeroSet _
  · rw [hy, ← negative_veronese_ambient_flow_conjugacy b hF hk u hu t]
    exact neg_veronese_mem_toricZeroSet _

/-- The stabilized angular orbit of a cone point has zero penalty for
all times. -/
theorem completeToricEnergy_stabilizedCubicAmbientAngularFlow_of_cone
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k)
    (y : RealVeroneseSpace n k) (hQ : Q y = 1)
    (hW : completeToricEnergy y = 0) (t : ℝ) :
    completeToricEnergy (stabilizedCubicAmbientAngularFlow b t y) = 0 :=
  (toricPenalty_eq_zero_iff_mem_toricZeroSet_real _).mpr
    (stabilizedCubicAmbientAngularFlow_mem_toricZeroSet_of_cone
      b hF hk y hQ hW t)

/-- On the toric zero set, the stabilized and unstabilized angular fields
coincide. -/
theorem weightedAngularField_stabilized_eq_cubicLift_of_mem_toricZeroSet
    (b : CubicLiftStabilizationBounds F k)
    {z : RealVeroneseSpace n k}
    (hz : z ∈ toricZeroSet (R := ℝ) n k) :
    weightedAngularField (evaluatedStabilizedCubicField b) z =
      weightedAngularField (evaluatedCubicLift (k := k) F) z := by
  have hpoint :
      evaluatedStabilizedCubicField b z =
        evaluatedCubicLift (k := k) F z :=
    eval_stabilizedCubicField_of_mem_toricZeroSet F b.K hz
  unfold weightedAngularField weightedRadialReward
  rw [hpoint]

/-- (P4) For a point of the zero-penalty core, the unstabilized and
stabilized angular flows agree for all real times. -/
theorem weightedAngularFlow_cubicLift_eq_stabilized_on_cone
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k)
    (y : RealVeroneseSpace n k) (hQ : Q y = 1)
    (hW : completeToricEnergy y = 0) (t : ℝ) :
    weightedAngularFlow (evaluatedCubicLift (k := k) F)
        (contDiff_evaluatedCubicLift F) t y =
      stabilizedCubicAmbientAngularFlow b t y := by
  let G := evaluatedCubicLift (k := k) F
  let Y := weightedAngularField G
  have hY : ContDiff ℝ 1 Y :=
    contDiff_weightedAngularField (contDiff_evaluatedCubicLift F)
  obtain ⟨K, hK⟩ :=
    hY.contDiffOn.exists_lipschitzOnWith
      one_ne_zero
      (convex_closedBall (0 : RealVeroneseSpace n k) 1)
      (isCompact_closedBall (0 : RealVeroneseSpace n k) 1)
  let γ₁ : ℝ → RealVeroneseSpace n k :=
    fun s ↦ weightedAngularFlow G (contDiff_evaluatedCubicLift F) s y
  let γ₂ : ℝ → RealVeroneseSpace n k :=
    fun s ↦ stabilizedCubicAmbientAngularFlow b s y
  have hγ₁ : IsIntegralCurve γ₁ (fun _ ↦ Y) :=
    weightedAngularFlow_isIntegralCurve G
      (contDiff_evaluatedCubicLift F) y hQ
  have hγ₂ : IsIntegralCurve γ₂ (fun _ ↦ Y) := by
    intro s
    have hs := stabilizedCubicAmbientAngularFlow_isIntegralCurve b y hQ s
    have hfield :=
      weightedAngularField_stabilized_eq_cubicLift_of_mem_toricZeroSet
        b (stabilizedCubicAmbientAngularFlow_mem_toricZeroSet_of_cone
          b hF hk y hQ hW s)
    simpa only [γ₂, Y, G, hfield] using hs
  have hγ₁Q : ∀ s, Q (γ₁ s) = 1 :=
    weightedAngularFlow_preserves_Q G
      (contDiff_evaluatedCubicLift F) y hQ
  have hγ₂Q : ∀ s, Q (γ₂ s) = 1 :=
    stabilizedCubicAmbientAngularFlow_preserves_Q b y hQ
  have heq : γ₁ = γ₂ := by
    apply ODE_solution_unique_univ
      (v := fun _ : ℝ ↦ Y)
      (s := fun _ ↦ closedBall (0 : RealVeroneseSpace n k) 1)
      (K := K) (t₀ := 0)
    · intro _
      exact hK
    · intro s
      exact ⟨hγ₁ s, by
        simpa [Metric.mem_closedBall, dist_zero_right] using
          norm_le_one_of_Q_eq_one (γ₁ s) (hγ₁Q s)⟩
    · intro s
      exact ⟨hγ₂ s, by
        simpa [Metric.mem_closedBall, dist_zero_right] using
          norm_le_one_of_Q_eq_one (γ₂ s) (hγ₂Q s)⟩
    · simp [γ₁, γ₂, Flow.map_zero_apply]
  exact congrFun heq t

/-- (P4, energy) The unstabilized angular orbit of a cone point also has
zero penalty for all times. -/
theorem completeToricEnergy_weightedAngularFlow_cubicLift_of_cone
    (b : CubicLiftStabilizationBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k)
    (y : RealVeroneseSpace n k) (hQ : Q y = 1)
    (hW : completeToricEnergy y = 0) (t : ℝ) :
    completeToricEnergy
        (weightedAngularFlow (evaluatedCubicLift (k := k) F)
          (contDiff_evaluatedCubicLift F) t y) = 0 := by
  rw [weightedAngularFlow_cubicLift_eq_stabilized_on_cone
    b hF hk y hQ hW t]
  exact completeToricEnergy_stabilizedCubicAmbientAngularFlow_of_cone
    b hF hk y hQ hW t

end

end HGAS.Veronese
