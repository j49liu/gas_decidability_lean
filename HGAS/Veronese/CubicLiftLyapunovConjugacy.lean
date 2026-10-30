import HGAS.Veronese.ConeDistance
import HGAS.Veronese.CubicLiftGASConjugacy
import HGAS.Veronese.CubicLiftShadowingBounds
import HGAS.Veronese.LyapunovAngularCriteria
import HGAS.Veronese.ShadowingPrelims
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Lyapunov stability is preserved by the stabilized cubic Veronese lift

For a rational polynomial source field `F` homogeneous of degree `2k+1`
(`k ≥ 1`) and shadowing data `b : CubicLiftShadowingBounds F k`, this module
proves

```
LyapunovStableWithExistence (evaluatedSourceField F) 0 ↔
  LyapunovStableWithExistence (evaluatedStabilizedCubicField b) 0.
```

Both sides are characterized by a uniform upper bound on the forward radial
cocycle of the corresponding angular flow
(`LyapunovAngularCriteria`).  The reverse implication restricts the
stabilized cocycle to the positive Veronese sheet.  The forward implication
uses a **finite-horizon shadowing** estimate: every stabilized angular orbit
starting in the tube `W ≤ η` stays exponentially close, on any finite time
window `[0, τ]`, to an orbit on the zero-penalty cone, chosen by projecting
the endpoint of the window to the cone and flowing backwards.  The
exponential contraction rate `λ = K c - C ≥ 2L + 1` of the penalty beats the
Lipschitz separation rate `L` of the unstabilized angular field, so the
backward comparison argument gives a bound which is uniform in the window
length.  Integrating the Lipschitz bound of the radial reward then shows
that the stabilized cocycle exceeds a cone cocycle by at most a uniform
constant; on the cone the cocycle is `k` times a source cocycle.

The module also proves that shadowing data exist for every such source
field (`exists_cubicLiftShadowingBounds`).
-/

namespace HGAS.Veronese

open Set Function Metric Filter
open scoped Topology NNReal

noncomputable section

variable {n k : ℕ} {F : HGAS.PolynomialField n}

/-! ## Elementary norm comparisons -/

/-- The sup norm is dominated by the weighted norm. -/
private theorem lyapShadow_norm_le_sqrt_weightedNormSq
    (h : RealVeroneseSpace n k) :
    ‖h‖ ≤ Real.sqrt (weightedNormSq h) := by
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro a
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
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

/-- A square root of a quantity decaying like `exp (-2 μ t)` decays like
`exp (-μ t)`. -/
private theorem lyapShadow_sqrt_le_of_le_exp
    {X A μ t : ℝ} (hA : 0 ≤ A)
    (hX : X ≤ A * Real.exp (-(2 * μ) * t)) :
    Real.sqrt X ≤ Real.sqrt A * Real.exp (-μ * t) := by
  have hexp :
      Real.exp (-(2 * μ) * t) =
        Real.exp (-μ * t) * Real.exp (-μ * t) := by
    rw [← Real.exp_add]
    ring_nf
  calc
    Real.sqrt X ≤ Real.sqrt (A * Real.exp (-(2 * μ) * t)) :=
      Real.sqrt_le_sqrt hX
    _ = Real.sqrt A * Real.exp (-μ * t) := by
      rw [Real.sqrt_mul hA, hexp,
        Real.sqrt_mul_self (Real.exp_pos _).le]

/-! ## Existence of shadowing data -/

/-- Shadowing data exist for every source field homogeneous of degree
`2k+1`.

The Lipschitz constants come from the `C¹` regularity of the unstabilized
angular field and radial reward on the compact ball `‖y‖ ≤ 1`, which
contains `Q = 1`.  A natural gain larger than the three thresholds
`(C + 2L + 1)/c` and `(A+1)/(4η)` then satisfies all gain inequalities. -/
theorem exists_cubicLiftShadowingBounds
    (F : HGAS.PolynomialField n)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F) (hk : 1 ≤ k) :
    Nonempty (CubicLiftShadowingBounds F k) := by
  obtain ⟨c, η, hc, hη, hMorseBott⟩ :=
    exists_positive_morseBott_coercivity_constants
      (n := n) hk
  obtain ⟨C, hC, hTangency⟩ :=
    exists_cubicLift_angularPenaltyLieDerivative_linear_bound
      F hF hk
  obtain ⟨A, hA, hRadial⟩ :=
    exists_radialReward_bound_on_weightedUnitSphere
      (continuous_evaluatedCubicLift (k := k) F)
  have hG := contDiff_evaluatedCubicLift (k := k) F
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
  set L : ℝ := (K₁ : ℝ) + K₂ with hLdef
  have hK₁0 : (0 : ℝ) ≤ K₁ := K₁.2
  have hK₂0 : (0 : ℝ) ≤ K₂ := K₂.2
  have hL0 : 0 ≤ L := add_nonneg hK₁0 hK₂0
  have hball :
      ∀ y : RealVeroneseSpace n k, Q y = 1 →
        y ∈ closedBall (0 : RealVeroneseSpace n k) 1 := by
    intro y hy
    simpa [Metric.mem_closedBall, dist_zero_right] using
      norm_le_one_of_Q_eq_one y hy
  have hAngular :
      ∀ y y' : RealVeroneseSpace n k, Q y = 1 → Q y' = 1 →
        ‖weightedAngularField (evaluatedCubicLift (k := k) F) y -
            weightedAngularField (evaluatedCubicLift (k := k) F) y'‖ ≤
          L * ‖y - y'‖ := by
    intro y y' hy hy'
    have hlip := hK₁.dist_le_mul y (hball y hy) y' (hball y' hy')
    rw [dist_eq_norm, dist_eq_norm] at hlip
    calc
      _ ≤ (K₁ : ℝ) * ‖y - y'‖ := hlip
      _ ≤ L * ‖y - y'‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have hRadialLip :
      ∀ y y' : RealVeroneseSpace n k, Q y = 1 → Q y' = 1 →
        |weightedRadialReward (evaluatedCubicLift (k := k) F) y -
            weightedRadialReward (evaluatedCubicLift (k := k) F) y'| ≤
          L * ‖y - y'‖ := by
    intro y y' hy hy'
    have hlip := hK₂.dist_le_mul y (hball y hy) y' (hball y' hy')
    rw [Real.dist_eq, dist_eq_norm] at hlip
    calc
      _ ≤ (K₂ : ℝ) * ‖y - y'‖ := hlip
      _ ≤ L * ‖y - y'‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  let threshold : ℝ :=
    max 0 (max ((C + 2 * L + 1) / c) ((A + 1) / (4 * η)))
  obtain ⟨N, hN⟩ := exists_nat_gt threshold
  have hN0 : (0 : ℝ) < N :=
    lt_of_le_of_lt (le_max_left _ _) hN
  have hNC : (C + 2 * L + 1) / c < (N : ℝ) :=
    lt_of_le_of_lt
      (le_trans (le_max_left _ _)
        (le_max_right 0
          (max ((C + 2 * L + 1) / c) ((A + 1) / (4 * η)))))
      hN
  have hNA : (A + 1) / (4 * η) < (N : ℝ) :=
    lt_of_le_of_lt
      (le_trans (le_max_right _ _)
        (le_max_right 0
          (max ((C + 2 * L + 1) / c) ((A + 1) / (4 * η)))))
      hN
  have hShadowGain : C + 2 * L + 1 < (N : ℝ) * c :=
    (div_lt_iff₀ hc).mp hNC
  have hAngularGain : C < (N : ℝ) * c := by linarith
  have hfourEta : 0 < 4 * η := mul_pos (by norm_num) hη
  have hRadialGain : A + 1 ≤ 4 * (N : ℝ) * η := by
    have hstrict : A + 1 < (N : ℝ) * (4 * η) :=
      (div_lt_iff₀ hfourEta).mp hNA
    nlinarith
  let K : ℚ := N
  have hKpos : 0 < K := by
    dsimp only [K]
    exact_mod_cast hN0
  have hKcast : (K : ℝ) = N := by
    simp only [K, Rat.cast_natCast]
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
    angularGain := by rw [hKcast]; exact hAngularGain
    radialGain := by rw [hKcast]; exact hRadialGain
    L := L
    L_nonneg := hL0
    angularLipschitz := hAngular
    radialLipschitz := hRadialLip
    shadowGain := by rw [hKcast]; linarith }⟩

/-! ## A backward comparison lemma -/

/-- Backward-in-time comparison.  If two differentiable curves satisfy a
linear differential inequality with an exponentially decaying forcing
term, and they are exponentially close at the end `τ` of a time window,
then they are exponentially close on the whole window, provided the decay
rate `μ` beats the growth rate `L`. -/
private theorem lyapShadow_backward_comparison
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v U V : ℝ → E} {L θ μ D τ : ℝ}
    (hu : ∀ t, HasDerivAt u (U t) t) (hv : ∀ t, HasDerivAt v (V t) t)
    (hbound : ∀ t ∈ Icc 0 τ,
      ‖U t - V t‖ ≤ L * ‖u t - v t‖ + θ * Real.exp (-μ * t))
    (hend : ‖u τ - v τ‖ ≤ D * Real.exp (-μ * τ))
    (hgain : L * D + θ < μ * D) :
    ∀ t ∈ Icc 0 τ, ‖u t - v t‖ ≤ D * Real.exp (-μ * t) := by
  set f : ℝ → E := fun s ↦ u (-s) - v (-s) with hfdef
  set f' : ℝ → E := fun s ↦
    (-1 : ℝ) • U (-s) - (-1 : ℝ) • V (-s) with hf'def
  set B : ℝ → ℝ := fun s ↦ D * Real.exp (μ * s) with hBdef
  have hf : ∀ s, HasDerivAt f (f' s) s := by
    intro s
    have h1 : HasDerivAt (fun r ↦ u (-r)) ((-1 : ℝ) • U (-s)) s :=
      (hu (-s)).scomp s (hasDerivAt_neg s)
    have h2 : HasDerivAt (fun r ↦ v (-r)) ((-1 : ℝ) • V (-s)) s :=
      (hv (-s)).scomp s (hasDerivAt_neg s)
    exact h1.sub h2
  have hB : ∀ s, HasDerivAt B (μ * B s) s := by
    intro s
    have h := ((hasDerivAt_id s).const_mul μ).exp.const_mul D
    convert h using 1
    simp only [hBdef, id]
    ring
  have hnormf' : ∀ s, ‖f' s‖ = ‖U (-s) - V (-s)‖ := by
    intro s
    simp only [hf'def]
    rw [← smul_sub, norm_smul, norm_neg, norm_one, one_mul]
  have key :=
    image_norm_le_of_norm_deriv_right_lt_deriv_boundary
      (f := f) (f' := f') (a := -τ) (b := 0) (B := B)
      (B' := fun s ↦ μ * B s)
      (fun s _ ↦ (hf s).continuousAt.continuousWithinAt)
      (fun s _ ↦ (hf s).hasDerivWithinAt)
      (by
        simp only [hfdef, hBdef, neg_neg]
        have : μ * -τ = -μ * τ := by ring
        rw [this]
        exact hend)
      hB
      (by
        intro s hs hfs
        have hs' : -s ∈ Icc 0 τ := ⟨by linarith [hs.2], by linarith [hs.1]⟩
        have hb := hbound (-s) hs'
        have hexp : -μ * -s = μ * s := by ring
        rw [hexp] at hb
        have hfs' : ‖u (-s) - v (-s)‖ = D * Real.exp (μ * s) := hfs
        rw [hfs'] at hb
        have hpos : 0 < Real.exp (μ * s) := Real.exp_pos _
        rw [hnormf']
        calc
          ‖U (-s) - V (-s)‖ ≤
              L * (D * Real.exp (μ * s)) + θ * Real.exp (μ * s) := hb
          _ = (L * D + θ) * Real.exp (μ * s) := by ring
          _ < (μ * D) * Real.exp (μ * s) :=
            mul_lt_mul_of_pos_right hgain hpos
          _ = μ * B s := by simp only [hBdef]; ring)
  intro t ht
  have hmem : -t ∈ Icc (-τ) 0 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h := key hmem
  simp only [hfdef, hBdef, neg_neg] at h
  have : μ * -t = -μ * t := by ring
  rw [this] at h
  exact h

/-! ## The stabilized fields in terms of the unstabilized lift -/

private theorem lyapShadow_field_eq
    (b : CubicLiftStabilizationBounds F k) :
    evaluatedStabilizedCubicField b =
      transverseStabilizedField
        (evaluatedCubicLift (k := k) F) (b.K : ℝ) := by
  funext z
  exact b.eval_stabilized_eq z

/-- `Y_H = Y_G - K grad_{S_Q} W`. -/
private theorem lyapShadow_angular_eq
    (b : CubicLiftStabilizationBounds F k) (y : RealVeroneseSpace n k) :
    weightedAngularField (evaluatedStabilizedCubicField b) y =
      weightedAngularField (evaluatedCubicLift (k := k) F) y -
        (b.K : ℝ) • penaltySphereGradient y := by
  rw [lyapShadow_field_eq]
  exact weightedAngularField_transverseStabilizedField _ _ y

/-- `a_H = a_G - 4 K W`. -/
private theorem lyapShadow_radialReward_eq
    (b : CubicLiftStabilizationBounds F k) (y : RealVeroneseSpace n k) :
    weightedRadialReward (evaluatedStabilizedCubicField b) y =
      weightedRadialReward (evaluatedCubicLift (k := k) F) y -
        4 * (b.K : ℝ) * completeToricEnergy y := by
  rw [lyapShadow_field_eq]
  exact weightedRadialReward_transverseStabilizedField _ _ y

/-- On the toric zero set the two radial rewards agree. -/
private theorem lyapShadow_radialReward_eq_of_mem_toricZeroSet
    (b : CubicLiftStabilizationBounds F k)
    {z : RealVeroneseSpace n k}
    (hz : z ∈ toricZeroSet (R := ℝ) n k) :
    weightedRadialReward (evaluatedStabilizedCubicField b) z =
      weightedRadialReward (evaluatedCubicLift (k := k) F) z := by
  have hpoint :
      evaluatedStabilizedCubicField b z =
        evaluatedCubicLift (k := k) F z :=
    eval_stabilizedCubicField_of_mem_toricZeroSet F b.K hz
  unfold weightedRadialReward
  rw [hpoint]

/-! ## Finite-horizon shadowing -/

/-- **Finite-horizon orbit shadowing.**

Write `λ = K c - C` for the transverse contraction rate.  There is a
constant `D` such that for every point `y` of the tube `W ≤ η` on `Q = 1`
and every time window `[0, τ]` there is a point `q` of the zero-penalty
cone (`Q q = 1`, `W q = 0`) whose stabilized angular orbit stays within
`D exp(-λ t / 2)` of the orbit of `y` for all `t ∈ [0, τ]`.

The point `q` is obtained by projecting `φ_τ y` to the cone and flowing
back for time `τ`; the estimate is a backward comparison argument that
uses `λ ≥ 2L + 1`. -/
theorem exists_finiteHorizonOrbitShadowing
    (b : CubicLiftShadowingBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F) (hk : 1 ≤ k) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ y : RealVeroneseSpace n k, Q y = 1 →
      completeToricEnergy y ≤ b.η → ∀ τ : ℝ, 0 ≤ τ →
      ∃ q : RealVeroneseSpace n k, Q q = 1 ∧ completeToricEnergy q = 0 ∧
        ∀ t ∈ Icc (0 : ℝ) τ,
          ‖stabilizedCubicAmbientAngularFlow
                b.toCubicLiftStabilizationBounds t y -
              stabilizedCubicAmbientAngularFlow
                b.toCubicLiftStabilizationBounds t q‖ ≤
            D * Real.exp (-(((b.K : ℝ) * b.c - b.C) / 2) * t) := by
  have hgainL : 2 * b.L + 1 ≤ (b.K : ℝ) * b.c - b.C := b.shadowGain
  have hη : 0 < b.η := b.η_pos
  have hK0 : (0 : ℝ) ≤ (b.K : ℝ) := le_of_lt (Rat.cast_pos.mpr b.K_pos)
  have hL0 : 0 ≤ b.L := b.L_nonneg
  obtain ⟨CW, hCW, hgrad⟩ :=
    exists_penaltySphereGradient_bound (n := n) (k := k)
  obtain ⟨Cd, hCd, hdist⟩ := exists_coneDistanceSq_le_energy (n := n) hk
  set bs := b.toCubicLiftStabilizationBounds with hbs
  set μ : ℝ := ((bs.K : ℝ) * bs.c - bs.C) / 2 with hμ
  set θ0 : ℝ := Real.sqrt (Cd * bs.η) with hθ0def
  set θ1 : ℝ := (bs.K : ℝ) * Real.sqrt (CW ^ 2 * bs.η) with hθ1def
  have hθ0 : 0 ≤ θ0 := Real.sqrt_nonneg _
  have hθ1 : 0 ≤ θ1 := mul_nonneg hK0 (Real.sqrt_nonneg _)
  set D : ℝ := 2 * θ0 + 2 * θ1 + 1 with hDdef
  have hD : 0 ≤ D := by rw [hDdef]; positivity
  have hgain : b.L * D + θ1 < μ * D := by
    have hμL : b.L + 1 / 2 ≤ μ := by rw [hμ]; linarith
    have h1 : (b.L + 1 / 2) * D ≤ μ * D :=
      mul_le_mul_of_nonneg_right hμL hD
    nlinarith
  refine ⟨D, hD, ?_⟩
  intro y hy hyη τ hτ
  -- Exponential decay of the penalty along the orbit of `y`.
  have hWdecay : ∀ t : ℝ, 0 ≤ t →
      completeToricEnergy (stabilizedCubicAmbientAngularFlow bs t y) ≤
        bs.η * Real.exp (-(2 * μ) * t) := by
    intro t ht
    have h := stabilizedCubicAmbientAngularFlow_energy_le_exp bs y hy hyη t ht
    have h2 : -(2 * μ) * t = -((bs.K : ℝ) * bs.c - bs.C) * t := by
      rw [hμ]; ring
    rw [h2]
    calc
      _ ≤ completeToricEnergy y *
            Real.exp (-((bs.K : ℝ) * bs.c - bs.C) * t) := h
      _ ≤ bs.η * Real.exp (-((bs.K : ℝ) * bs.c - bs.C) * t) :=
        mul_le_mul_of_nonneg_right hyη (Real.exp_pos _).le
  -- Project the endpoint of the window to the cone.
  obtain ⟨p, hpQ, hpW, hpdist⟩ :=
    hdist (stabilizedCubicAmbientAngularFlow bs τ y)
      (stabilizedCubicAmbientAngularFlow_preserves_Q bs y hy τ)
  let q : RealVeroneseSpace n k := stabilizedCubicAmbientAngularFlow bs (-τ) p
  have hqQ : Q q = 1 :=
    stabilizedCubicAmbientAngularFlow_preserves_Q bs p hpQ (-τ)
  have hqW : completeToricEnergy q = 0 :=
    completeToricEnergy_stabilizedCubicAmbientAngularFlow_of_cone
      bs hF hk p hpQ hpW (-τ)
  have hτq : stabilizedCubicAmbientAngularFlow bs τ q = p := by
    change stabilizedCubicAmbientAngularFlow bs τ
        (stabilizedCubicAmbientAngularFlow bs (-τ) p) = p
    rw [← Flow.map_add, add_neg_cancel, Flow.map_zero_apply]
  refine ⟨q, hqQ, hqW, ?_⟩
  apply lyapShadow_backward_comparison
    (u := fun t ↦ stabilizedCubicAmbientAngularFlow bs t y)
    (v := fun t ↦ stabilizedCubicAmbientAngularFlow bs t q)
    (U := fun t ↦ weightedAngularField (evaluatedStabilizedCubicField bs)
      (stabilizedCubicAmbientAngularFlow bs t y))
    (V := fun t ↦ weightedAngularField (evaluatedStabilizedCubicField bs)
      (stabilizedCubicAmbientAngularFlow bs t q))
    (L := b.L) (θ := θ1)
  · exact stabilizedCubicAmbientAngularFlow_isIntegralCurve bs y hy
  · exact stabilizedCubicAmbientAngularFlow_isIntegralCurve bs q hqQ
  · intro t ht
    have hQt : Q (stabilizedCubicAmbientAngularFlow bs t y) = 1 :=
      stabilizedCubicAmbientAngularFlow_preserves_Q bs y hy t
    have hQqt : Q (stabilizedCubicAmbientAngularFlow bs t q) = 1 :=
      stabilizedCubicAmbientAngularFlow_preserves_Q bs q hqQ t
    have hzero :=
      stabilizedCubicAmbientAngularFlow_mem_toricZeroSet_of_cone
        bs hF hk q hqQ hqW t
    rw [weightedAngularField_stabilized_eq_cubicLift_of_mem_toricZeroSet
      bs hzero, lyapShadow_angular_eq]
    set G := evaluatedCubicLift (k := k) F with hG
    set yt := stabilizedCubicAmbientAngularFlow bs t y with hyt
    set qt := stabilizedCubicAmbientAngularFlow bs t q with hqt
    have hsplit :
        weightedAngularField G yt - (bs.K : ℝ) • penaltySphereGradient yt -
            weightedAngularField G qt =
          (weightedAngularField G yt - weightedAngularField G qt) -
            (bs.K : ℝ) • penaltySphereGradient yt := by
      abel
    rw [hsplit]
    have hlip :
        ‖weightedAngularField G yt - weightedAngularField G qt‖ ≤
          b.L * ‖yt - qt‖ :=
      b.angularLipschitz yt qt hQt hQqt
    have hgradt :
        ‖(bs.K : ℝ) • penaltySphereGradient yt‖ ≤
          θ1 * Real.exp (-μ * t) := by
      rw [norm_smul, Real.norm_of_nonneg hK0, hθ1def, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hK0
      calc
        ‖penaltySphereGradient yt‖ ≤
            Real.sqrt (weightedNormSq (penaltySphereGradient yt)) :=
          lyapShadow_norm_le_sqrt_weightedNormSq _
        _ ≤ Real.sqrt (CW ^ 2 * bs.η) * Real.exp (-μ * t) := by
          apply lyapShadow_sqrt_le_of_le_exp (by positivity)
          calc
            _ ≤ CW ^ 2 * completeToricEnergy yt := hgrad yt hQt
            _ ≤ CW ^ 2 * (bs.η * Real.exp (-(2 * μ) * t)) :=
              mul_le_mul_of_nonneg_left (hWdecay t ht.1) (sq_nonneg _)
            _ = CW ^ 2 * bs.η * Real.exp (-(2 * μ) * t) := by ring
    calc
      _ ≤ ‖weightedAngularField G yt - weightedAngularField G qt‖ +
            ‖(bs.K : ℝ) • penaltySphereGradient yt‖ :=
        norm_sub_le _ _
      _ ≤ b.L * ‖yt - qt‖ + θ1 * Real.exp (-μ * t) :=
        add_le_add hlip hgradt
  · change ‖stabilizedCubicAmbientAngularFlow bs τ y -
        stabilizedCubicAmbientAngularFlow bs τ q‖ ≤ D * Real.exp (-μ * τ)
    rw [hτq]
    calc
      ‖stabilizedCubicAmbientAngularFlow bs τ y - p‖ ≤
          Real.sqrt
            (weightedNormSq (stabilizedCubicAmbientAngularFlow bs τ y - p)) :=
        lyapShadow_norm_le_sqrt_weightedNormSq _
      _ ≤ θ0 * Real.exp (-μ * τ) := by
        apply lyapShadow_sqrt_le_of_le_exp (by positivity)
        calc
          _ ≤ Cd * completeToricEnergy
                (stabilizedCubicAmbientAngularFlow bs τ y) := hpdist
          _ ≤ Cd * (bs.η * Real.exp (-(2 * μ) * τ)) :=
            mul_le_mul_of_nonneg_left (hWdecay τ hτ) hCd.le
          _ = Cd * bs.η * Real.exp (-(2 * μ) * τ) := by ring
      _ ≤ D * Real.exp (-μ * τ) :=
        mul_le_mul_of_nonneg_right (by rw [hDdef]; linarith)
          (Real.exp_pos _).le
  · exact hgain

/-- **Finite-horizon shadowing of the radial cocycle.**

There is a constant `Cstar` such that for every point `y` of the tube
`W ≤ η` on `Q = 1` and every time window `[0, τ]`, some point `q` of the
zero-penalty cone has stabilized radial cocycle over `[0, τ]` at least
the cocycle of `y` minus `Cstar`. -/
theorem exists_finiteHorizonShadowing
    (b : CubicLiftShadowingBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F) (hk : 1 ≤ k) :
    ∃ Cstar : ℝ, ∀ y : RealVeroneseSpace n k, Q y = 1 →
      completeToricEnergy y ≤ b.η → ∀ τ : ℝ, 0 ≤ τ →
      ∃ q : RealVeroneseSpace n k, Q q = 1 ∧ completeToricEnergy q = 0 ∧
        (∫ t in (0 : ℝ)..τ,
            weightedRadialReward
              (evaluatedStabilizedCubicField b.toCubicLiftStabilizationBounds)
              (stabilizedCubicAmbientAngularFlow
                b.toCubicLiftStabilizationBounds t y)) ≤
          (∫ t in (0 : ℝ)..τ,
            weightedRadialReward
              (evaluatedStabilizedCubicField b.toCubicLiftStabilizationBounds)
              (stabilizedCubicAmbientAngularFlow
                b.toCubicLiftStabilizationBounds t q)) + Cstar := by
  obtain ⟨D, hD, hshadow⟩ := exists_finiteHorizonOrbitShadowing b hF hk
  have hrate := cubicLiftStabilization_decayRate_pos
    b.toCubicLiftStabilizationBounds
  have hK0 : (0 : ℝ) ≤ (b.K : ℝ) := le_of_lt (Rat.cast_pos.mpr b.K_pos)
  have hL0 : 0 ≤ b.L := b.L_nonneg
  set bs := b.toCubicLiftStabilizationBounds with hbs
  set μ : ℝ := ((bs.K : ℝ) * bs.c - bs.C) / 2 with hμ
  have hμpos : 0 < μ := by rw [hμ]; linarith
  refine ⟨b.L * D / μ, ?_⟩
  intro y hy hyη τ hτ
  obtain ⟨q, hqQ, hqW, hclose⟩ := hshadow y hy hyη τ hτ
  refine ⟨q, hqQ, hqW, ?_⟩
  have hHcont :
      Continuous (weightedRadialReward (evaluatedStabilizedCubicField bs)) :=
    continuous_weightedRadialReward
      (contDiff_evaluatedStabilizedCubicField bs).continuous
  have hcont : ∀ x : RealVeroneseSpace n k,
      Continuous (fun t ↦
        weightedRadialReward (evaluatedStabilizedCubicField bs)
          (stabilizedCubicAmbientAngularFlow bs t x)) := fun x ↦
    hHcont.comp
      ((stabilizedCubicAmbientAngularFlow bs).continuous
        continuous_id continuous_const)
  have hexpcont :
      Continuous (fun t : ℝ ↦ b.L * D * Real.exp (-μ * t)) := by
    fun_prop
  have hpoint : ∀ t ∈ Icc (0 : ℝ) τ,
      weightedRadialReward (evaluatedStabilizedCubicField bs)
          (stabilizedCubicAmbientAngularFlow bs t y) ≤
        weightedRadialReward (evaluatedStabilizedCubicField bs)
            (stabilizedCubicAmbientAngularFlow bs t q) +
          b.L * D * Real.exp (-μ * t) := by
    intro t ht
    have hQt : Q (stabilizedCubicAmbientAngularFlow bs t y) = 1 :=
      stabilizedCubicAmbientAngularFlow_preserves_Q bs y hy t
    have hQqt : Q (stabilizedCubicAmbientAngularFlow bs t q) = 1 :=
      stabilizedCubicAmbientAngularFlow_preserves_Q bs q hqQ t
    have hzero :=
      stabilizedCubicAmbientAngularFlow_mem_toricZeroSet_of_cone
        bs hF hk q hqQ hqW t
    rw [lyapShadow_radialReward_eq_of_mem_toricZeroSet bs hzero,
      lyapShadow_radialReward_eq]
    set yt := stabilizedCubicAmbientAngularFlow bs t y with hyt
    set qt := stabilizedCubicAmbientAngularFlow bs t q with hqt
    have hlip :
        |weightedRadialReward (evaluatedCubicLift (k := k) F) yt -
            weightedRadialReward (evaluatedCubicLift (k := k) F) qt| ≤
          b.L * ‖yt - qt‖ :=
      b.radialLipschitz yt qt hQt hQqt
    have hW0 : 0 ≤ completeToricEnergy yt := toricPenalty_nonneg_real _
    have hc : ‖yt - qt‖ ≤ D * Real.exp (-μ * t) := hclose t ht
    have hLc : b.L * ‖yt - qt‖ ≤ b.L * (D * Real.exp (-μ * t)) :=
      mul_le_mul_of_nonneg_left hc hL0
    have habs := (abs_le.mp hlip).2
    have hKW : 0 ≤ 4 * (bs.K : ℝ) * completeToricEnergy yt := by
      positivity
    nlinarith
  have hint1 :
      (∫ t in (0 : ℝ)..τ,
        weightedRadialReward (evaluatedStabilizedCubicField bs)
          (stabilizedCubicAmbientAngularFlow bs t y)) ≤
        ∫ t in (0 : ℝ)..τ,
          (weightedRadialReward (evaluatedStabilizedCubicField bs)
              (stabilizedCubicAmbientAngularFlow bs t q) +
            b.L * D * Real.exp (-μ * t)) :=
    intervalIntegral.integral_mono_on hτ
      ((hcont y).intervalIntegrable (μ := MeasureTheory.volume) _ _)
      (((hcont q).add hexpcont).intervalIntegrable
        (μ := MeasureTheory.volume) _ _) hpoint
  rw [intervalIntegral.integral_add
    ((hcont q).intervalIntegrable (μ := MeasureTheory.volume) _ _)
    (hexpcont.intervalIntegrable (μ := MeasureTheory.volume) _ _)] at hint1
  have hexpint :
      (∫ t in (0 : ℝ)..τ, b.L * D * Real.exp (-μ * t)) ≤ b.L * D / μ := by
    have hderiv : ∀ x ∈ uIcc (0 : ℝ) τ,
        HasDerivAt (fun t ↦ -(b.L * D / μ) * Real.exp (-μ * t))
          (b.L * D * Real.exp (-μ * x)) x := by
      intro x _
      have h :=
        (((hasDerivAt_id' x).const_mul (-μ)).exp).const_mul (-(b.L * D / μ))
      convert h using 1
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hexpcont.intervalIntegrable _ _)]
    have hnonneg : 0 ≤ b.L * D / μ * Real.exp (-μ * τ) := by positivity
    simp only [mul_zero, Real.exp_zero, mul_one]
    linarith
  linarith

/-! ## Uniform cocycle bounds -/

/-- A uniform bound on the forward source cocycle gives a uniform bound on
the forward stabilized cocycle. -/
private theorem lyapShadow_stabilized_bound_of_source_bound
    (b : CubicLiftShadowingBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F) (hk : 1 ≤ k)
    (M : ℝ)
    (hM : ∀ x : Fin n → ℝ, sourceRadiusSq x = 1 → ∀ τ : ℝ, 0 ≤ τ →
      (∫ t in (0 : ℝ)..τ, HGAS.radialReward (evaluatedSourceField F)
        (polynomialSourceAngularAmbientFlow F t x)) ≤ M) :
    ∃ M' : ℝ, ∀ y : RealVeroneseSpace n k, Q y = 1 → ∀ τ : ℝ, 0 ≤ τ →
      (∫ t in (0 : ℝ)..τ,
        weightedRadialReward
          (evaluatedStabilizedCubicField b.toCubicLiftStabilizationBounds)
          (stabilizedCubicAmbientAngularFlow
            b.toCubicLiftStabilizationBounds t y)) ≤ M' := by
  obtain ⟨Cstar, hshadow⟩ := exists_finiteHorizonShadowing b hF hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set bs := b.toCubicLiftStabilizationBounds with hbs
  refine ⟨max 0 ((k : ℝ) * M + Cstar), ?_⟩
  intro y hy τ hτ
  have hHcont :
      Continuous (weightedRadialReward (evaluatedStabilizedCubicField bs)) :=
    continuous_weightedRadialReward
      (contDiff_evaluatedStabilizedCubicField bs).continuous
  have hcont : ∀ x : RealVeroneseSpace n k,
      Continuous (fun t ↦
        weightedRadialReward (evaluatedStabilizedCubicField bs)
          (stabilizedCubicAmbientAngularFlow bs t x)) := fun x ↦
    hHcont.comp
      ((stabilizedCubicAmbientAngularFlow bs).continuous
        continuous_id continuous_const)
  have hWcont :
      Continuous (fun t ↦
        completeToricEnergy (stabilizedCubicAmbientAngularFlow bs t y)) :=
    continuous_completeToricEnergy.comp
      ((stabilizedCubicAmbientAngularFlow bs).continuous
        continuous_id continuous_const)
  have hout : ∀ t : ℝ,
      bs.η < completeToricEnergy (stabilizedCubicAmbientAngularFlow bs t y) →
        weightedRadialReward (evaluatedStabilizedCubicField bs)
          (stabilizedCubicAmbientAngularFlow bs t y) ≤ 0 := by
    intro t ht
    have h :=
      stabilizedCubicAngular_radialReward_le_neg_one bs
        (stabilizedCubicAmbientAngularFlow bs t y)
        (stabilizedCubicAmbientAngularFlow_preserves_Q bs y hy t) ht.le
    linarith
  set S : Set ℝ := Icc 0 τ ∩
    {t | completeToricEnergy (stabilizedCubicAmbientAngularFlow bs t y) ≤
      bs.η} with hS
  by_cases hne : S.Nonempty
  · have hSclosed : IsClosed S :=
      isClosed_Icc.inter (isClosed_le hWcont continuous_const)
    have hSbdd : BddBelow S := ⟨0, fun t ht ↦ ht.1.1⟩
    have ht0mem : sInf S ∈ S := hSclosed.csInf_mem hne hSbdd
    set t0 := sInf S with ht0
    have ht00 : 0 ≤ t0 := ht0mem.1.1
    have ht0τ : t0 ≤ τ := ht0mem.1.2
    -- Before entering the tube, the reward is nonpositive.
    have hfirst :
        (∫ t in (0 : ℝ)..t0,
          weightedRadialReward (evaluatedStabilizedCubicField bs)
            (stabilizedCubicAmbientAngularFlow bs t y)) ≤ 0 := by
      have h :=
        intervalIntegral.integral_mono_on_of_le_Ioo ht00
          ((hcont y).intervalIntegrable _ _)
          (continuous_const.intervalIntegrable (μ := MeasureTheory.volume)
            (u := fun _ : ℝ ↦ (0 : ℝ)) _ _)
          (by
            intro t ht
            apply hout
            by_contra hle
            have htS : t ∈ S :=
              ⟨⟨ht.1.le, by linarith [ht.2]⟩, not_lt.mp hle⟩
            have := csInf_le hSbdd htS
            linarith [ht.2])
      simpa using h
    -- After entering the tube, shadow by a cone orbit.
    have hy1Q : Q (stabilizedCubicAmbientAngularFlow bs t0 y) = 1 :=
      stabilizedCubicAmbientAngularFlow_preserves_Q bs y hy t0
    have hy1W :
        completeToricEnergy (stabilizedCubicAmbientAngularFlow bs t0 y) ≤
          bs.η := ht0mem.2
    have hτ' : 0 ≤ τ - t0 := by linarith
    obtain ⟨q, hqQ, hqW, hq⟩ :=
      hshadow (stabilizedCubicAmbientAngularFlow bs t0 y) hy1Q hy1W
        (τ - t0) hτ'
    have hsecond :
        (∫ t in t0..τ,
          weightedRadialReward (evaluatedStabilizedCubicField bs)
            (stabilizedCubicAmbientAngularFlow bs t y)) =
          ∫ s in (0 : ℝ)..(τ - t0),
            weightedRadialReward (evaluatedStabilizedCubicField bs)
              (stabilizedCubicAmbientAngularFlow bs s
                (stabilizedCubicAmbientAngularFlow bs t0 y)) := by
      have h :=
        intervalIntegral.integral_comp_add_right
          (fun t ↦
            weightedRadialReward (evaluatedStabilizedCubicField bs)
              (stabilizedCubicAmbientAngularFlow bs t y))
          (a := 0) (b := τ - t0) t0
      simp only [zero_add, sub_add_cancel, Flow.map_add] at h
      exact h.symm
    -- The cone cocycle is `k` times a source cocycle.
    have hcone :
        (∫ s in (0 : ℝ)..(τ - t0),
          weightedRadialReward (evaluatedStabilizedCubicField bs)
            (stabilizedCubicAmbientAngularFlow bs s q)) ≤ (k : ℝ) * M := by
      obtain ⟨u, hu⟩ :=
        exists_source_orbitIntegral_eq_of_mem_core bs hF hk (τ - t0)
          ⟨q, hqQ⟩ hqW
      rw [stabilizedSubtype_orbitIntegral_eq,
        sourceSubtype_orbitIntegral_eq] at hu
      have hu' :
          (∫ s in (0 : ℝ)..(τ - t0),
            weightedRadialReward (evaluatedStabilizedCubicField bs)
              (stabilizedCubicAmbientAngularFlow bs s q)) =
            (k : ℝ) *
              ∫ s in (0 : ℝ)..(τ - t0),
                HGAS.radialReward (evaluatedSourceField F)
                  (polynomialSourceAngularAmbientFlow F s u.1) := hu
      rw [hu']
      exact mul_le_mul_of_nonneg_left (hM u.1 u.2 (τ - t0) hτ') hk0
    have hsplit :=
      intervalIntegral.integral_add_adjacent_intervals
        ((hcont y).intervalIntegrable (μ := MeasureTheory.volume) 0 t0)
        ((hcont y).intervalIntegrable (μ := MeasureTheory.volume) t0 τ)
    have htotal :
        (∫ t in (0 : ℝ)..τ,
          weightedRadialReward (evaluatedStabilizedCubicField bs)
            (stabilizedCubicAmbientAngularFlow bs t y)) ≤
          (k : ℝ) * M + Cstar := by
      rw [← hsplit, hsecond]
      linarith
    exact htotal.trans (le_max_right _ _)
  · have hall : ∀ t ∈ Icc (0 : ℝ) τ,
        weightedRadialReward (evaluatedStabilizedCubicField bs)
            (stabilizedCubicAmbientAngularFlow bs t y) ≤ 0 := by
      intro t ht
      apply hout
      by_contra hle
      exact hne ⟨t, ht, not_lt.mp hle⟩
    have h :=
      intervalIntegral.integral_mono_on hτ
        ((hcont y).intervalIntegrable _ _)
        (continuous_const.intervalIntegrable (μ := MeasureTheory.volume)
          (u := fun _ : ℝ ↦ (0 : ℝ)) _ _) hall
    simp only [intervalIntegral.integral_zero] at h
    exact h.trans (le_max_left _ _)

/-! ## Lyapunov stability is preserved -/

/-- **The stabilized cubic Veronese lift preserves Lyapunov stability.**

For every source field homogeneous of degree `2k+1`, with `k ≥ 1`, and
all shadowing data `b`, the source field is Lyapunov stable at the origin
(with existence of forward solutions) if and only if the stabilized
rational cubic field is. -/
theorem sourceLS_iff_stabilizedCubicLS
    (b : CubicLiftShadowingBounds F k)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k) :
    HGAS.LyapunovStableWithExistence (evaluatedSourceField F) 0 ↔
      HGAS.LyapunovStableWithExistence
        (evaluatedStabilizedCubicField b.toCubicLiftStabilizationBounds) 0 := by
  rw [lyapunovStableWithExistence_iff_boundedSourceAngularCocycle
      (evaluatedSourceField F) (2 * k)
      (evaluatedSourceField_scalesAsDegree F hF)
      (contDiff_evaluatedSourceField F)
      (evaluatedSourceField_zero F hF (by omega)),
    lyapunovStableWithExistence_iff_boundedWeightedAngularCocycle
      (evaluatedStabilizedCubicField b.toCubicLiftStabilizationBounds) 2
      (by
        simpa using
          evaluatedStabilizedCubicField_scalesAsDegree
            b.toCubicLiftStabilizationBounds)
      (contDiff_evaluatedStabilizedCubicField b.toCubicLiftStabilizationBounds)
      (evaluatedStabilizedCubicField_zero b.toCubicLiftStabilizationBounds)]
  constructor
  · rintro ⟨M, hM⟩
    obtain ⟨M', hM'⟩ :=
      lyapShadow_stabilized_bound_of_source_bound b hF hk M hM
    exact ⟨M', hM'⟩
  · rintro ⟨M, hM⟩
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    refine ⟨M / k, ?_⟩
    intro x hx τ hτ
    let u : sourceUnitSphere n := ⟨x, hx⟩
    have h :=
      positiveVeronese_orbitIntegral_eq
        b.toCubicLiftStabilizationBounds hF hk τ u
    rw [stabilizedSubtype_orbitIntegral_eq,
      sourceSubtype_orbitIntegral_eq] at h
    have hb :
        (∫ t in (0 : ℝ)..τ,
          weightedRadialReward
            (evaluatedStabilizedCubicField b.toCubicLiftStabilizationBounds)
            (stabilizedCubicAmbientAngularFlow
              b.toCubicLiftStabilizationBounds t
              (positiveVeroneseSphereMap k u).1)) ≤ M :=
      hM (positiveVeroneseSphereMap k u).1
        (positiveVeroneseSphereMap k u).2 τ hτ
    rw [h] at hb
    change
      (∫ t in (0 : ℝ)..τ,
        HGAS.radialReward (evaluatedSourceField F)
          (polynomialSourceAngularAmbientFlow F t u.1)) ≤ M / k
    rw [le_div_iff₀ hkpos]
    linarith

end

end HGAS.Veronese
