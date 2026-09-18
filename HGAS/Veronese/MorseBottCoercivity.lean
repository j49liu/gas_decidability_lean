import HGAS.Veronese.AffineConeChart
import HGAS.Veronese.CompactTransverseBounds
import HGAS.Veronese.CubicLiftToricFactorization
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-!
# Effective local coercivity of the complete Veronese penalty

For the complete family of balanced quadratic Veronese relations, let

```
W(y) = ∑ r, q_r(y)^2
```

and let `D(y)` be the squared weighted norm of the gradient of `W`
tangent to `Q(y)=1`.  This file proves the local Polyak--Łojasiewicz
(equivalently, Morse--Bott) estimate

```
c W(y) ≤ D(y)
```

in a sufficiently small `W`-tube around the real Veronese cone.

The proof is deliberately elementary.  It does not invoke a tubular
neighborhood theorem or a library theorem about Morse--Bott functions.
Instead, it uses the explicit affine reconstruction `affineConeChart`
and argues by a normalized bad sequence.  The chart error vanishes in
the pure and adjacent coordinates.  At a limiting cone point, the
differentials of the one-token transfer quadrics then force a normalized
error in the differential kernel to be zero, contradicting its weighted
norm one.
-/

namespace HGAS.Veronese

open scoped BigOperators Topology
open Filter

noncomputable section

variable {n k : ℕ}

/-! ## Continuity and positivity used by the compactness argument -/

theorem continuous_penaltyAmbientGradient :
    Continuous
      (penaltyAmbientGradient :
        RealVeroneseSpace n k → RealVeroneseSpace n k) := by
  apply continuous_pi
  intro a
  exact
    (continuous_eval₂Hom_rational_real
      (MvPolynomial.pderiv a (toricPenaltyPolynomial n k))).div_const
      (multinomialWeight a : ℝ)

theorem continuous_penaltySphereGradient :
    Continuous
      (penaltySphereGradient :
        RealVeroneseSpace n k → RealVeroneseSpace n k) := by
  unfold penaltySphereGradient quarticSphereGradient
  exact continuous_penaltyAmbientGradient.sub
    ((continuous_const.mul continuous_completeToricEnergy).smul
      continuous_id)

theorem continuous_penaltyDissipation :
    Continuous
      (penaltyDissipation :
        RealVeroneseSpace n k → ℝ) := by
  change Continuous
    (fun y : RealVeroneseSpace n k ↦
      ∑ a, (multinomialWeight a : ℝ) *
        penaltySphereGradient y a * penaltySphereGradient y a)
  apply continuous_finsetSum
  intro a _
  exact
    (continuous_const.mul
      (continuous_apply a |>.comp continuous_penaltySphereGradient)).mul
        (continuous_apply a |>.comp continuous_penaltySphereGradient)

theorem penaltyDissipation_nonneg
    (y : RealVeroneseSpace n k) :
    0 ≤ penaltyDissipation y := by
  rw [penaltyDissipation, weightedNormSq_eq_Q]
  exact Q_nonneg_real _

/-! ## Elementary scaling identities -/

theorem Q_inv_sqrt_Q_smul_eq_one
    (e : RealVeroneseSpace n k) (he : e ≠ 0) :
    Q ((Real.sqrt (Q e))⁻¹ • e) = 1 := by
  have hQpos : 0 < Q e :=
    (Q_nonneg_real e).lt_of_ne
      (fun hzero ↦
        he ((Q_eq_zero_iff_real e).mp hzero.symm))
  have hsqrt : Real.sqrt (Q e) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hQpos)
  rw [Q_smul, inv_pow, Real.sq_sqrt (le_of_lt hQpos)]
  field_simp

theorem sqrt_Q_pos_of_ne_zero
    (e : RealVeroneseSpace n k) (he : e ≠ 0) :
    0 < Real.sqrt (Q e) := by
  rw [Real.sqrt_pos]
  exact
    (Q_nonneg_real e).lt_of_ne
      (fun hzero ↦
        he ((Q_eq_zero_iff_real e).mp hzero.symm))

/-- The reciprocal scales used simultaneously as candidate coercivity
constants and tube radii. -/
def morseBottScale (m : ℕ) : ℝ :=
  1 / ((m : ℝ) + 1)

theorem morseBottScale_pos (m : ℕ) :
    0 < morseBottScale m := by
  unfold morseBottScale
  positivity

theorem morseBottScale_tendsto_zero :
    Tendsto morseBottScale atTop (𝓝 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem sqrt_Q_smul_inv_sqrt_Q_smul
    (e : RealVeroneseSpace n k) (he : e ≠ 0) :
    Real.sqrt (Q e) • ((Real.sqrt (Q e))⁻¹ • e) = e := by
  rw [smul_smul, mul_inv_cancel₀
    (ne_of_gt (sqrt_Q_pos_of_ne_zero e he)), one_smul]

theorem toricPenalty_div_sq_eq_sum_chart_normalized
    (y : RealVeroneseSpace n k) (hk : 1 ≤ k) (i : Fin n)
    (ρ : ℝ) (v : RealVeroneseSpace n k)
    (hρ : ρ ≠ 0)
    (herr : affineConeError y hk i = ρ • v) :
    toricPenalty y / ρ ^ 2 =
      ∑ r : ToricRelationIndex n k,
        (toricRelationDifferential r (affineConeChart y hk i) v +
          ρ * toricRelation r v) ^ 2 := by
  rw [toricPenalty, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  rw [← div_pow,
    toricRelation_div_eq_differential_add
      r y hk i ρ v hρ herr]

/-- There is a reciprocal integer scale which is simultaneously a tube
radius and a coercivity constant.

The proof is by contradiction.  If every reciprocal scale failed, choose
a bad point at each scale.  Compactness first produces a limiting toric
point `p`.  In an affine chart about `p`, subtract the exact reconstructed
cone point and normalize the error to weighted norm one.  A second compact
subsequence gives a limiting error `vlim`.

The failed estimates force the normalized spherical gradient to tend to
zero.  The exact quadratic relation expansion then says that the limiting
sum of squares of all relation differentials is zero.  Since `vlim`
vanishes in all chart coordinates, the one-token transfer kernel lemma
forces `vlim=0`, contradicting its weighted norm one. -/
theorem exists_morseBottScale_coercivity (hk : 1 ≤ k) :
    ∃ m : ℕ,
      ∀ y : RealVeroneseSpace n k,
        Q y = 1 →
          completeToricEnergy y ≤ morseBottScale m →
            morseBottScale m * completeToricEnergy y ≤
              penaltyDissipation y := by
  by_contra hcontra
  push Not at hcontra
  choose y hyQ hyW hyfail using hcontra
  have hyWpos (m : ℕ) :
      0 < completeToricEnergy (y m) := by
    have hnonneg := toricPenalty_nonneg_real (y m)
    have hDnonneg := penaltyDissipation_nonneg (y m)
    by_contra hnot
    have hzero : completeToricEnergy (y m) = 0 :=
      le_antisymm (le_of_not_gt hnot) hnonneg
    have hbad := hyfail m
    rw [hzero, mul_zero] at hbad
    exact (not_lt_of_ge hDnonneg) hbad
  have hyWtendsto :
      Tendsto (fun m ↦ completeToricEnergy (y m))
        atTop (𝓝 0) := by
    exact squeeze_zero
      (fun m ↦ toricPenalty_nonneg_real (y m))
      (fun m ↦ hyW m)
      morseBottScale_tendsto_zero
  obtain ⟨p, hpQ, φ, hφmono, hφtendsto⟩ :=
    isCompact_weightedUnitSphere.tendsto_subseq
      (x := y) (fun m ↦ hyQ m)
  change Q p = 1 at hpQ
  have hpW : completeToricEnergy p = 0 := by
    have hzero :
        (0 : ℝ) = completeToricEnergy p :=
      tendsto_nhds_unique
        (hyWtendsto.comp hφmono.tendsto_atTop)
        (by
          simpa only [Function.comp_apply] using
            continuous_completeToricEnergy.continuousAt.tendsto.comp
              hφtendsto)
    exact hzero.symm
  have hp0 : p ≠ 0 := by
    intro hpzero
    have hQzero : Q p = 0 :=
      (Q_eq_zero_iff_real p).2 hpzero
    linarith
  have hpToric : p ∈ toricZeroSet (R := ℝ) n k :=
    (toricPenalty_eq_zero_iff_mem_toricZeroSet_real p).mp hpW
  obtain ⟨i, hpure⟩ :=
    exists_pureMultiIndex_ne_zero hk hpToric hp0
  have hpureEventually :
      ∀ᶠ m in atTop,
        y (φ m) (pureMultiIndex i) ≠ 0 := by
    have ht :
        Tendsto (fun m ↦ y (φ m) (pureMultiIndex i))
          atTop (𝓝 (p (pureMultiIndex i))) := by
      simpa only [Function.comp_apply] using
        (tendsto_pi_nhds.mp hφtendsto (pureMultiIndex i))
    exact ht.eventually_ne hpure
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hpureEventually)
  let z : ℕ → RealVeroneseSpace n k :=
    fun m ↦ y (φ (m + N))
  have hzPure (m : ℕ) :
      z m (pureMultiIndex i) ≠ 0 := by
    exact hN (m + N) (Nat.le_add_left N m)
  have hzTendsto : Tendsto z atTop (𝓝 p) := by
    exact hφtendsto.comp (tendsto_add_atTop_nat N)
  let C : ℕ → RealVeroneseSpace n k :=
    fun m ↦ affineConeChart (z m) hk i
  let e : ℕ → RealVeroneseSpace n k :=
    fun m ↦ affineConeError (z m) hk i
  let ρ : ℕ → ℝ :=
    fun m ↦ Real.sqrt (Q (e m))
  let v : ℕ → RealVeroneseSpace n k :=
    fun m ↦ (ρ m)⁻¹ • e m
  have hchartP : affineConeChart p hk i = p :=
    affineConeChart_eq_of_mem_toricZeroSet p hk hpToric i hpure
  have hCTendsto : Tendsto C atTop (𝓝 p) := by
    simpa only [C, hchartP] using
      (continuousAt_affineConeChart p hk i hpure).tendsto.comp
        hzTendsto
  have heTendsto : Tendsto e atTop (𝓝 0) := by
    simpa only [e, affineConeError, sub_self] using
      hzTendsto.sub hCTendsto
  have heNe (m : ℕ) : e m ≠ 0 := by
    exact affineConeError_ne_zero_of_toricPenalty_ne_zero
      (z m) hk i (ne_of_gt (hyWpos (φ (m + N))))
  have hQePos (m : ℕ) : 0 < Q (e m) := by
    have hQne : Q (e m) ≠ 0 := by
      intro hzero
      exact heNe m ((Q_eq_zero_iff_real (e m)).mp hzero)
    exact lt_of_le_of_ne (Q_nonneg_real (e m)) hQne.symm
  have hρPos (m : ℕ) : 0 < ρ m :=
    Real.sqrt_pos.2 (hQePos m)
  have herr (m : ℕ) : e m = ρ m • v m := by
    funext a
    simp only [v, Pi.smul_apply, smul_eq_mul]
    field_simp [ne_of_gt (hρPos m)]
  have hvQ (m : ℕ) : Q (v m) = 1 := by
    change Q ((ρ m)⁻¹ • e m) = 1
    rw [Q_smul]
    have hsqrt : ρ m ^ 2 = Q (e m) := by
      exact Real.sq_sqrt (Q_nonneg_real (e m))
    rw [inv_pow, hsqrt]
    exact inv_mul_cancel₀ (ne_of_gt (hQePos m))
  have hvEdge (m : ℕ) (j : Fin n) :
      v m (edgeMultiIndex hk i j) = 0 := by
    change (ρ m)⁻¹ * e m (edgeMultiIndex hk i j) = 0
    rw [show e m (edgeMultiIndex hk i j) = 0 by
      exact affineConeError_edge (z m) hk i j (hzPure m)]
    ring
  have hρTendsto : Tendsto ρ atTop (𝓝 0) := by
    have hQe :
        Tendsto (fun m ↦ Q (e m)) atTop (𝓝 0) := by
      have hQzero :
          Q (0 : RealVeroneseSpace n k) = 0 :=
        (Q_eq_zero_iff_real _).2 rfl
      simpa only [Function.comp_apply, hQzero] using
        continuous_Q_real.continuousAt.tendsto.comp heTendsto
    simpa only [ρ, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hQe
  obtain ⟨vlim, hvlimQ, θ, hθmono, hvTendsto⟩ :=
    isCompact_weightedUnitSphere.tendsto_subseq
      (x := v) (fun m ↦ hvQ m)
  change Q vlim = 1 at hvlimQ
  have hzSubTendsto :
      Tendsto (z ∘ θ) atTop (𝓝 p) :=
    hzTendsto.comp hθmono.tendsto_atTop
  have hCSubTendsto :
      Tendsto (C ∘ θ) atTop (𝓝 p) :=
    hCTendsto.comp hθmono.tendsto_atTop
  have heSubTendsto :
      Tendsto (e ∘ θ) atTop (𝓝 0) :=
    heTendsto.comp hθmono.tendsto_atTop
  have hρSubTendsto :
      Tendsto (ρ ∘ θ) atTop (𝓝 0) :=
    hρTendsto.comp hθmono.tendsto_atTop
  have hvlimEdge (j : Fin n) :
      vlim (edgeMultiIndex hk i j) = 0 := by
    have ht :=
      tendsto_pi_nhds.mp hvTendsto (edgeMultiIndex hk i j)
    have hz :
        Tendsto
          (fun m ↦ v (θ m) (edgeMultiIndex hk i j))
          atTop (𝓝 0) := by
      simpa only [hvEdge] using
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
    exact (tendsto_nhds_unique hz ht).symm
  let A : ℕ → ToricRelationIndex n k → ℝ :=
    fun m r ↦ toricRelation r (z (θ m)) / ρ (θ m)
  let alim : ToricRelationIndex n k → ℝ :=
    fun r ↦ toricRelationDifferential r p vlim
  have hAeq (m : ℕ) (r : ToricRelationIndex n k) :
      A m r =
        toricRelationDifferential r (C (θ m)) (v (θ m)) +
          ρ (θ m) * toricRelation r (v (θ m)) := by
    have hexp :=
      toricRelation_div_eq_differential_add
        r (z (θ m)) hk i (ρ (θ m)) (v (θ m))
        (ne_of_gt (hρPos (θ m))) (by
          simpa only [e] using herr (θ m))
    simpa only [A, C] using hexp
  have hdqTendsto (r : ToricRelationIndex n k) :
      Tendsto
        (fun m ↦
          toricRelationDifferential r (C (θ m)) (v (θ m)))
        atTop (𝓝 (toricRelationDifferential r p vlim)) := by
    unfold toricRelationDifferential
    exact
      ((((tendsto_pi_nhds.mp hvTendsto r.alpha).mul
          (tendsto_pi_nhds.mp hCSubTendsto r.beta)).add
        ((tendsto_pi_nhds.mp hCSubTendsto r.alpha).mul
          (tendsto_pi_nhds.mp hvTendsto r.beta))).sub
        (((tendsto_pi_nhds.mp hvTendsto r.gamma).mul
          (tendsto_pi_nhds.mp hCSubTendsto r.delta)).add
        ((tendsto_pi_nhds.mp hCSubTendsto r.gamma).mul
          (tendsto_pi_nhds.mp hvTendsto r.delta))))
  have hqvTendsto (r : ToricRelationIndex n k) :
      Tendsto (fun m ↦ toricRelation r (v (θ m)))
        atTop (𝓝 (toricRelation r vlim)) := by
    simpa only [Function.comp_apply] using
      (continuous_toricRelation_real r).continuousAt.tendsto.comp
        hvTendsto
  have hATendsto (r : ToricRelationIndex n k) :
      Tendsto (fun m ↦ A m r) atTop (𝓝 (alim r)) := by
    have hsum :
        Tendsto
          (fun m ↦
            toricRelationDifferential r (C (θ m)) (v (θ m)) +
              ρ (θ m) * toricRelation r (v (θ m)))
          atTop (𝓝 (alim r)) := by
      simpa only [alim, zero_mul, add_zero] using
        (hdqTendsto r).add
          (hρSubTendsto.mul (hqvTendsto r))
    refine hsum.congr' ?_
    exact Eventually.of_forall fun m ↦ (hAeq m r).symm
  let S : ℕ → ℝ :=
    fun m ↦ ∑ r : ToricRelationIndex n k, A m r ^ 2
  let Slim : ℝ :=
    ∑ r : ToricRelationIndex n k, alim r ^ 2
  have hSTendsto : Tendsto S atTop (𝓝 Slim) := by
    unfold S Slim
    apply tendsto_finsetSum
    intro r _
    exact (hATendsto r).pow 2
  have hW_eq (m : ℕ) :
      completeToricEnergy (z (θ m)) =
        ρ (θ m) ^ 2 * S m := by
    unfold completeToricEnergy toricPenalty S A
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    field_simp [ne_of_gt (hρPos (θ m))]
  let μ : ℕ → ℕ :=
    fun m ↦ φ (θ m + N)
  have hzμ (m : ℕ) : z (θ m) = y (μ m) := rfl
  have hμTendsto : Tendsto μ atTop atTop := by
    exact hφmono.tendsto_atTop.comp
      ((tendsto_add_atTop_nat N).comp hθmono.tendsto_atTop)
  have hscaleTendsto :
      Tendsto (morseBottScale ∘ μ) atTop (𝓝 0) :=
    morseBottScale_tendsto_zero.comp hμTendsto
  let s : ℕ → RealVeroneseSpace n k :=
    fun m ↦ penaltySphereGradient (z (θ m))
  let t : ℕ → RealVeroneseSpace n k :=
    fun m ↦ (ρ (θ m))⁻¹ • s m
  have hD_eq_Qs (m : ℕ) :
      penaltyDissipation (z (θ m)) = Q (s m) := by
    rw [penaltyDissipation, weightedNormSq_eq_Q]
  have hQt_le (m : ℕ) :
      Q (t m) ≤ morseBottScale (μ m) * S m := by
    have hbad := hyfail (μ m)
    rw [← hzμ m, hD_eq_Qs m, hW_eq m] at hbad
    change Q ((ρ (θ m))⁻¹ • s m) ≤
      morseBottScale (μ m) * S m
    rw [Q_smul]
    calc
      (ρ (θ m))⁻¹ ^ 2 * Q (s m) ≤
          (ρ (θ m))⁻¹ ^ 2 *
            (morseBottScale (μ m) *
              (ρ (θ m) ^ 2 * S m)) :=
        mul_le_mul_of_nonneg_left (le_of_lt hbad) (sq_nonneg _)
      _ = morseBottScale (μ m) * S m := by
        field_simp [ne_of_gt (hρPos (θ m))]
  have hQtTendsto :
      Tendsto (fun m ↦ Q (t m)) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun m ↦ Q_nonneg_real (t m))
      hQt_le
    simpa only [Function.comp_apply, zero_mul] using
      hscaleTendsto.mul hSTendsto
  let B : ℕ → ℝ :=
    fun m ↦ weightedInner (t m) (v (θ m))
  have hAbsB_le (m : ℕ) :
      |B m| ≤ Real.sqrt (Q (t m)) := by
    apply Real.abs_le_sqrt
    have hcs := weightedInner_sq_le (t m) (v (θ m))
    rw [hvQ, mul_one] at hcs
    exact hcs
  have hSqrtQtTendsto :
      Tendsto (fun m ↦ Real.sqrt (Q (t m))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hQtTendsto
  have hAbsBTendsto :
      Tendsto (fun m ↦ |B m|) atTop (𝓝 0) :=
    squeeze_zero (fun m ↦ abs_nonneg (B m)) hAbsB_le
      hSqrtQtTendsto
  have hBTendsto : Tendsto B atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero B).2 hAbsBTendsto
  have hInnerZVTendsto :
      Tendsto
        (fun m ↦ weightedInner (z (θ m)) (v (θ m)))
        atTop (𝓝 (weightedInner p vlim)) := by
    unfold weightedInner
    apply tendsto_finsetSum
    intro a _
    exact
      ((tendsto_const_nhds.mul
        (tendsto_pi_nhds.mp hzSubTendsto a)).mul
          (tendsto_pi_nhds.mp hvTendsto a))
  let R : ℕ → ℝ :=
    fun m ↦
      weightedInner
        ((ρ (θ m))⁻¹ •
          penaltyAmbientGradient (z (θ m)))
        (v (θ m))
  have hgradDecomp (m : ℕ) :
      penaltyAmbientGradient (z (θ m)) =
        s m +
          (4 * completeToricEnergy (z (θ m))) • z (θ m) := by
    exact ambientQGradient_decomposition
      (z (θ m)) (toricPenalty (z (θ m)))
        (ordinaryPenaltyGradientReal (z (θ m)))
  have hR_eq (m : ℕ) :
      R m =
        B m +
          4 * ρ (θ m) * S m *
            weightedInner (z (θ m)) (v (θ m)) := by
    change
      weightedInner
          ((ρ (θ m))⁻¹ • penaltyAmbientGradient (z (θ m)))
          (v (θ m)) =
        _
    rw [weightedInner_comm, weightedInner_smul_right,
      weightedInner_comm]
    rw [hgradDecomp m]
    have hinnerDecomp :
        weightedInner
            (s m +
              (4 * completeToricEnergy (z (θ m))) • z (θ m))
            (v (θ m)) =
          weightedInner (s m) (v (θ m)) +
            (4 * completeToricEnergy (z (θ m))) *
              weightedInner (z (θ m)) (v (θ m)) := by
      rw [weightedInner_comm, weightedInner_add_right,
        weightedInner_smul_right,
        weightedInner_comm (v (θ m)) (s m),
        weightedInner_comm (v (θ m)) (z (θ m))]
    rw [hinnerDecomp]
    have hB :
        B m =
          (ρ (θ m))⁻¹ *
            weightedInner (s m) (v (θ m)) := by
      change
        weightedInner ((ρ (θ m))⁻¹ • s m) (v (θ m)) = _
      rw [weightedInner_comm,
        weightedInner_smul_right, weightedInner_comm]
    rw [hB, hW_eq m]
    field_simp [ne_of_gt (hρPos (θ m))]
  have hRemainderTendsto :
      Tendsto
        (fun m ↦
          4 * ρ (θ m) * S m *
            weightedInner (z (θ m)) (v (θ m)))
        atTop (𝓝 0) := by
    simpa only [Function.comp_apply, zero_mul, mul_zero] using
      (((tendsto_const_nhds :
          Tendsto (fun _ : ℕ ↦ (4 : ℝ)) atTop (𝓝 4)).mul
        hρSubTendsto).mul hSTendsto).mul
        hInnerZVTendsto
  have hRTendsto : Tendsto R atTop (𝓝 0) := by
    have hsum := hBTendsto.add hRemainderTendsto
    simpa only [zero_add] using
      hsum.congr' (Eventually.of_forall fun m ↦ (hR_eq m).symm)
  have hdqyTendsto (r : ToricRelationIndex n k) :
      Tendsto
        (fun m ↦
          toricRelationDifferential r (z (θ m)) (v (θ m)))
        atTop (𝓝 (alim r)) := by
    unfold alim toricRelationDifferential
    exact
      ((((tendsto_pi_nhds.mp hvTendsto r.alpha).mul
          (tendsto_pi_nhds.mp hzSubTendsto r.beta)).add
        ((tendsto_pi_nhds.mp hzSubTendsto r.alpha).mul
          (tendsto_pi_nhds.mp hvTendsto r.beta))).sub
        (((tendsto_pi_nhds.mp hvTendsto r.gamma).mul
          (tendsto_pi_nhds.mp hzSubTendsto r.delta)).add
        ((tendsto_pi_nhds.mp hzSubTendsto r.gamma).mul
          (tendsto_pi_nhds.mp hvTendsto r.delta))))
  let P : ℕ → ℝ :=
    fun m ↦
      ∑ r : ToricRelationIndex n k,
        2 * A m r *
          toricRelationDifferential r (z (θ m)) (v (θ m))
  have hR_eq_P (m : ℕ) : R m = P m := by
    change
      weightedInner
          ((ρ (θ m))⁻¹ • penaltyAmbientGradient (z (θ m)))
          (v (θ m)) =
        ∑ r : ToricRelationIndex n k,
          2 * A m r *
            toricRelationDifferential r (z (θ m)) (v (θ m))
    rw [weightedInner_comm, weightedInner_smul_right,
      weightedInner_comm,
      ← toricPenaltyDirectional_eq_weightedInner]
    unfold toricPenaltyDirectional
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    simp only [A]
    field_simp [ne_of_gt (hρPos (θ m))]
  have hPTendsto :
      Tendsto P atTop (𝓝 (2 * Slim)) := by
    have hsum :
        Tendsto
          (fun m ↦
            ∑ r : ToricRelationIndex n k,
              2 * A m r *
                toricRelationDifferential r
                  (z (θ m)) (v (θ m)))
          atTop
          (𝓝
            (∑ r : ToricRelationIndex n k,
              2 * alim r * alim r)) := by
      apply tendsto_finsetSum
      intro r _
      exact (tendsto_const_nhds.mul (hATendsto r)).mul
        (hdqyTendsto r)
    have hlimit :
        (∑ r : ToricRelationIndex n k,
          2 * alim r * alim r) = 2 * Slim := by
      unfold Slim
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    simpa only [P, hlimit] using hsum
  have hPZeroTendsto : Tendsto P atTop (𝓝 0) :=
    hRTendsto.congr'
      (Eventually.of_forall fun m ↦ hR_eq_P m)
  have hSlim : Slim = 0 := by
    have hzero : (0 : ℝ) = 2 * Slim :=
      tendsto_nhds_unique hPZeroTendsto hPTendsto
    linarith
  have halim (r : ToricRelationIndex n k) : alim r = 0 := by
    have hrsq :
        alim r ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun q _ ↦ sq_nonneg (alim q))).mp hSlim
          r (Finset.mem_univ r)
    exact sq_eq_zero_iff.mp hrsq
  have hvlimZero : vlim = 0 := by
    apply
      eq_zero_of_toricRelationDifferential_eq_zero_of_edge_eq_zero
        hk p vlim i hpure hvlimEdge
    intro r
    exact halim r
  rw [hvlimZero] at hvlimQ
  have hQzero :
      Q (0 : RealVeroneseSpace n k) = 0 :=
    (Q_eq_zero_iff_real _).2 rfl
  rw [hQzero] at hvlimQ
  norm_num at hvlimQ

/-- Effective Morse--Bott coercivity with positive real constants. -/
theorem exists_positive_morseBott_coercivity_constants
    (hk : 1 ≤ k) :
    ∃ c η : ℝ,
      0 < c ∧ 0 < η ∧
        ∀ y : RealVeroneseSpace n k,
          Q y = 1 →
            completeToricEnergy y ≤ η →
              c * completeToricEnergy y ≤ penaltyDissipation y := by
  obtain ⟨m, hm⟩ := exists_morseBottScale_coercivity (n := n) hk
  exact
    ⟨morseBottScale m, morseBottScale m,
      morseBottScale_pos m, morseBottScale_pos m, hm⟩

/-- The constants may be chosen rational, as claimed in the effective
form of the paper.  Concretely, both are the same reciprocal integer
`1/(m+1)`. -/
theorem exists_positive_rational_morseBott_coercivity_constants
    (hk : 1 ≤ k) :
    ∃ c η : ℚ,
      0 < c ∧ 0 < η ∧
        ∀ y : RealVeroneseSpace n k,
          Q y = 1 →
            completeToricEnergy y ≤ (η : ℝ) →
              (c : ℝ) * completeToricEnergy y ≤
                penaltyDissipation y := by
  obtain ⟨m, hm⟩ := exists_morseBottScale_coercivity (n := n) hk
  let q : ℚ := 1 / ((m : ℚ) + 1)
  have hqpos : 0 < q := by
    unfold q
    positivity
  have hqcast : (q : ℝ) = morseBottScale m := by
    simp [q, morseBottScale]
  refine ⟨q, q, hqpos, hqpos, ?_⟩
  intro y hQ hW
  rw [hqcast] at hW ⊢
  exact hm y hQ hW
end

end HGAS.Veronese
