import HGAS.Veronese.AffineConeChart
import HGAS.Veronese.CompactTransverseBounds
import Mathlib.Tactic

/-!
# Quadratic distance to the normalized Veronese cone

Let `W(y) = ∑ r, q_r(y)^2` be the complete toric energy, the sum of the
squares of all balanced quadratic Veronese relations.  This module proves
the global error bound

```
dist_Q(y, 𝒱 ∩ {Q=1})^2 ≤ C W(y)      for all y with Q(y) = 1,
```

where `dist_Q` is the multinomially weighted metric.

The proof is elementary.

* **Chart estimate.**  If `|y_(k e_i)| ≥ δ`, the explicit affine chart
  point `π = affineConeChart y hk i` agrees with `y` in the pure and
  adjacent coordinates.  For any other multiindex `α`, a one-token
  transfer quadric gives
  `(y_α - π_α) y_(k e_i) = q(y) + (y_α' - π_α') y_((k-1)e_i+e_j)`,
  where `α'` is one step closer to the vertex `k e_i`.  Induction on
  `k - α_i` gives `|y_α - π_α| ≤ C_δ sqrt(W(y))`.
* **Normalization.**  Rescaling `π` to `Q=1` costs at most a factor
  `16` in the squared weighted distance (Cauchy--Schwarz).
* **Compactness.**  On `Q=1` the continuous function
  `W(y) + ∑ i |y_(k e_i)|` is positive, because every nonzero toric point
  has a nonzero pure coordinate.  Hence either some pure coordinate is
  uniformly large, or `W` itself is uniformly large; in the latter case
  any normalized cone point is at squared distance at most `4`.
-/

namespace HGAS.Veronese

open scoped BigOperators

noncomputable section

variable {n k : ℕ}

/-! ## Elementary weighted-metric facts -/

/-- The weighted norm square of a difference is at most twice the sum of
the weighted norm squares. -/
theorem Q_sub_le_two_mul_add
    (u v : RealVeroneseSpace n k) :
    Q (u - v) ≤ 2 * Q u + 2 * Q v := by
  unfold Q
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  have hw : (0 : ℝ) ≤ multinomialWeight a := Nat.cast_nonneg _
  simp only [Pi.sub_apply]
  nlinarith [mul_nonneg hw (sq_nonneg (u a + v a))]

/-- Every coordinate of a point of `Q=1` has absolute value at most one. -/
theorem abs_apply_le_one_of_Q_eq_one
    {y : RealVeroneseSpace n k} (hQ : Q y = 1)
    (a : MultiIndex n k) :
    |y a| ≤ 1 := by
  have hnorm := norm_le_one_of_Q_eq_one y hQ
  have hcoord : ‖y a‖ ≤ ‖y‖ := norm_le_pi_norm y a
  rw [Real.norm_eq_abs] at hcoord
  linarith

/-- A nonzero point rescaled by the inverse weighted norm lies on
`Q=1`. -/
theorem Q_inv_sqrt_Q_smul_of_ne_zero
    (e : RealVeroneseSpace n k) (he : e ≠ 0) :
    Q ((Real.sqrt (Q e))⁻¹ • e) = 1 := by
  have hQpos : 0 < Q e :=
    (Q_nonneg_real e).lt_of_ne
      (fun hzero ↦ he ((Q_eq_zero_iff_real e).mp hzero.symm))
  rw [Q_smul, inv_pow, Real.sq_sqrt (le_of_lt hQpos)]
  exact inv_mul_cancel₀ (ne_of_gt hQpos)

/-- Normalizing an approximating point to `Q=1` costs at most a factor
`16` in the squared weighted distance to a point of `Q=1`. -/
theorem weightedNormSq_sub_normalize_le
    (y π : RealVeroneseSpace n k) (hQ : Q y = 1) (hπ : π ≠ 0) :
    weightedNormSq (y - (Real.sqrt (Q π))⁻¹ • π) ≤
      16 * weightedNormSq (y - π) := by
  have hQπpos : 0 < Q π :=
    (Q_nonneg_real π).lt_of_ne
      (fun hzero ↦ hπ ((Q_eq_zero_iff_real π).mp hzero.symm))
  set t := Real.sqrt (Q π) with ht_def
  have htpos : 0 < t := Real.sqrt_pos.2 hQπpos
  have htsq : t ^ 2 = Q π := Real.sq_sqrt (le_of_lt hQπpos)
  set c := weightedInner π y with hc_def
  have hcs : c ^ 2 ≤ t ^ 2 := by
    have h := weightedInner_sq_le π y
    rw [hQ, mul_one, ← htsq] at h
    exact h
  have hcabs : |c| ≤ t := abs_le_of_sq_le_sq hcs (le_of_lt htpos)
  set u := c / t with hu_def
  have hcu : c = u * t := by
    rw [hu_def]
    field_simp
  have hu1 : u ≤ 1 := by
    rw [hu_def, div_le_one htpos]
    exact le_trans (le_abs_self c) hcabs
  have hu2 : -1 ≤ u := by
    rw [hu_def, le_div_iff₀ htpos]
    have := neg_abs_le c
    linarith
  have hL : weightedNormSq (y - t⁻¹ • π) = 2 - 2 * u := by
    rw [weightedNormSq_sub_smul, weightedNormSq_eq_Q,
      weightedNormSq_eq_Q, hQ, ← hc_def, ← htsq, hcu]
    field_simp
    ring
  have hD : weightedNormSq (y - π) = 1 - 2 * u * t + t ^ 2 := by
    have h := weightedNormSq_sub_smul π y (1 : ℝ)
    rw [one_smul] at h
    rw [h, weightedNormSq_eq_Q, weightedNormSq_eq_Q, hQ, ← hc_def,
      ← htsq, hcu]
    ring
  rw [hL, hD]
  nlinarith [mul_nonneg (sub_nonneg.2 hu2) (sq_nonneg (1 - t)),
    mul_nonneg (sub_nonneg.2 hu1)
      (add_nonneg (le_of_lt htpos) (sq_nonneg t))]

/-! ## A normalized cone point always exists -/

/-- If `Q=1` is nonempty, it contains a normalized Veronese point. -/
theorem exists_cone_point_of_Q_eq_one
    (hk : 1 ≤ k) {y : RealVeroneseSpace n k} (hQ : Q y = 1) :
    ∃ p : RealVeroneseSpace n k,
      Q p = 1 ∧ completeToricEnergy p = 0 := by
  have hy0 : y ≠ 0 := by
    intro hzero
    rw [(Q_eq_zero_iff_real y).2 hzero] at hQ
    norm_num at hQ
  obtain ⟨a, _⟩ := Function.ne_iff.mp hy0
  have hsum : (∑ i, a.1 i) ≠ 0 := by
    rw [multiIndex_degree a]
    omega
  obtain ⟨i, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hunit : ∑ j, (Pi.single i (1 : ℝ) : Fin n → ℝ) j ^ 2 = 1 := by
    classical
    simp [Pi.single_apply]
  obtain ⟨_, hpQ⟩ :=
    veronese_mem_toricSphereZeroSet_of_unit (k := k)
      (Pi.single i (1 : ℝ)) hunit
  exact ⟨veroneseMap (k := k) (Pi.single i (1 : ℝ)), hpQ,
    toricPenalty_veronese _⟩

/-! ## The affine chart estimate -/

/-- One-token transfer identity for the chart error. -/
theorem sub_affineConeChart_mul_pure
    (y : RealVeroneseSpace n k) (hk : 1 ≤ k) (i j : Fin n)
    (hji : j ≠ i) (a : MultiIndex n k) (hj : 0 < a.1 j)
    (hpure : y (pureMultiIndex i) ≠ 0) :
    (y a - affineConeChart y hk i a) * y (pureMultiIndex i) =
      toricRelation (baseTransferRelation a hk i j hji hj) y +
        (y (transferMultiIndex a i j hji.symm hj) -
            affineConeChart y hk i
              (transferMultiIndex a i j hji.symm hj)) *
          y (edgeMultiIndex hk i j) := by
  have hz :=
    affineConeChart_mem_toricZeroSet y hk i
      (baseTransferRelation a hk i j hji hj)
  have hpureChart :
      affineConeChart y hk i (pureMultiIndex i) =
        y (pureMultiIndex i) := by
    simpa using affineConeChart_edge y hk i i hpure
  have hedgeChart := affineConeChart_edge y hk i j hpure
  simp only [toricRelation, baseTransferRelation] at hz ⊢
  rw [hpureChart, hedgeChart] at hz
  linear_combination -hz

/-- Coordinatewise chart estimate: with `M |y_(k e_i)| ≥ 1`, every
coordinate of the chart error is bounded by `m M^m sqrt(W)`, where
`m = k - α_i`. -/
theorem abs_sub_affineConeChart_le_aux
    (hk : 1 ≤ k) (y : RealVeroneseSpace n k) (hQ : Q y = 1)
    (i : Fin n) (M : ℝ) (hM : 1 ≤ M)
    (hpure : 1 ≤ M * |y (pureMultiIndex i)|)
    (a : MultiIndex n k) :
    |y a - affineConeChart y hk i a| ≤
      ((k - a.1 i : ℕ) : ℝ) * M ^ (k - a.1 i) *
        Real.sqrt (completeToricEnergy y) := by
  have hpure0 : y (pureMultiIndex i) ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero, mul_zero] at hpure
    norm_num at hpure
  have hR : 0 ≤ Real.sqrt (completeToricEnergy y) := Real.sqrt_nonneg _
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  generalize hm : k - a.1 i = m
  induction m using Nat.strong_induction_on generalizing a with
  | h m ih =>
      by_cases hai : a.1 i = k
      · have ha : a = pureMultiIndex i :=
          multiIndex_eq_pure_of_apply_eq_degree a i hai
        subst a
        have hzero :
            y (pureMultiIndex i) -
                affineConeChart y hk i (pureMultiIndex i) = 0 := by
          have h := affineConeChart_edge y hk i i hpure0
          simp only [edgeMultiIndex_same] at h
          rw [h, sub_self]
        rw [hzero, abs_zero]
        positivity
      · have hailt : a.1 i < k :=
          lt_of_le_of_ne (multiIndex_apply_le_degree a i) hai
        obtain ⟨j, hji, hj⟩ :=
          exists_ne_base_apply_pos a i hailt
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        set ap := transferMultiIndex a i j hji.symm hj with hap_def
        have hapi : ap.1 i = a.1 i + 1 :=
          transferMultiIndex_apply_same a i j hji.symm hj
        have hIH :
            |y ap - affineConeChart y hk i ap| ≤
              (m' : ℝ) * M ^ m' *
                Real.sqrt (completeToricEnergy y) := by
          have h := ih m' (by omega) ap (by omega)
          exact h
        have hid :=
          sub_affineConeChart_mul_pure y hk i j hji a hj hpure0
        rw [← hap_def] at hid
        set X := |y a - affineConeChart y hk i a| with hX
        set Y := |y ap - affineConeChart y hk i ap| with hY
        set R := Real.sqrt (completeToricEnergy y) with hR_def
        have hq :
            |toricRelation (baseTransferRelation a hk i j hji hj) y| ≤
              R :=
          abs_toricRelation_le_sqrt_completeToricEnergy _ y
        have he : |y (edgeMultiIndex hk i j)| ≤ 1 :=
          abs_apply_le_one_of_Q_eq_one hQ _
        have hX0 : 0 ≤ X := abs_nonneg _
        have hY0 : 0 ≤ Y := abs_nonneg _
        have hXs :
            X * |y (pureMultiIndex i)| ≤ R + Y := by
          calc
            X * |y (pureMultiIndex i)| =
                |(y a - affineConeChart y hk i a) *
                  y (pureMultiIndex i)| := by
              rw [abs_mul]
            _ = |toricRelation (baseTransferRelation a hk i j hji hj) y +
                  (y ap - affineConeChart y hk i ap) *
                    y (edgeMultiIndex hk i j)| := by
              rw [hid]
            _ ≤ |toricRelation (baseTransferRelation a hk i j hji hj) y| +
                  Y * |y (edgeMultiIndex hk i j)| := by
              rw [← abs_mul]
              exact abs_add_le _ _
            _ ≤ R + Y * 1 := by
              gcongr
            _ = R + Y := by ring
        have hMpow : M ≤ M ^ (m' + 1) :=
          le_self_pow₀ hM (by omega)
        have hYM : M * Y ≤ (m' : ℝ) * M ^ (m' + 1) * R := by
          calc
            M * Y ≤ M * ((m' : ℝ) * M ^ m' * R) :=
              mul_le_mul_of_nonneg_left hIH hM0
            _ = (m' : ℝ) * M ^ (m' + 1) * R := by ring
        calc
          X ≤ X * (M * |y (pureMultiIndex i)|) :=
            le_mul_of_one_le_right hX0 hpure
          _ = M * (X * |y (pureMultiIndex i)|) := by ring
          _ ≤ M * (R + Y) :=
            mul_le_mul_of_nonneg_left hXs hM0
          _ = M * R + M * Y := by ring
          _ ≤ M ^ (m' + 1) * R + (m' : ℝ) * M ^ (m' + 1) * R := by
            gcongr
          _ = ((m' + 1 : ℕ) : ℝ) * M ^ (m' + 1) * R := by
            push_cast
            ring

/-- Uniform coordinatewise chart estimate. -/
theorem abs_sub_affineConeChart_le
    (hk : 1 ≤ k) (y : RealVeroneseSpace n k) (hQ : Q y = 1)
    (i : Fin n) (M : ℝ) (hM : 1 ≤ M)
    (hpure : 1 ≤ M * |y (pureMultiIndex i)|)
    (a : MultiIndex n k) :
    |y a - affineConeChart y hk i a| ≤
      (k : ℝ) * M ^ k * Real.sqrt (completeToricEnergy y) := by
  refine (abs_sub_affineConeChart_le_aux hk y hQ i M hM hpure a).trans ?_
  have hR : 0 ≤ Real.sqrt (completeToricEnergy y) := Real.sqrt_nonneg _
  have hcast : ((k - a.1 i : ℕ) : ℝ) ≤ k := by
    exact_mod_cast Nat.sub_le k (a.1 i)
  have hpow : M ^ (k - a.1 i) ≤ M ^ k :=
    pow_le_pow_right₀ hM (Nat.sub_le k (a.1 i))
  gcongr

/-- Weighted squared chart error is bounded by the complete energy. -/
theorem weightedNormSq_sub_affineConeChart_le
    (hk : 1 ≤ k) (y : RealVeroneseSpace n k) (hQ : Q y = 1)
    (i : Fin n) (M : ℝ) (hM : 1 ≤ M)
    (hpure : 1 ≤ M * |y (pureMultiIndex i)|) :
    weightedNormSq (y - affineConeChart y hk i) ≤
      ((∑ a : MultiIndex n k, (multinomialWeight a : ℝ)) *
          ((k : ℝ) * M ^ k) ^ 2) *
        completeToricEnergy y := by
  have hW : 0 ≤ completeToricEnergy y := toricPenalty_nonneg_real y
  rw [weightedNormSq_eq_Q]
  unfold Q
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _
  have hw : (0 : ℝ) ≤ multinomialWeight a := Nat.cast_nonneg _
  have habs := abs_sub_affineConeChart_le hk y hQ i M hM hpure a
  have hsq :
      (y a - affineConeChart y hk i a) ^ 2 ≤
        ((k : ℝ) * M ^ k) ^ 2 * completeToricEnergy y := by
    calc
      (y a - affineConeChart y hk i a) ^ 2 =
          |y a - affineConeChart y hk i a| ^ 2 := (sq_abs _).symm
      _ ≤ ((k : ℝ) * M ^ k * Real.sqrt (completeToricEnergy y)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = ((k : ℝ) * M ^ k) ^ 2 * completeToricEnergy y := by
        rw [mul_pow, Real.sq_sqrt hW]
  simp only [Pi.sub_apply]
  calc
    (multinomialWeight a : ℝ) * (y a - affineConeChart y hk i a) ^ 2 ≤
        (multinomialWeight a : ℝ) *
          (((k : ℝ) * M ^ k) ^ 2 * completeToricEnergy y) :=
      mul_le_mul_of_nonneg_left hsq hw
    _ = (multinomialWeight a : ℝ) * ((k : ℝ) * M ^ k) ^ 2 *
          completeToricEnergy y := by ring

/-! ## Compactness: a large pure coordinate or a large energy -/

/-- On `Q=1`, either the complete energy or some pure coordinate is
uniformly bounded below. -/
theorem exists_energy_or_pure_lower_bound (hk : 1 ≤ k) :
    ∃ η : ℝ, 0 < η ∧
      ∀ y : RealVeroneseSpace n k, Q y = 1 →
        η ≤ completeToricEnergy y ∨
          ∃ i : Fin n, η ≤ |y (pureMultiIndex i)| := by
  let h : RealVeroneseSpace n k → ℝ :=
    fun y ↦ completeToricEnergy y +
      ∑ i : Fin n, |y (pureMultiIndex i)|
  have hcont : Continuous h := by
    apply continuous_completeToricEnergy.add
    apply continuous_finsetSum
    intro i _
    exact (continuous_apply (pureMultiIndex i)).abs
  rcases (weightedUnitSphere n k).eq_empty_or_nonempty with hempty | hne
  · refine ⟨1, one_pos, ?_⟩
    intro y hQ
    have hy : y ∈ weightedUnitSphere n k := hQ
    rw [hempty] at hy
    exact hy.elim
  obtain ⟨y₀, hy₀, hmin⟩ :=
    isCompact_weightedUnitSphere.exists_isMinOn hne hcont.continuousOn
  have hy₀Q : Q y₀ = 1 := hy₀
  have hpos : 0 < h y₀ := by
    have hW0 : 0 ≤ completeToricEnergy y₀ := toricPenalty_nonneg_real y₀
    have hS0 : 0 ≤ ∑ i : Fin n, |y₀ (pureMultiIndex i)| :=
      Finset.sum_nonneg fun i _ ↦ abs_nonneg _
    by_contra hnot
    have hsum : h y₀ = 0 := le_antisymm (le_of_not_gt hnot) (add_nonneg hW0 hS0)
    have hWzero : completeToricEnergy y₀ = 0 := by
      simp only [h] at hsum
      linarith
    have hSzero : ∑ i : Fin n, |y₀ (pureMultiIndex i)| = 0 := by
      simp only [h] at hsum
      linarith
    have hy₀0 : y₀ ≠ 0 := by
      intro hzero
      rw [(Q_eq_zero_iff_real y₀).2 hzero] at hy₀Q
      norm_num at hy₀Q
    have hToric : y₀ ∈ toricZeroSet (R := ℝ) n k :=
      (toricPenalty_eq_zero_iff_mem_toricZeroSet_real y₀).mp hWzero
    obtain ⟨i, hi⟩ := exists_pureMultiIndex_ne_zero hk hToric hy₀0
    have hiZero :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ abs_nonneg (y₀ (pureMultiIndex j)))).mp
        hSzero i (Finset.mem_univ i)
    exact hi (abs_eq_zero.mp hiZero)
  set η₀ := h y₀ with hη₀
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine ⟨η₀ / (2 * ((n : ℝ) + 1)), by positivity, ?_⟩
  intro y hQ
  by_contra hfail
  push Not at hfail
  obtain ⟨hW, hpure⟩ := hfail
  have hy : y ∈ weightedUnitSphere n k := hQ
  have hle : η₀ ≤ h y := hmin hy
  have hS :
      ∑ i : Fin n, |y (pureMultiIndex i)| ≤
        (n : ℝ) * (η₀ / (2 * ((n : ℝ) + 1))) := by
    calc
      ∑ i : Fin n, |y (pureMultiIndex i)| ≤
          ∑ _i : Fin n, η₀ / (2 * ((n : ℝ) + 1)) :=
        Finset.sum_le_sum fun i _ ↦ le_of_lt (hpure i)
      _ = (n : ℝ) * (η₀ / (2 * ((n : ℝ) + 1))) := by
        simp
  have hhy :
      h y < η₀ / (2 * ((n : ℝ) + 1)) +
        (n : ℝ) * (η₀ / (2 * ((n : ℝ) + 1))) := by
    simp only [h]
    linarith
  have hcalc :
      η₀ / (2 * ((n : ℝ) + 1)) +
          (n : ℝ) * (η₀ / (2 * ((n : ℝ) + 1))) = η₀ / 2 := by
    field_simp
    ring
  rw [hcalc] at hhy
  linarith

/-! ## The global distance estimate -/

/-- **Quadratic distance to the normalized Veronese cone.**

There is a constant `C > 0` such that every point `y` of the weighted
unit sphere `Q=1` lies within squared weighted distance
`C · W(y)` of a normalized cone point `p` (that is, `Q p = 1` and
`W p = 0`). -/
theorem exists_coneDistanceSq_le_energy (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : RealVeroneseSpace n k, Q y = 1 →
      ∃ p : RealVeroneseSpace n k, Q p = 1 ∧ completeToricEnergy p = 0 ∧
        weightedNormSq (y - p) ≤ C * completeToricEnergy y := by
  obtain ⟨η, hη, hsplit⟩ := exists_energy_or_pure_lower_bound (n := n) hk
  set M : ℝ := max 1 η⁻¹ with hM_def
  have hM : 1 ≤ M := le_max_left _ _
  set A : ℝ :=
    (∑ a : MultiIndex n k, (multinomialWeight a : ℝ)) *
      ((k : ℝ) * M ^ k) ^ 2 with hA_def
  have hA : 0 ≤ A := by
    apply mul_nonneg
    · exact Finset.sum_nonneg fun a _ ↦ Nat.cast_nonneg _
    · exact sq_nonneg _
  refine ⟨16 * A + 4 / η, by positivity, ?_⟩
  intro y hQ
  have hW : 0 ≤ completeToricEnergy y := toricPenalty_nonneg_real y
  rcases hsplit y hQ with hWlarge | ⟨i, hpure⟩
  · obtain ⟨p, hpQ, hpW⟩ := exists_cone_point_of_Q_eq_one hk hQ
    refine ⟨p, hpQ, hpW, ?_⟩
    rw [weightedNormSq_eq_Q]
    have h4 : Q (y - p) ≤ 4 := by
      have h := Q_sub_le_two_mul_add y p
      rw [hQ, hpQ] at h
      linarith
    have h4W : 4 ≤ 4 / η * completeToricEnergy y := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hη]
      linarith
    nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hA]
  · have hMpure : 1 ≤ M * |y (pureMultiIndex i)| := by
      calc
        (1 : ℝ) = η⁻¹ * η := (inv_mul_cancel₀ (ne_of_gt hη)).symm
        _ ≤ M * |y (pureMultiIndex i)| := by
          apply mul_le_mul (le_max_right _ _) hpure (le_of_lt hη)
          exact le_trans zero_le_one hM
    have hpure0 : y (pureMultiIndex i) ≠ 0 := by
      intro hzero
      rw [hzero, abs_zero] at hpure
      linarith
    set π := affineConeChart y hk i with hπ_def
    have hπ0 : π ≠ 0 := by
      intro hzero
      have h := affineConeChart_edge y hk i i hpure0
      simp only [edgeMultiIndex_same] at h
      rw [← hπ_def, hzero] at h
      exact hpure0 (by simpa using h.symm)
    have hπW : completeToricEnergy π = 0 :=
      (toricPenalty_eq_zero_iff_mem_toricZeroSet_real π).mpr
        (affineConeChart_mem_toricZeroSet y hk i)
    refine ⟨(Real.sqrt (Q π))⁻¹ • π,
      Q_inv_sqrt_Q_smul_of_ne_zero π hπ0, ?_, ?_⟩
    · change toricPenalty ((Real.sqrt (Q π))⁻¹ • π) = 0
      rw [toricPenalty_smul]
      change (Real.sqrt (Q π))⁻¹ ^ 4 * completeToricEnergy π = 0
      rw [hπW, mul_zero]
    · have hchart :=
        weightedNormSq_sub_affineConeChart_le hk y hQ i M hM hMpure
      rw [← hπ_def, ← hA_def] at hchart
      have hnorm := weightedNormSq_sub_normalize_le y π hQ hπ0
      have hηW : 0 ≤ 4 / η * completeToricEnergy y := by positivity
      nlinarith

end

end HGAS.Veronese
