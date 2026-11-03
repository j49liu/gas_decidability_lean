import HGAS.Dynamics.LyapunovDirect
import HGAS.Dynamics.LyapunovForwardCompleteness
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Tactic

/-!
# A globally asymptotically stable planar block of prescribed degree

The field `degreeCarrier d` is the literal planar block

`w' = -w^3`, `z' = -z^3 + w^d`

used to prescribe the exact degree of a polynomial vector field. For every
`d ≥ 3`, its origin is globally asymptotically stable.

The manuscript proves this by bounding trajectories and then using the local
quadratic function `w^2 + z^2`. Here a single global polynomial Lyapunov
function proves the same assertion. Writing `d = k + 3`, we use

`V(w,z) = w^2 + w^(4*k+2) + z^2`.

Two applications of the elementary square inequality give
`DV(w,z)[degreeCarrier d (w,z)] ≤ -w^4-z^4`. Coercivity gives forward
completeness; strict decrease on compact Lyapunov annuli gives attraction.
-/

namespace Stability

open Set

noncomputable section

/-- The planar stable factor used to prescribe an exact polynomial degree. -/
def degreeCarrier (d : ℕ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (-p.1 ^ 3, -p.2 ^ 3 + p.1 ^ d)

theorem degreeCarrier_contDiff (d : ℕ) :
    ContDiff ℝ 1 (degreeCarrier d) := by
  unfold degreeCarrier
  fun_prop

@[simp] theorem degreeCarrier_zero (d : ℕ) (hd : 0 < d) :
    degreeCarrier d 0 = 0 := by
  simp [degreeCarrier, zero_pow (Nat.ne_of_gt hd)]

/-- The local quadratic estimate used in the manuscript. The additional
power in the global energy below makes a separate entry-into-the-strip
argument unnecessary for the formal GAS proof. -/
theorem degreeCarrier_quadratic_derivative_le (d : ℕ) (hd : 3 ≤ d)
    (p : ℝ × ℝ) (hp : |p.1| ≤ 1) :
    fderiv ℝ (fun q : ℝ × ℝ ↦ q.1 ^ 2 + q.2 ^ 2) p (degreeCarrier d p) ≤
      -(1 / 4 : ℝ) * (p.1 ^ 2 + p.2 ^ 2) ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, d = k + 3 := ⟨d - 3, (Nat.sub_add_cancel hd).symm⟩
  have hfst : HasFDerivAt (fun p : ℝ × ℝ ↦ p.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hsnd : HasFDerivAt (fun p : ℝ × ℝ ↦ p.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have hderiv :
      fderiv ℝ (fun q : ℝ × ℝ ↦ q.1 ^ 2 + q.2 ^ 2) p
          (degreeCarrier (k + 3) p) =
        -2 * p.1 ^ 4 - 2 * p.2 ^ 4 + 2 * p.2 * p.1 ^ (k + 3) := by
    change fderiv ℝ ((fun q : ℝ × ℝ ↦ q.1 ^ 2) + fun q ↦ q.2 ^ 2) p
      (degreeCarrier (k + 3) p) = _
    rw [((hfst.pow 2).add (hsnd.pow 2)).fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', degreeCarrier,
      smul_eq_mul, nsmul_eq_mul]
    norm_num
    ring
  have habs : |p.1 ^ (k + 1)| ≤ |p.1| := by
    rw [pow_succ, abs_mul]
    apply mul_le_of_le_one_left (abs_nonneg p.1)
    simpa only [abs_pow] using pow_le_one₀ (n := k) (abs_nonneg p.1) hp
  have hsquare : (p.1 ^ (k + 1)) ^ 2 ≤ p.1 ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (p.1 ^ (k + 1))) (abs_nonneg p.1)).mpr habs
  have hforcing : p.1 ^ (k + 3) = p.1 ^ (k + 1) * p.1 ^ 2 := by
    rw [← pow_add]
  rw [hderiv, hforcing]
  have hproduct := mul_le_mul_of_nonneg_left hsquare (sq_nonneg p.2)
  nlinarith [sq_nonneg (p.1 ^ 2 - p.2 * p.1 ^ (k + 1)),
    sq_nonneg (p.1 ^ 2 - p.2 ^ 2), sq_nonneg (p.2 ^ 2)]

private def carrierEnergy (k : ℕ) (p : ℝ × ℝ) : ℝ :=
  p.1 ^ 2 + p.1 ^ (4 * k + 2) + p.2 ^ 2

private theorem carrierEnergy_contDiff (k : ℕ) :
    ContDiff ℝ 1 (carrierEnergy k) := by
  unfold carrierEnergy
  fun_prop

private theorem carrierEnergy_zero (k : ℕ) : carrierEnergy k 0 = 0 := by
  simp [carrierEnergy]

private theorem carrierEnergy_lower (k : ℕ) (p : ℝ × ℝ) :
    ‖p‖ ^ 2 ≤ carrierEnergy k p := by
  have hpow : 0 ≤ p.1 ^ (4 * k + 2) := by
    rw [show 4 * k + 2 = (2 * k + 1) * 2 by omega, pow_mul]
    exact sq_nonneg _
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  rcases le_total |p.1| |p.2| with h | h
  · rw [max_eq_right h, sq_abs]
    dsimp [carrierEnergy]
    nlinarith [sq_nonneg p.1]
  · rw [max_eq_left h, sq_abs]
    dsimp [carrierEnergy]
    nlinarith [sq_nonneg p.2]

private theorem carrierEnergy_derivative (k : ℕ) (p : ℝ × ℝ) :
    fderiv ℝ (carrierEnergy k) p (degreeCarrier (k + 3) p) =
      -2 * p.1 ^ 4 - (4 * (k : ℝ) + 2) * p.1 ^ (4 * k + 4) -
        2 * p.2 ^ 4 + 2 * p.2 * p.1 ^ (k + 3) := by
  have hfst : HasFDerivAt (fun p : ℝ × ℝ ↦ p.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hsnd : HasFDerivAt (fun p : ℝ × ℝ ↦ p.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  rw [show fderiv ℝ (carrierEnergy k) p =
      (2 • p.1 ^ (2 - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        ((4 * k + 2) • p.1 ^ (4 * k + 2 - 1)) •
          ContinuousLinearMap.fst ℝ ℝ ℝ +
        (2 • p.2 ^ (2 - 1)) • ContinuousLinearMap.snd ℝ ℝ ℝ from
    ((hfst.pow 2).add (hfst.pow (4 * k + 2))).add (hsnd.pow 2) |>.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', degreeCarrier,
    smul_eq_mul, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [show 4 * k + 2 - 1 = 4 * k + 1 by omega,
    show 4 * k + 4 = (4 * k + 1) + 3 by omega, pow_add]
  norm_num
  ring

private theorem carrierEnergy_decreases (k : ℕ) (p : ℝ × ℝ) :
    fderiv ℝ (carrierEnergy k) p (degreeCarrier (k + 3) p) ≤
      -(p.1 ^ 4 + p.2 ^ 4) := by
  rw [carrierEnergy_derivative]
  have hforcing : p.1 ^ (k + 3) = p.1 ^ (k + 1) * p.1 ^ 2 := by
    rw [← pow_add]
  have hhigh : p.1 ^ (4 * k + 4) = (p.1 ^ (k + 1)) ^ 4 := by
    rw [← pow_mul]
    congr 1
    omega
  rw [hforcing, hhigh]
  have h1 := sq_nonneg (p.1 ^ 2 - p.2 * p.1 ^ (k + 1))
  have h2 := sq_nonneg (p.2 ^ 2 - (p.1 ^ (k + 1)) ^ 2)
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hhighnonneg : 0 ≤ (p.1 ^ (k + 1)) ^ 4 := by positivity
  have hproduct := mul_nonneg hk hhighnonneg
  nlinarith [sq_nonneg (p.1 ^ 2), sq_nonneg (p.2 ^ 2)]

private theorem carrierEnergy_nonneg (k : ℕ) (p : ℝ × ℝ) :
    0 ≤ carrierEnergy k p :=
  (sq_nonneg ‖p‖).trans (carrierEnergy_lower k p)

private theorem carrierEnergy_nonincreasing (k : ℕ) (p : ℝ × ℝ) :
    fderiv ℝ (carrierEnergy k) p (degreeCarrier (k + 3) p) ≤ 0 :=
  (carrierEnergy_decreases k p).trans (neg_nonpos.mpr (by positivity))

private theorem degreeCarrier_forwardComplete (k : ℕ) :
    HGAS.ForwardComplete (degreeCarrier (k + 3)) := by
  apply HGAS.forwardComplete_of_coercive_lyapunov
    (degreeCarrier (k + 3)) (carrierEnergy k)
    (degreeCarrier_contDiff (k + 3))
    ((carrierEnergy_contDiff k).differentiable (by norm_num))
    (c := 1) (by norm_num)
  · intro p
    simpa using carrierEnergy_lower k p
  · exact carrierEnergy_nonincreasing k

private theorem carrierEnergy_trajectory_derivative (k : ℕ)
    {p₀ : ℝ × ℝ} {γ : ℝ → ℝ × ℝ}
    (hγ : HGAS.IsForwardTrajectory (degreeCarrier (k + 3)) γ p₀)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ carrierEnergy k (γ s))
      (fderiv ℝ (carrierEnergy k) (γ t) (degreeCarrier (k + 3) (γ t))) t := by
  have hγt : HasDerivAt γ (degreeCarrier (k + 3) (γ t)) t :=
    (hγ.2 t ht.le).hasDerivAt (Ici_mem_nhds ht)
  exact (((carrierEnergy_contDiff k).differentiable (by norm_num))
    (γ t)).hasFDerivAt.comp_hasDerivAt t hγt

private theorem carrierEnergy_trajectory_continuous (k : ℕ)
    {p₀ : ℝ × ℝ} {γ : ℝ → ℝ × ℝ}
    (hγ : HGAS.IsForwardTrajectory (degreeCarrier (k + 3)) γ p₀) :
    ContinuousOn (fun t ↦ carrierEnergy k (γ t)) (Ici 0) := by
  apply (carrierEnergy_contDiff k).continuous.comp_continuousOn
  intro t ht
  exact (hγ.2 t ht).continuousWithinAt

private theorem carrierEnergy_trajectory_antitone (k : ℕ)
    {p₀ : ℝ × ℝ} {γ : ℝ → ℝ × ℝ}
    (hγ : HGAS.IsForwardTrajectory (degreeCarrier (k + 3)) γ p₀) :
    AntitoneOn (fun t ↦ carrierEnergy k (γ t)) (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (carrierEnergy_trajectory_continuous k hγ)
  · intro t ht
    have htpos : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    exact (carrierEnergy_trajectory_derivative k hγ htpos).differentiableAt.differentiableWithinAt
  · intro t ht
    have htpos : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    rw [(carrierEnergy_trajectory_derivative k hγ htpos).deriv]
    exact carrierEnergy_nonincreasing k (γ t)

private theorem degreeCarrier_stable (k : ℕ) :
    HGAS.LyapunovStable (degreeCarrier (k + 3)) 0 := by
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp
    (carrierEnergy_contDiff k).continuous.continuousAt (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨δ, hδ, ?_⟩
  intro p₀ hp₀ γ hγ t ht
  have hV₀ : carrierEnergy k p₀ < ε ^ 2 := by
    have hc := hclose hp₀
    rw [carrierEnergy_zero, dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg (carrierEnergy_nonneg k p₀)] at hc
    exact hc
  have hVt : carrierEnergy k (γ t) ≤ carrierEnergy k p₀ := by
    rw [← hγ.1]
    exact carrierEnergy_trajectory_antitone k hγ (by simp) ht ht
  rw [dist_zero_right]
  have hnorm := carrierEnergy_lower k (γ t)
  nlinarith [norm_nonneg (γ t)]

private theorem carrierDecay_pos {p : ℝ × ℝ} (hp : p ≠ 0) :
    0 < p.1 ^ 4 + p.2 ^ 4 := by
  have hp' : p.1 ≠ 0 ∨ p.2 ≠ 0 := by
    contrapose! hp
    exact Prod.ext hp.1 hp.2
  rcases hp' with h | h
  · have hsq := sq_pos_of_ne_zero h
    nlinarith [sq_pos_of_pos hsq, sq_nonneg (p.2 ^ 2)]
  · have hsq := sq_pos_of_ne_zero h
    nlinarith [sq_pos_of_pos hsq, sq_nonneg (p.1 ^ 2)]

private theorem carrierEnergy_compact_annulus (k : ℕ) (η M : ℝ) :
    IsCompact {p : ℝ × ℝ | η ≤ carrierEnergy k p ∧ carrierEnergy k p ≤ M} := by
  have hbounded : Bornology.IsBounded {p : ℝ × ℝ | carrierEnergy k p ≤ M} := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨M + 1, ?_⟩
    intro p hp
    have hlower := carrierEnergy_lower k p
    have hsquare := sq_nonneg (‖p‖ - (1 / 2 : ℝ))
    change carrierEnergy k p ≤ M at hp
    nlinarith
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · exact (isClosed_Ici.preimage (carrierEnergy_contDiff k).continuous).inter
      (isClosed_Iic.preimage (carrierEnergy_contDiff k).continuous)
  · exact hbounded.subset (by intro p hp; exact hp.2)

private theorem carrierEnergy_eventually_lt (k : ℕ)
    {p₀ : ℝ × ℝ} {γ : ℝ → ℝ × ℝ}
    (hγ : HGAS.IsForwardTrajectory (degreeCarrier (k + 3)) γ p₀)
    {η : ℝ} (hη : 0 < η) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → carrierEnergy k (γ t) < η := by
  have hQ : Continuous (fun p : ℝ × ℝ ↦ p.1 ^ 4 + p.2 ^ 4) := by fun_prop
  obtain ⟨δ, hδ, hbound⟩ :=
    (carrierEnergy_compact_annulus k η (carrierEnergy k p₀)).exists_forall_le'
      hQ.continuousOn (a := 0) (by
        intro p hp
        apply carrierDecay_pos
        intro hpzero
        subst p
        have h := hp.1
        rw [carrierEnergy_zero] at h
        exact (not_le_of_gt hη) h)
  apply HGAS.eventually_lt_of_antitoneOn_of_hasDerivAt_le
    (carrierEnergy_trajectory_continuous k hγ)
    (carrierEnergy_trajectory_antitone k hγ)
    (fun t _ ↦ carrierEnergy_nonneg k (γ t)) hδ
  intro t ht hηt
  refine ⟨_, carrierEnergy_trajectory_derivative k hγ ht, ?_⟩
  have hupper : carrierEnergy k (γ t) ≤ carrierEnergy k p₀ := by
    rw [← hγ.1]
    exact carrierEnergy_trajectory_antitone k hγ (by simp) ht.le ht.le
  have hlower := hbound (γ t) ⟨hηt, hupper⟩
  exact (carrierEnergy_decreases k (γ t)).trans (neg_le_neg hlower)

private theorem degreeCarrier_attractive (k : ℕ) :
    HGAS.GloballyAttractive (degreeCarrier (k + 3)) 0 := by
  apply HGAS.globallyAttractive_of_lower_quadratic_of_eventually_lt
    (degreeCarrier (k + 3)) 0 (carrierEnergy k) (c := 1) (by norm_num)
  · intro p
    simpa using carrierEnergy_lower k p
  · intro p₀ γ hγ η hη
    exact carrierEnergy_eventually_lt k hγ hη

/-- The planar degree-prescribing block is globally asymptotically stable
for every prescribed degree at least three, including even degrees. -/
theorem degreeCarrier_gas (d : ℕ) (hd : 3 ≤ d) :
    HGAS.GloballyAsymptoticallyStable (degreeCarrier d) 0 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, d = k + 3 := ⟨d - 3, (Nat.sub_add_cancel hd).symm⟩
  exact ⟨degreeCarrier_zero (k + 3) (by omega), degreeCarrier_forwardComplete k,
    degreeCarrier_stable k, degreeCarrier_attractive k⟩

end

end Stability
