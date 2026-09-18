import HGAS.Analysis.QuadraticHomogeneousRegularity
import HGAS.Dynamics.AngularGAS
import HGAS.Dynamics.LyapunovDirect
import HGAS.Dynamics.LyapunovForwardCompleteness
import Mathlib.Tactic

/-!
# The direct theorem for strict homogeneous `C¹` Lyapunov functions

This file proves the elementary, but logically indispensable, direction of
the homogeneous converse-Lyapunov argument:

> a positive, strict, degree-two homogeneous `C¹` Lyapunov function for a
> `C¹` vector field proves global asymptotic stability of the origin.

The proof is deliberately independent of polynomial coordinates.
It works on every finite-dimensional real normed space.

There are four steps.

1. Compactness of the unit sphere and degree-two homogeneity give global
   quadratic lower and upper bounds for the Lyapunov function.
2. Strict decrease and continuity give a positive decay margin on every
   compact Lyapunov annulus

   `η ≤ V(x) ≤ V(x₀)`.

3. Quadratic coercivity and nonincrease give forward completeness via the
   smooth-cutoff continuation theorem.
4. The usual finite-entry argument gives attraction, while the quadratic
   comparison bounds give Lyapunov stability.

Notice that no homogeneity assumption on the vector field is needed for
this direct implication.  Compact Lyapunov annuli replace a global
homogeneous decay estimate.
-/

namespace HGAS

open Metric Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : E → E}

namespace StrictHomogeneousC1Lyapunov

/-- A degree-two homogeneous Lyapunov function vanishes at the cone tip. -/
@[simp]
theorem value_zero
    (L : StrictHomogeneousC1Lyapunov F 2) :
    L.V 0 = 0 := by
  have h := L.homogeneous 2 (by norm_num) (0 : E)
  norm_num at h
  linarith

/-- Strict positivity on nonzero vectors has a uniform positive margin on
the unit sphere. -/
theorem exists_pos_lower_bound_on_unitSphere
    [FiniteDimensional ℝ E]
    (L : StrictHomogeneousC1Lyapunov F 2) :
    ∃ c : ℝ, 0 < c ∧
      ∀ u : E, ‖u‖ = 1 → c ≤ L.V u := by
  obtain ⟨c, hc, hbound⟩ :=
    (isCompact_sphere (0 : E) 1).exists_forall_le'
      L.contDiff.continuous.continuousOn
      (a := 0) (by
        intro u hu
        have hunorm : ‖u‖ = 1 := by
          simpa [mem_sphere, dist_zero_right] using hu
        have hune : u ≠ 0 := by
          intro hzero
          subst u
          simp at hunorm
        exact L.positive u hune)
  refine ⟨c, hc, ?_⟩
  intro u hu
  exact hbound u (by
    simpa [mem_sphere, dist_zero_right] using hu)

/-- Positivity and degree-two homogeneity give a global quadratic coercivity
estimate. -/
theorem exists_positive_quadratic_lower_bound
    [FiniteDimensional ℝ E]
    (L : StrictHomogeneousC1Lyapunov F 2) :
    ∃ c : ℝ, 0 < c ∧
      ∀ x : E, c * ‖x‖ ^ 2 ≤ L.V x := by
  obtain ⟨c, hc, hunit⟩ := L.exists_pos_lower_bound_on_unitSphere
  refine ⟨c, hc, ?_⟩
  intro x
  by_cases hx : x = 0
  · subst x
    simp
  · let u : E := (‖x‖ : ℝ)⁻¹ • x
    have hu : ‖u‖ = 1 := by
      simpa only [u, mem_sphere_zero_iff_norm] using
        inv_norm_smul_mem_unitSphere hx
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hxray : ‖x‖ • u = x := by
      simpa only [u] using norm_smul_inv_norm_smul hx
    have hscale := L.homogeneous ‖x‖ hr u
    rw [hxray] at hscale
    rw [hscale]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (hunit u hu)
        (sq_nonneg ‖x‖)

/-- Degree-two homogeneity and continuity give a global quadratic upper
estimate.  The constant is chosen strictly positive for convenient use in
comparison arguments. -/
theorem exists_positive_quadratic_upper_bound
    [FiniteDimensional ℝ E]
    (L : StrictHomogeneousC1Lyapunov F 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x : E, L.V x ≤ C * ‖x‖ ^ 2 := by
  obtain ⟨C₀, hC₀, hbound⟩ :=
    exists_quadratic_bound_of_twoHomogeneous
      L.V L.value_zero
      L.contDiff.continuous.continuousOn
      L.homogeneous
  let C : ℝ := C₀ + 1
  have hC : 0 < C := by
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro x
  calc
    L.V x ≤ ‖L.V x‖ := by
      simpa [Real.norm_eq_abs] using le_abs_self (L.V x)
    _ ≤ C₀ * ‖x‖ ^ 2 := hbound x
    _ ≤ C * ‖x‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right
      · dsimp only [C]
        linarith
      · positivity

/-- The nonnegative decay associated with a strict Lyapunov function. -/
def decay (L : StrictHomogeneousC1Lyapunov F 2) (x : E) : ℝ :=
  -fderiv ℝ L.V x (F x)

/-- For a continuous field, strict Lyapunov decay is continuous. -/
theorem continuous_decay
    (L : StrictHomogeneousC1Lyapunov F 2)
    (hF : Continuous F) :
    Continuous L.decay := by
  exact
    ((L.contDiff.continuous_fderiv (by norm_num)).clm_apply hF).neg

/-- Decay is strictly positive away from the origin. -/
theorem decay_pos
    (L : StrictHomogeneousC1Lyapunov F 2)
    {x : E} (hx : x ≠ 0) :
    0 < L.decay x := by
  exact neg_pos.mpr (L.decreases x hx)

/-- If the origin is an equilibrium, decay is nonnegative everywhere. -/
theorem decay_nonneg
    (L : StrictHomogeneousC1Lyapunov F 2)
    (hzero : F 0 = 0) (x : E) :
    0 ≤ L.decay x := by
  by_cases hx : x = 0
  · subst x
    simp [decay, hzero]
  · exact (L.decay_pos hx).le

/-- For a continuous field, strict decrease of a positive degree-two
homogeneous Lyapunov function already forces the origin to be an
equilibrium.

Indeed, suppose `v = F(0) ≠ 0`.  Euler's identity gives
`DV(v)[v] = 2 V(v) > 0`.  Continuity of `F` then gives
`DV(v)[F(s v)] > 0` for all sufficiently small positive `s`.  On the other
hand, differentiated homogeneity says
`DV(s v) = s DV(v)`, and strict decrease at `s v` forces
`DV(v)[F(s v)] < 0`, a contradiction. -/
theorem equilibrium_of_continuous
    (L : StrictHomogeneousC1Lyapunov F 2)
    (hF : Continuous F) :
    F 0 = 0 := by
  by_contra hzero
  let v : E := F 0
  have hv : v ≠ 0 := by
    simpa only [v] using hzero
  let A : E →L[ℝ] ℝ := fderiv ℝ L.V v
  have hAv : 0 < A v := by
    have heuler := L.euler_identity v
    have hVpos := L.positive v hv
    dsimp only [A]
    rw [heuler]
    positivity
  let g : E → ℝ := fun x ↦ A (F x)
  have hg : Continuous g := by
    exact A.continuous.comp hF
  have hgzero : 0 < g 0 := by
    simpa only [g, v] using hAv
  have hopen : IsOpen {x : E | 0 < g x} :=
    isOpen_lt continuous_const hg
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp (hopen.mem_nhds hgzero)
  let s : ℝ := ε / (2 * (‖v‖ + 1))
  have hden : 0 < 2 * (‖v‖ + 1) := by
    positivity
  have hs : 0 < s := by
    exact div_pos hε hden
  have hnormlt : ‖v‖ < 2 * (‖v‖ + 1) := by
    nlinarith [norm_nonneg v]
  have hsmulnorm : s * ‖v‖ < ε := by
    calc
      s * ‖v‖ < s * (2 * (‖v‖ + 1)) :=
        mul_lt_mul_of_pos_left hnormlt hs
      _ = ε := by
        dsimp only [s]
        field_simp [hden.ne']
  have hsvBall : s • v ∈ ball (0 : E) ε := by
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hs]
    exact hsmulnorm
  have hgpos : 0 < g (s • v) :=
    hball hsvBall
  have hsvne : s • v ≠ 0 :=
    smul_ne_zero hs.ne' hv
  have hdecrease := L.decreases (s • v) hsvne
  have hscale :=
    fderiv_pos_smul_of_twoHomogeneous
      L.V L.homogeneous s hs v
  have hgneg : g (s • v) < 0 := by
    dsimp only [g, A]
    rw [hscale] at hdecrease
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at hdecrease
    nlinarith
  linarith

/-- A coercive Lyapunov sublevel is bounded. -/
theorem isBounded_sublevel
    (L : StrictHomogeneousC1Lyapunov F 2)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ x : E, c * ‖x‖ ^ 2 ≤ L.V x)
    (M : ℝ) :
    Bornology.IsBounded {x : E | L.V x ≤ M} := by
  rw [isBounded_iff_forall_norm_le]
  let R : ℝ := max (M / c) 0 + 1
  refine ⟨R, ?_⟩
  intro x hx
  have hsquare : ‖x‖ ^ 2 ≤ M / c := by
    apply (le_div_iff₀ hc).2
    simpa [mul_comm] using (hlower x).trans hx
  have hnorm_le : ‖x‖ ≤ ‖x‖ ^ 2 + 1 := by
    nlinarith [sq_nonneg (‖x‖ - (1 / 2 : ℝ))]
  calc
    ‖x‖ ≤ ‖x‖ ^ 2 + 1 := hnorm_le
    _ ≤ M / c + 1 := by
      simpa [add_comm] using add_le_add_right hsquare 1
    _ ≤ R := by
      dsimp only [R]
      gcongr
      exact le_max_left (M / c) 0

/-- A closed Lyapunov annulus bounded by a coercive sublevel is compact. -/
theorem isCompact_lyapunovAnnulus
    [FiniteDimensional ℝ E]
    (L : StrictHomogeneousC1Lyapunov F 2)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ x : E, c * ‖x‖ ^ 2 ≤ L.V x)
    (η M : ℝ) :
    IsCompact {x : E | η ≤ L.V x ∧ L.V x ≤ M} := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · exact
      (isClosed_Ici.preimage L.contDiff.continuous).inter
        (isClosed_Iic.preimage L.contDiff.continuous)
  · exact (isBounded_sublevel L hc hlower M).subset (by
      intro x hx
      exact hx.2)

/-- Strict continuous decay has a positive uniform margin on each compact
positive Lyapunov annulus. -/
theorem exists_pos_decay_lower_bound_on_annulus
    [FiniteDimensional ℝ E]
    (L : StrictHomogeneousC1Lyapunov F 2)
    (hF : Continuous F)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ x : E, c * ‖x‖ ^ 2 ≤ L.V x)
    {η M : ℝ} (hη : 0 < η) :
    ∃ d : ℝ, 0 < d ∧
      ∀ x : E, η ≤ L.V x → L.V x ≤ M → d ≤ L.decay x := by
  let K : Set E := {x : E | η ≤ L.V x ∧ L.V x ≤ M}
  have hK : IsCompact K := by
    simpa only [K] using L.isCompact_lyapunovAnnulus hc hlower η M
  obtain ⟨d, hd, hbound⟩ :=
    hK.exists_forall_le'
      (L.continuous_decay hF).continuousOn
      (a := 0) (by
        intro x hx
        have hxne : x ≠ 0 := by
          intro hzero
          subst x
          change η ≤ L.V 0 ∧ L.V 0 ≤ M at hx
          rw [L.value_zero] at hx
          linarith
        exact L.decay_pos hxne)
  refine ⟨d, hd, ?_⟩
  intro x hηx hxM
  exact hbound x ⟨hηx, hxM⟩

/-- Along every forward trajectory, the Lyapunov value has derivative
`-decay`. -/
theorem hasDerivAt_value_along
    (L : StrictHomogeneousC1Lyapunov F 2)
    {x₀ : E} {γ : ℝ → E}
    (hγ : IsForwardTrajectory F γ x₀)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ L.V (γ s)) (-L.decay (γ t)) t := by
  have hγt : HasDerivAt γ (F (γ t)) t :=
    (hγ.2 t ht.le).hasDerivAt (Ici_mem_nhds ht)
  have hcomp :=
    (L.contDiff.differentiable (by norm_num) (γ t)).hasFDerivAt
      |>.comp_hasDerivAt t hγt
  simpa only [decay, neg_neg] using hcomp

/-- Along every forward trajectory, the Lyapunov value is nonincreasing. -/
theorem antitoneOn_value_along
    (L : StrictHomogeneousC1Lyapunov F 2)
    (hzero : F 0 = 0)
    {x₀ : E} {γ : ℝ → E}
    (hγ : IsForwardTrajectory F γ x₀) :
    AntitoneOn (fun t ↦ L.V (γ t)) (Ici 0) := by
  have hcontinuous :
      ContinuousOn (fun t ↦ L.V (γ t)) (Ici 0) := by
    have hγcontinuous : ContinuousOn γ (Ici 0) :=
      fun t ht ↦ (hγ.2 t ht).continuousWithinAt
    exact L.contDiff.continuous.comp_continuousOn hγcontinuous
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hcontinuous
  · intro t ht
    have htpos : 0 < t := by
      simpa only [interior_Ici, mem_Ioi] using ht
    exact (L.hasDerivAt_value_along hγ htpos).differentiableAt
      |>.differentiableWithinAt
  · intro t ht
    have htpos : 0 < t := by
      simpa only [interior_Ici, mem_Ioi] using ht
    rw [(L.hasDerivAt_value_along hγ htpos).deriv]
    exact neg_nonpos.mpr (L.decay_nonneg hzero (γ t))

/-- Every forward trajectory eventually enters, and then remains in, each
positive Lyapunov sublevel. -/
theorem eventually_value_lt
    [FiniteDimensional ℝ E]
    (L : StrictHomogeneousC1Lyapunov F 2)
    (hF : Continuous F)
    (hzero : F 0 = 0)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ x : E, c * ‖x‖ ^ 2 ≤ L.V x)
    {x₀ : E} {γ : ℝ → E}
    (hγ : IsForwardTrajectory F γ x₀)
    {η : ℝ} (hη : 0 < η) :
    ∃ T : ℝ, 0 ≤ T ∧
      ∀ t : ℝ, T ≤ t → L.V (γ t) < η := by
  have hanti := L.antitoneOn_value_along hzero hγ
  obtain ⟨d, hd, hdecay⟩ :=
    L.exists_pos_decay_lower_bound_on_annulus
      hF hc hlower (M := L.V x₀) hη
  apply eventually_lt_of_antitoneOn_of_hasDerivAt_le
    (h := fun t ↦ L.V (γ t)) (d := d)
  · have hγcontinuous : ContinuousOn γ (Ici 0) :=
      fun t ht ↦ (hγ.2 t ht).continuousWithinAt
    exact L.contDiff.continuous.comp_continuousOn hγcontinuous
  · exact hanti
  · intro t _ht
    exact (mul_nonneg hc.le (sq_nonneg ‖γ t‖)).trans (hlower (γ t))
  · exact hd
  · intro t ht hlevel
    have hupper : L.V (γ t) ≤ L.V x₀ := by
      rw [← hγ.1]
      exact hanti (by simp) ht.le ht.le
    refine ⟨-L.decay (γ t), L.hasDerivAt_value_along hγ ht, ?_⟩
    exact neg_le_neg (hdecay (γ t) hlevel hupper)

/-- **Strict homogeneous Lyapunov direct theorem, equilibrium form.**

A `C¹` field with an equilibrium at the origin and a strict positive
degree-two homogeneous `C¹` Lyapunov function is globally asymptotically
stable. -/
theorem globallyAsymptoticallyStable_of_equilibrium
    [FiniteDimensional ℝ E]
    (L : StrictHomogeneousC1Lyapunov F 2)
    (hF : ContDiff ℝ 1 F)
    (hzero : F 0 = 0) :
    GloballyAsymptoticallyStable F 0 := by
  obtain ⟨c, hc, hlower⟩ := L.exists_positive_quadratic_lower_bound
  obtain ⟨C, hC, hupper⟩ := L.exists_positive_quadratic_upper_bound
  let b : ℝ := max C c⁻¹
  have hb : 0 < b := hC.trans_le (le_max_left C c⁻¹)
  have hVnonneg : ∀ x : E, 0 ≤ L.V x := by
    intro x
    exact (mul_nonneg hc.le (sq_nonneg ‖x‖)).trans (hlower x)
  have hstableLower : ∀ x : E,
      dist x 0 ^ 2 ≤ b * L.V x := by
    intro x
    rw [dist_zero_right]
    have hbase : ‖x‖ ^ 2 ≤ c⁻¹ * L.V x := by
      rw [inv_mul_eq_div]
      exact (le_div_iff₀ hc).2 (by
        simpa [mul_comm] using hlower x)
    exact hbase.trans
      (mul_le_mul_of_nonneg_right (le_max_right C c⁻¹)
        (hVnonneg x))
  have hstableUpper : ∀ x : E,
      L.V x ≤ b * dist x 0 ^ 2 := by
    intro x
    rw [dist_zero_right]
    exact (hupper x).trans
      (mul_le_mul_of_nonneg_right (le_max_left C c⁻¹)
        (sq_nonneg ‖x‖))
  have hattractLower : ∀ x : E,
      c * dist x 0 ^ 2 ≤ L.V x := by
    intro x
    simpa [dist_zero_right] using hlower x
  have hcomplete : ForwardComplete F := by
    apply forwardComplete_of_coercive_lyapunov
      F L.V hF (L.contDiff.differentiable one_ne_zero) hc hlower
    intro x
    exact neg_nonneg.mp (L.decay_nonneg hzero x)
  have hanti :
      ∀ {x₀ : E} {γ : ℝ → E}, IsForwardTrajectory F γ x₀ →
        AntitoneOn (fun t ↦ L.V (γ t)) (Ici 0) :=
    fun hγ ↦ L.antitoneOn_value_along hzero hγ
  have heventually :
      ∀ {x₀ : E} {γ : ℝ → E}, IsForwardTrajectory F γ x₀ →
        ∀ η : ℝ, 0 < η →
          ∃ T : ℝ, 0 ≤ T ∧
            ∀ t : ℝ, T ≤ t → L.V (γ t) < η := by
    intro x₀ γ hγ η hη
    exact L.eventually_value_lt hF.continuous hzero hc hlower hγ hη
  exact
    { equilibrium := hzero
      forwardComplete := hcomplete
      stable :=
        lyapunovStable_of_quadratic_bounds
          F 0 L.V hb hstableLower hstableUpper hanti
      attractive :=
        globallyAttractive_of_lower_quadratic_of_eventually_lt
          F 0 L.V hc hattractLower heventually }

/-- **Strict homogeneous Lyapunov direct theorem.**

A `C¹` finite-dimensional vector field admitting a strict positive
degree-two homogeneous `C¹` Lyapunov function is globally asymptotically
stable at the origin.  The equilibrium identity is a consequence, rather
than an additional hypothesis. -/
theorem globallyAsymptoticallyStable
    [FiniteDimensional ℝ E]
    (L : StrictHomogeneousC1Lyapunov F 2)
    (hF : ContDiff ℝ 1 F) :
    GloballyAsymptoticallyStable F 0 :=
  L.globallyAsymptoticallyStable_of_equilibrium
    hF (L.equilibrium_of_continuous hF.continuous)

end StrictHomogeneousC1Lyapunov

end

end HGAS
