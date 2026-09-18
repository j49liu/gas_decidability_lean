import HGAS.Dynamics.Stability
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# Quantitative lemmas for Lyapunov's direct method

This file contains the state-space-independent estimates used in elementary
Lyapunov arguments.  The main lemmas are first stated for a caller-supplied
nonnegative distance function.  This is useful when a construction is
implemented in one ambient norm but its estimates are simplest in an
equivalent norm.  Two small bridge theorems identify the specialization to
`dist` with the ambient notions from `HGAS.Dynamics.Stability`.

The three substantive results are:

* quadratic upper and lower bounds, together with monotonicity of a Lyapunov
  function, imply Lyapunov stability;
* a nonnegative decreasing scalar function enters every region on which its
  derivative is bounded by a fixed negative constant;
* eventual entry into every positive Lyapunov sublevel, together with a
  quadratic lower bound, implies global attraction.

All statements quantify over every forward trajectory.  In particular, none
of the arguments below assumes uniqueness of solutions.
-/

namespace HGAS

open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Lyapunov stability measured by a caller-supplied state-space distance.

This auxiliary notion has exactly the same trajectory quantifiers as
`LyapunovStable`; only the function used to measure displacement from the
equilibrium is replaced. -/
def LyapunovStableWith
    (distance : E → E → ℝ) (F : E → E) (xEq : E) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x₀ : E, distance x₀ xEq < δ →
        ∀ γ : ℝ → E, IsForwardTrajectory F γ x₀ →
          ∀ t : ℝ, 0 ≤ t → distance (γ t) xEq < ε

/-- Global attraction measured by a caller-supplied state-space distance.

As in `GloballyAttractive`, the entry time may depend on the initial state
and trajectory, while every later nonnegative time remains close to the
equilibrium. -/
def GloballyAttractiveWith
    (distance : E → E → ℝ) (F : E → E) (xEq : E) : Prop :=
  ∀ x₀ : E, ∀ γ : ℝ → E, IsForwardTrajectory F γ x₀ →
    ∀ ε : ℝ, 0 < ε →
      ∃ T : ℝ, 0 ≤ T ∧
        ∀ t : ℝ, T ≤ t → distance (γ t) xEq < ε

/-- Using the ambient metric in `LyapunovStableWith` recovers
`LyapunovStable` definitionally. -/
@[simp] theorem lyapunovStableWith_dist_iff
    (F : E → E) (xEq : E) :
    LyapunovStableWith (dist : E → E → ℝ) F xEq ↔
      LyapunovStable F xEq :=
  Iff.rfl

/-- Using the ambient metric in `GloballyAttractiveWith` recovers
`GloballyAttractive` definitionally. -/
@[simp] theorem globallyAttractiveWith_dist_iff
    (F : E → E) (xEq : E) :
    GloballyAttractiveWith (dist : E → E → ℝ) F xEq ↔
      GloballyAttractive F xEq :=
  Iff.rfl

/-- Quadratic comparison bounds and monotonicity of a Lyapunov function imply
Lyapunov stability.

The same positive constant `b` is allowed in both comparison estimates:

`distance z xEq ^ 2 ≤ b * V z ≤ b ^ 2 * distance z xEq ^ 2`.

Thus an initial displacement smaller than `ε / b` forces every later
displacement to remain smaller than `ε`. -/
theorem lyapunovStableWith_of_quadratic_bounds
    (distance : E → E → ℝ) (F : E → E) (xEq : E) (V : E → ℝ)
    {b : ℝ} (hb : 0 < b)
    (hdistance : ∀ z : E, 0 ≤ distance z xEq)
    (hlower : ∀ z : E, distance z xEq ^ 2 ≤ b * V z)
    (hupper : ∀ z : E, V z ≤ b * distance z xEq ^ 2)
    (hanti : ∀ {x₀ : E} {γ : ℝ → E}, IsForwardTrajectory F γ x₀ →
      AntitoneOn (fun t ↦ V (γ t)) (Ici 0)) :
    LyapunovStableWith distance F xEq := by
  intro ε hε
  refine ⟨ε / b, div_pos hε hb, ?_⟩
  intro x₀ hx₀ γ hγ t ht
  have hVt_le_V0 : V (γ t) ≤ V x₀ := by
    rw [← hγ.1]
    exact hanti hγ (by simp) ht ht
  have hdistance_sq :
      distance (γ t) xEq ^ 2 ≤ b ^ 2 * distance x₀ xEq ^ 2 := by
    calc
      distance (γ t) xEq ^ 2 ≤ b * V (γ t) := hlower (γ t)
      _ ≤ b * V x₀ := mul_le_mul_of_nonneg_left hVt_le_V0 hb.le
      _ ≤ b * (b * distance x₀ xEq ^ 2) :=
        mul_le_mul_of_nonneg_left (hupper x₀) hb.le
      _ = b ^ 2 * distance x₀ xEq ^ 2 := by ring
  have hb_distance_lt : b * distance x₀ xEq < ε := by
    simpa [mul_comm] using (lt_div_iff₀ hb).mp hx₀
  have hb_distance_nonneg : 0 ≤ b * distance x₀ xEq :=
    mul_nonneg hb.le (hdistance x₀)
  have hsq_lt : (b * distance x₀ xEq) ^ 2 < ε ^ 2 :=
    (sq_lt_sq₀ hb_distance_nonneg hε.le).mpr hb_distance_lt
  have htarget_sq : distance (γ t) xEq ^ 2 < ε ^ 2 := by
    refine lt_of_le_of_lt hdistance_sq ?_
    simpa [mul_pow] using hsq_lt
  exact (sq_lt_sq₀ (hdistance (γ t)) hε.le).mp htarget_sq

/-- Ambient-distance specialization of
`lyapunovStableWith_of_quadratic_bounds`. -/
theorem lyapunovStable_of_quadratic_bounds
    (F : E → E) (xEq : E) (V : E → ℝ)
    {b : ℝ} (hb : 0 < b)
    (hlower : ∀ z : E, dist z xEq ^ 2 ≤ b * V z)
    (hupper : ∀ z : E, V z ≤ b * dist z xEq ^ 2)
    (hanti : ∀ {x₀ : E} {γ : ℝ → E}, IsForwardTrajectory F γ x₀ →
      AntitoneOn (fun t ↦ V (γ t)) (Ici 0)) :
    LyapunovStable F xEq := by
  change LyapunovStableWith (dist : E → E → ℝ) F xEq
  exact lyapunovStableWith_of_quadratic_bounds
    dist F xEq V hb (fun z ↦ dist_nonneg) hlower hupper hanti

/-- A nonnegative, nonincreasing scalar quantity must eventually enter every
level above which its derivative has a fixed negative upper bound.

The proof is the elementary finite-entry argument.  If the function stayed
above `η` until time `T = h 0 / d + 1`, then `t ↦ h t + d*t` would be
nonincreasing on `[0,T]`.  This would force `h T < 0`, contradicting
nonnegativity.  Antitonicity then keeps the function below `η` forever. -/
theorem eventually_lt_of_antitoneOn_of_hasDerivAt_le
    {h : ℝ → ℝ} {d η : ℝ}
    (hcont : ContinuousOn h (Ici 0))
    (hanti : AntitoneOn h (Ici 0))
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ h t)
    (hd : 0 < d)
    (hderiv : ∀ t : ℝ, 0 < t → η ≤ h t →
      ∃ h' : ℝ, HasDerivAt h h' t ∧ h' ≤ -d) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → h t < η := by
  let T : ℝ := h 0 / d + 1
  have hTpos : 0 < T := by
    dsimp [T]
    have hquot_nonneg : 0 ≤ h 0 / d :=
      div_nonneg (hnonneg 0 le_rfl) hd.le
    linarith
  have hTlt : h T < η := by
    by_contra hnot
    have hηT : η ≤ h T := le_of_not_gt hnot
    let q : ℝ → ℝ := fun t ↦ h t + d * t
    have hhcontIcc : ContinuousOn h (Icc 0 T) :=
      hcont.mono (fun _ ht ↦ ht.1)
    have hqcont : ContinuousOn q (Icc 0 T) := by
      have hlinear : ContinuousOn (fun t : ℝ ↦ d * t) (Icc 0 T) := by
        fun_prop
      exact hhcontIcc.add hlinear
    have hqanti : AntitoneOn q (Icc 0 T) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hqcont
      · intro t ht
        have htIoo : t ∈ Ioo 0 T := by
          simpa [interior_Icc] using ht
        obtain ⟨h', hhderiv, _hh'le⟩ :=
          hderiv t htIoo.1
            (le_trans hηT
              (hanti htIoo.1.le hTpos.le htIoo.2.le))
        have hlinderiv : HasDerivAt (fun s : ℝ ↦ d * s) d t := by
          simpa using (hasDerivAt_id t).const_mul d
        exact (hhderiv.add hlinderiv).differentiableAt.differentiableWithinAt
      · intro t ht
        have htIoo : t ∈ Ioo 0 T := by
          simpa [interior_Icc] using ht
        obtain ⟨h', hhderiv, hh'le⟩ :=
          hderiv t htIoo.1
            (le_trans hηT
              (hanti htIoo.1.le hTpos.le htIoo.2.le))
        have hlinderiv : HasDerivAt (fun s : ℝ ↦ d * s) d t := by
          simpa using (hasDerivAt_id t).const_mul d
        have hqderiv : HasDerivAt q (h' + d) t :=
          hhderiv.add hlinderiv
        rw [hqderiv.deriv]
        linarith
    have hq0T : q T ≤ q 0 :=
      hqanti ⟨le_rfl, hTpos.le⟩ ⟨hTpos.le, le_rfl⟩ hTpos.le
    have hdT : d * T = h 0 + d := by
      dsimp [T]
      field_simp [ne_of_gt hd]
    have hnegative : h T < 0 := by
      dsimp [q] at hq0T
      rw [hdT] at hq0T
      linarith
    exact (not_lt_of_ge (hnonneg T hTpos.le)) hnegative
  refine ⟨T, hTpos.le, ?_⟩
  intro t hTt
  have htle : h t ≤ h T :=
    hanti hTpos.le (le_trans hTpos.le hTt) hTt
  exact lt_of_le_of_lt htle hTlt

/-- A positive quadratic lower bound and eventual entry into every positive
Lyapunov sublevel imply global attraction.

For a target radius `ε`, enter the sublevel `V < c * ε^2`.  The lower bound
`c * distance^2 ≤ V` then places every later state inside that radius. -/
theorem globallyAttractiveWith_of_lower_quadratic_of_eventually_lt
    (distance : E → E → ℝ) (F : E → E) (xEq : E) (V : E → ℝ)
    {c : ℝ} (hc : 0 < c)
    (hdistance : ∀ z : E, 0 ≤ distance z xEq)
    (hlower : ∀ z : E, c * distance z xEq ^ 2 ≤ V z)
    (heventually : ∀ {x₀ : E} {γ : ℝ → E}, IsForwardTrajectory F γ x₀ →
      ∀ η : ℝ, 0 < η →
        ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → V (γ t) < η) :
    GloballyAttractiveWith distance F xEq := by
  intro x₀ γ hγ ε hε
  obtain ⟨T, hT, hafter⟩ := heventually hγ (c * ε ^ 2)
    (mul_pos hc (sq_pos_of_pos hε))
  refine ⟨T, hT, ?_⟩
  intro t hTt
  have hscaled : c * distance (γ t) xEq ^ 2 < c * ε ^ 2 :=
    lt_of_le_of_lt (hlower (γ t)) (hafter t hTt)
  have hdistance_sq : distance (γ t) xEq ^ 2 < ε ^ 2 :=
    lt_of_mul_lt_mul_left hscaled hc.le
  exact (sq_lt_sq₀ (hdistance (γ t)) hε.le).mp hdistance_sq

/-- Ambient-distance specialization of
`globallyAttractiveWith_of_lower_quadratic_of_eventually_lt`. -/
theorem globallyAttractive_of_lower_quadratic_of_eventually_lt
    (F : E → E) (xEq : E) (V : E → ℝ)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ z : E, c * dist z xEq ^ 2 ≤ V z)
    (heventually : ∀ {x₀ : E} {γ : ℝ → E}, IsForwardTrajectory F γ x₀ →
      ∀ η : ℝ, 0 < η →
        ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → V (γ t) < η) :
    GloballyAttractive F xEq := by
  change GloballyAttractiveWith (dist : E → E → ℝ) F xEq
  exact globallyAttractiveWith_of_lower_quadratic_of_eventually_lt
    dist F xEq V hc (fun z ↦ dist_nonneg) hlower heventually

end

end HGAS
