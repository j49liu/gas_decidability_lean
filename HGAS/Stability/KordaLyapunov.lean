import HGAS.Computability.HGASLanguage
import HGAS.Dynamics.HomogeneousScaling
import Mathlib.Tactic

/-!
# Lyapunov stability with existence of solutions

The project-wide predicate `LyapunovStable` quantifies over forward
trajectories only, so a polynomial field whose nearby solutions blow up in
finite time satisfies it vacuously.  The decision problem `HLS` of the paper
uses Korda's definition (Korda, *Lyapunov stability of polynomial vector
fields is undecidable*, Definition 1.1): every solution starting close to
the equilibrium exists for all forward time and stays close.  This file
defines that predicate, the corresponding finite-code language `HLSQ`, and
proves Korda's Lemma 1.5: for a homogeneous field, Lyapunov stability is
equivalent to a uniform linear bound on all forward trajectories.
-/

namespace HGAS

open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Lyapunov stability in Korda's sense: small initial states admit a
trajectory on the whole forward time ray, and every forward trajectory from a
small initial state stays small. -/
def LyapunovStableWithExistence (F : E → E) (xEq : E) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x₀ : E, dist x₀ xEq < δ →
        (∃ γ : ℝ → E, IsForwardTrajectory F γ x₀) ∧
          ∀ γ : ℝ → E, IsForwardTrajectory F γ x₀ →
            ∀ t : ℝ, 0 ≤ t → dist (γ t) xEq < ε

/-- Korda's notion implies the trajectory-only notion used for GAS. -/
theorem LyapunovStableWithExistence.lyapunovStable
    {F : E → E} {xEq : E} (h : LyapunovStableWithExistence F xEq) :
    LyapunovStable F xEq := by
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := h ε hε
  exact ⟨δ, hδ, fun x₀ hx₀ γ hγ t ht ↦ (hball x₀ hx₀).2 γ hγ t ht⟩

/-- GAS implies Lyapunov stability in Korda's sense, because GAS contains
forward completeness. -/
theorem GloballyAsymptoticallyStable.lyapunovStableWithExistence
    {F : E → E} {xEq : E} (h : GloballyAsymptoticallyStable F xEq) :
    LyapunovStableWithExistence F xEq := by
  intro ε hε
  obtain ⟨δ, hδ, hstable⟩ := h.stable ε hε
  exact ⟨δ, hδ, fun x₀ hx₀ ↦
    ⟨h.forwardComplete x₀, fun γ hγ t ht ↦ hstable x₀ hx₀ γ hγ t ht⟩⟩

/-- A uniform linear bound on all forward trajectories, together with
existence of forward trajectories through every state. -/
def HasUniformLinearTrajectoryBound (F : E → E) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ x₀ : E,
      (∃ γ : ℝ → E, IsForwardTrajectory F γ x₀) ∧
        ∀ γ : ℝ → E, IsForwardTrajectory F γ x₀ →
          ∀ t : ℝ, 0 ≤ t → ‖γ t‖ ≤ C * ‖x₀‖

/-- A uniform linear bound implies Lyapunov stability with existence. -/
theorem lyapunovStableWithExistence_of_uniformLinearTrajectoryBound
    {F : E → E} (h : HasUniformLinearTrajectoryBound F) :
    LyapunovStableWithExistence F 0 := by
  obtain ⟨C, hC, hbound⟩ := h
  intro ε hε
  refine ⟨ε / (2 * C), div_pos hε (by positivity), ?_⟩
  intro x₀ hx₀
  refine ⟨(hbound x₀).1, ?_⟩
  intro γ hγ t ht
  rw [dist_zero_right] at hx₀ ⊢
  have h1 := (hbound x₀).2 γ hγ t ht
  have h2 : C * ‖x₀‖ ≤ C * (ε / (2 * C)) :=
    mul_le_mul_of_nonneg_left hx₀.le hC.le
  have h3 : C * (ε / (2 * C)) = ε / 2 := by
    field_simp
  linarith

/-- **Korda's Lemma 1.5.**  For a field homogeneous of degree `k+1`, the
origin is Lyapunov stable (with existence of solutions) if and only if every
state admits a forward trajectory and all forward trajectories satisfy one
uniform linear bound `‖γ t‖ ≤ C ‖γ 0‖`. -/
theorem lyapunovStableWithExistence_iff_uniformLinearTrajectoryBound
    (F : E → E) (k : ℕ)
    (hF : ∀ (c : ℝ) (x : E), F (c • x) = c ^ (k + 1) • F x) :
    LyapunovStableWithExistence F 0 ↔
      HasUniformLinearTrajectoryBound F := by
  refine ⟨?_, lyapunovStableWithExistence_of_uniformLinearTrajectoryBound⟩
  intro h
  obtain ⟨δ, hδ, hball⟩ := h 1 one_pos
  refine ⟨2 / δ, by positivity, ?_⟩
  intro x₀
  by_cases hx₀ : x₀ = 0
  · subst hx₀
    have h0 : dist (0 : E) 0 < δ := by simpa using hδ
    refine ⟨(hball 0 h0).1, ?_⟩
    intro γ hγ t ht
    -- every trajectory from the origin stays at the origin
    have hsmall : ∀ ε : ℝ, 0 < ε → ‖γ t‖ < ε := by
      intro ε hε
      obtain ⟨δ', hδ', hball'⟩ := h ε hε
      have := (hball' 0 (by simpa using hδ')).2 γ hγ t ht
      simpa [dist_zero_right] using this
    have hzero : ‖γ t‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖γ t‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      exact lt_irrefl _ (hsmall _ hpos)
    simp [hzero]
  · have hnorm : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀
    set c : ℝ := δ / (2 * ‖x₀‖) with hc_def
    have hc : 0 < c := div_pos hδ (by positivity)
    have hcx : dist (c • x₀) 0 < δ := by
      rw [dist_zero_right, norm_smul, Real.norm_of_nonneg hc.le, hc_def]
      field_simp
      nlinarith
    constructor
    · -- existence: scale a trajectory from `c • x₀` back by `1/c`
      obtain ⟨γ', hγ'⟩ := (hball (c • x₀) hcx).1
      refine ⟨scaledForwardCurve k c⁻¹ γ', ?_⟩
      have hscaled :=
        hγ'.scale_of_homogeneous F k hF c⁻¹ (inv_nonneg.mpr hc.le)
      simpa [smul_smul, inv_mul_cancel₀ hc.ne'] using hscaled
    · intro γ hγ t ht
      have hscaled := hγ.scale_of_homogeneous F k hF c hc.le
      -- the rescaled trajectory starts in the `δ`-ball
      have hs : 0 ≤ t * (c ^ k)⁻¹ :=
        mul_nonneg ht (inv_nonneg.mpr (pow_nonneg hc.le k))
      have hlt := (hball (c • x₀) hcx).2 _ hscaled (t * (c ^ k)⁻¹) hs
      have hck : (c ^ k) ≠ 0 := pow_ne_zero k hc.ne'
      have htime : t * (c ^ k)⁻¹ * c ^ k = t := by
        field_simp
      simp only [scaledForwardCurve, htime, dist_zero_right, norm_smul,
        Real.norm_of_nonneg hc.le] at hlt
      -- `c * ‖γ t‖ < 1`, hence `‖γ t‖ < 1 / c = (2/δ) ‖x₀‖`
      have hγt : ‖γ t‖ < 1 / c := by
        rw [lt_div_iff₀ hc]
        linarith
      have h1c : 1 / c = 2 / δ * ‖x₀‖ := by
        rw [hc_def]
        field_simp
      linarith

/-! ## The finite-code language -/

/-- The exact rational fixed-dimension, fixed-degree homogeneous Lyapunov
stability language.  Invalid homogeneity codes are negative by definition. -/
def HLSQ (n d : ℕ) (F : PolynomialFieldCode n) : Prop :=
  PolynomialFieldCode.homogeneous d F = true ∧
    LyapunovStableWithExistence (PolynomialFieldCode.realize F) 0

/-- A valid code is in `HLSQ` exactly when its realized field is Lyapunov
stable. -/
theorem hlsQ_iff_of_homogeneous
    {n d : ℕ} (F : PolynomialFieldCode n)
    (hvalid : PolynomialFieldCode.homogeneous d F = true) :
    HLSQ n d F ↔
      LyapunovStableWithExistence (PolynomialFieldCode.realize F) 0 := by
  simp [HLSQ, hvalid]

/-- Every GAS code is a Lyapunov-stable code. -/
theorem hlsQ_of_hgasQ {n d : ℕ} {F : PolynomialFieldCode n}
    (h : HGASQ n d F) : HLSQ n d F :=
  ⟨h.1, h.2.lyapunovStableWithExistence⟩

end

end HGAS
