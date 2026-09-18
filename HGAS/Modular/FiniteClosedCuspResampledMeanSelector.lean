import HGAS.Modular.FiniteClosedCuspMeanSelector
import HGAS.Modular.LinkedConstantTimeRescaling
import Mathlib.Tactic

/-!
# Finite cusp selection from means in another constant clock

The detector moments naturally live in physical time, while the modular
column is standardized by a possibly negative constant change of time.
It is unnecessary, and potentially misleading, to pretend those are the
same forward clock.  This file proves the invariant formulation directly:
if the raw means of `z(b t)` are normalized for any `b ≠ 0`, then the
finite cusp chart of `z(t)` is still the normalized infinity chart.

The proof applies the unresampled selector to the trajectory
`z_b(t)=z(b t)`.  Its horizontal speed is `s b`, which remains nonzero
for either sign of `b`.  The resulting literal theta formulas are then
pulled back by `t ↦ t/b`.
-/

namespace HGAS.Modular

open Filter
open scoped Topology

noncomputable section

/-- A horizontal line remains horizontal after any constant resampling. -/
theorem horizontalLine_mul_time
    (x y s b : ℝ) (hy : 0 < y) (t : ℝ) :
    horizontalLine x y s hy (b * t) =
      horizontalLine x y (s * b) hy t := by
  apply UpperHalfPlane.ext
  apply Complex.ext
  · simp
    ring
  · simp

/-- Pulling the resampled horizontal line back by the inverse scale
recovers the original parameterization. -/
theorem horizontalLine_mul_div_time
    (x y s b : ℝ) (hy : 0 < y)
    (hb : b ≠ 0) (t : ℝ) :
    horizontalLine x y (s * b) hy (t / b) =
      horizontalLine x y s hy t := by
  rw [← horizontalLine_mul_time]
  congr 1
  field_simp

/-- Finite closed-cusp selection when the normalized raw means are known
in an arbitrary nonzero constant clock `t ↦ b t`.

The conclusion is deliberately expressed in the original chart clock,
including coherent original root branches and literal `Y=θ₃`,
`p₄=θ₄²` identities. -/
theorem finiteClosedCuspMeanSelection_of_resampled_means
    {κZ κPhi : ℂ}
    (cusp : GammaTwoCuspLabel)
    (z : ℝ → LinkedJacobiState ℂ)
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    (x y s : ℝ) (hy : 0 < y) (hs : s ≠ 0)
    (q : ℂ) (hq : q ≠ 0)
    (hamplitude :
      ∀ t,
        HasCuspQuarticAmplitude cusp (z t).unary
          (horizontalLine x y s hy t) q)
    (hresidual :
      ∀ t (r : LinkedJacobiResidualIndex),
        linkedJacobiResidual r (z t) = 0)
    (b : ℝ) (hb : b ≠ 0)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    (hmeanY :
      Tendsto
        (fun n ↦
          HGAS.Analysis.cesaroMeanAt
            (fun t ↦ (z (b * t)).unary.Y) (T n))
        atTop (nhds 1))
    (hmeanP4 :
      Tendsto
        (fun n ↦
          HGAS.Analysis.cesaroMeanAt
            (fun t ↦ (z (b * t)).jacobi.p4) (T n))
        atTop (nhds 1)) :
    Nonempty (FiniteClosedCuspMeanSelection cusp z x y s hy q) := by
  let zb : ℝ → LinkedJacobiState ℂ :=
    fun t ↦ z (b * t)
  let sb : ℝ := s * b
  have hsb : sb ≠ 0 :=
    mul_ne_zero hs hb
  have hzb :
      IsScaledLinkedJacobiTrajectory
        ((b : ℂ) * κZ) ((b : ℂ) * κPhi) zb := by
    simpa only [zb] using hz.rescale b
  have hamplitude_b :
      ∀ t,
        HasCuspQuarticAmplitude cusp (zb t).unary
          (horizontalLine x y sb hy t) q := by
    intro t
    simpa only [zb, sb, horizontalLine_mul_time] using
      hamplitude (b * t)
  have hresidual_b :
      ∀ t (r : LinkedJacobiResidualIndex),
        linkedJacobiResidual r (zb t) = 0 := by
    intro t r
    exact hresidual (b * t) r
  obtain ⟨resampled⟩ :=
    finiteClosedCuspMeanSelection
      cusp zb hzb x y sb hy hsb q hq
      hamplitude_b hresidual_b hT hmeanY hmeanP4
  have hY :
      ∀ t,
        (z t).unary.Y =
          theta₃ (horizontalLine x y s hy t) := by
    intro t
    have h := resampled.Y_eq_theta₃ (t / b)
    have hbtime : b * (t / b) = t := by
      field_simp
    rw [show zb (t / b) = z t by
      simp only [zb, hbtime]] at h
    rw [horizontalLine_mul_div_time x y s b hy hb t] at h
    exact h
  have hp4 :
      ∀ t,
        (z t).jacobi.p4 =
          theta₄ (horizontalLine x y s hy t) ^ 2 := by
    intro t
    have h := resampled.p4_eq_theta₄_sq (t / b)
    have hbtime : b * (t / b) = t := by
      field_simp
    rw [show zb (t / b) = z t by
      simp only [zb, hbtime]] at h
    rw [horizontalLine_mul_div_time x y s b hy hb t] at h
    exact h
  have hcusp : cusp = .infinity :=
    resampled.cusp_eq_infinity
  subst cusp
  obtain ⟨branches⟩ :=
    exists_cuspLinkedRootBranches_horizontalLine
      .infinity z hz x y s hy q hq hamplitude hresidual
  have hyScale : branches.yScale = 1 := by
    have hbranch := branches.y_eq 0
    rw [hY 0] at hbranch
    apply mul_right_cancel₀
      (theta₃_ne_zero (horizontalLine x y s hy 0))
    simpa only [cuspYRoot, one_mul] using hbranch.symm
  have hp4Scale : branches.p4Scale = 1 := by
    have hbranch := branches.p4_eq 0
    rw [hp4 0] at hbranch
    apply mul_right_cancel₀
      (pow_ne_zero 2
        (theta₄_ne_zero (horizontalLine x y s hy 0)))
    simpa only [cuspP4Root, one_mul] using hbranch.symm
  exact
    ⟨{
      branches := branches
      cusp_eq_infinity := rfl
      yScale_eq_one := hyScale
      p4Scale_eq_one := hp4Scale
      q_eq_one := resampled.q_eq_one
      Y_eq_theta₃ := hY
      p4_eq_theta₄_sq := hp4
    }⟩

end

end HGAS.Modular
