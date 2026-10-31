import HGAS.Compactification.PositiveCentralChartTrajectory
import HGAS.Veronese.SourceAngularFlow

/-!
# The positive central chart in projective code coordinates

The final coordinate is the positive scale `c = (1 + |x|²)^(-1/2)`.
The preceding coordinates are `c x`. This packages the preserved central
chart in the `Fin (n + 1)` coordinates used by the polynomial compiler.
-/

namespace Stability.ProjectivePolynomialCode

open HGAS HGAS.Veronese
open scoped BigOperators

noncomputable section

variable {n : ℕ}

abbrev centralScale (x : Fin n → ℝ) : ℝ := positiveCentralScale x

def centralLift (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.lastCases (centralScale x) (fun i ↦ centralScale x * x i)

@[simp] theorem centralLift_last (x : Fin n → ℝ) :
    centralLift x (Fin.last n) = centralScale x := by simp [centralLift]

@[simp] theorem centralLift_castSucc (x : Fin n → ℝ) (i : Fin n) :
    centralLift x i.castSucc = centralScale x * x i := by simp [centralLift]

theorem centralScale_pos (x : Fin n → ℝ) : 0 < centralScale x :=
  positiveCentralScale_pos x

theorem centralScale_sq_mul (x : Fin n → ℝ) :
    centralScale x ^ 2 * (1 + HGAS.normSq x) = 1 := positiveCentralScale_sq_mul x

theorem sourceRadiusSq_centralLift (x : Fin n → ℝ) :
    sourceRadiusSq (centralLift x) = 1 := by
  rw [← HGAS.normSq_eq_sourceRadiusSq]
  unfold HGAS.normSq HGAS.dot
  rw [Fin.sum_univ_castSucc]
  simp only [centralLift_castSucc, centralLift_last]
  have hs : (∑ i, centralScale x * x i * (centralScale x * x i)) =
      centralScale x ^ 2 * HGAS.normSq x := by
    simp only [HGAS.normSq, HGAS.dot, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  nlinarith [centralScale_sq_mul x]

theorem centralLift_quotient (x : Fin n → ℝ) :
    (fun i : Fin n ↦ centralLift x i.castSucc / centralLift x (Fin.last n)) = x := by
  funext i
  simp only [centralLift_castSucc, centralLift_last]
  exact mul_div_cancel_left₀ (x i) (centralScale_pos x).ne'

theorem continuous_centralScale : Continuous (centralScale (n := n)) := by
  have hn : Continuous (fun x : Fin n → ℝ ↦ 1 + HGAS.normSq x) := by
    unfold HGAS.normSq HGAS.dot
    fun_prop
  exact hn.sqrt.inv₀ (fun x ↦ (Real.sqrt_pos.mpr (one_add_normSq_pos x)).ne')

theorem continuous_centralLift : Continuous (centralLift (n := n)) := by
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa only [centralLift_last] using continuous_centralScale (n := n)
  · simpa only [centralLift_castSucc] using
      continuous_centralScale.mul (continuous_apply j)

theorem centralScale_hasDerivAt {x : ℝ → Fin n → ℝ} {v : Fin n → ℝ} {t : ℝ}
    (hx : HasDerivAt x v t) :
    HasDerivAt (fun s ↦ centralScale (x s))
      (-(centralScale (x t) ^ 3) * HGAS.dot (x t) v) t := by
  simpa only [one_mul, neg_mul, centralScale] using
    positiveCentralScale_hasDerivAt x (fun _ ↦ v) (fun _ ↦ 1) t
      (fun i ↦ by simpa only [one_mul] using (hasDerivAt_pi.mp hx) i)

theorem centralLift_hasDerivAt {x : ℝ → Fin n → ℝ} {v : Fin n → ℝ} {t : ℝ}
    (hx : HasDerivAt x v t) :
    HasDerivAt (fun s ↦ centralLift (x s))
      (centralScale (x t) • Fin.lastCases 0 v -
        (centralScale (x t) ^ 2 * HGAS.dot (x t) v) • centralLift (x t)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa only [centralLift_last, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Fin.lastCases_last, mul_zero, zero_sub, pow_succ, neg_mul, mul_assoc,
      mul_comm (HGAS.dot (x t) v) (centralScale (x t))] using centralScale_hasDerivAt hx
  · convert (centralScale_hasDerivAt hx).mul ((hasDerivAt_pi.mp hx) j) using 1
    · simp only [centralLift_castSucc]
      rfl
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        Fin.lastCases_castSucc, centralLift_castSucc]
      ring

end

end Stability.ProjectivePolynomialCode
