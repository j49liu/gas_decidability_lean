import HGAS.Modular.ClosedUnaryHorocycleLinkedRootBranches
import HGAS.Modular.HorizontalThetaCesaro
import Mathlib.Tactic

/-!
# The finite closed-cusp mean selector

Suppose a linked unary--Jacobi trajectory has been put in an exact
horizontal cusp chart

```text
  τ(t) = x + s t + i y,      y > 0,      s ≠ 0.
```

The linked residuals and the exact quartic amplitude first give coherent
root branches.  Thus, for one constant nonzero complex scalar in each
line, the coordinates `Y` and `p₄` are:

```text
 cusp          Y                       p₄
 ----------------------------------------------------------
 infinity      yScale · θ₃             p4Scale · θ₄²
 zero          yScale · θ₃             p4Scale · θ₂²
 one           yScale · θ₂             p4Scale · θ₃² .
```

On every nonconstant horizontal line, `θ₂` and `θ₂²` have Cesàro mean
zero, whereas `θ₃`, `θ₄²`, and `θ₃²` have mean one.  Consequently the
normalizations

```text
  Cesàro(Y)  → 1,       Cesàro(p₄) → 1
```

exclude the zero and one cusps.  At the remaining infinity cusp, uniqueness
of limits gives `yScale = p4Scale = 1`.  The coefficient-link residual and
zero-freeness of `θ₄` then force the common quartic amplitude to be exactly
`q = 1`.

All means below are taken along an arbitrary sequence of horizons tending
to `+∞`; no special choice of averaging times is made.
-/

namespace HGAS.Modular

open Filter
open scoped Topology

noncomputable section

/-- The reusable output of the finite closed-cusp selector.

Besides identifying the cusp, the structure retains the coherent root
branches and records both the scalar normalization and the resulting
literal formulas for the two coordinates used by the selector. -/
structure FiniteClosedCuspMeanSelection
    (cusp : GammaTwoCuspLabel)
    (z : ℝ → LinkedJacobiState ℂ)
    (x y s : ℝ) (hy : 0 < y)
    (q : ℂ) where
  branches :
    CuspLinkedRootBranches cusp z
      (fun t ↦ horizontalLine x y s hy t)
  cusp_eq_infinity : cusp = .infinity
  yScale_eq_one : branches.yScale = 1
  p4Scale_eq_one : branches.p4Scale = 1
  q_eq_one : q = 1
  Y_eq_theta₃ :
    ∀ t,
      (z t).unary.Y =
        theta₃ (horizontalLine x y s hy t)
  p4_eq_theta₄_sq :
    ∀ t,
      (z t).jacobi.p4 =
        theta₄ (horizontalLine x y s hy t) ^ 2

/-- Multiplying a function by a fixed scalar commutes with the arbitrary-
horizon Cesàro limit. -/
private theorem tendsto_cesaroMeanAt_const_mul
    (c : ℂ) (f : ℝ → ℂ) {T : ℕ → ℝ} {L : ℂ}
    (h :
      Tendsto
        (fun n ↦ HGAS.Analysis.cesaroMeanAt f (T n))
        atTop (nhds L)) :
    Tendsto
      (fun n ↦
        HGAS.Analysis.cesaroMeanAt (fun t ↦ c * f t) (T n))
      atTop (nhds (c * L)) := by
  simpa only [cesaroMeanAt_const_mul] using h.const_mul c

/-- The finite closed-cusp selector.

The assumptions deliberately expose every bridge used in the argument:
the scaled linked ODE, all algebraic residuals, the pointwise exact
quartic amplitude, a genuine nonzero-speed horizontal line, arbitrary
diverging horizons, and the two raw coordinate means. -/
theorem finiteClosedCuspMeanSelection
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
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    (hmeanY :
      Tendsto
        (fun n ↦
          HGAS.Analysis.cesaroMeanAt
            (fun t ↦ (z t).unary.Y) (T n))
        atTop (nhds 1))
    (hmeanP4 :
      Tendsto
        (fun n ↦
          HGAS.Analysis.cesaroMeanAt
            (fun t ↦ (z t).jacobi.p4) (T n))
        atTop (nhds 1)) :
    Nonempty (FiniteClosedCuspMeanSelection cusp z x y s hy q) := by
  obtain ⟨branches⟩ :=
    exists_cuspLinkedRootBranches_horizontalLine
      cusp z hz x y s hy q hq hamplitude hresidual
  cases cusp with
  | infinity =>
      have htheta₃ :=
        cesaroMeanAt_theta₃_horizontalLine_tendsto_one
          x y s hy hs hT
      have hYfromBranch :
          Tendsto
            (fun n ↦
              HGAS.Analysis.cesaroMeanAt
                (fun t ↦ (z t).unary.Y) (T n))
            atTop (nhds branches.yScale) := by
        have hscaled :=
          tendsto_cesaroMeanAt_const_mul
            branches.yScale
            (fun t ↦ theta₃ (horizontalLine x y s hy t))
            htheta₃
        simpa only [
          branches.y_eq, cuspYRoot, mul_one] using hscaled
      have hyScale : branches.yScale = 1 :=
        tendsto_nhds_unique hYfromBranch hmeanY
      have htheta₄sq :=
        cesaroMeanAt_theta₄_sq_horizontalLine_tendsto_one
          x y s hy hs hT
      have hp4fromBranch :
          Tendsto
            (fun n ↦
              HGAS.Analysis.cesaroMeanAt
                (fun t ↦ (z t).jacobi.p4) (T n))
            atTop (nhds branches.p4Scale) := by
        have hscaled :=
          tendsto_cesaroMeanAt_const_mul
            branches.p4Scale
            (fun t ↦
              theta₄ (horizontalLine x y s hy t) ^ 2)
            htheta₄sq
        simpa only [
          branches.p4_eq, cuspP4Root, mul_one] using hscaled
      have hp4Scale : branches.p4Scale = 1 :=
        tendsto_nhds_unique hp4fromBranch hmeanP4
      have hp4square :
          (z 0).jacobi.p4 ^ 2 = (z 0).unary.C := by
        have hR := hresidual 0 .coefficientLinkFour
        change
          (z 0).jacobi.p4 ^ 2 - (z 0).unary.C = 0 at hR
        exact sub_eq_zero.mp hR
      have hC :
          (z 0).unary.C =
            q * H₄ (horizontalLine x y s hy 0) :=
        (hamplitude 0).2.2.2
      have hquartic :
          theta₄ (horizontalLine x y s hy 0) ^ 4 =
            q * theta₄ (horizontalLine x y s hy 0) ^ 4 := by
        rw [branches.p4_eq 0, hp4Scale, one_mul, hC] at hp4square
        calc
          theta₄ (horizontalLine x y s hy 0) ^ 4 =
              (theta₄ (horizontalLine x y s hy 0) ^ 2) ^ 2 := by
            ring
          _ = q * theta₄ (horizontalLine x y s hy 0) ^ 4 := by
            simpa only [cuspP4Root, H₄] using hp4square
      have htheta₄fourth :
          theta₄ (horizontalLine x y s hy 0) ^ 4 ≠ 0 :=
        pow_ne_zero 4
          (theta₄_ne_zero (horizontalLine x y s hy 0))
      have hqOne : q = 1 := by
        apply mul_right_cancel₀ htheta₄fourth
        simpa only [one_mul] using hquartic.symm
      refine ⟨{
        branches := branches
        cusp_eq_infinity := rfl
        yScale_eq_one := hyScale
        p4Scale_eq_one := hp4Scale
        q_eq_one := hqOne
        Y_eq_theta₃ := ?_
        p4_eq_theta₄_sq := ?_
      }⟩
      · intro t
        simpa only [cuspYRoot, hyScale, one_mul] using
          branches.y_eq t
      · intro t
        simpa only [cuspP4Root, hp4Scale, one_mul] using
          branches.p4_eq t
  | zero =>
      have htheta₂sq :=
        cesaroMeanAt_theta₂_sq_horizontalLine_tendsto_zero
          x y s hy hs hT
      have hp4zero :
          Tendsto
            (fun n ↦
              HGAS.Analysis.cesaroMeanAt
                (fun t ↦ (z t).jacobi.p4) (T n))
            atTop (nhds 0) := by
        have hscaled :=
          tendsto_cesaroMeanAt_const_mul
            branches.p4Scale
            (fun t ↦
              theta₂ (horizontalLine x y s hy t) ^ 2)
            htheta₂sq
        simpa only [
          branches.p4_eq, cuspP4Root, mul_zero] using hscaled
      have hzeroOne : (0 : ℂ) = 1 :=
        tendsto_nhds_unique hp4zero hmeanP4
      exact (zero_ne_one hzeroOne).elim
  | one =>
      have htheta₂ :=
        cesaroMeanAt_theta₂_horizontalLine_tendsto_zero
          x y s hy hs hT
      have hYzero :
          Tendsto
            (fun n ↦
              HGAS.Analysis.cesaroMeanAt
                (fun t ↦ (z t).unary.Y) (T n))
            atTop (nhds 0) := by
        have hscaled :=
          tendsto_cesaroMeanAt_const_mul
            branches.yScale
            (fun t ↦ theta₂ (horizontalLine x y s hy t))
            htheta₂
        simpa only [
          branches.y_eq, cuspYRoot, mul_zero] using hscaled
      have hzeroOne : (0 : ℂ) = 1 :=
        tendsto_nhds_unique hYzero hmeanY
      exact (zero_ne_one hzeroOne).elim

end

end HGAS.Modular
