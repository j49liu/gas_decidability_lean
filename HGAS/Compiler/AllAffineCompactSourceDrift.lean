import HGAS.Compiler.AllAffineCompactSourceClock
import Mathlib.Tactic

/-!
# Drift observables in the finite all-affine chart

For a one-block central compactification with exponent `2K`, the compact
accumulator drift is

```
                    κ w^(2K) h(z)
              =     κ a_K(z) h(z).
```

This file bundles its pullback to the invariant finite source chart as a
bounded continuous observable and proves that identity exactly.  The
result is the pointwise bridge used to convert compact-time Birkhoff
averages into ordinary-time detector moments.
-/

namespace HGAS

open _root_.MvPolynomial
open Set
open scoped BoundedContinuousFunction

noncomputable section

namespace CompactAccumulatorPipelineCode

namespace AllAffineCompactSourceDrift

open AllAffineCompactSourceChart
open AllAffineCompactSourceTrajectory

variable {n m : ℕ}

/-- Pull the complete compact-base drift vector back to the finite source
chart. -/
def finiteDriftBCF
    (K : ℕ) (κ : RationalCode)
    (h : Fin m → PolynomialCode n) :
    FiniteSourceSpace n m →ᵇ FinVector m ℝ :=
  (baseDriftBCF (layout n) (2 * K) κ h).compContinuous
    ⟨restrictedBaseProjection (m := m) (layout n),
      continuous_restrictedBaseProjection (m := m) (layout n)⟩

@[simp]
theorem finiteDriftBCF_apply
    (K : ℕ) (κ : RationalCode)
    (h : Fin m → PolynomialCode n)
    (v : FiniteSourceSpace n m) :
    finiteDriftBCF K κ h v =
      baseDriftBCF (layout n) (2 * K) κ h
        (restrictedBaseProjection (layout n) v) :=
  rfl

/-- One real drift coordinate, bundled separately for finite-family
pointwise ergodic selection. -/
def finiteDriftCoordinateBCF
    (K : ℕ) (κ : RationalCode)
    (h : Fin m → PolynomialCode n) (i : Fin m) :
    FiniteSourceSpace n m →ᵇ ℝ :=
  let g := finiteDriftBCF K κ h
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun v ↦ g v i)
    ((continuous_apply i).comp g.continuous)
    ‖g‖
    (fun v ↦
      (norm_le_pi_norm (g v) i).trans
        (g.norm_coe_le_norm v))

@[simp]
theorem finiteDriftCoordinateBCF_apply
    (K : ℕ) (κ : RationalCode)
    (h : Fin m → PolynomialCode n) (i : Fin m)
    (v : FiniteSourceSpace n m) :
    finiteDriftCoordinateBCF K κ h i v =
      baseDriftBCF (layout n) (2 * K) κ h
        (restrictedBaseProjection (layout n) v) i :=
  rfl

/-- Exact finite-chart semantics of one compact drift coordinate. -/
theorem finiteDriftCoordinateBCF_eq
    (K : ℕ) (κ : RationalCode)
    (h : Fin m → PolynomialCode n)
    (hh :
      ∀ i,
        MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
          (layout n) (2 * K) (h i))
    (i : Fin m) (v : FiniteSourceSpace n m) :
    finiteDriftCoordinateBCF K κ h i v =
      (RationalCode.decode κ : ℝ) *
        affineSpeed K (affinePoint v) *
          eval₂Hom (algebraMap ℚ ℝ) (affinePoint v)
            (PolynomialCode.decode (h i)) := by
  rw [finiteDriftCoordinateBCF_apply,
    baseDriftBCF_apply]
  change
    eval₂Hom (algebraMap ℚ ℝ)
        (sourceBasePoint v.1)
        (PolynomialCode.decode
          (slowedDriftCode (layout n) (2 * K) κ h i)) =
      _
  rw [← scaledChartPoint_affinePoint v]
  rw [eval₂Hom_slowedDriftCode_scaledChart
    (layout n) (2 * K) κ h hh i
    (fun _ ↦ weight v.1) (affinePoint v)]
  rw [slowdown_eq_weight_pow,
    weight_evenPow_eq_affineSpeed]

end AllAffineCompactSourceDrift

end CompactAccumulatorPipelineCode

end

end HGAS
