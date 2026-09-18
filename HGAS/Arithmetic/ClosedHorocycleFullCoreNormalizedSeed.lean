import HGAS.Arithmetic.FixedDetectorNormalizedForwardBlochColumn
import HGAS.Modular.GammaTwoClosedHorocycleCuspNormalization
import Mathlib.Tactic

/-!
# Closed-horocycle charts and full-core detector normalization

This file keeps two logically different normalization steps separate.

First, a primitive-row completion converts a closed horocycle into the
explicit affine path

```text
        τ(t) = a b + a² σ t + i a².
```

The structure `ClosedHorocycleAffineChart` records the exact
identification of these three real coefficients with the affine Bloch
parameters `u₀`, `γ`, and `κ`.  It also retains the six-valued mod-two
characteristic label of the integral completion and its three-valued
level-two cusp label.

Second, the theta/Jacobi normalization must identify the *entire*
reciprocal-free Jacobi core at time zero.  A twisted theta seed alone
does not imply this polynomial-state equality.  The structure
`ClosedHorocycleFullCoreNormalization` therefore names that remaining
obligation `fullCore_transport`.  Once it and the other detector
normalizations are supplied, `toNormalizedSeed` constructs the exact
forward seed consumed by the rigorous continuation theorem.
-/

namespace HGAS

open Set
open Modular
open Clocks
open Clocks.ControllerPhaseProductCharacterCode

noncomputable section

namespace ClosedHorocycleFullCoreNormalizedSeed

open FixedDetectorForwardSubtrajectoryCrosswalk
open FixedDetectorForwardTrajectoryReverseCrosswalk
open FixedDetectorOrdinaryTimeBlochCrosswalk
open FixedDetectorReverseTrajectoryCrosswalk

variable {eqs vars : ℕ}

/-- An affine Bloch modular path together with its exact normalized
closed-horocycle chart. -/
structure ClosedHorocycleAffineChart
    (p : AffineBlochParameters) where
  frame : RealModularFrame
  primitiveRow : PrimitiveIntegralRow
  horizontalization :
    PrimitiveRowHorizontalization primitiveRow frame
  orbitSpeed : ℝ
  orbitSpeed_ne_zero : orbitSpeed ≠ 0
  u0_eq :
    p.u0 =
      horizontalization.upperLeft *
        horizontalization.upperRight
  gamma_eq :
    p.gamma = horizontalization.upperLeft ^ 2
  kappa_eq :
    p.kappa =
      horizontalization.upperLeft ^ 2 * orbitSpeed

namespace ClosedHorocycleAffineChart

/-- The primitive row stored in a chart is horizontal for its frame. -/
theorem primitiveRowMul_fst_eq_zero
    {p : AffineBlochParameters}
    (c : ClosedHorocycleAffineChart p) :
    primitiveIntegralRowMul c.primitiveRow c.frame 0 = 0 := by
  rw [← integralCompletion_lowerLeft_eq_rowMul
    c.primitiveRow c.frame c.horizontalization.completion
    c.horizontalization.completion_row_zero
    c.horizontalization.completion_row_one]
  rw [c.horizontalization.completedFrame_eq]
  rfl

/-- Hence every chart really does lie over a periodic `Γ(2)`
horocycle. -/
theorem isPeriodicHorocyclePoint
    {p : AffineBlochParameters}
    (c : ClosedHorocycleAffineChart p) :
    IsPeriodicHorocyclePoint 1
      (gammaTwoFrameQuotientMk c.frame) := by
  exact
    isPeriodicHorocyclePoint_of_primitiveRowMul_fst_eq_zero
      c.primitiveRow c.frame c.primitiveRowMul_fst_eq_zero

/-- The modular parameter of the affine Bloch path is exactly the
base path of the completed, scaled horocycle. -/
theorem tau_eq_completed_scaledOrbit
    {p : AffineBlochParameters}
    (c : ClosedHorocycleAffineChart p)
    (t : ℝ) :
    p.tau t =
      realModularFrameBasePoint
        (c.horizontalization.completion •
          (c.frame *
            upperUnipotent (c.orbitSpeed * t))) := by
  rw [c.horizontalization.basePath_scaled_eq_horizontal]
  apply UpperHalfPlane.coe_injective
  apply Complex.ext
  · simp [c.u0_eq, c.kappa_eq]
  · simp [c.gamma_eq]

/-- The affine horizontal speed in the chart is nonzero. -/
theorem kappa_ne_zero
    {p : AffineBlochParameters}
    (c : ClosedHorocycleAffineChart p) :
    p.kappa ≠ 0 := by
  rw [c.kappa_eq]
  exact
    c.horizontalization.scaledSpeed_ne_zero
      c.orbitSpeed_ne_zero

/-- Six-valued theta characteristic of the chosen integral
completion. -/
def characteristicLabel
    {p : AffineBlochParameters}
    (c : ClosedHorocycleAffineChart p) :
    LevelTwoCharacteristicLabel :=
  c.horizontalization.characteristicLabel

/-- Three-valued cusp supporting the closed horocycle. -/
def cuspLabel
    {p : AffineBlochParameters}
    (c : ClosedHorocycleAffineChart p) :
    GammaTwoCuspLabel :=
  c.horizontalization.cuspLabel

/-- The cusp-normalized completion differs from the chosen cusp
representative by an element of `Γ(2)`. -/
theorem cuspNormalizedGammaTwoFactor_mem
    {p : AffineBlochParameters}
    (c : ClosedHorocycleAffineChart p) :
    cuspNormalizedGammaTwoFactor
        c.horizontalization.completion ∈
      GammaTwo :=
  Modular.cuspNormalizedGammaTwoFactor_mem
    c.horizontalization.completion

end ClosedHorocycleAffineChart

/-- Affine Bloch parameters canonically associated with a completed
primitive row and a scaled horocycle, while leaving the elliptic and
Bloch data free. -/
def affineBlochParametersOfHorizontalization
    {v : PrimitiveIntegralRow}
    {g : RealModularFrame}
    (h : PrimitiveRowHorizontalization v g)
    (σ : ℝ)
    (w0 : ℂ) (nu : ℝ)
    (a0 b0 c0 : ℂ) :
    AffineBlochParameters where
  u0 := h.upperLeft * h.upperRight
  gamma := h.upperLeft ^ 2
  kappa := h.upperLeft ^ 2 * σ
  gamma_pos := sq_pos_of_ne_zero h.upperLeft_ne_zero
  w0 := w0
  nu := nu
  a0 := a0
  b0 := b0
  c0 := c0

/-- The preceding canonical parameter choice carries its tautological
closed-horocycle chart. -/
def canonicalClosedHorocycleAffineChart
    {v : PrimitiveIntegralRow}
    {g : RealModularFrame}
    (h : PrimitiveRowHorizontalization v g)
    (σ : ℝ) (hσ : σ ≠ 0)
    (w0 : ℂ) (nu : ℝ)
    (a0 b0 c0 : ℂ) :
    ClosedHorocycleAffineChart
      (affineBlochParametersOfHorizontalization
        h σ w0 nu a0 b0 c0) where
  frame := g
  primitiveRow := v
  horizontalization := h
  orbitSpeed := σ
  orbitSpeed_ne_zero := hσ
  u0_eq := rfl
  gamma_eq := rfl
  kappa_eq := rfl

/-- All data required to turn a normalized closed-horocycle column into
the full-core forward detector seed.

The field `fullCore_transport` is intentionally an equality of
`jacobiCorePoint`s, not an equality of one twisted theta coordinate.
This makes the exact remaining theta-transformation obligation visible
at the interface boundary. -/
structure ClosedHorocycleFullCoreNormalization
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters)
    (d : ℂ) : Type where
  chart : ClosedHorocycleAffineChart p
  structured :
    IsForwardStructuredTrajectory parameters I x x₀
  controller_lock :
    ∀ i,
      Controller.IsControllerEquilibrium
        (RationalCode.decode (parameters i) : ℝ)
        (controller i)
  controllers_zero :
    (recoveredState x 0).base.base.source.controllers =
      CanonicalFixedDetectorTrajectory.clockPath
        parameters controller phase₀ 0
  reciprocal :
    ∀ t, 0 ≤ t →
      ((recoveredState x t).base.base.source.linked j).jacobi.U *
          ((recoveredState x t).base.base.source.linked j).jacobi.T1 =
        1
  fullCore_transport :
    jacobiCorePoint
        ((recoveredState x 0).base.base.source.linked j).jacobi =
      jacobiCorePoint (p.jacobiBlochPath 0)
  gauge_zero :
    (recoveredState x 0).base.base.gauge j =
      p.fourthRootGauge d 0
  clocks :
    MatchesDetectorClocksRealPi p
      (CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j)
      (CanonicalFixedDetectorTrajectory.numberFrequency
        parameters I controller j)
  c0_ne_zero : p.c0 ≠ 0

namespace ClosedHorocycleFullCoreNormalization

/-- Forgetting the closed-orbit chart yields precisely the strict
full-core seed used by forward Jacobi continuation. -/
theorem toNormalizedSeed
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters)
    (d : ℂ)
    (h :
      ClosedHorocycleFullCoreNormalization
        parameters I x x₀ controller phase₀ j p d) :
    FixedDetectorNormalizedForwardBlochColumn.NormalizedSeed
      parameters I x x₀ controller phase₀ j p d where
  structured := h.structured
  controller_lock := h.controller_lock
  controllers_zero := h.controllers_zero
  reciprocal := h.reciprocal
  jacobi_core_zero := h.fullCore_transport
  gauge_zero := h.gauge_zero
  clocks := h.clocks
  c0_ne_zero := h.c0_ne_zero

/-- The modular path attached to a full-core normalization is the exact
completed horocycle path, not merely a circle-locus description. -/
theorem tau_eq_completed_scaledOrbit
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters)
    (d : ℂ)
    (h :
      ClosedHorocycleFullCoreNormalization
        parameters I x x₀ controller phase₀ j p d)
    (t : ℝ) :
    p.tau t =
      realModularFrameBasePoint
        (h.chart.horizontalization.completion •
          (h.chart.frame *
            upperUnipotent (h.chart.orbitSpeed * t))) :=
  h.chart.tau_eq_completed_scaledOrbit t

/-- The full-core normalization therefore supplies the pointwise
compiled Bloch identity on every nonnegative physical time. -/
theorem matchesCompiledGaugedBlochPhaseAt
    (parameters :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        RationalCode)
    (I : DQLSystem eqs vars)
    (x :
      ℝ →
        Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (x₀ :
      Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ)
    (controller :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ :
      Fin (FixedDetectorPolynomialCode.clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters)
    (d : ℂ)
    (h :
      ClosedHorocycleFullCoreNormalization
        parameters I x x₀ controller phase₀ j p d) :
    ∀ t, 0 ≤ t →
      MatchesCompiledGaugedBlochPhaseAt
        parameters controller phase₀ j p d t
        (recoveredState x t) := by
  exact
    FixedDetectorNormalizedForwardBlochColumn.matchesCompiledGaugedBlochPhaseAt
      parameters I x x₀ controller phase₀ j p d
        (toNormalizedSeed
          parameters I x x₀ controller phase₀ j p d h)

end ClosedHorocycleFullCoreNormalization

end ClosedHorocycleFullCoreNormalizedSeed

end

end HGAS
