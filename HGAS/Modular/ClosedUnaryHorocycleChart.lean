import HGAS.Modular.ClosedHorocycleUnaryCuspBranch
import HGAS.Modular.RecurrentLiftExactFrame

/-!
# Exact horizontal cusp charts for periodic unary lifts

This file packages the data needed after the modular
periodic/nonperiodic dichotomy.  A literal frame-valued lift

```text
        T(t) = basePoint (g * upperUnipotent (σ t))
```

whose level-two frame orbit is periodic admits a primitive integral row.
Completing that row and applying the one-step cusp normalization produces
an exact horizontal modulus.  At the same time, every generic unary state
over `T(t)` lies in one of the three projective theta branches.

The package deliberately retains:

* the original real frame and signed speed;
* the primitive row and its integral completion;
* the finite cusp label;
* the exact horizontal speed; and
* the projective quartic identity at every time.

These are the inputs used by the finite moment selector.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I

noncomputable section

/-- A periodic frame-valued canonical-lambda lift together with one
primitive-row horizontalization. -/
structure ClosedUnaryHorocycleChart
    (z : ℝ → UnaryModularState ℂ)
    (T : ℝ → UpperHalfPlane) where
  frame : RealModularFrame
  orbitSpeed : ℝ
  orbitSpeed_ne_zero : orbitSpeed ≠ 0
  lift_eq :
    ∀ t,
      T t =
        realModularFrameBasePoint
          (frame * upperUnipotent (orbitSpeed * t))
  periodic :
    IsPeriodicHorocyclePoint 1
      (gammaTwoFrameQuotientMk frame)
  primitiveRow : PrimitiveIntegralRow
  horizontalization :
    PrimitiveRowHorizontalization primitiveRow frame

namespace ClosedUnaryHorocycleChart

variable {z : ℝ → UnaryModularState ℂ}
  {T : ℝ → UpperHalfPlane}

/-- The cusp label of the normalized horizontal chart. -/
def cuspLabel
    (c : ClosedUnaryHorocycleChart z T) :
    GammaTwoCuspLabel :=
  c.horizontalization.cuspLabel

/-- Modulus obtained by applying the normalized integral completion to
the original lift. -/
def horizontalModulus
    (c : ClosedUnaryHorocycleChart z T)
    (t : ℝ) : UpperHalfPlane :=
  c.horizontalization.cuspNormalizedModulus (T t)

/-- The completed modulus is the explicit horizontal line supplied by
the primitive row. -/
theorem horizontalModulus_eq
    (c : ClosedUnaryHorocycleChart z T)
    (t : ℝ) :
    c.horizontalModulus t =
      horizontalLine
        (c.horizontalization.cuspNormalized.upperLeft *
          c.horizontalization.cuspNormalized.upperRight)
        (c.horizontalization.cuspNormalized.upperLeft ^ 2)
        (c.horizontalization.cuspNormalized.upperLeft ^ 2 *
          c.orbitSpeed)
        (sq_pos_of_ne_zero
          c.horizontalization.cuspNormalized.upperLeft_ne_zero)
        t := by
  unfold horizontalModulus
    PrimitiveRowHorizontalization.cuspNormalizedModulus
  rw [c.lift_eq]
  rw [← realModularFrameBasePoint_integral_smul]
  exact
    c.horizontalization.cuspNormalized.basePath_scaled_eq_horizontal
      c.orbitSpeed t

/-- The horizontal speed is nonzero. -/
theorem horizontalSpeed_ne_zero
    (c : ClosedUnaryHorocycleChart z T) :
    c.horizontalization.cuspNormalized.upperLeft ^ 2 *
        c.orbitSpeed ≠ 0 :=
  c.horizontalization.cuspNormalized.scaledSpeed_ne_zero
    c.orbitSpeed_ne_zero

/-- Along a generic lambda lift, the unary quartics lie in the cusp
branch of the exact horizontal chart at every time. -/
theorem isCuspQuarticBranch
    (c : ClosedUnaryHorocycleChart z T)
    (hB : ∀ t, UnaryModularState.B (z t) ≠ 0)
    (hC : ∀ t, (z t).C ≠ 0)
    (hlambda :
      ∀ t,
        UnaryModularState.lambdaCoordinate (z t) =
          canonicalLambda (T t))
    (t : ℝ) :
    IsCuspQuarticBranch c.cuspLabel
      (z t) (c.horizontalModulus t) := by
  exact
    c.horizontalization.isCuspQuarticBranch
      (z t) (T t) (hB t) (hC t) (hlambda t)

end ClosedUnaryHorocycleChart

/-- A literal nonzero-speed frame lift on a periodic level-two orbit
admits a closed unary horocycle chart. -/
theorem exists_closedUnaryHorocycleChart
    (z : ℝ → UnaryModularState ℂ)
    (T : ℝ → UpperHalfPlane)
    (g : RealModularFrame) (σ : ℝ)
    (hσ : σ ≠ 0)
    (hlift :
      ∀ t,
        T t =
          realModularFrameBasePoint
            (g * upperUnipotent (σ * t)))
    (hperiodic :
      IsPeriodicHorocyclePoint 1
        (gammaTwoFrameQuotientMk g)) :
    Nonempty (ClosedUnaryHorocycleChart z T) := by
  obtain ⟨v, ⟨h⟩⟩ :=
    exists_primitiveRowHorizontalization_of_isPeriodicHorocyclePoint
      g hperiodic
  exact
    ⟨{
      frame := g
      orbitSpeed := σ
      orbitSpeed_ne_zero := hσ
      lift_eq := hlift
      periodic := hperiodic
      primitiveRow := v
      horizontalization := h
    }⟩

end

end HGAS.Modular
