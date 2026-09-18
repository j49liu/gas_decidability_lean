import HGAS.Compiler.ComplexGaugeFamilyPolynomialCode
import HGAS.Modular.GaugeFourthRootDynamics
import Mathlib.Tactic

/-!
# Dynamic propagation of compiled gauge residuals

The polynomial compiler is algebraic; this file supplies its trajectory
semantics.  If a source character satisfies

```text
                         χ' = iνχ
```

and the adjoined gauge satisfies

```text
                         G' = (iν/4)G,
```

then `G⁴-λχ` obeys the homogeneous scalar equation

```text
                    (G⁴-λχ)' = iν(G⁴-λχ).
```

Continuity of `ν` and uniqueness for scalar linear ODEs therefore propagate
the gauge equation from one time to every real time.  The statement is
componentwise and works for an arbitrary finite gauge family, including
the empty family.
-/

namespace HGAS

namespace ComplexGaugeFamilyPolynomialCode

open _root_.MvPolynomial
open Clocks.ControllerPhaseProductCharacterCode

noncomputable section

variable {n b : ℕ}

/-- One component of a genuine compiled gauge trajectory is an instance of
the reusable fourth-root trajectory interface. -/
theorem isGaugeFourthRootTrajectory_component
    (frequency : Fin b → PolynomialCode n)
    (scale : Fin b → RationalCode)
    (character : ObservableFamily n b)
    (z : ℝ → State n b)
    (a : Fin b)
    (hfrequency :
      Continuous
        (fun t ↦ evalRealObservable (frequency a) (z t).1))
    (hcharacter :
      ∀ t,
        HasDerivAt
          (fun s ↦ evalPair (character a) (z s).1)
          (Complex.I *
            (evalRealObservable (frequency a) (z t).1 : ℂ) *
              evalPair (character a) (z t).1) t)
    (hgauge :
      ∀ t,
        HasDerivAt
          (fun s ↦ (z s).2 a)
          (gaugeVelocity frequency (z t) a) t) :
    Modular.IsGaugeFourthRootTrajectory
      (fun t ↦
        Complex.I *
          ((evalRealObservable (frequency a) (z t).1 / 4 : ℝ) : ℂ))
      (fun t ↦ (z t).2 a)
      (fun t ↦
        ((RationalCode.decode (scale a) : ℝ) : ℂ) *
          evalPair (character a) (z t).1) where
  G_eq := by
    intro t
    simpa [gaugeVelocity] using hgauge t
  C_eq := by
    intro t
    have h :=
      (hasDerivAt_const t
        (((RationalCode.decode (scale a) : ℝ) : ℂ))).mul
        (hcharacter t)
    convert h using 1
    push_cast
    ring
  continuous_a := by
    exact
      continuous_const.mul
        (Complex.continuous_ofReal.comp
          (hfrequency.div_const 4))

/-- A vanishing compiled gauge residual propagates in one component. -/
theorem residual_eq_zero_along_trajectory
    (frequency : Fin b → PolynomialCode n)
    (scale : Fin b → RationalCode)
    (character : ObservableFamily n b)
    (z : ℝ → State n b)
    (a : Fin b)
    (hfrequency :
      Continuous
        (fun t ↦ evalRealObservable (frequency a) (z t).1))
    (hcharacter :
      ∀ t,
        HasDerivAt
          (fun s ↦ evalPair (character a) (z s).1)
          (Complex.I *
            (evalRealObservable (frequency a) (z t).1 : ℂ) *
              evalPair (character a) (z t).1) t)
    (hgauge :
      ∀ t,
        HasDerivAt
          (fun s ↦ (z s).2 a)
          (gaugeVelocity frequency (z t) a) t)
    {t₀ : ℝ}
    (hzero : residual scale character (z t₀) a = 0) :
    ∀ t, residual scale character (z t) a = 0 := by
  let C : ℝ → ℂ :=
    fun t ↦
      ((RationalCode.decode (scale a) : ℝ) : ℂ) *
        evalPair (character a) (z t).1
  have htrajectory :=
    isGaugeFourthRootTrajectory_component
      frequency scale character z a
      hfrequency hcharacter hgauge
  have hzero' :
      Modular.gaugeFourthRootResidual ((z t₀).2 a) (C t₀) = 0 := by
    simpa [C, residual, Modular.gaugeFourthRootResidual] using hzero
  have hall := htrajectory.residual_eq_zero hzero'
  intro t
  simpa [C, residual, Modular.gaugeFourthRootResidual] using hall t

/-- Simultaneous version for every component of a finite gauge family. -/
theorem forall_residual_eq_zero_along_trajectory
    (frequency : Fin b → PolynomialCode n)
    (scale : Fin b → RationalCode)
    (character : ObservableFamily n b)
    (z : ℝ → State n b)
    (hfrequency :
      ∀ a,
        Continuous
          (fun t ↦ evalRealObservable (frequency a) (z t).1))
    (hcharacter :
      ∀ a t,
        HasDerivAt
          (fun s ↦ evalPair (character a) (z s).1)
          (Complex.I *
            (evalRealObservable (frequency a) (z t).1 : ℂ) *
              evalPair (character a) (z t).1) t)
    (hgauge :
      ∀ a t,
        HasDerivAt
          (fun s ↦ (z s).2 a)
          (gaugeVelocity frequency (z t) a) t)
    {t₀ : ℝ}
    (hzero : ∀ a, residual scale character (z t₀) a = 0) :
    ∀ t a, residual scale character (z t) a = 0 := by
  intro t a
  exact
    residual_eq_zero_along_trajectory
      frequency scale character z a
      (hfrequency a) (hcharacter a) (hgauge a)
      (hzero a) t

end

end ComplexGaugeFamilyPolynomialCode

end HGAS
