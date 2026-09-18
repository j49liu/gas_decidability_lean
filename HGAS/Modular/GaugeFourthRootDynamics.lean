import HGAS.Analysis.LinearODEZero
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
# Invariance of a fourth-root gauge link

The Jacobi chart contains a gauge coordinate `G` and a clock monomial `C`
linked by

```
                              G⁴ = C.
```

For the two derivations in the written proof, `G` has logarithmic
derivative `i/4` or `i/2`, while `C` has the corresponding logarithmic
derivative `i` or `2i`.  The following reusable lemma isolates the only
algebra involved:

```
 G' = aG,  C' = 4aC
       ⟹
 (G⁴-C)' = 4a(G⁴-C).
```

The coefficient `a` may vary continuously with real time.  Hence the
gauge link is not merely formally invariant: ordinary linear-ODE
uniqueness propagates it along every trajectory.
-/

namespace HGAS.Modular

open HGAS

noncomputable section

/-- The fourth-root gauge residual. -/
def gaugeFourthRootResidual
    (G C : ℂ) : ℂ :=
  G ^ 4 - C

/-- Pointwise calculus identity for the fourth-root gauge residual. -/
theorem gaugeFourthRootResidual_hasDerivAt
    {G C : ℝ → ℂ} {a : ℂ} {t : ℝ}
    (hG : HasDerivAt G (a * G t) t)
    (hC : HasDerivAt C (4 * a * C t) t) :
    HasDerivAt
      (fun s ↦ gaugeFourthRootResidual (G s) (C s))
      (4 * a *
        gaugeFourthRootResidual (G t) (C t)) t := by
  have hraw := (hG.fun_pow 4).sub hC
  convert hraw using 1
  simp only [gaugeFourthRootResidual]
  ring

/-- A trajectory carrying a gauge fourth root and its fourth power, with
a possibly time-dependent logarithmic coefficient. -/
structure IsGaugeFourthRootTrajectory
    (a G C : ℝ → ℂ) : Prop where
  G_eq : ∀ t, HasDerivAt G (a t * G t) t
  C_eq : ∀ t, HasDerivAt C (4 * a t * C t) t
  continuous_a : Continuous a

namespace IsGaugeFourthRootTrajectory

variable {a G C : ℝ → ℂ}

theorem residual_hasDerivAt
    (h : IsGaugeFourthRootTrajectory a G C)
    (t : ℝ) :
    HasDerivAt
      (fun s ↦ gaugeFourthRootResidual (G s) (C s))
      ((4 * a t) *
        gaugeFourthRootResidual (G t) (C t)) t := by
  exact gaugeFourthRootResidual_hasDerivAt
    (h.G_eq t) (h.C_eq t)

/-- A vanishing gauge link propagates for all real time. -/
theorem residual_eq_zero
    (h : IsGaugeFourthRootTrajectory a G C)
    {t₀ : ℝ}
    (hzero :
      gaugeFourthRootResidual (G t₀) (C t₀) = 0) :
    ∀ t, gaugeFourthRootResidual (G t) (C t) = 0 := by
  have hcoeff : Continuous (fun t ↦ 4 * a t) :=
    continuous_const.mul h.continuous_a
  have hident :=
    complex_eq_zero_of_hasDerivAt_eq_mul
      (fun t ↦ 4 * a t)
      (fun t ↦ gaugeFourthRootResidual (G t) (C t))
      hcoeff h.residual_hasDerivAt hzero
  intro t
  exact congrFun hident t

end IsGaugeFourthRootTrajectory

end

end HGAS.Modular
