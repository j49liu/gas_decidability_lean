import HGAS.Dynamics.AngularGAS
import HGAS.Dynamics.LinearConjugacyGAS
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

/-!
# Regularity, homogeneity, and Lyapunov data under linear conjugacy

`LinearConjugacyGAS` proves that global asymptotic stability is invariant
under a continuous linear change of coordinates.  This companion module
records the three corresponding facts needed by converse-Lyapunov
arguments:

* differentiability is preserved;
* a homogeneous field keeps the same degree; and
* a strict homogeneous `C¹` Lyapunov function for the conjugated field
  pulls back to one for the original field.

Keeping these facts independent of coordinates makes it safe to pass
between finite coordinate functions (with their convenient polynomial
syntax) and a genuine Euclidean `ℓ²` space (with its canonical inner
product).
-/

namespace HGAS

noncomputable section

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

namespace StrictHomogeneousC1Lyapunov

variable {F : E → E} {degree : ℕ}

/-- Pull a strict homogeneous Lyapunov function through a continuous
linear coordinate equivalence. -/
noncomputable def pullback_conjugateField
    (e : E ≃L[ℝ] H)
    (L : StrictHomogeneousC1Lyapunov
      (conjugateField e F) degree) :
    StrictHomogeneousC1Lyapunov F degree where
  V := fun x ↦ L.V (e x)
  contDiff := L.contDiff.comp e.contDiff
  degree_pos := L.degree_pos
  homogeneous := by
    intro s hs x
    rw [map_smul, L.homogeneous s hs]
  positive := by
    intro x hx
    exact L.positive (e x) (by
      simpa using e.injective.ne hx)
  decreases := by
    intro x hx
    have hex : e x ≠ 0 :=
      by simpa using e.injective.ne hx
    have hcomp :
        HasFDerivAt (fun y ↦ L.V (e y))
          ((fderiv ℝ L.V (e x)).comp
            e.toContinuousLinearMap) x :=
      (L.contDiff.differentiable (by norm_num)
        (e x)).hasFDerivAt.comp x
          e.toContinuousLinearMap.hasFDerivAt
    rw [hcomp.fderiv]
    simpa only [ContinuousLinearMap.comp_apply,
      conjugateField_apply_equiv] using
        L.decreases (e x) hex

end StrictHomogeneousC1Lyapunov

end

end HGAS
