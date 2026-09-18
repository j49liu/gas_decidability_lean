import HGAS.Modular.ClosedUnaryHorocycleExactAmplitude
import HGAS.Modular.CanonicalLambdaLocal

/-!
# Exact amplitude for an already horizontal unary lift

The affine branch of the recurrent lift classification needs no cusp
completion.  Its lift is already

```text
                          T(t) = x + s t + i y.
```

The derivative comparison forces `s` to be nonzero on the generic
locus, and the unary quartics have literal amplitude `s` in the infinity
branch.  This file packages both conclusions without requiring the caller
to separately prove nonvanishing of the horizontal speed.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I

noncomputable section

/-- A generic standard-clock unary trajectory whose lambda lift is a
horizontal line has nonzero speed and exact infinity-cusp amplitude equal
to that speed. -/
theorem hasCuspQuarticAmplitude_of_horizontalLine
    {z : ℝ → UnaryModularState ℂ}
    {T : ℝ → UpperHalfPlane}
    (hz :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock z)
    (hB : ∀ t, UnaryModularState.B (z t) ≠ 0)
    (hlambda :
      ∀ t,
        UnaryModularState.lambdaCoordinate (z t) =
          canonicalLambda (T t))
    (x y s : ℝ) (hy : 0 < y)
    (hline :
      ∀ t, T t = horizontalLine x y s hy t) :
    s ≠ 0 ∧
      ∀ t,
        HasCuspQuarticAmplitude .infinity
          (z t) (horizontalLine x y s hy t)
          (cuspQuarticAmplitude .infinity s) := by
  have hTline :
      ∀ t,
        HasDerivAt
          (fun u : ℝ ↦ (T u : ℂ)) (s : ℂ) t := by
    intro t
    have heq :
        (fun u : ℝ ↦ (T u : ℂ)) =
          fun u : ℝ ↦
            complexHorizontalAffine x y s (u : ℂ) := by
      funext u
      rw [hline u]
      exact (complexHorizontalAffine_ofReal x y s u hy).symm
    rw [heq]
    exact
      (complexHorizontalAffine_hasDerivAt
        x y s (t : ℂ)).comp_ofReal
  have hcomparison :
      ∀ t,
        HasDerivAt
          (fun u : ℝ ↦ (T u : ℂ))
          (unaryComparisonV z
            (fun u ↦ canonicalUnaryTheta (T u)) t) t := by
    intro t
    exact
      canonicalLambdaLift_hasDerivAt_comparisonV
        hz hB hlambda (fun u ↦ ⟨s, hTline u⟩) t
  have hspeed :
      ∀ t,
        unaryComparisonV z
            (fun u ↦ canonicalUnaryTheta (T u)) t =
          (s : ℂ) :=
    fun t ↦ (hcomparison t).unique (hTline t)
  have hs : s ≠ 0 := by
    intro hs0
    have hvzero :
        unaryComparisonV z
            (fun u ↦ canonicalUnaryTheta (T u)) 0 = 0 := by
      rw [hspeed 0, hs0]
      norm_num
    have hcanonicalB :
        UnaryModularState.B (canonicalUnaryTheta (T 0)) =
          H₃ (T 0) := by
      have hJacobi :
          H₂ (T 0) + H₄ (T 0) = H₃ (T 0) := by
        simpa only [Pi.add_apply] using
          congrFun jacobi_quartic_identity (T 0)
      simpa only [UnaryModularState.B,
        canonicalUnaryTheta_A, canonicalUnaryTheta_C] using hJacobi
    unfold unaryComparisonV at hvzero
    rw [hcanonicalB] at hvzero
    have hratio :
        UnaryModularState.B (z 0) / H₃ (T 0) ≠ 0 :=
      div_ne_zero (hB 0) (H₃_ne_zero (T 0))
    exact hratio hvzero
  refine ⟨hs, ?_⟩
  intro t
  have h :=
    hasCuspQuarticAmplitude_of_horizontalized_comparison
      .infinity (1 : IntegralModularGroup)
      (by simp [cuspRepresentative])
      z T hB hlambda x y s hy hs
      (by
        intro u
        simpa only [one_smul] using congrArg id (hline u))
      t (hcomparison t)
  simpa only [one_smul, hline t] using h

end

end HGAS.Modular
