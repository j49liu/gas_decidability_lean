import HGAS.Modular.ClosedHorocycleUnaryProjectiveBranches

/-!
# Projective unary data in the horizontal chart of a closed horocycle

This module connects the geometric cusp normalization to the algebraic
three-branch ledger.

Let `T` be a canonical-lambda lift of a generic unary state and let `h`
complete a primitive row of a closed `Γ(2)` horocycle.  The normalized
completion

```text
                       h.cuspNormalized.completion
```

maps `T` to the exact horizontal chart while reducing modulo two to the
fixed representative of `h.cuspLabel`.  Equivariance of modular lambda
then places the unary quartics in precisely the projective branch proved
in `ClosedHorocycleUnaryProjectiveBranches`.

The theorem is pointwise.  It can therefore be applied at every time of
the closed orbit without making any global choice of theta multiplier.
-/

namespace HGAS.Modular

open Complex

noncomputable section

/-- Ambient-complex form of the complete six-valued lambda
transformation law. -/
theorem canonicalLambda_smul
    (g : IntegralModularGroup) (τ : UpperHalfPlane) :
    canonicalLambda (g • τ) =
      lambdaCrossRatio (reduceModTwo g) (canonicalLambda τ) := by
  have h :=
    congrArg Subtype.val
      (canonicalLambdaPunctured_smul g τ)
  simpa only [canonicalLambdaPunctured_coe,
    lambdaCrossRatio_smul_coe,
    lambdaCrossRatioPunctured_coe] using h

/-- The upper-half-plane modulus in the cusp-normalized horizontal
chart. -/
def PrimitiveRowHorizontalization.cuspNormalizedModulus
    {v : PrimitiveIntegralRow} {g : RealModularFrame}
    (h : PrimitiveRowHorizontalization v g)
    (τ : UpperHalfPlane) : UpperHalfPlane :=
  h.cuspNormalized.completion • τ

/-- Exact reduction modulo two of the normalized completion, phrased
using the cusp label stored by the original horizontalization. -/
theorem PrimitiveRowHorizontalization.reduce_cuspNormalized_completion
    {v : PrimitiveIntegralRow} {g : RealModularFrame}
    (h : PrimitiveRowHorizontalization v g) :
    reduceModTwo h.cuspNormalized.completion =
      reduceModTwo (cuspRepresentative h.cuspLabel) := by
  rw [h.cuspNormalized_completion,
    reduce_cuspNormalizedCompletion]
  rfl

/-- A generic unary state lifted by `T` lies in the projective theta
branch of the exact cusp-normalized horizontal chart. -/
theorem PrimitiveRowHorizontalization.isCuspQuarticBranch
    {v : PrimitiveIntegralRow} {g : RealModularFrame}
    (h : PrimitiveRowHorizontalization v g)
    (z : UnaryModularState ℂ) (T : UpperHalfPlane)
    (hB : UnaryModularState.B z ≠ 0)
    (hC : z.C ≠ 0)
    (hlambda :
      UnaryModularState.lambdaCoordinate z =
        canonicalLambda T) :
    IsCuspQuarticBranch h.cuspLabel z
      (h.cuspNormalizedModulus T) := by
  apply
    isCuspQuarticBranch_of_cuspRepresentative_lambda
      h.cuspLabel z (h.cuspNormalizedModulus T) hB hC
  calc
    canonicalLambda (h.cuspNormalizedModulus T) =
        lambdaCrossRatio
          (reduceModTwo h.cuspNormalized.completion)
          (canonicalLambda T) := by
      exact canonicalLambda_smul
        h.cuspNormalized.completion T
    _ =
        lambdaCrossRatio
          (reduceModTwo (cuspRepresentative h.cuspLabel))
          (UnaryModularState.lambdaCoordinate z) := by
      rw [h.reduce_cuspNormalized_completion, hlambda]

end

end HGAS.Modular
