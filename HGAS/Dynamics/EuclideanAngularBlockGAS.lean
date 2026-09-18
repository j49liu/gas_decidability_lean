import HGAS.Dynamics.HomogeneousGASNegativeAngularBlock
import HGAS.Lyapunov.EuclideanAngularConverse
import HGAS.Lyapunov.StrictHomogeneousDirect
import Mathlib.Tactic

/-!
# The Euclidean angular-block characterization of GAS

Let `F` be a homogeneous `C²` vector field on a finite-dimensional real
inner-product space.  Its Euclidean angular equation on the unit sphere is

```
u' = F(u) - ⟪u,F(u)⟫ u.
```

This module packages the precise finite-time criterion:

> the origin is globally asymptotically stable if and only if there are
> `T,c > 0` such that every unit angular orbit has radial-reward integral
> at most `-c` over `[0,T]`.

The forward implication is the homogeneous angular-to-physical time-change
theorem.  For the reverse implication,
`EuclideanAngularConverse` constructs a positive, strict, degree-two
homogeneous `C¹` Lyapunov function from the finite cocycle block, and
`StrictHomogeneousDirect` proves GAS directly from that function.

The block is deliberately stated only on the invariant unit sphere.  It
cannot be stated on the whole cutoff ambient flow: the cutoff reward
vanishes at the origin, so a strictly negative block there is impossible.
-/

namespace HGAS

open scoped BoundedContinuousFunction RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- One common strictly negative radial-reward block on the Euclidean unit
sphere. -/
def HasUniformNegativeEuclideanAngularBlock
    (F : E → E) (hF : ContDiff ℝ 1 F) : Prop :=
  ∃ T c : ℝ, 0 < T ∧ 0 < c ∧
    ∀ u : E, ‖u‖ = 1 →
      Dynamics.orbitIntegral
        (euclideanAngularFlow F hF)
        (boundedCutoffInnerRadialReward F hF) T u ≤ -c

/-- A common negative Euclidean angular block implies GAS.

The proof object built by the finite-cocycle construction is explicit once
the witnessing time and margin are unpacked. -/
theorem globallyAsymptoticallyStable_of_uniformNegativeEuclideanAngularBlock
    (F : E → E) (d : ℕ)
    (hFhom : ScalesAsDegree ℝ d F)
    (hF : ContDiff ℝ 2 F)
    (hzero : F 0 = 0)
    (hblock :
      HasUniformNegativeEuclideanAngularBlock F
        (hF.of_le (by norm_num))) :
    GloballyAsymptoticallyStable F 0 := by
  obtain ⟨T, c, hT, hc, hnegative⟩ := hblock
  let L : StrictHomogeneousC1Lyapunov F 2 :=
    strictHomogeneousC1Lyapunov_of_uniformNegativeEuclideanAngularBlock
      F d hFhom hF hT hc hnegative
  exact L.globallyAsymptoticallyStable_of_equilibrium
    (hF.of_le (by norm_num)) hzero

/-- **Euclidean angular-block criterion.**

For a `C²` field homogeneous of degree `k+1`, with the origin as an
equilibrium, GAS is equivalent to one common strictly negative angular
block on the unit sphere.
-/
theorem globallyAsymptoticallyStable_iff_uniformNegativeEuclideanAngularBlock
    (F : E → E) (k : ℕ)
    (hFhom : ScalesAsDegree ℝ (k + 1) F)
    (hF : ContDiff ℝ 2 F)
    (hzero : F 0 = 0) :
    GloballyAsymptoticallyStable F 0 ↔
      HasUniformNegativeEuclideanAngularBlock F
        (hF.of_le (by norm_num)) := by
  constructor
  · intro hgas
    exact hgas.exists_uniformNegativeEuclideanAngularBlock
      hFhom (hF.of_le (by norm_num))
  · exact
      globallyAsymptoticallyStable_of_uniformNegativeEuclideanAngularBlock
        F (k + 1) hFhom hF hzero

end

end HGAS
