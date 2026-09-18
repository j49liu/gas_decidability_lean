import HGAS.Wrapper.UnitSphereWrapperInvariantAverage
import Mathlib.Tactic

/-!
# End-to-end concrete product-sphere reduction theorem

All wrapper-side hypotheses of the semantic GAS theorem are now
discharged.  Starting from a sparse rational polynomial source field `P`
and reward `a` on a compact product of spheres, the executable compiler
produces the homogeneous rational polynomial field

```
finalFieldCode sourceBlock D P a.
```

Provided the source field is tangent to every sphere block and the stated
degree bounds hold, GAS of the compiled field is equivalent to strict
negativity of the source maximal invariant reward average.

The second theorem allows an upstream construction to use any independently
defined source flow.  It need only prove that its ambient trajectories
solve `y' = P(y)`; ODE uniqueness identifies it with the canonical wrapper
source flow.
-/

namespace HGAS

open Function Metric Set
open scoped BoundedContinuousFunction

noncomputable section

namespace UnitSpherePolynomialWrapper

variable {n k : ℕ}

/-- **Concrete wrapper reduction to the canonical source maximum.** -/
theorem realize_finalFieldCode_gas_iff_sourceMaximum_neg
    (sourceBlock : Fin n → Fin k)
    [Nonempty (SourceProductSphere sourceBlock)]
    (D : ℕ) (hD : 3 ≤ D) (hDodd : D % 2 = 1)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j))
    (a : PolynomialCode n)
    (ha : PolynomialCode.TermsDegreeLE (D - 1) a)
    (i : Fin k)
    (htangent :
      ∀ y : SourceProductSphere sourceBlock,
        SourceTangentAt sourceBlock y.1
          (PolynomialFieldCode.realize P y.1)) :
    GloballyAsymptoticallyStable
        (PolynomialFieldCode.realize
          (finalFieldCode sourceBlock D P a)) 0 ↔
      Dynamics.maximalInvariantAverage
        (positiveSourceFlow sourceBlock D P a)
        (sourceRewardBCF sourceBlock a) < 0 :=
  realize_finalFieldCode_gas_iff_of_sourceMaximum
    sourceBlock D hD hDodd P hP a ha i
    (Dynamics.maximalInvariantAverage
      (positiveSourceFlow sourceBlock D P a)
      (sourceRewardBCF sourceBlock a))
    (fullStratumMaximum_chartReward
      sourceBlock D hDodd P hP a ha htangent)

/-- **Concrete wrapper reduction for an independently supplied source
flow.**

The sole compatibility hypothesis is the literal polynomial
integral-curve equation in ambient source coordinates. -/
theorem realize_finalFieldCode_gas_iff_externalSourceMaximum_neg
    (sourceBlock : Fin n → Fin k)
    [Nonempty (SourceProductSphere sourceBlock)]
    (D : ℕ) (hD : 3 ≤ D) (hDodd : D % 2 = 1)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j))
    (a : PolynomialCode n)
    (ha : PolynomialCode.TermsDegreeLE (D - 1) a)
    (i : Fin k)
    (htangent :
      ∀ y : SourceProductSphere sourceBlock,
        SourceTangentAt sourceBlock y.1
          (PolynomialFieldCode.realize P y.1))
    (ψ : Flow ℝ (SourceProductSphere sourceBlock))
    (hψ :
      ∀ y,
        IsIntegralCurve
          (fun t ↦ (ψ t y).1)
          (fun _ x ↦ PolynomialFieldCode.realize P x)) :
    GloballyAsymptoticallyStable
        (PolynomialFieldCode.realize
          (finalFieldCode sourceBlock D P a)) 0 ↔
      Dynamics.maximalInvariantAverage
        ψ (sourceRewardBCF sourceBlock a) < 0 := by
  have hflow :
      ψ = positiveSourceFlow sourceBlock D P a :=
    sourceFlow_eq_positiveSourceFlow
      sourceBlock D hDodd P hP a htangent ψ hψ
  rw [hflow]
  exact realize_finalFieldCode_gas_iff_sourceMaximum_neg
    sourceBlock D hD hDodd P hP a ha i htangent

end UnitSpherePolynomialWrapper

end

end HGAS
