import HGAS.Dynamics.InvariantProbability

/-!
# Transporting invariant probabilities across equal flows

Occasionally two flow constructions are proved equal only after a
homeomorphism or restriction has been unfolded.  Lean can transport an
`InvariantProbabilityMeasure` across that equality with `Eq.mpr`, but the
resulting term hides the elementary fact that its underlying probability
measure has not changed.

The constructor below performs the same transport explicitly: it keeps the
probability measure verbatim and rewrites only the invariance proof.  Its
measure projection is therefore definitionally transparent.
-/

noncomputable section

namespace HGAS.Dynamics

variable {K : Type*}
  [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]

namespace InvariantProbabilityMeasure

/-- Regard an invariant probability for `ϕ` as one for an equal flow `ψ`,
without changing its underlying probability measure. -/
def transportFlow
    {ϕ ψ : Flow ℝ K}
    (h : ϕ = ψ)
    (μ : InvariantProbabilityMeasure ϕ) :
    InvariantProbabilityMeasure ψ where
  measure := μ.measure
  invariant := by
    rw [← h]
    exact μ.invariant

@[simp]
theorem transportFlow_measure
    {ϕ ψ : Flow ℝ K}
    (h : ϕ = ψ)
    (μ : InvariantProbabilityMeasure ϕ) :
    (μ.transportFlow h).measure = μ.measure :=
  rfl

end InvariantProbabilityMeasure

end HGAS.Dynamics
