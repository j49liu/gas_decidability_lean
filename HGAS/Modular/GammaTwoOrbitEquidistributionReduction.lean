import HGAS.Dynamics.TimeAverages
import HGAS.Modular.GammaTwoFiniteVolumeConsequences
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# From pointwise horocycle equidistribution to the ergodic measure dichotomy

This file replaces the opaque measure-classification input by the two
standard pointwise statements from which it follows.

For a continuous real flow `ϕ`, a point `x` is forward generic for a
probability `μ` when the averages

```text
       1 / (n + 1) ∫₀ⁿ⁺¹ f(ϕₜ x) dt
```

converge to `∫ f dμ` for every compactly supported continuous real
observable `f`.  Compactly supported observables are used because the
level-two frame quotient is locally compact but noncompact, and they
determine every regular Borel measure.

The two inputs isolated below are mathematically different.

* `GammaTwoNonperiodicOrbitEquidistribution ν` is the geometric
  Dani--Smillie theorem: every nonperiodic horocycle is equidistributed
  for normalized Haar probability `ν`.
* `GammaTwoErgodicGenericPointAlternative` is the abstract
  pointwise-ergodic input: an ergodic probability is either carried by a
  periodic horocycle or has a nonperiodic generic point.

The main theorem proves, in the kernel, that these two pointwise inputs
imply `GammaTwoErgodicHorocycleDichotomy`.  Thus the remaining
horocycle-specific trust boundary is no longer a reformulation of the
desired measure dichotomy: it is the orbit-average theorem proved by
S. G. Dani and J. Smillie, *Uniform distribution of horocycle orbits for
Fuchsian groups*, Duke Math. J. 51 (1984), no. 1, 185--194,
doi:10.1215/S0012-7094-84-05110-X.

Mathlib currently contains the von Neumann mean ergodic theorem and
Poincare recurrence, but not the pointwise Birkhoff theorem for a real
flow.  The generic-point proposition is therefore kept separate from the
Dani--Smillie proposition, so a future abstract pointwise-ergodic module
can discharge it without touching any modular geometry.
-/

namespace HGAS.Modular

open Filter _root_.MeasureTheory Set Topology
open scoped BoundedContinuousFunction CompactlySupported

noncomputable section

/-! ## Generic points for continuous real flows -/

variable {X : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The forward orbit average at the positive time `n + 1`.

The shift by one avoids a special case at time zero and gives a sequence
whose time lengths tend to infinity. -/
def forwardOrbitAverage
    (ϕ : Flow ℝ X) (f : C_c(X, ℝ))
    (n : ℕ) (x : X) : ℝ :=
  (n + 1 : ℝ)⁻¹ *
    HGAS.Dynamics.orbitIntegral ϕ
      f.toBoundedContinuousFunction (n + 1 : ℝ) x

/-- A point is forward generic for `μ` if every compactly supported
continuous observable has the expected forward time average along its
orbit. -/
def IsForwardGenericFor
    (ϕ : Flow ℝ X) (μ : ProbabilityMeasure X) (x : X) : Prop :=
  ∀ f : C_c(X, ℝ),
    Tendsto (fun n : ℕ ↦ forwardOrbitAverage ϕ f n x)
      atTop
      (𝓝 (∫ y, f y ∂(μ : Measure X)))

/-- A single point cannot be generic for two different regular
probabilities.

This is precisely why compactly supported observables were chosen:
the Riesz--Markov uniqueness theorem says that their integrals determine a
regular Borel measure on a locally compact space. -/
theorem IsForwardGenericFor.probability_eq
    [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X]
    {ϕ : Flow ℝ X}
    {μ ν : ProbabilityMeasure X} {x : X}
    (hμ : IsForwardGenericFor ϕ μ x)
    (hν : IsForwardGenericFor ϕ ν x) :
    μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  exact tendsto_nhds_unique (hμ f) (hν f)

/-! ## The two exact pointwise inputs -/

/-- The pointwise Dani--Smillie assertion for a chosen normalized Haar
probability: every nonperiodic unit-speed horocycle is forward generic for
that probability. -/
def GammaTwoNonperiodicOrbitEquidistribution
    (ν : ProbabilityMeasure GammaTwoFrameQuotient) : Prop :=
  ∀ q : GammaTwoFrameQuotient,
    ¬ IsPeriodicHorocyclePoint 1 q →
      IsForwardGenericFor gammaTwoHorocycleFlow ν q

/-- The abstract generic-point alternative needed to pass from a
pointwise orbit theorem to classification of ergodic probabilities.

The periodic branch is stated using the project's exact closed-horocycle
predicate.  In the other branch, the witness is explicitly nonperiodic
and generic for the given ergodic probability.  This proposition contains
no Haar measure and no horocycle equidistribution conclusion. -/
def GammaTwoErgodicGenericPointAlternative : Prop :=
  ∀ μ : ProbabilityMeasure GammaTwoFrameQuotient,
    HGAS.Dynamics.IsErgodicInvariantProbability
        gammaTwoHorocycleFlow μ →
      IsClosedHorocycleProbability 1 μ ∨
        ∃ q : GammaTwoFrameQuotient,
          ¬ IsPeriodicHorocyclePoint 1 q ∧
            IsForwardGenericFor gammaTwoHorocycleFlow μ q

/-- Pointwise nonperiodic-orbit equidistribution implies the desired
classification for every ergodic probability once the abstract
generic-point alternative is available. -/
theorem ergodicHorocycleDichotomy_of_nonperiodicEquidistribution
    (hgeneric : GammaTwoErgodicGenericPointAlternative)
    (ν : ProbabilityMeasure GammaTwoFrameQuotient)
    (hν :
      GammaTwoNonperiodicOrbitEquidistribution ν)
    (μ : ProbabilityMeasure GammaTwoFrameQuotient)
    (hμ :
      HGAS.Dynamics.IsErgodicInvariantProbability
        gammaTwoHorocycleFlow μ) :
    IsClosedHorocycleProbability 1 μ ∨ μ = ν := by
  rcases hgeneric μ hμ with hclosed | ⟨q, hqnonperiodic, hqμ⟩
  · exact Or.inl hclosed
  · exact Or.inr <|
      hqμ.probability_eq (hν q hqnonperiodic)

/-- A normalization-independent form of the Dani--Smillie pointwise
theorem.  It asks for equidistribution with respect to whichever
right-invariant frame probability is supplied. -/
def GammaTwoPointwiseHorocycleEquidistribution : Prop :=
  ∀ ν : ProbabilityMeasure GammaTwoFrameQuotient,
    IsRightInvariantFrameProbability ν →
      GammaTwoNonperiodicOrbitEquidistribution ν

/-- **Pointwise-to-measure Dani--Smillie reduction.**

The orbit-equidistribution theorem and the abstract generic-point
alternative together imply the exact
`GammaTwoErgodicHorocycleDichotomy` consumed by the finite-volume and
recurrent-measure modules. -/
theorem gammaTwoErgodicHorocycleDichotomy_of_pointwiseEquidistribution
    (hpointwise : GammaTwoPointwiseHorocycleEquidistribution)
    (hgeneric : GammaTwoErgodicGenericPointAlternative) :
    GammaTwoErgodicHorocycleDichotomy := by
  intro ν hν μ hμ
  exact
    ergodicHorocycleDichotomy_of_nonperiodicEquidistribution
      hgeneric ν (hpointwise ν hν) μ hμ

/-- Consequently, the pointwise Dani--Smillie theorem and the abstract
generic-point alternative give the complete classification interface
used by the rest of the development.  Finite Haar volume is supplied by
the explicit fundamental domain, not assumed here. -/
theorem gammaTwoDaniSmillieTheorem_of_pointwiseEquidistribution
    (hpointwise : GammaTwoPointwiseHorocycleEquidistribution)
    (hgeneric : GammaTwoErgodicGenericPointAlternative) :
    GammaTwoDaniSmillieTheorem :=
  gammaTwoDaniSmillieTheorem_of_ergodicHorocycleDichotomy
    (gammaTwoErgodicHorocycleDichotomy_of_pointwiseEquidistribution
      hpointwise hgeneric)

end

end HGAS.Modular
