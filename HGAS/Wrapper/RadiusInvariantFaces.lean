import HGAS.Wrapper.RadiusCleanup
import HGAS.Dynamics.AngularGAS
import Mathlib.Tactic

/-!
# Invariant radius faces of the product-sphere cleanup

`RadiusCleanup` proves the pointwise polynomial identities.  This file
adds the invariant-measure argument in an abstract form that can be
instantiated by any actual wrapper flow.

The only dynamical datum required is an orbit-coboundary certificate for
the Lyapunov identity: the time-one integral of the radius dissipation is
the change of a bounded potential.  This is the precise flow-level
calculus obligation that a concrete polynomial wrapper must discharge;
it is kept visible rather than hidden in a theorem name.
-/

namespace HGAS

open Function MeasureTheory Set
open scoped BoundedContinuousFunction BigOperators

noncomputable section

variable {K : Type*} [MetricSpace K] [MeasurableSpace K] [BorelSpace K]
  [CompactSpace K]
variable {blocks : ℕ}

/-- When the total squared radius equals the number of blocks, every
zero-dissipation radius vector is either the full unit-radius stratum or
has at least one absent block. -/
theorem radius_all_one_or_zero_coordinate
    (hblocks : 0 < blocks)
    (s : FinVector blocks ℝ)
    (hsum : ∑ i, s i = (blocks : ℝ))
    (hs : ∀ i, 0 ≤ s i)
    (hzero : radiusDissipation (blocks : ℝ) s = 0) :
    (∀ i, s i = 1) ∨ ∃ i, s i = 0 := by
  classical
  by_cases hface : ∃ i, s i = 0
  · exact Or.inr hface
  · left
    have hnonzero : ∀ i, s i ≠ 0 := by
      intro i hi
      exact hface ⟨i, hi⟩
    have hsupport : radiusSupport s = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i
      simp [radiusSupport, hnonzero i]
    intro i
    have hi :=
      (radius_eq_zero_or_eq_card_quotient
        (blocks : ℝ) s (by positivity) hsum hs hzero i).resolve_left
          (hnonzero i)
    rw [hsupport, Finset.card_univ] at hi
    have hcast : ((blocks : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast hblocks.ne'
    rw [hi]
    simpa using div_self hcast

/-- Flow-level certificate for the radius cleanup.

`radii i` is the squared radius of block `i`; `dissipation` is required
pointwise to be the algebraic quantity from `RadiusCleanup`; and
`orbit_coboundary` is the integrated chain rule for the cleanup potential.
-/
structure RadiusCleanupFlowCertificate
    (ϕ : Flow ℝ K) (blocks : ℕ) where
  blocks_pos : 0 < blocks
  radii : Fin blocks → K →ᵇ ℝ
  potential : K →ᵇ ℝ
  dissipation : K →ᵇ ℝ
  radii_nonnegative : ∀ x i, 0 ≤ radii i x
  radii_sum : ∀ x, ∑ i, radii i x = (blocks : ℝ)
  dissipation_eq :
    ∀ x,
      dissipation x =
        radiusDissipation (blocks : ℝ) (fun i ↦ radii i x)
  orbit_coboundary :
    ∀ x,
      Dynamics.orbitIntegral ϕ dissipation 1 x =
        potential (ϕ 1 x) - potential x

namespace RadiusCleanupFlowCertificate

variable {ϕ : Flow ℝ K}

/-- Build the flow-level certificate from the pointwise chain rule along
every orbit.  This exposes the exact calculus fact needed from a concrete
wrapper vector field. -/
def ofHasDerivAt
    (hblocks : 0 < blocks)
    (radii : Fin blocks → K →ᵇ ℝ)
    (potential dissipation : K →ᵇ ℝ)
    (hradiiNonnegative : ∀ x i, 0 ≤ radii i x)
    (hradiiSum : ∀ x, ∑ i, radii i x = (blocks : ℝ))
    (hdissipation :
      ∀ x,
        dissipation x =
          radiusDissipation (blocks : ℝ) (fun i ↦ radii i x))
    (hderiv :
      ∀ x t,
        HasDerivAt
          (fun s ↦ potential (ϕ s x))
          (dissipation (ϕ t x)) t) :
    RadiusCleanupFlowCertificate ϕ blocks where
  blocks_pos := hblocks
  radii := radii
  potential := potential
  dissipation := dissipation
  radii_nonnegative := hradiiNonnegative
  radii_sum := hradiiSum
  dissipation_eq := hdissipation
  orbit_coboundary x := by
    rw [Dynamics.orbitIntegral]
    have hcontinuous :
        Continuous (fun t : ℝ ↦ dissipation (ϕ t x)) :=
      Dynamics.continuous_orbitObservable ϕ dissipation x
    have hFTC :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (0 : ℝ)) (b := (1 : ℝ))
        (f := fun t ↦ potential (ϕ t x))
        (f' := fun t ↦ dissipation (ϕ t x))
        (fun t _ ↦ hderiv x t)
        (hcontinuous.intervalIntegrable 0 1)
    simpa using hFTC

/-- Points on the intended product of unit spheres. -/
def fullStratum
    (certificate : RadiusCleanupFlowCertificate ϕ blocks) :
    Set K :=
  {x | ∀ i, certificate.radii i x = 1}

/-- Points on a proper block face. -/
def properFace
    (certificate : RadiusCleanupFlowCertificate ϕ blocks) :
    Set K :=
  {x | ∃ i, certificate.radii i x = 0}

omit [MeasurableSpace K] [BorelSpace K] [CompactSpace K] in
theorem isClosed_fullStratum
    (certificate : RadiusCleanupFlowCertificate ϕ blocks) :
    IsClosed certificate.fullStratum := by
  rw [show certificate.fullStratum =
      ⋂ i, {x | certificate.radii i x = 1} by
    ext x
    simp [fullStratum]]
  exact isClosed_iInter fun i =>
    isClosed_eq (certificate.radii i).continuous continuous_const

omit [CompactSpace K] in
theorem measurableSet_fullStratum
    (certificate : RadiusCleanupFlowCertificate ϕ blocks) :
    MeasurableSet certificate.fullStratum :=
  certificate.isClosed_fullStratum.measurableSet

/-- Every invariant probability annihilates the radius dissipation. -/
theorem dissipation_average_eq_zero
    (certificate : RadiusCleanupFlowCertificate ϕ blocks)
    (μ : Dynamics.InvariantProbabilityMeasure ϕ) :
    Dynamics.observableAverage certificate.dissipation μ.measure = 0 :=
  Dynamics.observableAverage_eq_zero_of_orbitIntegral_eq_coboundary
    ϕ certificate.dissipation certificate.potential
    certificate.orbit_coboundary μ

/-- Every invariant probability is almost surely in the zero set of the
radius dissipation. -/
theorem ae_dissipation_eq_zero
    (certificate : RadiusCleanupFlowCertificate ϕ blocks)
    (μ : Dynamics.InvariantProbabilityMeasure ϕ) :
    ∀ᵐ x ∂(μ.measure : Measure K),
      certificate.dissipation x = 0 := by
  have hintegral :
      (∫ x, certificate.dissipation x
          ∂(μ.measure : Measure K)) = 0 := by
    simpa [Dynamics.observableAverage] using
      certificate.dissipation_average_eq_zero μ
  have hnonnegative :
      ∀ x, 0 ≤ certificate.dissipation x := by
    intro x
    rw [certificate.dissipation_eq]
    exact radiusDissipation_nonneg
      (blocks : ℝ) (fun i ↦ certificate.radii i x)
      (certificate.radii_nonnegative x)
  have hae :
      certificate.dissipation =ᵐ[
        (μ.measure : Measure K)] 0 :=
    (integral_eq_zero_iff_of_nonneg hnonnegative
      (certificate.dissipation.integrable _)).mp hintegral
  exact hae

/-- **Invariant radius-face classification.**

Every invariant probability is concentrated on the intended full stratum
and the union of proper block faces. -/
theorem ae_mem_fullStratum_or_properFace
    (certificate : RadiusCleanupFlowCertificate ϕ blocks)
    (μ : Dynamics.InvariantProbabilityMeasure ϕ) :
    ∀ᵐ x ∂(μ.measure : Measure K),
      x ∈ certificate.fullStratum ∨
        x ∈ certificate.properFace := by
  filter_upwards [certificate.ae_dissipation_eq_zero μ] with x hx
  have hzero :
      radiusDissipation (blocks : ℝ)
        (fun i ↦ certificate.radii i x) = 0 := by
    rw [← certificate.dissipation_eq]
    exact hx
  rcases radius_all_one_or_zero_coordinate
      certificate.blocks_pos
      (fun i ↦ certificate.radii i x)
      (certificate.radii_sum x)
      (certificate.radii_nonnegative x) hzero with hfull | hproper
  · exact Or.inl hfull
  · exact Or.inr hproper

end RadiusCleanupFlowCertificate

end

end HGAS
