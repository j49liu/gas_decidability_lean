import HGAS.Modular.SeparableZeroAtInfty
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# A countable measure-determining family of `C₀` observables

On a second-countable locally compact Hausdorff space, `C₀(X, ℝ)` is
separable by `SeparableZeroAtInfty`.  A fixed dense sequence therefore
determines every finite regular Borel measure: integration is a continuous
linear functional for the supremum norm, so equality on the sequence
extends to all of `C₀`; compactly supported continuous functions then give
Riesz--Markov uniqueness.
-/

namespace HGAS.Dynamics

open Filter Function _root_.MeasureTheory Set Topology
open scoped BoundedContinuousFunction CompactlySupported
  ZeroAtInfty

noncomputable section

variable {X : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [SecondCountableTopology X]
  [LocallyCompactSpace X]

/-- Integration of a `C₀` observable against a probability, as a
continuous linear functional in the supremum norm. -/
def c0IntegralCLM (μ : ProbabilityMeasure X) :
    C₀(X, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦
        ∫ x, f x ∂(μ : Measure X)
      map_add' := by
        intro f g
        exact integral_add (μ := (μ : Measure X))
          (f.toBCF.integrable (μ : Measure X))
          (g.toBCF.integrable (μ : Measure X))
      map_smul' := by
        intro c f
        exact integral_smul (μ := (μ : Measure X)) c f }
    1
    (fun f ↦ by
      simpa only [one_mul,
        ZeroAtInftyContinuousMap.norm_toBCF_eq_norm] using
        f.toBCF.norm_integral_le_norm (μ : Measure X))

omit [T2Space X] [SecondCountableTopology X]
  [LocallyCompactSpace X] in
@[simp]
theorem c0IntegralCLM_apply
    (μ : ProbabilityMeasure X) (f : C₀(X, ℝ)) :
    c0IntegralCLM μ f =
      ∫ x, f x ∂(μ : Measure X) :=
  rfl

/-- The canonical dense sequence of `C₀(X, ℝ)`. -/
def c0DenseTest (n : ℕ) : C₀(X, ℝ) :=
  TopologicalSpace.denseSeq C₀(X, ℝ) n

omit [MeasurableSpace X] [BorelSpace X] in
/-- The canonical test sequence is dense for the supremum norm. -/
theorem denseRange_c0DenseTest :
    DenseRange (c0DenseTest (X := X)) :=
  TopologicalSpace.denseRange_denseSeq C₀(X, ℝ)

/-- A compactly supported continuous function, regarded as a function
vanishing at infinity. -/
def compactlySupportedToC0 (f : C_c(X, ℝ)) :
    C₀(X, ℝ) where
  toFun := f
  continuous_toFun := map_continuous f
  zero_at_infty' := by
    rw [← Filter.coclosedCompact_eq_cocompact]
    exact Filter.Tendsto.congr'
      (hasCompactSupport_iff_eventuallyEq.mp
        f.hasCompactSupport).symm
      tendsto_const_nhds

omit [MeasurableSpace X] [BorelSpace X] in
@[simp]
theorem compactlySupportedToC0_apply
    (f : C_c(X, ℝ)) (x : X) :
    compactlySupportedToC0 f x = f x :=
  rfl

/-- Equality of integrals on the canonical countable family determines
probability measures. -/
theorem probability_eq_of_integral_c0DenseTest_eq
    [TopologicalSpace.PseudoMetrizableSpace X]
    {μ ν : ProbabilityMeasure X}
    (h :
      ∀ n : ℕ,
        (∫ x, c0DenseTest (X := X) n x
            ∂(μ : Measure X)) =
          ∫ x, c0DenseTest (X := X) n x
            ∂(ν : Measure X)) :
    μ = ν := by
  have hfunCoe :
      (c0IntegralCLM μ : C₀(X, ℝ) → ℝ) =
        (c0IntegralCLM ν : C₀(X, ℝ) → ℝ) := by
    apply denseRange_c0DenseTest.equalizer
      (c0IntegralCLM μ).continuous
      (c0IntegralCLM ν).continuous
    funext n
    exact h n
  have hfun :
      c0IntegralCLM μ = c0IntegralCLM ν := by
    apply ContinuousLinearMap.ext
    intro f
    exact congrFun hfunCoe f
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hf :=
    congrArg (fun L : C₀(X, ℝ) →L[ℝ] ℝ ↦
      L (compactlySupportedToC0 f)) hfun
  simpa only [c0IntegralCLM_apply,
    compactlySupportedToC0_apply] using hf

end

end HGAS.Dynamics
