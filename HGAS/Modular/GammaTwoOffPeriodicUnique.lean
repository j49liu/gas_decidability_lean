import HGAS.Dynamics.FlowPointwiseErgodicGeneral
import HGAS.Modular.GammaTwoGoodReturnTimes
import HGAS.Modular.GammaTwoOccupationInputsUnconditional

/-!
# Uniqueness of invariant probabilities off periodic horocycles

This file closes the last hypothesis in the occupation-measure proof of
the Dani--Smillie theorem.

Let `μ` be a horocycle-invariant probability which gives no mass to the
periodic horocycles, and let `ν` be Haar probability.  For a `C₀`
observable `f`, the nonergodic pointwise ergodic theorem says that the
full sequence of positive integer averages converges at almost every
point to the mean-ergodic `L²` projection `G_f`.  Almost every such point
is nonperiodic.  The good-return-time theorem supplies, at each of these
points, a subsequence of the same averages converging to the Haar mean of
`f`.  Uniqueness of limits therefore gives

```text
  G_f(x) = ∫ f dν                  for μ-almost every x.
```

The integral of `G_f` is `∫ f dμ`, so `μ` and `ν` agree on every member
of the canonical dense family in `C₀`.  These tests determine
probability measures, hence `μ = ν`.

No ergodic decomposition is used.  Combining this uniqueness theorem
with the already formalized nonescape and periodic-mass avoidance
arguments yields unconditional pointwise equidistribution and the full
level-two Dani--Smillie classification interface.
-/

namespace HGAS.Modular

open Filter Function _root_.MeasureTheory Set Topology
open scoped BoundedContinuousFunction ZeroAtInfty

noncomputable section

/-- A right-invariant frame probability is the unique
horocycle-invariant probability which gives zero mass to the union of
periodic horocycles. -/
theorem IsRightInvariantFrameProbability.offPeriodicUnique
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν) :
    GammaTwoInvariantProbabilityOffPeriodicUnique ν := by
  intro μ hμInvariant hμPeriodic
  let μi :
      HGAS.Dynamics.InvariantProbabilityMeasure
        gammaTwoHorocycleFlow :=
    ⟨μ, hμInvariant⟩
  apply
    HGAS.Dynamics.probability_eq_of_integral_c0DenseTest_eq
  intro j
  let f : C₀(GammaTwoFrameQuotient, ℝ) :=
    HGAS.Dynamics.c0DenseTest
      (X := GammaTwoFrameQuotient) j
  let G :
      Lp ℝ 2 (μ : Measure GammaTwoFrameQuotient) :=
    μi.integerAverageL2Limit f.toBCF
  let c : ℝ :=
    ∫ x, f x ∂(ν : Measure GammaTwoFrameQuotient)
  have hfull :
      ∀ᵐ x ∂(μ : Measure GammaTwoFrameQuotient),
        Tendsto
          (fun n : ℕ ↦
            HGAS.Dynamics.integerOrbitAverageObservable
              gammaTwoHorocycleFlow f.toBCF (n + 1) x)
          atTop (𝓝 (G x)) := by
    simpa only [G] using
      μi.ae_tendsto_integerOrbitAverage_L2Limit f.toBCF
  have hnonperiodic :
      ∀ᵐ x ∂(μ : Measure GammaTwoFrameQuotient),
        ¬ IsPeriodicHorocyclePoint 1 x := by
    have hnotmem :
        ∀ᵐ x ∂(μ : Measure GammaTwoFrameQuotient),
          x ∉ gammaTwoPeriodicHorocycleSet :=
      measure_eq_zero_iff_ae_notMem.mp hμPeriodic
    simpa only [gammaTwoPeriodicHorocycleSet, mem_setOf_eq]
      using hnotmem
  have hGconst :
      (G : GammaTwoFrameQuotient → ℝ) =ᵐ[
          (μ : Measure GammaTwoFrameQuotient)]
        Function.const GammaTwoFrameQuotient c := by
    filter_upwards [hfull, hnonperiodic]
      with x hxfull hxnonperiodic
    obtain
      ⟨N, hNtop, hNpos, _hNreturn, hxgood⟩ :=
      hν.exists_good_integer_return_lengths
        x hxnonperiodic f
    have hpredTop :
        Tendsto (fun n ↦ N n - 1) atTop atTop :=
      (tendsto_sub_atTop_nat 1).comp hNtop
    have hxsub :
        Tendsto
          (fun n ↦
            HGAS.Dynamics.integerOrbitAverageObservable
              gammaTwoHorocycleFlow f.toBCF (N n) x)
          atTop (𝓝 (G x)) := by
      have hcomp := hxfull.comp hpredTop
      exact hcomp.congr fun n ↦ by
        have hNone : 1 ≤ N n :=
          Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (hNpos n))
        simp only [Function.comp_apply]
        rw [Nat.sub_add_cancel hNone]
    exact tendsto_nhds_unique hxsub <| by
      simpa only [c] using hxgood
  have hGintegral :
      (∫ x, G x ∂(μ : Measure GammaTwoFrameQuotient)) =
        ∫ x, f x ∂(μ : Measure GammaTwoFrameQuotient) := by
    simpa only [G] using
      μi.integral_integerAverageL2Limit f.toBCF
  calc
    (∫ x,
        HGAS.Dynamics.c0DenseTest
          (X := GammaTwoFrameQuotient) j x
        ∂(μ : Measure GammaTwoFrameQuotient)) =
        ∫ x, f x ∂(μ : Measure GammaTwoFrameQuotient) := by
          rfl
    _ = ∫ x, G x ∂(μ : Measure GammaTwoFrameQuotient) :=
      hGintegral.symm
    _ = ∫ _x : GammaTwoFrameQuotient, c
        ∂(μ : Measure GammaTwoFrameQuotient) :=
      integral_congr_ae hGconst
    _ = c := by simp
    _ = ∫ x, f x ∂(ν : Measure GammaTwoFrameQuotient) := by
      rfl
    _ = ∫ x,
        HGAS.Dynamics.c0DenseTest
          (X := GammaTwoFrameQuotient) j x
        ∂(ν : Measure GammaTwoFrameQuotient) := by
          rfl

/-- The off-periodic uniqueness input in the occupation reduction is
now unconditional for every choice of normalized Haar probability. -/
theorem gammaTwoInvariantProbabilityOffPeriodicUnique_unconditional :
    ∀ ν : ProbabilityMeasure GammaTwoFrameQuotient,
      IsRightInvariantFrameProbability ν →
        GammaTwoInvariantProbabilityOffPeriodicUnique ν :=
  fun _ hν ↦ hν.offPeriodicUnique

/-- Every nonperiodic level-two horocycle is unconditionally
equidistributed with respect to normalized Haar probability. -/
theorem gammaTwoPointwiseHorocycleEquidistribution_unconditional :
    GammaTwoPointwiseHorocycleEquidistribution :=
  gammaTwoPointwiseHorocycleEquidistribution_of_offPeriodicUnique
    gammaTwoInvariantProbabilityOffPeriodicUnique_unconditional

/-- Unconditional level-two Dani--Smillie classification, in the exact
interface consumed by the later modular measure-classification files. -/
theorem gammaTwoDaniSmillieTheorem_unconditional :
    GammaTwoDaniSmillieTheorem :=
  gammaTwoDaniSmillieTheorem_of_offPeriodicUnique
    gammaTwoInvariantProbabilityOffPeriodicUnique_unconditional

end

end HGAS.Modular
