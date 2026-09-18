import HGAS.Modular.CompactlySupportedDenseInC0
import HGAS.Modular.GammaTwoC0GenericReduction
import HGAS.Modular.GammaTwoOrbitEquidistributionReduction

/-!
# From the usual `C_c` orbit theorem to the `C₀` orbit theorem

The Dani--Smillie theorem is naturally stated for compactly supported
continuous test functions.  The countable generic-point reduction is most
convenient in the separable Banach space `C₀`.  This file proves that the
two formulations are equivalent for the purpose at hand.

The only estimate is that both finite orbit averaging and integration
against a probability have norm at most one in the uniform norm.
Together with density of `C_c` in `C₀`, a standard three-epsilon argument
extends convergence from compactly supported tests to all tests vanishing
at infinity.
-/

namespace HGAS.Dynamics

open Filter Function _root_.MeasureTheory Set Topology
open scoped BoundedContinuousFunction ZeroAtInfty

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- A positive integer-time orbit average is a contraction in the
observable for the uniform norm. -/
theorem dist_integerOrbitAverageObservable_apply_le
    (ϕ : Flow ℝ X) (f g : X →ᵇ ℝ)
    {n : ℕ} (hn : 0 < n) (x : X) :
    dist
        (integerOrbitAverageObservable ϕ f n x)
        (integerOrbitAverageObservable ϕ g n x) ≤
      dist f g := by
  rw [Real.dist_eq, integerOrbitAverageObservable_apply,
    integerOrbitAverageObservable_apply, ← mul_sub]
  have hsub :
      orbitIntegral ϕ f (n : ℝ) x -
          orbitIntegral ϕ g (n : ℝ) x =
        orbitIntegral ϕ (f - g) (n : ℝ) x := by
    unfold orbitIntegral
    rw [← intervalIntegral.integral_sub
      ((continuous_orbitObservable ϕ f x).intervalIntegrable
        0 (n : ℝ))
      ((continuous_orbitObservable ϕ g x).intervalIntegrable
        0 (n : ℝ))]
    rfl
  rw [hsub, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
  calc
    (n : ℝ)⁻¹ *
          |orbitIntegral ϕ (f - g) (n : ℝ) x| ≤
        (n : ℝ)⁻¹ * (‖f - g‖ * |(n : ℝ)|) := by
      gcongr
      simpa only [Real.norm_eq_abs] using
        norm_orbitIntegral_le ϕ (f - g) (n : ℝ) x
    _ = ‖f - g‖ := by
      rw [abs_of_nonneg (Nat.cast_nonneg n)]
      field_simp
    _ = dist f g := by
      rw [dist_eq_norm]

variable [MeasurableSpace X] [BorelSpace X]

/-- Integration against a probability is a contraction on real `C₀`
observables. -/
theorem dist_integral_c0_le
    (μ : ProbabilityMeasure X) (f g : C₀(X, ℝ)) :
    dist
        (∫ x, f x ∂(μ : Measure X))
        (∫ x, g x ∂(μ : Measure X)) ≤
      dist f g := by
  rw [Real.dist_eq]
  change
    |(∫ x, f.toBCF x ∂(μ : Measure X)) -
      ∫ x, g.toBCF x ∂(μ : Measure X)| ≤ dist f g
  rw [← integral_sub
    (f.toBCF.integrable (μ : Measure X))
    (g.toBCF.integrable (μ : Measure X))]
  calc
    |∫ x, f x - g x ∂(μ : Measure X)| ≤
        ‖(f - g).toBCF‖ := by
      simpa only [Real.norm_eq_abs,
        ZeroAtInftyContinuousMap.coe_sub] using
          (f - g).toBCF.norm_integral_le_norm
            (μ : Measure X)
    _ = ‖f - g‖ :=
      ZeroAtInftyContinuousMap.norm_toBCF_eq_norm
    _ = dist f g := by rw [dist_eq_norm]

end

end HGAS.Dynamics

namespace HGAS.Modular

open Filter Function _root_.MeasureTheory Set Topology
open scoped BoundedContinuousFunction CompactlySupported ZeroAtInfty

noncomputable section

/-- The customary compactly-supported formulation of nonperiodic orbit
equidistribution implies its `C₀` formulation. -/
theorem nonperiodicOrbitC0Equidistribution_of_compactlySupported
    (ν : ProbabilityMeasure GammaTwoFrameQuotient)
    (hν : GammaTwoNonperiodicOrbitEquidistribution ν) :
    GammaTwoNonperiodicOrbitC0Equidistribution ν := by
  intro q hq f
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨g, hgf⟩ :=
    HGAS.Dynamics.exists_compactlySupported_dist_lt
      f (by positivity : 0 < ε / 3)
  let g₀ : C₀(GammaTwoFrameQuotient, ℝ) :=
    HGAS.Dynamics.compactlySupportedToC0 g
  have hg₀f : dist g₀ f < ε / 3 := hgf
  have hbcf :
      g₀.toBCF = g.toBoundedContinuousFunction := by
    ext x
    rfl
  have hgconv :
      Tendsto
        (fun n : ℕ ↦
          HGAS.Dynamics.integerOrbitAverageObservable
            gammaTwoHorocycleFlow g₀.toBCF (n + 1) q)
        atTop
        (𝓝 (∫ y, g₀ y
          ∂(ν : Measure GammaTwoFrameQuotient))) := by
    simpa only [hbcf, forwardOrbitAverage,
      HGAS.Dynamics.integerOrbitAverageObservable_apply,
      HGAS.Dynamics.compactlySupportedToC0_apply,
      Nat.cast_add, Nat.cast_one, g₀] using
        hν q hq g
  have hmiddle :
      ∀ᶠ n : ℕ in atTop,
        dist
            (HGAS.Dynamics.integerOrbitAverageObservable
              gammaTwoHorocycleFlow g₀.toBCF (n + 1) q)
            (∫ y, g₀ y
              ∂(ν : Measure GammaTwoFrameQuotient)) <
          ε / 3 :=
    (Metric.tendsto_nhds.mp hgconv) (ε / 3)
      (by positivity)
  filter_upwards [hmiddle] with n hn
  calc
    dist
        (HGAS.Dynamics.integerOrbitAverageObservable
          gammaTwoHorocycleFlow f.toBCF (n + 1) q)
        (∫ y, f y
          ∂(ν : Measure GammaTwoFrameQuotient)) ≤
      dist
          (HGAS.Dynamics.integerOrbitAverageObservable
            gammaTwoHorocycleFlow f.toBCF (n + 1) q)
          (HGAS.Dynamics.integerOrbitAverageObservable
            gammaTwoHorocycleFlow g₀.toBCF (n + 1) q) +
        dist
          (HGAS.Dynamics.integerOrbitAverageObservable
            gammaTwoHorocycleFlow g₀.toBCF (n + 1) q)
          (∫ y, g₀ y
            ∂(ν : Measure GammaTwoFrameQuotient)) +
        dist
          (∫ y, g₀ y
            ∂(ν : Measure GammaTwoFrameQuotient))
          (∫ y, f y
            ∂(ν : Measure GammaTwoFrameQuotient)) :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
      gcongr
      · exact
          (HGAS.Dynamics.dist_integerOrbitAverageObservable_apply_le
            gammaTwoHorocycleFlow f.toBCF g₀.toBCF
            (Nat.succ_pos n) q).trans_lt
              (by simpa only [dist_comm] using hg₀f)
      · exact
          (HGAS.Dynamics.dist_integral_c0_le ν g₀ f).trans_lt
            hg₀f
    _ = ε := by ring

/-- Hence the ordinary pointwise Dani--Smillie statement, with no
additional generic-point axiom, implies the exact ergodic measure
dichotomy. -/
theorem gammaTwoErgodicHorocycleDichotomy_of_nonperiodicEquidistribution'
    (hpointwise : GammaTwoPointwiseHorocycleEquidistribution) :
    GammaTwoErgodicHorocycleDichotomy := by
  apply gammaTwoErgodicHorocycleDichotomy_of_c0Equidistribution
  intro ν hν
  exact nonperiodicOrbitC0Equidistribution_of_compactlySupported
    ν (hpointwise ν hν)

/-- The ordinary compactly-supported pointwise theorem therefore implies
the complete Dani--Smillie classification interface. -/
theorem gammaTwoDaniSmillieTheorem_of_nonperiodicEquidistribution
    (hpointwise : GammaTwoPointwiseHorocycleEquidistribution) :
    GammaTwoDaniSmillieTheorem :=
  gammaTwoDaniSmillieTheorem_of_ergodicHorocycleDichotomy
    (gammaTwoErgodicHorocycleDichotomy_of_nonperiodicEquidistribution'
      hpointwise)

end

end HGAS.Modular
