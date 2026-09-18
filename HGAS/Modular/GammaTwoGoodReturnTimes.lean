import HGAS.Dynamics.FlowPointwiseErgodic
import HGAS.Modular.GammaTwoFiniteTimeShearComparison
import HGAS.Modular.GammaTwoIntegerGeodesicReturns
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic

/-!
# Good integer return times for nonperiodic horocycles

This file is the measure-theoretic conclusion of the shearing argument.
Suppose that `N n → ∞` and that the geodesic translates

```text
  q · a(log (N n))
```

stay in the fixed compact return core.  Then, for every `C₀` observable,
the length-`N n` horocycle averages at `q` converge to Haar measure.

Here is the proof in one paragraph.  Haar ergodicity gives almost-everywhere
convergence of the integer averages and hence convergence in measure.  At
length `N`, the anisotropic shear box about `q` has widths

```text
  δ/N,  δ,  ρ N
```

in lower-unipotent, diagonal, and upper-unipotent coordinates.  Geodesic
translation by `log N` sends this box exactly to a fixed-size box about the
return point.  Compactness of the return core therefore gives a uniform
positive lower bound for its Haar mass.  For large `N`, the set on which
the length-`N` average is bad has smaller mass, so the box contains a good
point.  The finite-time shear estimate transfers goodness from that point
back to `q`.

The main theorem deliberately accepts an arbitrary return sequence.  Thus
the sequence is chosen from geometry alone and is independent of the test
function, which makes this module reusable in later diagonal arguments.
-/

namespace HGAS.Modular

open Filter Function _root_.MeasureTheory Set Topology
open scoped BoundedContinuousFunction MatrixGroups ZeroAtInfty

noncomputable section

/-- Every integer geodesic-return sequence is a sequence of good
horocycle averaging times for every `C₀` observable. -/
theorem
    IsRightInvariantFrameProbability.tendsto_integerOrbitAverage_along_returns
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν)
    (q : GammaTwoFrameQuotient)
    (N : ℕ → ℕ)
    (hNtop : Tendsto N atTop atTop)
    (hNpos : ∀ n, 0 < N n)
    (hNreturn :
      ∀ n,
        gammaTwoFrameRightMul
            (geodesicFrame (Real.log (N n : ℝ))) q ∈
          gammaTwoIntegerReturnCompactCore)
    (f : C₀(GammaTwoFrameQuotient, ℝ)) :
    Tendsto
      (fun n ↦
        HGAS.Dynamics.integerOrbitAverageObservable
          gammaTwoHorocycleFlow f.toBCF (N n) q)
      atTop
      (𝓝 (∫ x, f x ∂(ν : Measure GammaTwoFrameQuotient))) := by
  let μ :
      HGAS.Dynamics.InvariantProbabilityMeasure
        gammaTwoHorocycleFlow :=
    ⟨ν, hν.horocycleInvariant⟩
  let c : ℝ :=
    ∫ x, f x ∂(ν : Measure GammaTwoFrameQuotient)
  let A : ℕ → GammaTwoFrameQuotient → ℝ :=
    fun k x ↦
      HGAS.Dynamics.integerOrbitAverageObservable
        gammaTwoHorocycleFlow f.toBCF (k + 1) x
  have hae :
      ∀ᵐ x ∂(ν : Measure GammaTwoFrameQuotient),
        Tendsto (fun k ↦ A k x) atTop (𝓝 c) := by
    simpa only [A, c, μ] using
      hν.horocycleErgodic.ae_tendsto_integerOrbitAverage
        μ f.toBCF
  have hAmeas :
      ∀ k,
        AEStronglyMeasurable (A k)
          (ν : Measure GammaTwoFrameQuotient) := by
    intro k
    exact
      (HGAS.Dynamics.integerOrbitAverageObservable
          gammaTwoHorocycleFlow f.toBCF (k + 1)).continuous
        |>.aestronglyMeasurable
  have hmeasure :
      TendstoInMeasure
        (ν : Measure GammaTwoFrameQuotient)
        A atTop (Function.const GammaTwoFrameQuotient c) := by
    apply tendstoInMeasure_of_tendsto_ae hAmeas
    simpa only [Function.const_apply] using hae
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let C : ℝ := 1 + 4 * ‖f‖
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  let ρ : ℝ := ε / (2 * C)
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    positivity
  obtain ⟨δ, hδ, hδhalf, hshear⟩ :=
    exists_delta_integerOrbitAverage_shear_box_close f hρ
  have hKnonempty :
      gammaTwoIntegerReturnCompactCore.Nonempty :=
    ⟨gammaTwoFrameRightMul
        (geodesicFrame (Real.log (N 0 : ℝ))) q,
      hNreturn 0⟩
  obtain ⟨η, hη, hboxUniform⟩ :=
    hν.exists_pos_uniform_measure_gammaTwoShearBox_on_compact
      isCompact_gammaTwoIntegerReturnCompactCore
      hKnonempty hδ hδ hρ
  have hbadBase :
      Tendsto
        (fun k ↦
          (ν : Measure GammaTwoFrameQuotient)
            {x |
              ε / 2 ≤
                dist (A k x) c})
        atTop (𝓝 0) := by
    have h :=
      (tendstoInMeasure_iff_dist.mp hmeasure)
        (ε / 2) (half_pos hε)
    simpa only [Function.const_apply] using h
  have hpredTop :
      Tendsto (fun n ↦ N n - 1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp hNtop
  have hbad :
      Tendsto
        (fun n ↦
          (ν : Measure GammaTwoFrameQuotient)
            {x |
              ε / 2 ≤
                dist (A (N n - 1) x) c})
        atTop (𝓝 0) :=
    hbadBase.comp hpredTop
  have hbadEventually :
      ∀ᶠ n in atTop,
        (ν : Measure GammaTwoFrameQuotient)
            {x |
              ε / 2 ≤
                dist (A (N n - 1) x) c} < η :=
    (tendsto_order.mp hbad).2 η hη
  obtain ⟨n₀, hn₀⟩ :=
    eventually_atTop.mp hbadEventually
  refine ⟨n₀, fun n hn ↦ ?_⟩
  let L : ℝ := Real.log (N n : ℝ)
  let B : Set GammaTwoFrameQuotient :=
    gammaTwoShearBox q
      (δ * Real.exp (-L)) δ (ρ * Real.exp L)
  let E : Set GammaTwoFrameQuotient :=
    {x |
      ε / 2 ≤
        dist (A (N n - 1) x) c}
  have hcenter :
      gammaTwoFrameRightMul (geodesicFrame L) q ∈
        gammaTwoIntegerReturnCompactCore := by
    simpa only [L] using hNreturn n
  have hfixedMass :
      η ≤
        (ν : Measure GammaTwoFrameQuotient)
          (gammaTwoShearBox
            (gammaTwoFrameRightMul (geodesicFrame L) q)
            δ δ ρ) :=
    hboxUniform _ hcenter
  have hscaledMass :=
    hν.measure_gammaTwoShearBox_scaled q δ δ ρ L
  have hBmass :
      η ≤ (ν : Measure GammaTwoFrameQuotient) B := by
    exact hfixedMass.trans_eq <| by
      simpa only [B] using hscaledMass.symm
  have hEmass :
      (ν : Measure GammaTwoFrameQuotient) E < η := by
    simpa only [E] using hn₀ n hn
  have hnotSubset : ¬ B ⊆ E := by
    intro hBE
    have hmono :
        (ν : Measure GammaTwoFrameQuotient) B ≤
          (ν : Measure GammaTwoFrameQuotient) E :=
      measure_mono hBE
    exact (not_le_of_gt hEmass) (hBmass.trans hmono)
  obtain ⟨y, hyB, hyE⟩ := Set.not_subset.mp hnotSubset
  have hyGood :
      dist
        (HGAS.Dynamics.integerOrbitAverageObservable
          gammaTwoHorocycleFlow f.toBCF (N n) y)
        c < ε / 2 := by
    have hyGood' :
        dist (A (N n - 1) y) c < ε / 2 := by
      simpa only [E, mem_setOf_eq, not_le] using hyE
    have hNone : 1 ≤ N n :=
      Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (hNpos n))
    have hpred :
        N n - 1 + 1 = N n :=
      Nat.sub_add_cancel hNone
    simpa only [A, hpred] using hyGood'
  obtain ⟨r, t, h, hr, ht, hh, hy⟩ :=
    mem_gammaTwoShearBox_iff.mp hyB
  have hNR : 0 < (N n : ℝ) := by
    exact_mod_cast hNpos n
  have hexplog :
      Real.exp L = (N n : ℝ) := by
    dsimp only [L]
    exact Real.exp_log hNR
  have hexpneg :
      Real.exp (-L) = (N n : ℝ)⁻¹ := by
    rw [Real.exp_neg, hexplog]
  have hr' : |r| < δ / (N n : ℝ) := by
    simpa only [B, div_eq_mul_inv, hexpneg] using hr
  have hh' : |h| < ρ * (N n : ℝ) := by
    simpa only [B, hexplog] using hh
  have hcompare :=
    hshear (N n) r t h q (hNpos n) hr' ht hh'
  rw [hy] at hcompare
  have hρC : ρ * C = ε / 2 := by
    dsimp only [ρ]
    field_simp [hC.ne']
  have hqToY :
      dist
        (HGAS.Dynamics.integerOrbitAverageObservable
          gammaTwoHorocycleFlow f.toBCF (N n) q)
        (HGAS.Dynamics.integerOrbitAverageObservable
          gammaTwoHorocycleFlow f.toBCF (N n) y) ≤
          ε / 2 := by
    rw [Real.dist_eq]
    calc
      |HGAS.Dynamics.integerOrbitAverageObservable
            gammaTwoHorocycleFlow f.toBCF (N n) q -
          HGAS.Dynamics.integerOrbitAverageObservable
            gammaTwoHorocycleFlow f.toBCF (N n) y| ≤
          ρ * (1 + 4 * ‖f‖) :=
        hcompare
      _ = ρ * C := by rfl
      _ = ε / 2 := hρC
  calc
    dist
        (HGAS.Dynamics.integerOrbitAverageObservable
          gammaTwoHorocycleFlow f.toBCF (N n) q)
        (∫ x, f x ∂(ν : Measure GammaTwoFrameQuotient)) =
      dist
        (HGAS.Dynamics.integerOrbitAverageObservable
          gammaTwoHorocycleFlow f.toBCF (N n) q) c := by
            rfl
    _ ≤
        dist
          (HGAS.Dynamics.integerOrbitAverageObservable
            gammaTwoHorocycleFlow f.toBCF (N n) q)
          (HGAS.Dynamics.integerOrbitAverageObservable
            gammaTwoHorocycleFlow f.toBCF (N n) y) +
        dist
          (HGAS.Dynamics.integerOrbitAverageObservable
            gammaTwoHorocycleFlow f.toBCF (N n) y) c :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 :=
      add_lt_add_of_le_of_lt hqToY hyGood
    _ = ε := by ring

/-- Every nonperiodic point admits positive integer averaging lengths,
tending to infinity, along which every fixed `C₀` observable converges
to Haar measure.  The returned lengths also retain their geometric
return property. -/
theorem
    IsRightInvariantFrameProbability.exists_good_integer_return_lengths
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν)
    (q : GammaTwoFrameQuotient)
    (hnonperiodic : ¬ IsPeriodicHorocyclePoint 1 q)
    (f : C₀(GammaTwoFrameQuotient, ℝ)) :
    ∃ N : ℕ → ℕ,
      Tendsto N atTop atTop ∧
      (∀ n, 0 < N n) ∧
      (∀ n,
        gammaTwoFrameRightMul
            (geodesicFrame (Real.log (N n : ℝ))) q ∈
          gammaTwoIntegerReturnCompactCore) ∧
      Tendsto
        (fun n ↦
          HGAS.Dynamics.integerOrbitAverageObservable
            gammaTwoHorocycleFlow f.toBCF (N n) q)
        atTop
        (𝓝 (∫ x, f x ∂(ν : Measure GammaTwoFrameQuotient))) := by
  obtain ⟨N, hNtop, hNpos, hNreturn⟩ :=
    exists_integer_gammaTwoGeodesic_return_lengths
      q hnonperiodic
  exact
    ⟨N, hNtop, hNpos, hNreturn,
      hν.tendsto_integerOrbitAverage_along_returns
        q N hNtop hNpos hNreturn f⟩

end

end HGAS.Modular
