import HGAS.Dynamics.C1FlowProfileRegularity
import HGAS.Dynamics.TimeAverages
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
import Mathlib.Tactic

/-!
# Invariant probabilities and the infinitesimal generator

For a complete `C¹` ODE flow on a finite-dimensional real normed space,
invariance of a probability measure is equivalent to the familiar weak
generator identity

```
  ∫ x, Dφ(x)[F(x)] ∂μ = 0
```

for every compactly supported `C¹` test function `φ`.

The proof is deliberately elementary.  The fundamental theorem of calculus
turns the increment of a test function along an orbit into the time integral
of its Lie derivative.  In one direction flow invariance then makes the
average increment vanish.  In the other direction we apply the weak identity
to every time translate of the test function, use Fubini, and recover
invariance first for smooth compactly supported tests and then for all
compactly supported continuous tests by smooth approximation.

This criterion is the reusable analytic input for the invariant-measure
time-change theorem.
-/

noncomputable section

open Function MeasureTheory Set
open scoped BoundedContinuousFunction Interval

namespace HGAS.Dynamics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The Lie derivative of a scalar test function along a vector field. -/
def lieDerivative (F : E → E) (φ : E → ℝ) (x : E) : ℝ :=
  fderiv ℝ φ x (F x)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The Lie derivative is continuous for a `C¹` test function and a
continuous vector field. -/
theorem continuous_lieDerivative
    {F : E → E} {φ : E → ℝ}
    (hF : Continuous F) (hφ : ContDiff ℝ 1 φ) :
    Continuous (lieDerivative F φ) := by
  exact (hφ.continuous_fderiv_apply one_ne_zero).comp
    (continuous_id.prodMk hF)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A Lie derivative vanishes away from the topological support of its test
function. -/
theorem support_lieDerivative_subset
    (F : E → E) (φ : E → ℝ) :
    support (lieDerivative F φ) ⊆ tsupport φ := by
  intro x hx
  by_contra hxt
  have hzero : fderiv ℝ φ x = 0 :=
    fderiv_of_notMem_tsupport ℝ hxt
  exact hx (by simp [lieDerivative, hzero])

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Compact support is inherited by the Lie derivative. -/
theorem HasCompactSupport.lieDerivative
    {F : E → E} {φ : E → ℝ}
    (hφ : HasCompactSupport φ) :
    HasCompactSupport (lieDerivative F φ) :=
  hφ.mono' (support_lieDerivative_subset F φ)

/-- Bundle a compactly supported continuous Lie derivative as a bounded
continuous function. -/
def lieDerivativeBCF
    (F : E → E) (φ : E → ℝ)
    (hF : Continuous F) (hφc : ContDiff ℝ 1 φ)
    (hφs : HasCompactSupport φ) : E →ᵇ ℝ :=
  ofCompactSupport
    (lieDerivative F φ)
    (continuous_lieDerivative hF hφc)
    (HasCompactSupport.lieDerivative hφs)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem lieDerivativeBCF_apply
    (F : E → E) (φ : E → ℝ)
    (hF : Continuous F) (hφc : ContDiff ℝ 1 φ)
    (hφs : HasCompactSupport φ) (x : E) :
    lieDerivativeBCF F φ hF hφc hφs x =
      lieDerivative F φ x :=
  rfl

/-- Weak invariance under the infinitesimal generator, tested against
compactly supported `C¹` functions. -/
def IsGeneratorInvariant
    (F : E → E) (μ : ProbabilityMeasure E) : Prop :=
  ∀ φ : E → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
    ∫ x, lieDerivative F φ x ∂(μ : Measure E) = 0

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A `C¹` ODE flow transports its generator by its own time maps. -/
theorem C1ODEFlow.fderiv_timeMap_generator
    (Φ : C1ODEFlow E) (s : ℝ) (x : E) :
    fderiv ℝ (Φ.flow s) x (Φ.generator x) =
      Φ.generator (Φ.flow s x) := by
  have hsmooth :
      ContDiff ℝ 1 (Φ.flow s) := by
    exact Φ.jointContDiff.comp (contDiff_const.prodMk contDiff_id)
  have hleft :
      HasDerivAt
        (fun t : ℝ ↦ Φ.flow s (Φ.flow t x))
        (fderiv ℝ (Φ.flow s) x (Φ.generator x)) 0 := by
    have hmap :
        HasFDerivAt (Φ.flow s)
          (fderiv ℝ (Φ.flow s) x) x :=
      (hsmooth.differentiable one_ne_zero x).hasFDerivAt
    have horbit :
        HasDerivAt (fun t : ℝ ↦ Φ.flow t x)
          (Φ.generator x) 0 := by
      simpa only [Φ.flow.map_zero_apply] using Φ.generatorODE x 0
    exact hmap.comp_hasDerivAt_of_eq 0 horbit (by simp)
  have hright :
      HasDerivAt
        (fun t : ℝ ↦ Φ.flow (s + t) x)
        (Φ.generator (Φ.flow s x)) 0 := by
    have hbase :
        HasDerivAt (fun t : ℝ ↦ Φ.flow t x)
          (Φ.generator (Φ.flow s x)) (s + 0) := by
      simpa only [add_zero] using Φ.generatorODE x s
    exact hbase.comp_const_add s 0
  have heq :
      (fun t : ℝ ↦ Φ.flow s (Φ.flow t x)) =
        fun t : ℝ ↦ Φ.flow (s + t) x := by
    funext t
    exact (Φ.flow.map_add s t x).symm
  rw [heq] at hleft
  exact hleft.unique hright

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Lie derivatives commute with translating a test function by the flow. -/
theorem C1ODEFlow.lieDerivative_comp_time
    (Φ : C1ODEFlow E) (φ : E → ℝ)
    (hφ : ContDiff ℝ 1 φ) (s : ℝ) (x : E) :
    lieDerivative Φ.generator (fun y ↦ φ (Φ.flow s y)) x =
      lieDerivative Φ.generator φ (Φ.flow s x) := by
  have hsmooth :
      ContDiff ℝ 1 (Φ.flow s) :=
    Φ.jointContDiff.comp (contDiff_const.prodMk contDiff_id)
  rw [lieDerivative, lieDerivative]
  rw [show
      fderiv ℝ (fun y ↦ φ (Φ.flow s y)) x =
        (fderiv ℝ φ (Φ.flow s x)).comp
          (fderiv ℝ (Φ.flow s) x) by
        exact fderiv_comp x
          (hφ.differentiable one_ne_zero _)
          (hsmooth.differentiable one_ne_zero _)]
  simp only [ContinuousLinearMap.comp_apply]
  rw [Φ.fderiv_timeMap_generator]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A time translate of a compactly supported test function remains
compactly supported. -/
theorem C1ODEFlow.hasCompactSupport_comp_time
    (Φ : C1ODEFlow E) {φ : E → ℝ}
    (hφ : HasCompactSupport φ) (s : ℝ) :
    HasCompactSupport (fun x ↦ φ (Φ.flow s x)) := by
  exact hφ.comp_homeomorph (Φ.flow.toHomeomorph s)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A time translate of a `C¹` test function remains `C¹`. -/
theorem C1ODEFlow.contDiff_comp_time
    (Φ : C1ODEFlow E) {φ : E → ℝ}
    (hφ : ContDiff ℝ 1 φ) (s : ℝ) :
    ContDiff ℝ 1 (fun x ↦ φ (Φ.flow s x)) := by
  exact hφ.comp
    (Φ.jointContDiff.comp (contDiff_const.prodMk contDiff_id))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The generator of a jointly `C¹` ODE flow is continuous. -/
theorem C1ODEFlow.continuous_generator
    (Φ : C1ODEFlow E) :
    Continuous Φ.generator := by
  let curves : E → ℝ → E :=
    fun x t ↦ Φ.flow t x
  have hcurves :
      ContDiff ℝ 1 (Function.uncurry curves) := by
    simpa only [curves] using
      Φ.jointContDiff.comp (contDiff_snd.prodMk contDiff_fst)
  have hclm :
      Continuous
        (fun x : E ↦
          fderiv ℝ (curves x) 0) :=
    Continuous.fderiv_one hcurves continuous_const
  have happ :
      Continuous
        (fun x : E ↦
          fderiv ℝ (curves x) 0 (1 : ℝ)) :=
    isBoundedBilinearMap_apply.continuous.comp
      (hclm.prodMk continuous_const)
  have hgen :
      Φ.generator =
        fun x : E ↦ fderiv ℝ (curves x) 0 (1 : ℝ) := by
    funext x
    rw [fderiv_apply_one_eq_deriv]
    simpa only [curves, Φ.flow.map_zero_apply] using
      (Φ.generatorODE x 0).deriv.symm
  rw [hgen]
  exact happ

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Fundamental theorem of calculus for a compactly supported test
function along an ODE orbit. -/
theorem C1ODEFlow.testFunction_increment
    (Φ : C1ODEFlow E) (φ : E → ℝ)
    (hφ : ContDiff ℝ 1 φ)
    (hφs : HasCompactSupport φ)
    (T : ℝ) (x : E) :
    φ (Φ.flow T x) - φ x =
      orbitIntegral Φ.flow
        (lieDerivativeBCF Φ.generator φ
          Φ.continuous_generator hφ hφs)
        T x := by
  let b : E →ᵇ ℝ :=
    lieDerivativeBCF Φ.generator φ
      Φ.continuous_generator hφ hφs
  have hderiv :
      ∀ t : ℝ,
        HasDerivAt (fun s : ℝ ↦ φ (Φ.flow s x))
          (b (Φ.flow t x)) t := by
    intro t
    have hφat :
        HasFDerivAt φ (fderiv ℝ φ (Φ.flow t x))
          (Φ.flow t x) :=
      (hφ.differentiable one_ne_zero _).hasFDerivAt
    simpa only [b, lieDerivativeBCF_apply, lieDerivative] using
      hφat.comp_hasDerivAt t (Φ.generatorODE x t)
  have hint :
      IntervalIntegrable
        (fun t : ℝ ↦ b (Φ.flow t x)) volume 0 T :=
    (b.continuous.comp
      (Φ.flow.continuous continuous_id continuous_const)).intervalIntegrable
      0 T
  symm
  simpa only [orbitIntegral, b, Φ.flow.map_zero_apply] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ hderiv t) hint

omit [FiniteDimensional ℝ E] in
/-- Flow invariance implies the weak generator identity. -/
theorem InvariantProbabilityMeasure.isGeneratorInvariant
    (Φ : C1ODEFlow E)
    (μ : InvariantProbabilityMeasure Φ.flow) :
    IsGeneratorInvariant Φ.generator μ.measure := by
  intro φ hφ hφs
  let φb : E →ᵇ ℝ :=
    ofCompactSupport φ hφ.continuous hφs
  let b : E →ᵇ ℝ :=
    lieDerivativeBCF Φ.generator φ
      Φ.continuous_generator hφ hφs
  have hincrement :
      ∀ x : E,
        φ (Φ.flow 1 x) - φ x =
          orbitIntegral Φ.flow b 1 x := by
    intro x
    simpa only [b] using
      Φ.testFunction_increment φ hφ hφs 1 x
  have hintegral :
      (∫ x, φ (Φ.flow 1 x) - φ x
          ∂(μ.measure : Measure E)) =
        ∫ x, orbitIntegral Φ.flow b 1 x
          ∂(μ.measure : Measure E) :=
    integral_congr_ae (ae_of_all _ hincrement)
  have hφcomp :
      (∫ x, φ (Φ.flow 1 x) ∂(μ.measure : Measure E)) =
        ∫ x, φ x ∂(μ.measure : Measure E) := by
    simpa only [φb] using μ.integral_comp_time 1 φb
  have hleft :
      (∫ x, φ (Φ.flow 1 x) - φ x
          ∂(μ.measure : Measure E)) = 0 := by
    rw [integral_sub]
    · exact sub_eq_zero.mpr hφcomp
    · exact
        (ofCompactSupport
          (fun x ↦ φ (Φ.flow 1 x))
          (hφ.continuous.comp (Φ.flow.continuous_toFun 1))
          (Φ.hasCompactSupport_comp_time hφs 1)).integrable
          (μ.measure : Measure E)
    · exact φb.integrable (μ.measure : Measure E)
  have hright :
      (∫ x, orbitIntegral Φ.flow b 1 x
          ∂(μ.measure : Measure E)) =
        ∫ x, b x ∂(μ.measure : Measure E) := by
    simpa using
      integral_orbitIntegral_eq Φ.flow b μ 1
  rw [hleft, hright] at hintegral
  simpa only [b, lieDerivativeBCF_apply] using hintegral.symm

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Under the weak generator identity, every time translate of a compactly
supported `C¹` test has zero mean Lie derivative. -/
theorem integral_lieDerivative_comp_time_eq_zero
    (Φ : C1ODEFlow E) (μ : ProbabilityMeasure E)
    (hμ : IsGeneratorInvariant Φ.generator μ)
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hφs : HasCompactSupport φ) (s : ℝ) :
    (∫ x, lieDerivative Φ.generator φ (Φ.flow s x)
        ∂(μ : Measure E)) = 0 := by
  have hsmooth := Φ.contDiff_comp_time hφ s
  have hsupp := Φ.hasCompactSupport_comp_time hφs s
  have hzero :=
    hμ (fun x ↦ φ (Φ.flow s x)) hsmooth hsupp
  calc
    (∫ x, lieDerivative Φ.generator φ (Φ.flow s x)
        ∂(μ : Measure E)) =
        ∫ x,
          lieDerivative Φ.generator
            (fun y ↦ φ (Φ.flow s y)) x
          ∂(μ : Measure E) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (Φ.lieDerivative_comp_time φ hφ s x).symm
    _ = 0 := hzero

/-- The mean finite-time Lie-derivative cocycle vanishes under weak
generator invariance. -/
theorem integral_orbitIntegral_lieDerivative_eq_zero
    (Φ : C1ODEFlow E) (μ : ProbabilityMeasure E)
    (hμ : IsGeneratorInvariant Φ.generator μ)
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hφs : HasCompactSupport φ) (T : ℝ) :
    (∫ x,
        orbitIntegral Φ.flow
          (lieDerivativeBCF Φ.generator φ
            Φ.continuous_generator hφ hφs)
          T x
        ∂(μ : Measure E)) = 0 := by
  let b : E →ᵇ ℝ :=
    lieDerivativeBCF Φ.generator φ
      Φ.continuous_generator hφ hφs
  calc
    (∫ x, orbitIntegral Φ.flow b T x ∂(μ : Measure E)) =
        ∫ t in (0 : ℝ)..T,
          ∫ x, b (Φ.flow t x) ∂(μ : Measure E) := by
      symm
      exact intervalIntegral_integral_swap
        (integrable_uncurry_orbitObservable_uIoc
          Φ.flow b μ T)
    _ = ∫ _t in (0 : ℝ)..T, 0 := by
      apply intervalIntegral.integral_congr
      intro t _
      simpa only [b, lieDerivativeBCF_apply] using
        integral_lieDerivative_comp_time_eq_zero
          Φ μ hμ φ hφ hφs t
    _ = 0 := by simp

/-- Weak generator invariance already gives invariance of integrals of
compactly supported `C¹` tests under every time map. -/
theorem integral_comp_time_eq_of_isGeneratorInvariant
    (Φ : C1ODEFlow E) (μ : ProbabilityMeasure E)
    (hμ : IsGeneratorInvariant Φ.generator μ)
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hφs : HasCompactSupport φ) (T : ℝ) :
    (∫ x, φ (Φ.flow T x) ∂(μ : Measure E)) =
      ∫ x, φ x ∂(μ : Measure E) := by
  let φb : E →ᵇ ℝ :=
    ofCompactSupport φ hφ.continuous hφs
  let φTb : E →ᵇ ℝ :=
    ofCompactSupport
      (fun x ↦ φ (Φ.flow T x))
      (hφ.continuous.comp (Φ.flow.continuous_toFun T))
      (Φ.hasCompactSupport_comp_time hφs T)
  have hincrement :
      ∀ x : E,
        φ (Φ.flow T x) - φ x =
          orbitIntegral Φ.flow
            (lieDerivativeBCF Φ.generator φ
              Φ.continuous_generator hφ hφs)
            T x := by
    exact Φ.testFunction_increment φ hφ hφs T
  have hintegral :
      (∫ x, φ (Φ.flow T x) - φ x ∂(μ : Measure E)) =
        ∫ x,
          orbitIntegral Φ.flow
            (lieDerivativeBCF Φ.generator φ
              Φ.continuous_generator hφ hφs)
            T x
          ∂(μ : Measure E) :=
    integral_congr_ae (ae_of_all _ hincrement)
  rw [integral_orbitIntegral_lieDerivative_eq_zero
    Φ μ hμ φ hφ hφs T] at hintegral
  have hsub :
      (∫ x, φ (Φ.flow T x) - φ x ∂(μ : Measure E)) =
        (∫ x, φ (Φ.flow T x) ∂(μ : Measure E)) -
          ∫ x, φ x ∂(μ : Measure E) := by
    rw [integral_sub]
    · exact φTb.integrable (μ : Measure E)
    · exact φb.integrable (μ : Measure E)
  rw [hsub] at hintegral
  exact sub_eq_zero.mp hintegral

/-- Smooth compactly supported tests determine integrals of all continuous
compactly supported functions against probability measures.  This is the
uniform-approximation step in the generator criterion. -/
theorem integral_eq_of_contDiff_compactSupport_tests
    (μ ν : ProbabilityMeasure E)
    (htests :
      ∀ g : E → ℝ, ContDiff ℝ 1 g → HasCompactSupport g →
        (∫ x, g x ∂(μ : Measure E)) =
          ∫ x, g x ∂(ν : Measure E))
    {f : E → ℝ} (hf : Continuous f)
    (hfs : HasCompactSupport f) :
    (∫ x, f x ∂(μ : Measure E)) =
      ∫ x, f x ∂(ν : Measure E) := by
  by_contra hne
  let d : ℝ :=
    ‖(∫ x, f x ∂(μ : Measure E)) -
      ∫ x, f x ∂(ν : Measure E)‖
  have hd : 0 < d := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  let ε : ℝ := d / 4
  have hε : 0 < ε := by
    dsimp only [ε]
    positivity
  obtain ⟨g, hgdiff, hgclose, hgsupp⟩ :=
    hf.exists_contDiff_approx 1
      (ε := fun _ : E ↦ ε) continuous_const
      (fun _ ↦ hε)
  have hgcompact : HasCompactSupport g :=
    hfs.mono hgsupp
  let fb : E →ᵇ ℝ :=
    ofCompactSupport f hf hfs
  let gb : E →ᵇ ℝ :=
    ofCompactSupport g hgdiff.continuous hgcompact
  have hnorm : ‖fb - gb‖ ≤ ε := by
    apply (BoundedContinuousFunction.norm_le hε.le).2
    intro x
    change |f x - g x| ≤ ε
    simpa only [abs_sub_comm, Real.dist_eq] using
      (le_of_lt (hgclose x))
  have hμbound :
      ‖(∫ x, f x ∂(μ : Measure E)) -
          ∫ x, g x ∂(μ : Measure E)‖ ≤ ε := by
    change
      ‖(∫ x, fb x ∂(μ : Measure E)) -
          ∫ x, gb x ∂(μ : Measure E)‖ ≤ ε
    rw [← integral_sub
      (fb.integrable (μ : Measure E))
      (gb.integrable (μ : Measure E))]
    exact ((fb - gb).norm_integral_le_norm
      (μ : Measure E)).trans hnorm
  have hνbound :
      ‖(∫ x, f x ∂(ν : Measure E)) -
          ∫ x, g x ∂(ν : Measure E)‖ ≤ ε := by
    change
      ‖(∫ x, fb x ∂(ν : Measure E)) -
          ∫ x, gb x ∂(ν : Measure E)‖ ≤ ε
    rw [← integral_sub
      (fb.integrable (ν : Measure E))
      (gb.integrable (ν : Measure E))]
    exact ((fb - gb).norm_integral_le_norm
      (ν : Measure E)).trans hnorm
  have hgmean := htests g hgdiff hgcompact
  have htotal :
      d ≤ 2 * ε := by
    calc
      d =
          ‖(∫ x, f x ∂(μ : Measure E)) -
            ∫ x, f x ∂(ν : Measure E)‖ := rfl
      _ ≤
          ‖(∫ x, f x ∂(μ : Measure E)) -
            ∫ x, g x ∂(μ : Measure E)‖ +
          ‖(∫ x, g x ∂(μ : Measure E)) -
            ∫ x, f x ∂(ν : Measure E)‖ :=
        by
          simpa only [dist_eq_norm] using
            dist_triangle
              (∫ x, f x ∂(μ : Measure E))
              (∫ x, g x ∂(μ : Measure E))
              (∫ x, f x ∂(ν : Measure E))
      _ =
          ‖(∫ x, f x ∂(μ : Measure E)) -
            ∫ x, g x ∂(μ : Measure E)‖ +
          ‖(∫ x, g x ∂(ν : Measure E)) -
            ∫ x, f x ∂(ν : Measure E)‖ := by
        rw [hgmean]
      _ ≤ ε + ε := by
        exact add_le_add hμbound (by
          simpa only [norm_sub_rev] using hνbound)
      _ = 2 * ε := by ring
  dsimp only [ε] at htotal
  linarith

/-- Weak generator invariance implies actual invariance under every time
map of the complete `C¹` flow. -/
theorem isInvariantProbability_of_isGeneratorInvariant
    (Φ : C1ODEFlow E) (μ : ProbabilityMeasure E)
    (hμ : IsGeneratorInvariant Φ.generator μ) :
    IsInvariantProbability Φ.flow μ := by
  intro T
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  apply integral_eq_of_contDiff_compactSupport_tests
    (timePushforward Φ.flow μ T) μ
  · intro g hgdiff hgsupp
    have hmap :
        (∫ x, g x
            ∂(timePushforward Φ.flow μ T :
              ProbabilityMeasure E)) =
          ∫ x, g (Φ.flow T x) ∂(μ : Measure E) := by
      exact integral_map
        (μ := (μ : Measure E))
        (Φ.flow.continuous_toFun T).measurable.aemeasurable
        hgdiff.continuous.measurable.aestronglyMeasurable
    rw [hmap]
    exact
      integral_comp_time_eq_of_isGeneratorInvariant
        Φ μ hμ g hgdiff hgsupp T
  · exact f.continuous
  · exact f.hasCompactSupport

/-- **Generator criterion for invariant probabilities.** -/
theorem isInvariantProbability_iff_isGeneratorInvariant
    (Φ : C1ODEFlow E) (μ : ProbabilityMeasure E) :
    IsInvariantProbability Φ.flow μ ↔
      IsGeneratorInvariant Φ.generator μ := by
  constructor
  · intro hμ
    exact
      (InvariantProbabilityMeasure.mk μ hμ).isGeneratorInvariant Φ
  · exact isInvariantProbability_of_isGeneratorInvariant Φ μ

end HGAS.Dynamics
