import HGAS.Analysis.TorusCharacters
import HGAS.Clocks.Controller
import HGAS.Clocks.ControllerFlow
import HGAS.Clocks.RadicalIndependence
import HGAS.Dynamics.InvariantProbability
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Tactic

/-!
# Radical clocks and uniquely ergodic torus translations

This file supplies the dynamical half of the radical-clock lemma.  A
frequency vector `ω : d → ℝ` defines the translation flow

```
        x(t) = x(0) + t ω                     on (ℝ / ℤ)ᵈ.
```

If no nonzero integer character annihilates `ω`, normalized Haar measure
is the only invariant probability measure.  The proof is deliberately
split into reusable pieces:

* an explicit continuous translation flow on an arbitrary finite torus;
* invariance of normalized Haar measure;
* the translation formula for Fourier characters;
* Fourier annihilation for an arbitrary invariant probability;
* determination of a finite Borel measure by its Fourier coefficients,
  using the Stone--Weierstrass density theorem already available for
  `UnitAddTorus.mFourier`;
* specialization to signed square roots of distinct primes.

No abstract unique-ergodicity theorem is imported.  Thus the formal proof
closely mirrors the short paper proof: invariance kills every nonconstant
character, and density of trigonometric polynomials determines the measure.
-/

noncomputable section

open Function MeasureTheory Set
open scoped BigOperators ComplexConjugate ENNReal

namespace HGAS.Clocks.RadicalClock

/-! We use normalized Haar measure on each circle, with the same local
normalization as `HGAS.Analysis.TorusCharacters`. -/

local instance : MeasurableSpace Circle :=
  borel Circle

local instance : BorelSpace Circle :=
  ⟨rfl⟩

local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs
    (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs
    (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

/-- The point of the torus represented by the real vector `t ω`. -/
def torusDisplacement (ω : d → ℝ) (t : ℝ) : UnitAddTorus d :=
  fun i ↦ (t * ω i : UnitAddCircle)

/-- Translation at constant frequency `ω` is a continuous real flow on
the finite unit torus. -/
def torusTranslationFlow (ω : d → ℝ) :
    Flow ℝ (UnitAddTorus d) where
  toFun t x := x + torusDisplacement ω t
  cont' := by
    apply Continuous.add
    · fun_prop
    · apply continuous_pi
      intro i
      exact QuotientAddGroup.continuous_mk.comp
        (continuous_fst.mul (continuous_const.comp continuous_snd))
  map_add' := by
    intro t u x
    ext i
    simp only [Pi.add_apply, torusDisplacement]
    rw [show (t + u) * ω i = u * ω i + t * ω i by ring]
    simp only [QuotientAddGroup.mk_add]
    abel
  map_zero' := by
    intro x
    ext i
    simp [torusDisplacement]

omit [Fintype d] in
@[simp]
theorem torusTranslationFlow_apply
    (ω : d → ℝ) (t : ℝ) (x : UnitAddTorus d) :
    torusTranslationFlow ω t x =
      x + torusDisplacement ω t :=
  rfl

/-- Normalized Haar probability on the finite torus. -/
def torusHaarProbability : ProbabilityMeasure (UnitAddTorus d) :=
  ⟨volume, inferInstance⟩

@[simp]
theorem torusHaarProbability_toMeasure :
    (torusHaarProbability (d := d) :
      Measure (UnitAddTorus d)) = volume :=
  rfl

/-- Normalized Haar probability is invariant under every constant
translation flow. -/
theorem torusHaar_isInvariantProbability (ω : d → ℝ) :
    HGAS.Dynamics.IsInvariantProbability
      (torusTranslationFlow ω) (torusHaarProbability (d := d)) := by
  intro t
  apply ProbabilityMeasure.toMeasure_injective
  change
    Measure.map (fun x : UnitAddTorus d ↦
      x + torusDisplacement ω t) volume = volume
  exact map_add_right_eq_self volume (torusDisplacement ω t)

/-! ## Fourier characters along the translation flow -/

/-- Pair an integer torus character with a real frequency vector.  A zero
value is precisely a resonance. -/
def frequencyPairing (n : d → ℤ) (ω : d → ℝ) : ℝ :=
  ∑ i : d, (n i : ℝ) * ω i

/-- A circle Fourier character is multiplicative in its point argument.
Mathlib's theorem `fourier_add` concerns addition of the integer
frequencies; this companion lemma concerns addition on the circle. -/
theorem fourier_add_point
    (n : ℤ) (x y : UnitAddCircle) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp_rw [fourier_apply, zsmul_add, AddCircle.toCircle_add,
    Circle.coe_mul]

/-- A multivariate Fourier character is multiplicative under torus
addition. -/
theorem mFourier_add_point
    (n : d → ℤ) (x y : UnitAddTorus d) :
    UnitAddTorus.mFourier n (x + y) =
      UnitAddTorus.mFourier n x *
        UnitAddTorus.mFourier n y := by
  classical
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    Pi.add_apply, fourier_add_point, Finset.prod_mul_distrib]

/-- Exact evolution of a character on the linear torus orbit. -/
theorem mFourier_torusDisplacement
    (n : d → ℤ) (ω : d → ℝ) (t : ℝ) :
    UnitAddTorus.mFourier n (torusDisplacement ω t) =
      Complex.exp
        (2 * Real.pi * Complex.I *
          (t * frequencyPairing n ω)) := by
  classical
  rw [UnitAddTorus.mFourier]
  simp only [ContinuousMap.coe_mk, torusDisplacement,
    fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  simp only [frequencyPairing, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_intCast]
  norm_num
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- At the reciprocal half-period associated with a nonzero pairing, the
corresponding character changes sign. -/
theorem mFourier_torusDisplacement_halfPeriod
    (n : d → ℤ) (ω : d → ℝ)
    (hpair : frequencyPairing n ω ≠ 0) :
    UnitAddTorus.mFourier n
        (torusDisplacement ω
          (1 / (2 * frequencyPairing n ω))) = -1 := by
  rw [mFourier_torusDisplacement]
  convert Complex.exp_pi_mul_I using 2
  push_cast
  have hpairComplex :
      (frequencyPairing n ω : ℂ) ≠ 0 := by
    exact_mod_cast hpair
  field_simp [hpairComplex]

/-! ## Invariance annihilates nonresonant characters -/

/-- Integration of a complex continuous observable is invariant under a
time map.  This is the complex-valued analogue of
`InvariantProbabilityMeasure.integral_comp_time`. -/
theorem integral_comp_time_complex
    {K : Type*} [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]
    {ϕ : Flow ℝ K}
    (μ : HGAS.Dynamics.InvariantProbabilityMeasure ϕ)
    (t : ℝ) (f : C(K, ℂ)) :
    (∫ x, f (ϕ t x) ∂(μ.measure : Measure K)) =
      ∫ x, f x ∂(μ.measure : Measure K) := by
  calc
    (∫ x, f (ϕ t x) ∂(μ.measure : Measure K)) =
        ∫ y, f y ∂Measure.map (ϕ t)
          (μ.measure : Measure K) := by
      symm
      exact integral_map
        (ϕ.continuous_toFun t).measurable.aemeasurable
        f.continuous.measurable.aestronglyMeasurable
    _ = ∫ y, f y ∂(μ.measure : Measure K) := by
      rw [μ.map_time_toMeasure t]

/-- Every nonresonant Fourier coefficient of an invariant probability
vanishes. -/
theorem integral_mFourier_eq_zero_of_pairing_ne_zero
    (ω : d → ℝ)
    (μ : HGAS.Dynamics.InvariantProbabilityMeasure
      (torusTranslationFlow ω))
    (n : d → ℤ)
    (hpair : frequencyPairing n ω ≠ 0) :
    (∫ x : UnitAddTorus d,
      UnitAddTorus.mFourier n x
        ∂(μ.measure : Measure (UnitAddTorus d))) = 0 := by
  let t : ℝ := 1 / (2 * frequencyPairing n ω)
  let I : ℂ :=
    ∫ x : UnitAddTorus d,
      UnitAddTorus.mFourier n x
        ∂(μ.measure : Measure (UnitAddTorus d))
  have hinvariant :
      (∫ x : UnitAddTorus d,
        UnitAddTorus.mFourier n
          (torusTranslationFlow ω t x)
          ∂(μ.measure : Measure (UnitAddTorus d))) = I := by
    exact integral_comp_time_complex μ t
      (UnitAddTorus.mFourier n)
  have hhalf :
      UnitAddTorus.mFourier n
        (torusDisplacement ω t) = -1 := by
    exact mFourier_torusDisplacement_halfPeriod n ω hpair
  have hpoint :
      ∀ x : UnitAddTorus d,
        UnitAddTorus.mFourier n
          (torusTranslationFlow ω t x) =
            -UnitAddTorus.mFourier n x := by
    intro x
    rw [torusTranslationFlow_apply, mFourier_add_point, hhalf]
    ring
  have hnegative :
      (∫ x : UnitAddTorus d,
        UnitAddTorus.mFourier n
          (torusTranslationFlow ω t x)
          ∂(μ.measure : Measure (UnitAddTorus d))) = -I := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    exact
      integral_neg
        (μ := (μ.measure : Measure (UnitAddTorus d)))
        (f := fun x : UnitAddTorus d ↦
          UnitAddTorus.mFourier n x)
  have hnegSelf : -I = I :=
    hnegative.symm.trans hinvariant
  have hI : I = 0 :=
    CharZero.neg_eq_self_iff.mp hnegSelf
  exact hI

/-! ## Fourier coefficients determine a probability measure -/

/-- Integration against a probability measure, regarded as a continuous
complex-linear functional on the sup-normed space of continuous
functions.  Factoring through `L¹` makes continuity automatic and keeps
this construction reusable. -/
def continuousMapIntegral
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    (μ : ProbabilityMeasure K) :
    C(K, ℂ) →L[ℂ] ℂ :=
  (L1.integralCLM' ℂ).comp
    (ContinuousMap.toLp 1 (μ : Measure K) ℂ)

@[simp]
theorem continuousMapIntegral_apply
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    (μ : ProbabilityMeasure K) (f : C(K, ℂ)) :
    continuousMapIntegral μ f =
      ∫ x, f x ∂(μ : Measure K) := by
  change
    L1.integralCLM' ℂ
      (ContinuousMap.toLp 1 (μ : Measure K) ℂ f) =
        ∫ x, f x ∂(μ : Measure K)
  rw [← L1.integral_eq' ℂ, L1.integral_eq_integral]
  exact integral_congr_ae
    (ContinuousMap.coeFn_toLp (μ := (μ : Measure K)) f)

/-- On a finite torus, equality of all Fourier coefficients implies
equality of probability measures.

The key formal step is Stone--Weierstrass: the complex span of the
characters is dense in all continuous complex-valued functions.  The
difference of the two integration functionals has a closed kernel, so if
that kernel contains every character, it contains the whole function
space. -/
theorem probabilityMeasure_eq_of_integral_mFourier_eq
    (μ ν : ProbabilityMeasure (UnitAddTorus d))
    (hcoeff : ∀ n : d → ℤ,
      (∫ x, UnitAddTorus.mFourier n x
          ∂(μ : Measure (UnitAddTorus d))) =
        ∫ x, UnitAddTorus.mFourier n x
          ∂(ν : Measure (UnitAddTorus d))) :
    μ = ν := by
  let D : C(UnitAddTorus d, ℂ) →L[ℂ] ℂ :=
    continuousMapIntegral μ - continuousMapIntegral ν
  have hrange :
      Set.range (UnitAddTorus.mFourier (d := d)) ⊆
        D.ker := by
    rintro f ⟨n, rfl⟩
    change D (UnitAddTorus.mFourier n) = 0
    simp only [D, ContinuousLinearMap.sub_apply,
      continuousMapIntegral_apply, sub_eq_zero]
    exact hcoeff n
  have hspan :
      Submodule.span ℂ
          (Set.range (UnitAddTorus.mFourier (d := d))) ≤
        D.ker :=
    Submodule.span_le.mpr hrange
  have hclosure :
      (Submodule.span ℂ
          (Set.range
            (UnitAddTorus.mFourier (d := d)))).topologicalClosure ≤
        D.ker :=
    D.isClosed_ker.closure_subset_iff.mpr hspan
  have hker : D.ker = ⊤ := by
    apply top_unique
    rw [← UnitAddTorus.span_mFourier_closure_eq_top]
    exact hclosure
  have hcomplex :
      ∀ f : C(UnitAddTorus d, ℂ),
        (∫ x, f x ∂(μ : Measure (UnitAddTorus d))) =
          ∫ x, f x ∂(ν : Measure (UnitAddTorus d)) := by
    intro f
    have hf : f ∈ D.ker := by
      rw [hker]
      exact Submodule.mem_top
    change D f = 0 at hf
    simpa only [D, ContinuousLinearMap.sub_apply,
      continuousMapIntegral_apply, sub_eq_zero] using hf
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let fComplex : C(UnitAddTorus d, ℂ) :=
    ⟨fun x ↦ (f x : ℂ),
      Complex.continuous_ofReal.comp f.continuous⟩
  have hfcast :
      Complex.ofReal
          (∫ x, (f x : ℝ)
            ∂(μ : Measure (UnitAddTorus d))) =
        Complex.ofReal
          (∫ x, (f x : ℝ)
            ∂(ν : Measure (UnitAddTorus d))) := by
    calc
      Complex.ofReal
          (∫ x, (f x : ℝ)
            ∂(μ : Measure (UnitAddTorus d))) =
          ∫ x, (f x : ℂ)
            ∂(μ : Measure (UnitAddTorus d)) :=
        integral_complex_ofReal.symm
      _ = ∫ x, (f x : ℂ)
            ∂(ν : Measure (UnitAddTorus d)) := by
        simpa only [fComplex] using hcomplex fComplex
      _ = Complex.ofReal
          (∫ x, (f x : ℝ)
            ∂(ν : Measure (UnitAddTorus d))) :=
        integral_complex_ofReal
  exact Complex.ofReal_injective hfcast

/-! ## Unique ergodicity of a nonresonant translation -/

/-- Haar probability, bundled with its invariance under the translation
flow. -/
def torusHaarInvariantProbability (ω : d → ℝ) :
    HGAS.Dynamics.InvariantProbabilityMeasure
      (torusTranslationFlow ω) :=
  ⟨torusHaarProbability,
    torusHaar_isInvariantProbability ω⟩

/-- A frequency vector with no nontrivial annihilating integer character
has Haar probability as its only invariant probability. -/
theorem invariantProbability_eq_torusHaar_of_noCharacter
    (ω : d → ℝ)
    (hω :
      HGAS.Clocks.RadicalIndependence.HasNoNontrivialIntegerCharacter
        ω)
    (μ : HGAS.Dynamics.InvariantProbabilityMeasure
      (torusTranslationFlow ω)) :
    μ.measure = torusHaarProbability := by
  apply probabilityMeasure_eq_of_integral_mFourier_eq
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [UnitAddTorus.mFourier_zero,
      ContinuousMap.one_apply, integral_const,
      probReal_univ, one_smul, torusHaarProbability_toMeasure]
  · have hpair : frequencyPairing n ω ≠ 0 := by
      intro hzero
      apply hn
      exact hω n (by
        simpa only [frequencyPairing] using hzero)
    rw [integral_mFourier_eq_zero_of_pairing_ne_zero
      ω μ n hpair]
    simp only [torusHaarProbability_toMeasure,
      HGAS.Analysis.integral_mFourier, if_neg hn]

/-- Unbundled formulation: every invariant probability for a nonresonant
translation is normalized Haar probability. -/
theorem isInvariantProbability_iff_eq_torusHaar
    (ω : d → ℝ)
    (hω :
      HGAS.Clocks.RadicalIndependence.HasNoNontrivialIntegerCharacter
        ω)
    (μ : ProbabilityMeasure (UnitAddTorus d)) :
    HGAS.Dynamics.IsInvariantProbability
        (torusTranslationFlow ω) μ ↔
      μ = torusHaarProbability := by
  constructor
  · intro hμ
    exact invariantProbability_eq_torusHaar_of_noCharacter
      ω hω ⟨μ, hμ⟩
  · rintro rfl
    exact torusHaar_isInvariantProbability ω

/-- The exact radical-frequency specialization: for distinct prime
parameters and arbitrary choices of signs, normalized Haar probability is
the unique invariant probability on the joint phase torus. -/
theorem signedPrimeSqrt_uniqueInvariantProbability
    (p : d → ℕ)
    (hp : ∀ i : d, (p i).Prime)
    (hinjective : Function.Injective p)
    (sign : d → ℤ)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (μ : ProbabilityMeasure (UnitAddTorus d)) :
    HGAS.Dynamics.IsInvariantProbability
        (torusTranslationFlow
          (HGAS.Clocks.RadicalIndependence.signedPrimeSqrtFrequency
            p sign)) μ ↔
      μ = torusHaarProbability := by
  apply isInvariantProbability_iff_eq_torusHaar
  exact
    HGAS.Clocks.RadicalIndependence.signedPrimeSqrtFrequency_hasNoNontrivialIntegerCharacter
      p hp hinjective sign hsign

/-- Joint-clock marginal form of the radical-clock lemma.

The ambient invariant probability may contain arbitrarily dependent
controller, arithmetic, or auxiliary coordinates.  As soon as its phase
projection is equivariant with the signed radical translation, that
pushforward marginal is Haar.  Ergodicity of the ambient measure is not
needed, so this is stronger than the formulation in the manuscript. -/
theorem signedPrimeSqrt_equivariantMarginal_eq_haar
    {K : Type*} [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]
    {ϕ : Flow ℝ K}
    (p : d → ℕ)
    (hp : ∀ i : d, (p i).Prime)
    (hinjective : Function.Injective p)
    (sign : d → ℤ)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (μ : HGAS.Dynamics.InvariantProbabilityMeasure ϕ)
    (π : K → UnitAddTorus d)
    (hπ : Continuous π)
    (hequiv : ∀ t : ℝ,
      Function.Semiconj π (ϕ t)
        (torusTranslationFlow
          (HGAS.Clocks.RadicalIndependence.signedPrimeSqrtFrequency
            p sign) t)) :
    (μ.mapEquivariant π hπ hequiv).measure =
      torusHaarProbability := by
  apply invariantProbability_eq_torusHaar_of_noCharacter
  exact
    HGAS.Clocks.RadicalIndependence.signedPrimeSqrtFrequency_hasNoNontrivialIntegerCharacter
      p hp hinjective sign hsign

/-- Manuscript-facing name for the joint radical-clock marginal theorem.
It states the advertised conclusion for every invariant probability and
therefore, in particular, for every ergodic invariant probability. -/
theorem radicalClock_ergodic_marginal
    {K : Type*} [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]
    {ϕ : Flow ℝ K}
    (primes : d → ℕ)
    (hprime : ∀ i : d, (primes i).Prime)
    (hdistinct : Function.Injective primes)
    (controllerSign : d → ℤ)
    (hcontrollerSign :
      ∀ i, controllerSign i = 1 ∨ controllerSign i = -1)
    (μ : HGAS.Dynamics.InvariantProbabilityMeasure ϕ)
    (phaseProjection : K → UnitAddTorus d)
    (hcontinuous : Continuous phaseProjection)
    (hequivariant : ∀ t : ℝ,
      Function.Semiconj phaseProjection (ϕ t)
        (torusTranslationFlow
          (HGAS.Clocks.RadicalIndependence.signedPrimeSqrtFrequency
            primes controllerSign) t)) :
    (μ.mapEquivariant phaseProjection hcontinuous hequivariant).measure =
      torusHaarProbability :=
  signedPrimeSqrt_equivariantMarginal_eq_haar
    primes hprime hdistinct controllerSign hcontrollerSign
    μ phaseProjection hcontinuous hequivariant

/-! ## Bridge from locked polynomial controllers to signed radicals -/

omit [Fintype d] in
/-- A finite family of locked prime controllers supplies one sign choice
in every coordinate, and its actual frequency vector is exactly the
corresponding signed-prime-root vector. -/
theorem exists_signs_for_lockedPrimeControllers
    (p : d → ℕ)
    (x : d →
      HGAS.Clocks.Controller.ControllerState ℝ)
    (hlock : ∀ i : d,
      (p i : ℝ) * (x i).r ^ 2 = 1) :
    ∃ sign : d → ℤ,
      (∀ i, sign i = 1 ∨ sign i = -1) ∧
      (fun i ↦
        HGAS.Clocks.Controller.lockedFrequency
          (p i : ℝ) (x i)) =
        HGAS.Clocks.RadicalIndependence.signedPrimeSqrtFrequency
          p sign := by
  have hfrequency :
      ∀ i : d,
        HGAS.Clocks.Controller.lockedFrequency
            (p i : ℝ) (x i) =
            Real.sqrt (p i : ℝ) ∨
          HGAS.Clocks.Controller.lockedFrequency
            (p i : ℝ) (x i) =
            -Real.sqrt (p i : ℝ) := by
    intro i
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    rw [HGAS.Clocks.Controller.lockedFrequency_sq_of_lock
      (p i : ℝ) (x i) (hlock i)]
    exact (Real.sq_sqrt (Nat.cast_nonneg (p i))).symm
  let sign : d → ℤ :=
    fun i ↦
      if HGAS.Clocks.Controller.lockedFrequency
          (p i : ℝ) (x i) =
          Real.sqrt (p i : ℝ)
      then 1 else -1
  refine ⟨sign, ?_, ?_⟩
  · intro i
    by_cases hi :
        HGAS.Clocks.Controller.lockedFrequency
            (p i : ℝ) (x i) =
          Real.sqrt (p i : ℝ)
    · left
      simp only [sign, if_pos hi]
    · right
      simp only [sign, if_neg hi]
  · funext i
    rcases hfrequency i with hi | hi
    · simp [sign,
        HGAS.Clocks.RadicalIndependence.signedPrimeSqrtFrequency,
        hi]
    · simp [sign,
        HGAS.Clocks.RadicalIndependence.signedPrimeSqrtFrequency,
        hi]

omit [Fintype d] in
/-- At a unit-circle controller equilibrium, the preceding locking
hypothesis is automatic.  Thus all actual phase frequencies are signed
prime square roots. -/
theorem exists_signs_for_primeControllerEquilibria
    (p : d → ℕ)
    (x : d →
      HGAS.Clocks.Controller.ControllerState ℝ)
    (hunit : ∀ i : d,
      HGAS.Clocks.Controller.controllerRadiusSq (x i) = 1)
    (hequilibrium : ∀ i : d,
      HGAS.Clocks.Controller.IsControllerEquilibrium
        (p i : ℝ) (x i)) :
    ∃ sign : d → ℤ,
      (∀ i, sign i = 1 ∨ sign i = -1) ∧
      (fun i ↦
        HGAS.Clocks.Controller.lockedFrequency
          (p i : ℝ) (x i)) =
        HGAS.Clocks.RadicalIndependence.signedPrimeSqrtFrequency
          p sign := by
  apply exists_signs_for_lockedPrimeControllers p x
  intro i
  exact
    (HGAS.Clocks.Controller.isControllerEquilibrium_iff_lock_of_unit
        (p i : ℝ) (x i) (hunit i)).mp
      (hequilibrium i)

/-- Full equilibrium-to-Haar phase conclusion of the radical-clock
construction.  Once the polynomial controllers lie at unit-circle
equilibria, their literal frequencies are a signed radical vector, and
every equivariant joint invariant marginal is Haar. -/
theorem radicalClock_at_primeControllerEquilibria
    {K : Type*} [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]
    {ϕ : Flow ℝ K}
    (p : d → ℕ)
    (hp : ∀ i : d, (p i).Prime)
    (hinjective : Function.Injective p)
    (x : d →
      HGAS.Clocks.Controller.ControllerState ℝ)
    (hunit : ∀ i : d,
      HGAS.Clocks.Controller.controllerRadiusSq (x i) = 1)
    (hequilibrium : ∀ i : d,
      HGAS.Clocks.Controller.IsControllerEquilibrium
        (p i : ℝ) (x i))
    (μ : HGAS.Dynamics.InvariantProbabilityMeasure ϕ)
    (phaseProjection : K → UnitAddTorus d)
    (hcontinuous : Continuous phaseProjection)
    (hequivariant : ∀ t : ℝ,
      Function.Semiconj phaseProjection (ϕ t)
        (torusTranslationFlow
          (fun i ↦
            HGAS.Clocks.Controller.lockedFrequency
              (p i : ℝ) (x i)) t)) :
    ∃ sign : d → ℤ,
      (∀ i, sign i = 1 ∨ sign i = -1) ∧
      (fun i ↦
        HGAS.Clocks.Controller.lockedFrequency
          (p i : ℝ) (x i)) =
        HGAS.Clocks.RadicalIndependence.signedPrimeSqrtFrequency
          p sign ∧
      (μ.mapEquivariant phaseProjection hcontinuous
        hequivariant).measure = torusHaarProbability := by
  obtain ⟨sign, hsign, hfrequency⟩ :=
    exists_signs_for_primeControllerEquilibria
      p x hunit hequilibrium
  refine ⟨sign, hsign, hfrequency, ?_⟩
  have hequivariant' : ∀ t : ℝ,
      Function.Semiconj phaseProjection (ϕ t)
        (torusTranslationFlow
          (HGAS.Clocks.RadicalIndependence.signedPrimeSqrtFrequency
            p sign) t) := by
    simpa only [hfrequency] using hequivariant
  have hhaar :=
    signedPrimeSqrt_equivariantMarginal_eq_haar
      p hp hinjective sign hsign μ phaseProjection
      hcontinuous hequivariant'
  exact hhaar

/-! ## Full factor formulation

The preceding results can be used without choosing coordinates on a large
ambient reduction.  It is enough to exhibit each controller and the joint
phase torus as continuous equivariant factors. -/

/-- A natural prime is strictly larger than one after coercion to the
reals, as required by the explicit controller flow. -/
theorem realCast_prime_gt_one {q : ℕ} (hq : q.Prime) :
    (1 : ℝ) < q := by
  exact_mod_cast hq.one_lt

/-- Manuscript-facing radical-clock package on a fixed sign branch.

Suppose an arbitrary ambient invariant probability has:

* one equivariant polynomial-controller factor for each distinct prime;
* a joint phase factor rotating with one fixed choice of signed radical
  frequencies.

Then every controller factor is concentrated both on the zeros of the
literal polynomial field and, equivalently, on the displayed locked
coordinate squares.  Simultaneously, the joint phase marginal is Haar.
The ambient invariant probability need not be ergodic. -/
theorem radicalClock_controllerSupport_and_phaseHaar
    {K : Type*} [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]
    {ϕ : Flow ℝ K}
    (p : d → ℕ)
    (hp : ∀ i : d, (p i).Prime)
    (hinjective : Function.Injective p)
    (sign : d → ℤ)
    (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (μ : HGAS.Dynamics.InvariantProbabilityMeasure ϕ)
    (controllerProjection : d → K → Circle)
    (hcontrollerContinuous :
      ∀ i, Continuous (controllerProjection i))
    (hcontrollerEquivariant :
      ∀ i : d, ∀ t : ℝ,
        Function.Semiconj (controllerProjection i) (ϕ t)
          (HGAS.Clocks.ControllerFlow.controllerFlow
            (p i : ℝ) (realCast_prime_gt_one (hp i)) t))
    (phaseProjection : K → UnitAddTorus d)
    (hphaseContinuous : Continuous phaseProjection)
    (hphaseEquivariant : ∀ t : ℝ,
      Function.Semiconj phaseProjection (ϕ t)
        (torusTranslationFlow
          (HGAS.Clocks.RadicalIndependence.signedPrimeSqrtFrequency
            p sign) t)) :
    (∀ i : d,
      (((μ.mapEquivariant
          (controllerProjection i)
          (hcontrollerContinuous i)
          (hcontrollerEquivariant i)).measure :
            ProbabilityMeasure Circle) : Measure Circle)
        ({z : Circle |
          HGAS.Clocks.Controller.IsControllerEquilibrium (p i : ℝ)
            (HGAS.Clocks.ControllerFlow.circleControllerState z)}ᶜ) =
        0) ∧
    (∀ i : d,
      (((μ.mapEquivariant
          (controllerProjection i)
          (hcontrollerContinuous i)
          (hcontrollerEquivariant i)).measure :
            ProbabilityMeasure Circle) : Measure Circle)
        ({z : Circle |
          (z : ℂ).re ^ 2 = 1 / (p i : ℝ) ∧
          (z : ℂ).im ^ 2 = 1 - 1 / (p i : ℝ)}ᶜ) =
        0) ∧
    (μ.mapEquivariant phaseProjection hphaseContinuous
      hphaseEquivariant).measure = torusHaarProbability := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact
      HGAS.Clocks.ControllerFlow.invariantProbability_polynomialEquilibria_compl_eq_zero
        (p i : ℝ) (realCast_prime_gt_one (hp i))
        (μ.mapEquivariant
          (controllerProjection i)
          (hcontrollerContinuous i)
          (hcontrollerEquivariant i))
  · intro i
    exact
      HGAS.Clocks.ControllerFlow.invariantProbability_lockedCoordinateSquares_compl_eq_zero
        (p i : ℝ) (realCast_prime_gt_one (hp i))
        (μ.mapEquivariant
          (controllerProjection i)
          (hcontrollerContinuous i)
          (hcontrollerEquivariant i))
  · exact
      signedPrimeSqrt_equivariantMarginal_eq_haar
        p hp hinjective sign hsign μ phaseProjection
        hphaseContinuous hphaseEquivariant

end HGAS.Clocks.RadicalClock
