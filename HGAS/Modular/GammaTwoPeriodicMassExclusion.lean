import HGAS.Dynamics.RenormalizedPeriodicMassExclusion
import HGAS.Dynamics.RenormalizedOrbitOccupations
import HGAS.Modular.GammaTwoOccupationReduction
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Periodic-mass exclusion for level-two horocycles

This file specializes the abstract renormalization argument from
`HGAS.Dynamics.RenormalizedPeriodicMassExclusion` to
`Γ(2) \ SL(2,ℝ)`.

Positive diagonal right translation is the geodesic renormalization.  If

```text
  a(s) = diag(exp(s), exp(-s)),
```

then

```text
  a(s) u(exp(-2s) t) = u(t) a(s).
```

Thus positive geodesic time contracts every positive horocycle period by
`exp(-2s)`.

The final theorem gives a precise sufficient condition for
`GammaTwoNonperiodicOccupationLimitsAvoidPeriodic`: every occupation limit
must have a uniformly tight family of positive-geodesic pushforwards, and
compact subsets of the quotient must have a positive horocycle-period
systole.  These are exactly the two geometric facts used in Proposition 14
of Hubbard--Miller.  They are strictly sharper than bare pointwise
tightness of the original occupation sequence.
-/

namespace HGAS.Modular

open Filter Function Matrix _root_.MeasureTheory Set Topology
open scoped MatrixGroups

noncomputable section

local instance gammaTwoFrameQuotientMetricSpaceForPeriodicMass :
    MetricSpace GammaTwoFrameQuotient :=
  TopologicalSpace.metrizableSpaceMetric GammaTwoFrameQuotient

/-- The diagonal element `diag(exp(s), exp(-s))` of `SL(2,ℝ)`. -/
def gammaTwoGeodesicDiagonal (s : ℝ) : RealModularFrame :=
  ⟨!![Real.exp s, 0; 0, Real.exp (-s)], by
    rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one,
      mul_zero, sub_zero]
    rw [← Real.exp_add]
    simp⟩

@[simp]
theorem gammaTwoGeodesicDiagonal_coe (s : ℝ) :
    (gammaTwoGeodesicDiagonal s :
      Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.exp s, 0; 0, Real.exp (-s)] :=
  rfl

/-- The exact diagonal--unipotent renormalization identity. -/
theorem gammaTwoGeodesicDiagonal_mul_upperUnipotent
    (s t : ℝ) :
    gammaTwoGeodesicDiagonal s *
        upperUnipotent (Real.exp (-2 * s) * t) =
      upperUnipotent t * gammaTwoGeodesicDiagonal s := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp only [neg_mul, Fin.zero_eta, Fin.isValue, Fin.mk_one,
      Matrix.SpecialLinearGroup.coe_mul,
      gammaTwoGeodesicDiagonal_coe, upperUnipotent_coe,
      cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons,
      head_cons, smul_cons, smul_eq_mul, mul_one,
      Matrix.smul_empty, tail_cons, zero_smul, empty_vecMul,
      add_zero, mul_zero, zero_add, Matrix.empty_mul,
      Equiv.symm_apply_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.cons_val_zero, one_smul, add_cons,
      empty_add_empty]
  rw [← mul_assoc, ← Real.exp_add]
  ring

/-- Discrete positive geodesic renormalizers, sufficient for driving
periods to zero. -/
def gammaTwoDiscreteGeodesicRenormalizer
    (n : ℕ) : C(GammaTwoFrameQuotient, GammaTwoFrameQuotient) :=
  ⟨gammaTwoFrameRightMul
      (gammaTwoGeodesicDiagonal (n : ℝ)),
    gammaTwoFrameRightMul_continuous _⟩

/-- The period-contraction factor at the `n`th discrete geodesic time. -/
def gammaTwoDiscretePeriodContraction (n : ℕ) : ℝ :=
  Real.exp (-2 * (n : ℝ))

theorem gammaTwoDiscretePeriodContraction_pos
    (n : ℕ) :
    0 < gammaTwoDiscretePeriodContraction n :=
  Real.exp_pos _

/-- The discrete contraction factors become arbitrarily small. -/
theorem exists_gammaTwoDiscretePeriodContraction_lt
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, gammaTwoDiscretePeriodContraction n < ε := by
  have hlim :
      Tendsto (fun n : ℕ ↦ Real.exp (-(n : ℝ)))
        atTop (𝓝 0) := by
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hevent :
      ∀ᶠ n : ℕ in atTop, Real.exp (-(n : ℝ)) < ε :=
    hlim.eventually (Iio_mem_nhds hε)
  obtain ⟨n, hn⟩ := hevent.exists
  refine ⟨n, ?_⟩
  have hexp_le_one :
      Real.exp (-(n : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (Nat.cast_nonneg n))
  calc
    gammaTwoDiscretePeriodContraction n =
        Real.exp (-(n : ℝ)) * Real.exp (-(n : ℝ)) := by
          rw [gammaTwoDiscretePeriodContraction, ← Real.exp_add]
          congr 1
          ring
    _ ≤ Real.exp (-(n : ℝ)) * 1 := by
          gcongr
    _ < ε := by simpa using hn

/-- Discrete geodesic renormalization contracts every horocycle period by
the stated exponential factor. -/
theorem gammaTwoDiscreteGeodesicRenormalizer_period
    (n : ℕ) (q : GammaTwoFrameQuotient) (T : ℝ)
    (hperiod : gammaTwoHorocycleFlow T q = q) :
    gammaTwoHorocycleFlow
        (gammaTwoDiscretePeriodContraction n * T)
        (gammaTwoDiscreteGeodesicRenormalizer n q) =
      gammaTwoDiscreteGeodesicRenormalizer n q := by
  let a : RealModularFrame :=
    gammaTwoGeodesicDiagonal (n : ℝ)
  let uSmall : RealModularFrame :=
    upperUnipotent
      (gammaTwoDiscretePeriodContraction n * T)
  let u : RealModularFrame := upperUnipotent T
  change
    gammaTwoFrameRightMul uSmall
        (gammaTwoFrameRightMul a q) =
      gammaTwoFrameRightMul a q
  calc
    gammaTwoFrameRightMul uSmall
        (gammaTwoFrameRightMul a q) =
        gammaTwoFrameRightMul (a * uSmall) q := by
          simpa only [Function.comp_apply] using
            congrFun (gammaTwoFrameRightMul_mul a uSmall) q |>.symm
    _ = gammaTwoFrameRightMul (u * a) q := by
          rw [show a * uSmall = u * a by
            exact gammaTwoGeodesicDiagonal_mul_upperUnipotent
              (n : ℝ) T]
    _ = gammaTwoFrameRightMul a
        (gammaTwoFrameRightMul u q) := by
          simpa only [Function.comp_apply] using
            congrFun (gammaTwoFrameRightMul_mul u a) q
    _ = gammaTwoFrameRightMul a q := by
          change
            gammaTwoFrameRightMul a
                (gammaTwoHorocycleFlow T q) =
              gammaTwoFrameRightMul a q
          rw [hperiod]

/-- Exact covariance of the discrete geodesic renormalizer with the
horocycle flow.  Geodesic time `n` changes horocycle time by the factor
`exp(-2n)`. -/
theorem gammaTwoDiscreteGeodesicRenormalizer_horocycleFlow
    (n : ℕ) (t : ℝ) (q : GammaTwoFrameQuotient) :
    gammaTwoDiscreteGeodesicRenormalizer n
        (gammaTwoHorocycleFlow t q) =
      gammaTwoHorocycleFlow
        (gammaTwoDiscretePeriodContraction n * t)
        (gammaTwoDiscreteGeodesicRenormalizer n q) := by
  let a : RealModularFrame :=
    gammaTwoGeodesicDiagonal (n : ℝ)
  let uSmall : RealModularFrame :=
    upperUnipotent
      (gammaTwoDiscretePeriodContraction n * t)
  let u : RealModularFrame := upperUnipotent t
  change
    gammaTwoFrameRightMul a
        (gammaTwoFrameRightMul u q) =
      gammaTwoFrameRightMul uSmall
        (gammaTwoFrameRightMul a q)
  calc
    gammaTwoFrameRightMul a
        (gammaTwoFrameRightMul u q) =
        gammaTwoFrameRightMul (u * a) q := by
          simpa only [Function.comp_apply] using
            congrFun (gammaTwoFrameRightMul_mul u a) q |>.symm
    _ = gammaTwoFrameRightMul (a * uSmall) q := by
          rw [show u * a = a * uSmall by
            exact
              (gammaTwoGeodesicDiagonal_mul_upperUnipotent
                (n : ℝ) t).symm]
    _ = gammaTwoFrameRightMul uSmall
        (gammaTwoFrameRightMul a q) := by
          simpa only [Function.comp_apply] using
            congrFun (gammaTwoFrameRightMul_mul a uSmall) q

/-- Right multiplication by a frame is injective on the left quotient. -/
theorem gammaTwoFrameRightMul_injective
    (a : RealModularFrame) :
    Function.Injective (gammaTwoFrameRightMul a) := by
  intro q₁ q₂ h
  have h' :=
    congrArg (gammaTwoFrameRightMul a⁻¹) h
  have hleft :
      gammaTwoFrameRightMul a⁻¹
          (gammaTwoFrameRightMul a q₁) = q₁ := by
    calc
      gammaTwoFrameRightMul a⁻¹
          (gammaTwoFrameRightMul a q₁) =
          gammaTwoFrameRightMul (a * a⁻¹) q₁ := by
            simpa only [Function.comp_apply] using
              congrFun (gammaTwoFrameRightMul_mul a a⁻¹) q₁ |>.symm
      _ = q₁ := by simp
  have hright :
      gammaTwoFrameRightMul a⁻¹
          (gammaTwoFrameRightMul a q₂) = q₂ := by
    calc
      gammaTwoFrameRightMul a⁻¹
          (gammaTwoFrameRightMul a q₂) =
          gammaTwoFrameRightMul (a * a⁻¹) q₂ := by
            simpa only [Function.comp_apply] using
              congrFun (gammaTwoFrameRightMul_mul a a⁻¹) q₂ |>.symm
      _ = q₂ := by simp
  exact hleft ▸ hright ▸ h'

/-- Positive geodesic renormalization preserves nonperiodicity of a
horocycle. -/
theorem gammaTwoDiscreteGeodesicRenormalizer_nonperiodic
    (n : ℕ) (q : GammaTwoFrameQuotient)
    (hq : ¬ IsPeriodicHorocyclePoint 1 q) :
    ¬ IsPeriodicHorocyclePoint 1
      (gammaTwoDiscreteGeodesicRenormalizer n q) := by
  intro hperiodic
  apply hq
  obtain ⟨T, hTpos, hTperiod⟩ := hperiodic
  rw [scaledGammaTwoHorocycleFlow_one] at hTperiod
  let c : ℝ := gammaTwoDiscretePeriodContraction n
  have hcpos : 0 < c :=
    gammaTwoDiscretePeriodContraction_pos n
  refine ⟨T / c, div_pos hTpos hcpos, ?_⟩
  rw [scaledGammaTwoHorocycleFlow_one]
  apply gammaTwoFrameRightMul_injective
    (gammaTwoGeodesicDiagonal (n : ℝ))
  change
    gammaTwoDiscreteGeodesicRenormalizer n
        (gammaTwoHorocycleFlow (T / c) q) =
      gammaTwoDiscreteGeodesicRenormalizer n q
  rw [gammaTwoDiscreteGeodesicRenormalizer_horocycleFlow]
  change
    gammaTwoHorocycleFlow (c * (T / c))
        (gammaTwoDiscreteGeodesicRenormalizer n q) =
      gammaTwoDiscreteGeodesicRenormalizer n q
  rw [mul_div_cancel₀ T hcpos.ne']
  exact hTperiod

/-- The abstract positive-period set is the concrete union of periodic
unit-speed horocycles used by the occupation reduction. -/
theorem periodicPointSet_gammaTwoHorocycleFlow :
    HGAS.Dynamics.periodicPointSet gammaTwoHorocycleFlow =
      gammaTwoPeriodicHorocycleSet := by
  ext q
  simp only [HGAS.Dynamics.periodicPointSet,
    gammaTwoPeriodicHorocycleSet, IsPeriodicHorocyclePoint,
    mem_setOf_eq, scaledGammaTwoHorocycleFlow_one]

private theorem upperUnipotent_parameter_eq_zero_of_eq_one
    {t : ℝ} (h : upperUnipotent t = 1) :
    t = 0 := by
  have hentry :=
    congrArg
      (fun a : RealModularFrame ↦
        (a : Matrix (Fin 2) (Fin 2) ℝ) 0 1) h
  simpa only [upperUnipotent_coe, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_apply, ne_eq, OfNat.ofNat, Fin.zero_eta,
    Fin.isValue, Fin.mk_one, zero_ne_one, ↓reduceIte] using hentry

/-- Every quotient point has a neighborhood on which sufficiently short
positive horocycle returns are impossible. -/
theorem gammaTwoHorocycleFlow_locally_has_period_systole
    (q : GammaTwoFrameQuotient) :
    ∃ V : Set GammaTwoFrameQuotient,
      IsOpen V ∧ q ∈ V ∧
        ∃ δ : ℝ, 0 < δ ∧
          ∀ y ∈ V, ∀ T : ℝ,
            0 < T → T ≤ δ →
              gammaTwoHorocycleFlow T y ≠ y := by
  induction q using Quotient.inductionOn with
  | _ g =>
      obtain ⟨U, hUg, hUdeck⟩ :=
        gammaTwoFrameQuotientMk_isQuotientCoveringMap.disjoint g
      let F : RealModularFrame × ℝ → RealModularFrame :=
        fun p ↦ p.1 * upperUnipotent p.2
      have hFcontinuous : Continuous F :=
        continuous_fst.mul
          (upperUnipotent_continuous.comp continuous_snd)
      have hUatF : U ∈ 𝓝 (F (g, 0)) := by
        simpa only [F, upperUnipotent_zero, mul_one] using hUg
      have hpreimage :
          F ⁻¹' U ∈ 𝓝 (g, 0) :=
        hFcontinuous.continuousAt hUatF
      obtain ⟨W, hWg, I, hIzero, hWI⟩ :=
        mem_nhds_prod_iff.mp hpreimage
      obtain ⟨O, hOsub, hOopen, hgO⟩ :=
        mem_nhds_iff.mp (inter_mem hWg hUg)
      obtain ⟨d, hdpos, hballI⟩ :=
        Metric.mem_nhds_iff.mp hIzero
      let V : Set GammaTwoFrameQuotient :=
        gammaTwoFrameQuotientMk '' O
      have hVopen : IsOpen V :=
        gammaTwoFrameQuotientMk_isOpenQuotientMap.isOpenMap
          O hOopen
      have hqV :
          gammaTwoFrameQuotientMk g ∈ V :=
        ⟨g, hgO, rfl⟩
      refine ⟨V, hVopen, hqV, d / 2, half_pos hdpos, ?_⟩
      intro y hyV T hTpos hTle hperiod
      obtain ⟨h, hhO, rfl⟩ := hyV
      have hTball : T ∈ Metric.ball (0 : ℝ) d := by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero,
          abs_of_pos hTpos]
        exact hTle.trans_lt (half_lt_self hdpos)
      have hTI : T ∈ I :=
        hballI hTball
      have hhWU : h ∈ W ∩ U :=
        hOsub hhO
      have hmulU :
          h * upperUnipotent T ∈ U :=
        by
          change F (h, T) ∈ U
          exact hWI ⟨hhWU.1, hTI⟩
      have horbit := Quotient.exact hperiod
      change
        h * upperUnipotent T ∈
          MulAction.orbit GammaTwo h at horbit
      obtain ⟨γ, hγ⟩ :=
        MulAction.mem_orbit_iff.mp horbit
      have hinter :
          (((γ • ·) '' U) ∩ U).Nonempty := by
        refine ⟨h * upperUnipotent T, ?_, hmulU⟩
        exact ⟨h, hhWU.2, hγ⟩
      have hγone : γ = 1 :=
        hUdeck γ hinter
      rw [hγone, one_smul] at hγ
      have huone : upperUnipotent T = 1 := by
        apply mul_left_cancel (a := h)
        simpa only [mul_one] using hγ.symm
      exact hTpos.ne'
        (upperUnipotent_parameter_eq_zero_of_eq_one huone)

/-- The local quotient-geometry fact needed by periodic-mass exclusion:
on each compact subset, positive horocycle periods are bounded away from
zero. -/
def GammaTwoHorocycleCompactPeriodSystole : Prop :=
  HGAS.Dynamics.HasCompactPeriodSystole gammaTwoHorocycleFlow

/-- Compactness upgrades the preceding local flow-box estimate to a
uniform positive lower bound on periods over each compact subset. -/
theorem gammaTwoHorocycleCompactPeriodSystole :
    GammaTwoHorocycleCompactPeriodSystole := by
  intro K hKcompact
  choose V hVopen hxV δ hδpos hfree using
    gammaTwoHorocycleFlow_locally_has_period_systole
  by_cases hKempty : K = ∅
  · refine ⟨1, one_pos, ?_⟩
    intro x hxK
    exact (hKempty ▸ hxK).elim
  · have hKnonempty : K.Nonempty :=
      nonempty_iff_ne_empty.mpr hKempty
    have hKcover : K ⊆ ⋃ x : GammaTwoFrameQuotient, V x := by
      intro x hxK
      exact mem_iUnion.2 ⟨x, hxV x⟩
    obtain ⟨S, hScover⟩ :=
      hKcompact.elim_finite_subcover V hVopen hKcover
    have hSnonempty : S.Nonempty := by
      obtain ⟨x, hxK⟩ := hKnonempty
      have hxUnion := hScover hxK
      by_contra hSempty
      rw [Finset.not_nonempty_iff_eq_empty.mp hSempty] at hxUnion
      simp at hxUnion
    let D : Finset ℝ := S.image δ
    have hDnonempty : D.Nonempty :=
      hSnonempty.image _
    let δmin : ℝ := D.min' hDnonempty
    have hδminpos : 0 < δmin := by
      have hmem : δmin ∈ D :=
        Finset.min'_mem D hDnonempty
      obtain ⟨x, hxS, hδx⟩ :=
        Finset.mem_image.mp hmem
      rw [← hδx]
      exact hδpos x
    refine ⟨δmin, hδminpos, ?_⟩
    intro x hxK T hTpos hTle
    obtain ⟨i, hiS, hxi⟩ :=
      mem_iUnion₂.mp (hScover hxK)
    apply hfree i x hxi T hTpos
    exact hTle.trans
      (Finset.min'_le D (δ i)
        (Finset.mem_image.mpr ⟨i, hiS, rfl⟩))

/-- The exact renormalized nonescape property needed for occupation
limits.  It is stronger than tightness of the unrenormalized occupation
sequence: the same limit is pushed through all positive discrete geodesic
times, and that entire family must remain tight. -/
def GammaTwoNonperiodicOccupationLimitRenormalizationTightness : Prop :=
  ∀ q : GammaTwoFrameQuotient,
    ¬ IsPeriodicHorocyclePoint 1 q →
      HGAS.Dynamics.EveryOrbitOccupationLimitSatisfies
        gammaTwoHorocycleFlow q
        (fun μ ↦
          HGAS.Dynamics.HasTightRenormalizationFamily μ
            gammaTwoDiscreteGeodesicRenormalizer)

/-- The classical uniform cusp-nonescape estimate, stated directly for
long real-time occupation probabilities of nonperiodic level-two
horocycles.

For each error tolerance there is one compact core that works for every
nonperiodic starting frame.  The eventual time is allowed to depend on
the starting frame.  This is the quantifier pattern of
Hubbard--Miller Proposition 12. -/
def GammaTwoUniformNonperiodicRealOccupationNonescape : Prop :=
  HGAS.Dynamics.UniformRealOccupationNonescape
    gammaTwoHorocycleFlow
    (fun q ↦ ¬ IsPeriodicHorocyclePoint 1 q)

/-- The uniform finite-time cusp estimate supplies the renormalized
tightness needed by periodic-mass exclusion.

This theorem formally accounts for both implicit steps in the classical
argument: Portmanteau passes the cusp estimate to occupation limits, and
the diagonal--unipotent identity identifies every geodesic pushforward
with a rescaled long horocycle occupation. -/
theorem
    gammaTwoNonperiodicOccupationLimitRenormalizationTightness_of_uniformNonescape
    (hnonescape :
      GammaTwoUniformNonperiodicRealOccupationNonescape) :
    GammaTwoNonperiodicOccupationLimitRenormalizationTightness := by
  intro q hq r μ hr hμ
  exact
    HGAS.Dynamics.hasTightRenormalizationFamily_of_uniform_occupation_limit_nonescape
      gammaTwoHorocycleFlow
      (fun z ↦ ¬ IsPeriodicHorocyclePoint 1 z)
      gammaTwoDiscreteGeodesicRenormalizer
      gammaTwoDiscretePeriodContraction
      gammaTwoDiscretePeriodContraction_pos
      gammaTwoDiscreteGeodesicRenormalizer_horocycleFlow
      gammaTwoDiscreteGeodesicRenormalizer_nonperiodic
      (HGAS.Dynamics.uniformRealOccupationLimitNonescape_of_finiteTime
        gammaTwoHorocycleFlow
        (fun z ↦ ¬ IsPeriodicHorocyclePoint 1 z)
        hnonescape)
      q hq r μ hr hμ

/-- The corrected Hubbard--Miller periodic-mass exclusion step.

The proof uses bounded-period closed strata, rather than asserting without
qualification that an arbitrary compact subset of the full (nonclosed)
periodic set escapes uniformly under geodesic flow.
-/
theorem gammaTwoNonperiodicOccupationLimitsAvoidPeriodic_of_renormalization
    (hsystole : GammaTwoHorocycleCompactPeriodSystole)
    (hrenormalized :
      GammaTwoNonperiodicOccupationLimitRenormalizationTightness) :
    GammaTwoNonperiodicOccupationLimitsAvoidPeriodic := by
  intro q hq r μ hr hμ
  have htight :=
    hrenormalized q hq r μ hr hμ
  have hzero :=
    HGAS.Dynamics.measure_periodicPointSet_eq_zero_of_tight_renormalization
      gammaTwoHorocycleFlow μ
      gammaTwoDiscreteGeodesicRenormalizer
      gammaTwoDiscretePeriodContraction
      hsystole
      gammaTwoDiscreteGeodesicRenormalizer_period
      gammaTwoDiscretePeriodContraction_pos
      (fun ε hε ↦
        exists_gammaTwoDiscretePeriodContraction_lt hε)
      htight
  rwa [periodicPointSet_gammaTwoHorocycleFlow] at hzero

/-- The only remaining hypothesis in the periodic-mass exclusion step is
renormalized nonescape; the compact period-systole is unconditional for
the explicit `Γ(2)` quotient. -/
theorem gammaTwoNonperiodicOccupationLimitsAvoidPeriodic_of_nonescape
    (hrenormalized :
      GammaTwoNonperiodicOccupationLimitRenormalizationTightness) :
    GammaTwoNonperiodicOccupationLimitsAvoidPeriodic :=
  gammaTwoNonperiodicOccupationLimitsAvoidPeriodic_of_renormalization
    gammaTwoHorocycleCompactPeriodSystole hrenormalized

/-- Hubbard--Miller Proposition 14 from the finite-time uniform cusp
nonescape estimate of Proposition 12.

All ingredients after the cusp estimate are unconditional here: the
quotient flow-box argument gives a compact period-systole, positive
geodesic renormalization contracts periods, and the occupation
change-of-variables identity gives tightness of every renormalized limit
family. -/
theorem gammaTwoNonperiodicOccupationLimitsAvoidPeriodic_of_uniformNonescape
    (hnonescape :
      GammaTwoUniformNonperiodicRealOccupationNonescape) :
    GammaTwoNonperiodicOccupationLimitsAvoidPeriodic :=
  gammaTwoNonperiodicOccupationLimitsAvoidPeriodic_of_nonescape
    (gammaTwoNonperiodicOccupationLimitRenormalizationTightness_of_uniformNonescape
      hnonescape)

end

end HGAS.Modular
