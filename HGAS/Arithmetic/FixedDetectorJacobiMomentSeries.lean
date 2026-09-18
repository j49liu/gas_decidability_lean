import HGAS.Arithmetic.FixedDetectorMomentCode
import HGAS.Arithmetic.CanonicalFixedDetectorTrajectory
import HGAS.Analysis.LinearODEZero
import HGAS.Clocks.LockedControllerPhaseCharacterFormula
import HGAS.Modular.JacobiBlochGaugeSeries
import Mathlib.Tactic

/-!
# The compiled Jacobi moments are the three quadratic-series rows

`JacobiBlochGaugeSeries` proves the analytic normal form of a selected
affine Bloch output.  This file identifies the literal integral characters
emitted by `FixedDetectorMomentCode` with the three character twists in
that normal form.

For detector block `j`, write `ω` for its private modular frequency and
`N` for its DQL linear frequency.  On the all-one locked phase orbit, the
compiled characters have the exact frequencies

```text
  jacobiPlusExponent  : -(ω + N),
  jacobiMinusExponent : -(ω - N).
```

If the affine Bloch clocks are the clocks emitted by the linked-Jacobi
compiler,

```text
  κ = ω/π,       ν = (ω+N)/(2π),
```

then `Ω=ω` and `ρ=N/ω`.  Consequently the three literal compiler
observables `F`, `F(QV)⁻¹`, and `FQ⁻¹V` are, before subtracting their
rational target constants, exactly rows `r=0,1,-1` of
`quadraticMomentSeries`.
-/

namespace HGAS

open Complex
open Modular
open Clocks
open Clocks.ControllerPhaseProductCharacterCode

noncomputable section

namespace Clocks.LockedControllerPhaseTrajectory

variable {q : ℕ}

/-- Closed character formula for an arbitrary initial phase family.

Compared with the all-one formula, the only extra datum is the
time-independent initial character value.  This is the form needed for
all-state selection, where the orbit cannot be assumed to start at the
canonical phase origin. -/
theorem characterValue_stateFamily_eq_initial_mul_exponential
    (parameters : Fin q → RationalCode)
    (controller : Fin q → Controller.ControllerState ℝ)
    (phase₀ : Fin q → Circle)
    (exponents : Fin q → ℤ) (t : ℝ) :
    characterValue exponents
        (stateFamily parameters controller phase₀ t) =
      characterValue exponents
          (stateFamily parameters controller phase₀ 0) *
        HGAS.Analysis.realFrequencyExponential
          (characterFrequency parameters controller exponents) t := by
  let f : ℝ → ℂ :=
    fun s ↦
      characterValue exponents
        (stateFamily parameters controller phase₀ s)
  let ω : ℝ :=
    characterFrequency parameters controller exponents
  let g : ℝ → ℂ :=
    fun s ↦
      f 0 * HGAS.Analysis.realFrequencyExponential ω s
  have hf :
      ∀ s, HasDerivAt f
        (((ω : ℂ) * I) * f s) s := by
    intro s
    simpa only [f, ω, mul_comm I] using
      characterValue_hasDerivAt
        parameters controller phase₀ exponents s
  have hexponential :
      ∀ s,
        HasDerivAt
          (HGAS.Analysis.realFrequencyExponential ω)
          (((ω : ℂ) * I) *
            HGAS.Analysis.realFrequencyExponential ω s) s := by
    intro s
    have hcast :
        HasDerivAt (fun u : ℝ ↦ (u : ℂ)) 1 s :=
      (hasDerivAt_id s).ofReal_comp
    have hlinear :
        HasDerivAt
          (fun u : ℝ ↦ ((ω : ℂ) * I) * (u : ℂ))
          ((ω : ℂ) * I) s := by
      convert hcast.const_mul ((ω : ℂ) * I) using 1
      all_goals ring
    convert hlinear.cexp using 1
    all_goals unfold HGAS.Analysis.realFrequencyExponential
    all_goals ring
  have hg :
      ∀ s, HasDerivAt g
        (((ω : ℂ) * I) * g s) s := by
    intro s
    have h := (hexponential s).const_mul (f 0)
    convert h using 1
    all_goals simp only [g]
    all_goals ring
  let r : ℝ → ℂ := fun s ↦ f s - g s
  have hr :
      ∀ s, HasDerivAt r
        (((ω : ℂ) * I) * r s) s := by
    intro s
    have h := (hf s).sub (hg s)
    convert h using 1
    all_goals simp only [r]
    all_goals ring
  have hr0 : r 0 = 0 := by
    simp [r, g, HGAS.Analysis.realFrequencyExponential]
  have hzero :=
    HGAS.complex_eq_zero_of_hasDerivAt_eq_mul
      (fun _ ↦ (ω : ℂ) * I) r continuous_const hr hr0
  have hpoint := congrFun hzero t
  simpa only [r, sub_eq_zero, f, g, ω] using hpoint

end Clocks.LockedControllerPhaseTrajectory

namespace FixedDetectorMomentCode

variable {eqs vars : ℕ}

/-- The flattened private character reads exactly the private modular
frequency on a locked controller state. -/
theorem characterFrequency_privateExponent
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) :
    LockedControllerPhaseTrajectory.characterFrequency
        parameters controller (privateExponent j) =
      CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j := by
  unfold LockedControllerPhaseTrajectory.characterFrequency
    LockedControllerPhaseTrajectory.angularVelocity
    CanonicalFixedDetectorTrajectory.omegaFrequency
  apply Finset.sum_congr rfl
  intro i _
  simp only [privateExponent, DetectorCharacterCode.omegaWeights,
    ControllerPhaseProductCharacterCode.exponentWeightCode,
    RationalCode.decode_encode, Rat.cast_intCast]
  ring

/-- The flattened DQL character reads exactly the linear frequency on a
locked controller state. -/
theorem characterFrequency_linearExponent
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) :
    LockedControllerPhaseTrajectory.characterFrequency
        parameters controller (linearExponent I j) =
      CanonicalFixedDetectorTrajectory.numberFrequency
        parameters I controller j := by
  unfold LockedControllerPhaseTrajectory.characterFrequency
    LockedControllerPhaseTrajectory.angularVelocity
    CanonicalFixedDetectorTrajectory.numberFrequency
  apply Finset.sum_congr rfl
  intro i _
  simp only [linearExponent, DetectorCharacterCode.numberWeights,
    ControllerPhaseProductCharacterCode.exponentWeightCode,
    RationalCode.decode_encode, Rat.cast_intCast]
  ring

/-- Exact compiled frequency of the `(1,1)` Jacobi moment character. -/
theorem characterFrequency_jacobiPlusExponent
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) :
    LockedControllerPhaseTrajectory.characterFrequency
        parameters controller (jacobiPlusExponent I j) =
      -(CanonicalFixedDetectorTrajectory.omegaFrequency
          parameters controller j +
        CanonicalFixedDetectorTrajectory.numberFrequency
          parameters I controller j) := by
  have hprivate :=
    characterFrequency_privateExponent parameters controller j
  have hlinear :=
    characterFrequency_linearExponent parameters I controller j
  unfold LockedControllerPhaseTrajectory.characterFrequency at hprivate hlinear
  unfold LockedControllerPhaseTrajectory.characterFrequency
  unfold jacobiPlusExponent
  simp only [Int.cast_neg, Int.cast_add]
  have hsum :
      (∑ i : Fin (clockCount eqs vars),
          (-((privateExponent j i : ℝ) +
              (linearExponent I j i : ℝ))) *
            LockedControllerPhaseTrajectory.angularVelocity
              parameters controller i) =
        -(∑ i : Fin (clockCount eqs vars),
            (privateExponent j i : ℝ) *
              LockedControllerPhaseTrajectory.angularVelocity
                parameters controller i) -
          (∑ i : Fin (clockCount eqs vars),
            (linearExponent I j i : ℝ) *
              LockedControllerPhaseTrajectory.angularVelocity
                parameters controller i) := by
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib,
      ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum, hprivate, hlinear]
  ring

/-- Exact compiled frequency of the `(1,-1)` Jacobi moment character. -/
theorem characterFrequency_jacobiMinusExponent
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) :
    LockedControllerPhaseTrajectory.characterFrequency
        parameters controller (jacobiMinusExponent I j) =
      -CanonicalFixedDetectorTrajectory.omegaFrequency
          parameters controller j +
        CanonicalFixedDetectorTrajectory.numberFrequency
          parameters I controller j := by
  have hprivate :=
    characterFrequency_privateExponent parameters controller j
  have hlinear :=
    characterFrequency_linearExponent parameters I controller j
  unfold LockedControllerPhaseTrajectory.characterFrequency at hprivate hlinear
  unfold LockedControllerPhaseTrajectory.characterFrequency
  unfold jacobiMinusExponent
  simp only [Int.cast_add, Int.cast_neg]
  have hsum :
      (∑ i : Fin (clockCount eqs vars),
          (-(privateExponent j i : ℝ) +
            (linearExponent I j i : ℝ)) *
            LockedControllerPhaseTrajectory.angularVelocity
              parameters controller i) =
        -(∑ i : Fin (clockCount eqs vars),
            (privateExponent j i : ℝ) *
              LockedControllerPhaseTrajectory.angularVelocity
                parameters controller i) +
          (∑ i : Fin (clockCount eqs vars),
            (linearExponent I j i : ℝ) *
              LockedControllerPhaseTrajectory.angularVelocity
                parameters controller i) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum, hprivate, hlinear]

/-- Closed exponential formula for the literal `(1,1)` moment character
on the aligned all-one phase orbit. -/
theorem characterValue_jacobiPlusExponent_onePhase
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) (t : ℝ) :
    characterValue (jacobiPlusExponent I j)
        (CanonicalFixedDetectorTrajectory.clockPath
          parameters controller
          LockedControllerPhaseTrajectory.onePhase t) =
      HGAS.Analysis.realFrequencyExponential
        (-(CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j +
            CanonicalFixedDetectorTrajectory.numberFrequency
              parameters I controller j)) t := by
  unfold CanonicalFixedDetectorTrajectory.clockPath
  rw [LockedControllerPhaseTrajectory.characterValue_onePhase]
  rw [characterFrequency_jacobiPlusExponent]
  unfold HGAS.Analysis.realFrequencyExponential
  congr 1
  push_cast
  ring

/-- Closed exponential formula for the literal `(1,-1)` moment character
on the aligned all-one phase orbit. -/
theorem characterValue_jacobiMinusExponent_onePhase
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars) (t : ℝ) :
    characterValue (jacobiMinusExponent I j)
        (CanonicalFixedDetectorTrajectory.clockPath
          parameters controller
          LockedControllerPhaseTrajectory.onePhase t) =
      HGAS.Analysis.realFrequencyExponential
        (-CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j +
            CanonicalFixedDetectorTrajectory.numberFrequency
              parameters I controller j) t := by
  unfold CanonicalFixedDetectorTrajectory.clockPath
  rw [LockedControllerPhaseTrajectory.characterValue_onePhase]
  rw [characterFrequency_jacobiMinusExponent]
  unfold HGAS.Analysis.realFrequencyExponential
  congr 1
  push_cast
  ring

/-- Arbitrary-initial-phase form of the `(1,1)` character formula. -/
theorem characterValue_jacobiPlusExponent_phase
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (j : Fin vars) (t : ℝ) :
    characterValue (jacobiPlusExponent I j)
        (CanonicalFixedDetectorTrajectory.clockPath
          parameters controller phase₀ t) =
      characterValue (jacobiPlusExponent I j)
          (CanonicalFixedDetectorTrajectory.clockPath
            parameters controller phase₀ 0) *
        HGAS.Analysis.realFrequencyExponential
          (-(CanonicalFixedDetectorTrajectory.omegaFrequency
                parameters controller j +
              CanonicalFixedDetectorTrajectory.numberFrequency
                parameters I controller j)) t := by
  unfold CanonicalFixedDetectorTrajectory.clockPath
  rw [
    LockedControllerPhaseTrajectory.characterValue_stateFamily_eq_initial_mul_exponential,
    characterFrequency_jacobiPlusExponent]

/-- Arbitrary-initial-phase form of the `(1,-1)` character formula. -/
theorem characterValue_jacobiMinusExponent_phase
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (j : Fin vars) (t : ℝ) :
    characterValue (jacobiMinusExponent I j)
        (CanonicalFixedDetectorTrajectory.clockPath
          parameters controller phase₀ t) =
      characterValue (jacobiMinusExponent I j)
          (CanonicalFixedDetectorTrajectory.clockPath
            parameters controller phase₀ 0) *
        HGAS.Analysis.realFrequencyExponential
          (-CanonicalFixedDetectorTrajectory.omegaFrequency
                parameters controller j +
              CanonicalFixedDetectorTrajectory.numberFrequency
                parameters I controller j) t := by
  unfold CanonicalFixedDetectorTrajectory.clockPath
  rw [
    LockedControllerPhaseTrajectory.characterValue_stateFamily_eq_initial_mul_exponential,
    characterFrequency_jacobiMinusExponent]

end FixedDetectorMomentCode

namespace Modular.AffineBlochParameters

/-- The affine clocks match the two physical detector frequencies. -/
structure MatchesDetectorClocks
    (p : AffineBlochParameters) (ω N : ℝ) : Prop where
  kappa_eq : p.kappa = ω / π
  nu_eq : p.nu = (ω + N) / (2 * π)

namespace MatchesDetectorClocks

variable {p : AffineBlochParameters} {ω N : ℝ}

theorem quadraticOmega_eq
    (h : MatchesDetectorClocks p ω N) :
    p.quadraticOmega = ω := by
  rw [quadraticOmega, h.kappa_eq]
  field_simp [Real.pi_ne_zero]

theorem quadraticLinearFrequency_eq
    (h : MatchesDetectorClocks p ω N) :
    p.quadraticLinearFrequency = N := by
  calc
    p.quadraticLinearFrequency =
        2 * Real.pi *
          ((ω + N) / (2 * Real.pi)) - ω := by
      rw [quadraticLinearFrequency, h.quadraticOmega_eq, h.nu_eq]
    _ = N := by
      field_simp [Real.pi_ne_zero]
      ring

theorem kappa_ne_zero
    (h : MatchesDetectorClocks p ω N) (hω : ω ≠ 0) :
    p.kappa ≠ 0 := by
  rw [h.kappa_eq]
  exact div_ne_zero hω Real.pi_ne_zero

theorem quadraticClockRatio_eq
    (h : MatchesDetectorClocks p ω N) :
    p.quadraticClockRatio = N / ω := by
  rw [AffineBlochParameters.quadraticClockRatio,
    h.quadraticLinearFrequency_eq, h.quadraticOmega_eq]

end MatchesDetectorClocks

end Modular.AffineBlochParameters

namespace FixedDetectorMomentCode

variable {eqs vars : ℕ}

/-- The literal compiled `(1,1)` character times a selected affine output
is exactly quadratic moment row `r=1`. -/
theorem jacobiPlusCharacter_mul_gaugedBlochOutput_eq_series
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars)
    (p : AffineBlochParameters) (d : ℂ)
    (hclocks :
      p.MatchesDetectorClocks
        (CanonicalFixedDetectorTrajectory.omegaFrequency
          parameters controller j)
        (CanonicalFixedDetectorTrajectory.numberFrequency
          parameters I controller j))
    (ha : p.a0.im = 0)
    (hω :
      CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j ≠ 0)
    (t : ℝ) :
    let ω :=
      CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j
    let N :=
      CanonicalFixedDetectorTrajectory.numberFrequency
        parameters I controller j
    (p.fourthRootGauge d t * (p.jacobiBlochPath t).T1) *
        characterValue (jacobiPlusExponent I j)
          (CanonicalFixedDetectorTrajectory.clockPath
            parameters controller
            LockedControllerPhaseTrajectory.onePhase t) =
      quadraticMomentSeries
        (p.gaugedBlochCoefficient d) ω (N / ω) p.a0.re 1 t := by
  dsimp only
  rw [characterValue_jacobiPlusExponent_onePhase]
  rw [p.fourthRootGauge_mul_jacobiBlochPath_T1_eq_quadraticMomentSeries
    d ha (hclocks.kappa_ne_zero hω)]
  rw [hclocks.quadraticOmega_eq,
    hclocks.quadraticClockRatio_eq]
  rw [show
      -(CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j +
          CanonicalFixedDetectorTrajectory.numberFrequency
            parameters I controller j) =
        -(CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j) *
          (1 +
            CanonicalFixedDetectorTrajectory.numberFrequency
              parameters I controller j /
            CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j) by
    field_simp [hω]
    ]
  rw [mul_comm]
  exact quadraticMomentSeries_plus_character
    (p.gaugedBlochCoefficient d)
    (CanonicalFixedDetectorTrajectory.omegaFrequency
      parameters controller j)
    (CanonicalFixedDetectorTrajectory.numberFrequency
      parameters I controller j /
      CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j)
    p.a0.re t

/-- The literal compiled `(1,-1)` character times a selected affine output
is exactly quadratic moment row `r=-1`. -/
theorem jacobiMinusCharacter_mul_gaugedBlochOutput_eq_series
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars)
    (p : AffineBlochParameters) (d : ℂ)
    (hclocks :
      p.MatchesDetectorClocks
        (CanonicalFixedDetectorTrajectory.omegaFrequency
          parameters controller j)
        (CanonicalFixedDetectorTrajectory.numberFrequency
          parameters I controller j))
    (ha : p.a0.im = 0)
    (hω :
      CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j ≠ 0)
    (t : ℝ) :
    let ω :=
      CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j
    let N :=
      CanonicalFixedDetectorTrajectory.numberFrequency
        parameters I controller j
    (p.fourthRootGauge d t * (p.jacobiBlochPath t).T1) *
        characterValue (jacobiMinusExponent I j)
          (CanonicalFixedDetectorTrajectory.clockPath
            parameters controller
            LockedControllerPhaseTrajectory.onePhase t) =
      quadraticMomentSeries
        (p.gaugedBlochCoefficient d) ω (N / ω) p.a0.re (-1) t := by
  dsimp only
  rw [characterValue_jacobiMinusExponent_onePhase]
  rw [p.fourthRootGauge_mul_jacobiBlochPath_T1_eq_quadraticMomentSeries
    d ha (hclocks.kappa_ne_zero hω)]
  rw [hclocks.quadraticOmega_eq,
    hclocks.quadraticClockRatio_eq]
  rw [show
      -CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j +
          CanonicalFixedDetectorTrajectory.numberFrequency
            parameters I controller j =
        -(CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j) *
          (1 -
            CanonicalFixedDetectorTrajectory.numberFrequency
              parameters I controller j /
            CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j) by
    field_simp [hω]
    ring]
  rw [mul_comm]
  exact quadraticMomentSeries_minus_character
    (p.gaugedBlochCoefficient d)
    (CanonicalFixedDetectorTrajectory.omegaFrequency
      parameters controller j)
    (CanonicalFixedDetectorTrajectory.numberFrequency
      parameters I controller j /
      CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j)
    p.a0.re t

/-! ### Arbitrary initial controller phases -/

/-- All-state version of the `(1,1)` crosswalk.  The initial value of the
compiled character is absorbed coefficientwise; no phase-origin
normalization is assumed. -/
theorem jacobiPlusCharacter_mul_gaugedBlochOutput_eq_series_phase
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters) (d : ℂ)
    (hclocks :
      p.MatchesDetectorClocks
        (CanonicalFixedDetectorTrajectory.omegaFrequency
          parameters controller j)
        (CanonicalFixedDetectorTrajectory.numberFrequency
          parameters I controller j))
    (ha : p.a0.im = 0)
    (hω :
      CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j ≠ 0)
    (t : ℝ) :
    let ω :=
      CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j
    let N :=
      CanonicalFixedDetectorTrajectory.numberFrequency
        parameters I controller j
    let c :=
      characterValue (jacobiPlusExponent I j)
        (CanonicalFixedDetectorTrajectory.clockPath
          parameters controller phase₀ 0)
    (p.fourthRootGauge d t * (p.jacobiBlochPath t).T1) *
        characterValue (jacobiPlusExponent I j)
          (CanonicalFixedDetectorTrajectory.clockPath
            parameters controller phase₀ t) =
      quadraticMomentSeries
        (fun k ↦ c * p.gaugedBlochCoefficient d k)
        ω (N / ω) p.a0.re 1 t := by
  dsimp only
  rw [characterValue_jacobiPlusExponent_phase]
  rw [show
      -(CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j +
          CanonicalFixedDetectorTrajectory.numberFrequency
            parameters I controller j) =
        -(CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j) *
          (1 +
            CanonicalFixedDetectorTrajectory.numberFrequency
              parameters I controller j /
            CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j) by
    field_simp [hω]]
  let c : ℂ :=
    characterValue (jacobiPlusExponent I j)
      (CanonicalFixedDetectorTrajectory.clockPath
        parameters controller phase₀ 0)
  have hbase :=
    p.fourthRootGauge_mul_jacobiBlochPath_T1_eq_quadraticMomentSeries
      d ha (hclocks.kappa_ne_zero hω) t
  rw [hclocks.quadraticOmega_eq,
    hclocks.quadraticClockRatio_eq] at hbase
  calc
    (p.fourthRootGauge d t * (p.jacobiBlochPath t).T1) *
          (c *
            HGAS.Analysis.realFrequencyExponential
              (-(CanonicalFixedDetectorTrajectory.omegaFrequency
                    parameters controller j) *
                (1 +
                  CanonicalFixedDetectorTrajectory.numberFrequency
                      parameters I controller j /
                    CanonicalFixedDetectorTrajectory.omegaFrequency
                      parameters controller j)) t) =
        c *
          (HGAS.Analysis.realFrequencyExponential
              (-(CanonicalFixedDetectorTrajectory.omegaFrequency
                    parameters controller j) *
                (1 +
                  CanonicalFixedDetectorTrajectory.numberFrequency
                      parameters I controller j /
                    CanonicalFixedDetectorTrajectory.omegaFrequency
                      parameters controller j)) t *
            (p.fourthRootGauge d t *
              (p.jacobiBlochPath t).T1)) := by ring
    _ =
        c *
          quadraticMomentSeries
            (p.gaugedBlochCoefficient d)
            (CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j)
            (CanonicalFixedDetectorTrajectory.numberFrequency
                parameters I controller j /
              CanonicalFixedDetectorTrajectory.omegaFrequency
                parameters controller j)
            p.a0.re 1 t := by
      rw [hbase]
      rw [quadraticMomentSeries_plus_character]
    _ =
        quadraticMomentSeries
          (fun k ↦ c * p.gaugedBlochCoefficient d k)
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j)
          (CanonicalFixedDetectorTrajectory.numberFrequency
              parameters I controller j /
            CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j)
          p.a0.re 1 t :=
      const_mul_quadraticMomentSeries _ _ _ _ _ _ _

/-- All-state version of the `(1,-1)` crosswalk. -/
theorem jacobiMinusCharacter_mul_gaugedBlochOutput_eq_series_phase
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (phase₀ : Fin (clockCount eqs vars) → Circle)
    (j : Fin vars)
    (p : AffineBlochParameters) (d : ℂ)
    (hclocks :
      p.MatchesDetectorClocks
        (CanonicalFixedDetectorTrajectory.omegaFrequency
          parameters controller j)
        (CanonicalFixedDetectorTrajectory.numberFrequency
          parameters I controller j))
    (ha : p.a0.im = 0)
    (hω :
      CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j ≠ 0)
    (t : ℝ) :
    let ω :=
      CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j
    let N :=
      CanonicalFixedDetectorTrajectory.numberFrequency
        parameters I controller j
    let c :=
      characterValue (jacobiMinusExponent I j)
        (CanonicalFixedDetectorTrajectory.clockPath
          parameters controller phase₀ 0)
    (p.fourthRootGauge d t * (p.jacobiBlochPath t).T1) *
        characterValue (jacobiMinusExponent I j)
          (CanonicalFixedDetectorTrajectory.clockPath
            parameters controller phase₀ t) =
      quadraticMomentSeries
        (fun k ↦ c * p.gaugedBlochCoefficient d k)
        ω (N / ω) p.a0.re (-1) t := by
  dsimp only
  rw [characterValue_jacobiMinusExponent_phase]
  rw [show
      -CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j +
          CanonicalFixedDetectorTrajectory.numberFrequency
            parameters I controller j =
        -(CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j) *
          (1 -
            CanonicalFixedDetectorTrajectory.numberFrequency
              parameters I controller j /
            CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j) by
    field_simp [hω]
    ring]
  let c : ℂ :=
    characterValue (jacobiMinusExponent I j)
      (CanonicalFixedDetectorTrajectory.clockPath
        parameters controller phase₀ 0)
  have hbase :=
    p.fourthRootGauge_mul_jacobiBlochPath_T1_eq_quadraticMomentSeries
      d ha (hclocks.kappa_ne_zero hω) t
  rw [hclocks.quadraticOmega_eq,
    hclocks.quadraticClockRatio_eq] at hbase
  calc
    (p.fourthRootGauge d t * (p.jacobiBlochPath t).T1) *
          (c *
            HGAS.Analysis.realFrequencyExponential
              (-(CanonicalFixedDetectorTrajectory.omegaFrequency
                    parameters controller j) *
                (1 -
                  CanonicalFixedDetectorTrajectory.numberFrequency
                      parameters I controller j /
                    CanonicalFixedDetectorTrajectory.omegaFrequency
                      parameters controller j)) t) =
        c *
          (HGAS.Analysis.realFrequencyExponential
              (-(CanonicalFixedDetectorTrajectory.omegaFrequency
                    parameters controller j) *
                (1 -
                  CanonicalFixedDetectorTrajectory.numberFrequency
                      parameters I controller j /
                    CanonicalFixedDetectorTrajectory.omegaFrequency
                      parameters controller j)) t *
            (p.fourthRootGauge d t *
              (p.jacobiBlochPath t).T1)) := by ring
    _ =
        c *
          quadraticMomentSeries
            (p.gaugedBlochCoefficient d)
            (CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j)
            (CanonicalFixedDetectorTrajectory.numberFrequency
                parameters I controller j /
              CanonicalFixedDetectorTrajectory.omegaFrequency
                parameters controller j)
            p.a0.re (-1) t := by
      rw [hbase]
      rw [quadraticMomentSeries_minus_character]
    _ =
        quadraticMomentSeries
          (fun k ↦ c * p.gaugedBlochCoefficient d k)
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j)
          (CanonicalFixedDetectorTrajectory.numberFrequency
              parameters I controller j /
            CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j)
          p.a0.re (-1) t :=
      const_mul_quadraticMomentSeries _ _ _ _ _ _ _

/-! ## Evaluation of the three literal polynomial moment codes -/

/-- Pointwise identification of a structured compiler state with one
gauged affine Bloch output on the aligned controller orbit.

The interface mentions only the two pieces read by the Jacobi moment
codes: the common controller family and the product `G*T₁`.  It is
therefore reusable for a source trajectory obtained by an independent
compactification or time-reparameterization argument. -/
structure MatchesCompiledGaugedBlochAt
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars)
    (p : AffineBlochParameters) (d : ℂ) (t : ℝ)
    (z : FixedDetectorPolynomialCode.State eqs vars) : Prop where
  controllers_eq :
    z.base.base.source.controllers =
      CanonicalFixedDetectorTrajectory.clockPath
        parameters controller
        LockedControllerPhaseTrajectory.onePhase t
  output_eq :
    z.base.base.gauge j *
        (z.base.base.source.linked j).jacobi.T1 =
      p.fourthRootGauge d t * (p.jacobiBlochPath t).T1

/-- Evaluation of the literal mean code is quadratic row `r=0` minus its
target constant. -/
theorem evalPair_jacobiMeanCode_eq_quadraticMomentSeries
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars)
    (p : AffineBlochParameters) (d : ℂ)
    (hclocks :
      p.MatchesDetectorClocks
        (CanonicalFixedDetectorTrajectory.omegaFrequency
          parameters controller j)
        (CanonicalFixedDetectorTrajectory.numberFrequency
          parameters I controller j))
    (ha : p.a0.im = 0)
    (hω :
      CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j ≠ 0)
    (t : ℝ)
    (z : FixedDetectorPolynomialCode.State eqs vars)
    (hmatch :
      MatchesCompiledGaugedBlochAt
        parameters controller j p d t z) :
    evalPair (jacobiMeanCode j)
        (FixedDetectorPolynomialCode.point z) =
      quadraticMomentSeries
          (p.gaugedBlochCoefficient d)
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j)
          (CanonicalFixedDetectorTrajectory.numberFrequency
              parameters I controller j /
            CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j)
          p.a0.re 0 t -
        1 := by
  rw [evalPair_jacobiMeanCode, hmatch.output_eq]
  rw [p.fourthRootGauge_mul_jacobiBlochPath_T1_eq_quadraticMomentSeries
    d ha (hclocks.kappa_ne_zero hω)]
  rw [hclocks.quadraticOmega_eq,
    hclocks.quadraticClockRatio_eq]

/-- Evaluation of the literal `(1,1)` code is quadratic row `r=1` minus
the rational target `1/256`. -/
theorem evalPair_jacobiPlusMeanCode_eq_quadraticMomentSeries
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars)
    (p : AffineBlochParameters) (d : ℂ)
    (hclocks :
      p.MatchesDetectorClocks
        (CanonicalFixedDetectorTrajectory.omegaFrequency
          parameters controller j)
        (CanonicalFixedDetectorTrajectory.numberFrequency
          parameters I controller j))
    (ha : p.a0.im = 0)
    (hω :
      CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j ≠ 0)
    (t : ℝ)
    (z : FixedDetectorPolynomialCode.State eqs vars)
    (hmatch :
      MatchesCompiledGaugedBlochAt
        parameters controller j p d t z) :
    evalPair (jacobiPlusMeanCode I j)
        (FixedDetectorPolynomialCode.point z) =
      quadraticMomentSeries
          (p.gaugedBlochCoefficient d)
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j)
          (CanonicalFixedDetectorTrajectory.numberFrequency
              parameters I controller j /
            CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j)
          p.a0.re 1 t -
        (1 / 256 : ℚ) := by
  rw [evalPair_jacobiPlusMeanCode,
    hmatch.output_eq, hmatch.controllers_eq]
  rw [jacobiPlusCharacter_mul_gaugedBlochOutput_eq_series
    parameters I controller j p d hclocks ha hω t]

/-- Evaluation of the literal `(1,-1)` code is quadratic row `r=-1`
minus the same rational target. -/
theorem evalPair_jacobiMinusMeanCode_eq_quadraticMomentSeries
    (parameters : Fin (clockCount eqs vars) → RationalCode)
    (I : DQLSystem eqs vars)
    (controller :
      Fin (clockCount eqs vars) →
        Controller.ControllerState ℝ)
    (j : Fin vars)
    (p : AffineBlochParameters) (d : ℂ)
    (hclocks :
      p.MatchesDetectorClocks
        (CanonicalFixedDetectorTrajectory.omegaFrequency
          parameters controller j)
        (CanonicalFixedDetectorTrajectory.numberFrequency
          parameters I controller j))
    (ha : p.a0.im = 0)
    (hω :
      CanonicalFixedDetectorTrajectory.omegaFrequency
        parameters controller j ≠ 0)
    (t : ℝ)
    (z : FixedDetectorPolynomialCode.State eqs vars)
    (hmatch :
      MatchesCompiledGaugedBlochAt
        parameters controller j p d t z) :
    evalPair (jacobiMinusMeanCode I j)
        (FixedDetectorPolynomialCode.point z) =
      quadraticMomentSeries
          (p.gaugedBlochCoefficient d)
          (CanonicalFixedDetectorTrajectory.omegaFrequency
            parameters controller j)
          (CanonicalFixedDetectorTrajectory.numberFrequency
              parameters I controller j /
            CanonicalFixedDetectorTrajectory.omegaFrequency
              parameters controller j)
          p.a0.re (-1) t -
        (1 / 256 : ℚ) := by
  rw [evalPair_jacobiMinusMeanCode,
    hmatch.output_eq, hmatch.controllers_eq]
  rw [jacobiMinusCharacter_mul_gaugedBlochOutput_eq_series
    parameters I controller j p d hclocks ha hω t]

end FixedDetectorMomentCode

end

end HGAS
