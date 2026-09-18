import HGAS.Analysis.FiniteProductSeries
import HGAS.Arithmetic.DetectorCharacterCode
import Mathlib.Tactic

/-!
# Factorized and expanded forms of the arithmetic detector

The polynomial realization of the detector is naturally a product of one
theta series and one Poisson series for every arithmetic variable.  The
constant-term calculation, on the other hand, is most transparent after
expanding that product into one series indexed by two integer vectors.

This module proves that the two forms are literally equal.  It is the
analytic crosswalk between the human formula

```text
  χ_rhs · ∏ j (Θ_j · P_j)
```

and `expandedDetector`.  All rearrangements are justified by absolute
summability.
-/

noncomputable section

open scoped BigOperators

namespace HGAS

variable {eqs vars : ℕ}

namespace DetectorFactorizedFourier

/-- Character exponent of the `n`th term in theta factor `j`. -/
def thetaCoordinateExponent
    (I : DQLSystem eqs vars) (j : Fin vars) (n : ℤ) :
    DetectorPhase eqs vars → ℤ :=
  fun phase ↦
    n ^ 2 * DetectorCharacterCode.privateCharacter j phase +
      n * DetectorCharacterCode.linearCharacter I j phase

/-- Character exponent of the `s`th term in Poisson factor `j`. -/
def poissonCoordinateExponent
    (I : DQLSystem eqs vars) (j : Fin vars) (s : ℤ) :
    DetectorPhase eqs vars → ℤ :=
  fun phase ↦
    s * DetectorCharacterCode.poissonArgumentCharacter I j phase

/-- One Gaussian theta term on the detector torus. -/
def thetaTerm
    (lambda : ℝ) (I : DQLSystem eqs vars) (j : Fin vars)
    (n : ℤ) (phase : UnitAddTorus (DetectorPhase eqs vars)) : ℂ :=
  ((lambda ^ (n.natAbs ^ 2) : ℝ) : ℂ) *
    UnitAddTorus.mFourier
      (thetaCoordinateExponent I j n) phase

/-- One two-sided geometric Poisson term on the detector torus. -/
def poissonTerm
    (eta : ℝ) (I : DQLSystem eqs vars) (j : Fin vars)
    (s : ℤ) (phase : UnitAddTorus (DetectorPhase eqs vars)) : ℂ :=
  ((eta ^ s.natAbs : ℝ) : ℂ) *
    UnitAddTorus.mFourier
      (poissonCoordinateExponent I j s) phase

/-- The product presentation used by the analytic and polynomial
detectors. -/
def factorizedDetector
    (lambda eta : ℝ) (I : DQLSystem eqs vars)
    (phase : UnitAddTorus (DetectorPhase eqs vars)) : ℂ :=
  UnitAddTorus.mFourier (DetectorCharacterCode.rhsCharacter I) phase *
    (∏ j : Fin vars, ∑' n : ℤ, thetaTerm lambda I j n phase) *
    (∏ j : Fin vars, ∑' s : ℤ, poissonTerm eta I j s phase)

/-! ## Absolute convergence -/

theorem summable_norm_thetaTerm
    {lambda : ℝ} (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (I : DQLSystem eqs vars) (j : Fin vars)
    (phase : UnitAddTorus (DetectorPhase eqs vars)) :
    Summable (fun n : ℤ ↦ ‖thetaTerm lambda I j n phase‖) := by
  apply
    (Analysis.summable_gaussianIntWeight
      hlambda0 hlambda1).congr
  intro n
  simp only [thetaTerm, norm_mul, Complex.norm_real,
    UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
    fourier_apply, Circle.norm_coe, Finset.prod_const_one, mul_one,
    Analysis.gaussianIntWeight]
  exact (Real.norm_of_nonneg (pow_nonneg hlambda0 _)).symm

theorem summable_norm_poissonTerm
    {eta : ℝ} (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (I : DQLSystem eqs vars) (j : Fin vars)
    (phase : UnitAddTorus (DetectorPhase eqs vars)) :
    Summable (fun s : ℤ ↦ ‖poissonTerm eta I j s phase‖) := by
  apply
    (Analysis.summable_geometricIntWeight
      heta0 heta1).congr
  intro s
  simp only [poissonTerm, norm_mul, Complex.norm_real,
    UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
    fourier_apply, Circle.norm_coe, Finset.prod_const_one, mul_one,
    Analysis.geometricIntWeight]
  exact (Real.norm_of_nonneg (pow_nonneg heta0 _)).symm

/-! ## Character bookkeeping -/

private theorem mFourier_finset_sum
    {ι : Type*} (s : Finset ι)
    (a : ι → DetectorPhase eqs vars → ℤ)
    (phase : UnitAddTorus (DetectorPhase eqs vars)) :
    UnitAddTorus.mFourier (∑ i ∈ s, a i) phase =
      ∏ i ∈ s, UnitAddTorus.mFourier (a i) phase := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [UnitAddTorus.mFourier_zero]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi,
        UnitAddTorus.mFourier_add, ih]

private theorem mFourier_univ_sum
    (a : Fin vars → DetectorPhase eqs vars → ℤ)
    (phase : UnitAddTorus (DetectorPhase eqs vars)) :
    UnitAddTorus.mFourier (∑ j : Fin vars, a j) phase =
      ∏ j : Fin vars, UnitAddTorus.mFourier (a j) phase := by
  simpa only [Finset.sum_attach, Finset.prod_attach] using
    (mFourier_finset_sum (Finset.univ : Finset (Fin vars))
      a phase)

theorem expandedTermCharacter_coordinate_form
    (I : DQLSystem eqs vars)
    (x s : Fin vars → ℤ) :
    DetectorCharacterCode.expandedTermCharacter I x s =
      DetectorCharacterCode.rhsCharacter I +
        ∑ j : Fin vars,
          (thetaCoordinateExponent I j (x j) +
            poissonCoordinateExponent I j (s j)) := by
  funext phase
  simp only [DetectorCharacterCode.expandedTermCharacter,
    DetectorCharacterCode.thetaTermCharacter,
    thetaCoordinateExponent, poissonCoordinateExponent,
    Pi.add_apply, Finset.sum_apply]

theorem detector_mFourier_factorization
    (I : DQLSystem eqs vars)
    (x s : Fin vars → ℤ)
    (phase : UnitAddTorus (DetectorPhase eqs vars)) :
    UnitAddTorus.mFourier
          (DetectorCharacterCode.rhsCharacter I) phase *
        (∏ j : Fin vars,
          UnitAddTorus.mFourier
            (thetaCoordinateExponent I j (x j)) phase) *
        (∏ j : Fin vars,
          UnitAddTorus.mFourier
            (poissonCoordinateExponent I j (s j)) phase) =
      UnitAddTorus.mFourier (detectorExponent I (x, s)) phase := by
  rw [mul_assoc]
  rw [← Finset.prod_mul_distrib]
  simp_rw [← UnitAddTorus.mFourier_add]
  rw [← mFourier_univ_sum
    (fun j ↦
      thetaCoordinateExponent I j (x j) +
        poissonCoordinateExponent I j (s j)) phase]
  rw [← UnitAddTorus.mFourier_add]
  rw [←
    DetectorCharacterCode.expandedTermCharacter_eq_detectorExponent
      I x s]
  rw [← expandedTermCharacter_coordinate_form I x s]

/-! ## Equality of the two detector presentations -/

/-- **Product-to-expanded-series theorem.**

For parameters in `[0,1)`, the factorized theta--Poisson expression is
exactly the already audited expanded detector at every torus point. -/
theorem factorizedDetector_eq_expandedDetector
    {lambda eta : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (I : DQLSystem eqs vars)
    (phase : UnitAddTorus (DetectorPhase eqs vars)) :
    factorizedDetector lambda eta I phase =
      expandedDetector lambda eta I phase := by
  let theta :
      Fin vars → ℤ → ℂ :=
    fun j n ↦ thetaTerm lambda I j n phase
  let poisson :
      Fin vars → ℤ → ℂ :=
    fun j s ↦ poissonTerm eta I j s phase
  have htheta :
      ∀ j, Summable (fun n ↦ ‖theta j n‖) := by
    intro j
    exact summable_norm_thetaTerm
      hlambda0 hlambda1 I j phase
  have hpoisson :
      ∀ j, Summable (fun s ↦ ‖poisson j s‖) := by
    intro j
    exact summable_norm_poissonTerm
      heta0 heta1 I j phase
  have hthetaVector :
      Summable
        (fun x : Fin vars → ℤ ↦
          ‖∏ j, theta j (x j)‖) :=
    Analysis.summable_norm_finIntegerProductComplex theta htheta
  have hpoissonVector :
      Summable
        (fun s : Fin vars → ℤ ↦
          ‖∏ j, poisson j (s j)‖) :=
    Analysis.summable_norm_finIntegerProductComplex poisson hpoisson
  unfold factorizedDetector
  change
    UnitAddTorus.mFourier
          (DetectorCharacterCode.rhsCharacter I) phase *
        (∏ j : Fin vars, ∑' n : ℤ, theta j n) *
        (∏ j : Fin vars, ∑' s : ℤ, poisson j s) =
      expandedDetector lambda eta I phase
  rw [Analysis.prod_tsum_eq_tsum_finIntegerProduct theta htheta]
  rw [Analysis.prod_tsum_eq_tsum_finIntegerProduct poisson hpoisson]
  rw [mul_assoc]
  rw [tsum_mul_tsum_of_summable_norm
    hthetaVector hpoissonVector]
  rw [← tsum_mul_left]
  unfold expandedDetector
  apply tsum_congr
  intro p
  change
    UnitAddTorus.mFourier
          (DetectorCharacterCode.rhsCharacter I) phase *
        ((∏ j : Fin vars, theta j (p.1 j)) *
          ∏ j : Fin vars, poisson j (p.2 j)) =
      Analysis.torusSeriesTerm
        (detectorCoefficient lambda eta)
        (detectorExponent I) p phase
  rw [show
      (∏ j : Fin vars, theta j (p.1 j)) =
        ((lambda ^ integerVectorEnergy p.1 : ℝ) : ℂ) *
          ∏ j : Fin vars,
            UnitAddTorus.mFourier
              (thetaCoordinateExponent I j (p.1 j)) phase by
    simp only [theta, thetaTerm, Finset.prod_mul_distrib,
      ← Complex.ofReal_prod]
    have hcoefficient :
        (∏ i : Fin vars,
            lambda ^ (p.1 i).natAbs ^ 2) =
          lambda ^ integerVectorEnergy p.1 := by
      simpa only [Analysis.gaussianIntWeight] using
        gaussianProduct_eq_energyPower lambda p.1
    rw [hcoefficient]]
  rw [show
      (∏ j : Fin vars, poisson j (p.2 j)) =
        ((eta ^ poissonEnergy p.2 : ℝ) : ℂ) *
          ∏ j : Fin vars,
            UnitAddTorus.mFourier
              (poissonCoordinateExponent I j (p.2 j)) phase by
    simp only [poisson, poissonTerm, Finset.prod_mul_distrib,
      ← Complex.ofReal_prod]
    have hcoefficient :
        (∏ i : Fin vars,
            eta ^ (p.2 i).natAbs) =
          eta ^ poissonEnergy p.2 := by
      simpa only [Analysis.geometricIntWeight] using
        geometricProduct_eq_poissonPower eta p.2
    rw [hcoefficient]]
  unfold Analysis.torusSeriesTerm detectorCoefficient
  rw [← detector_mFourier_factorization I p.1 p.2 phase]
  push_cast
  ring

end DetectorFactorizedFourier

end HGAS
