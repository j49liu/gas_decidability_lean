import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorDifferentiableClosedChart
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorFiniteClosedHeightSelection
import HGAS.Modular.FiniteClosedCuspCanonicalRootSeed
import HGAS.Modular.JacobiBlochSelectedContinuation
import Mathlib.Tactic

/-!
# Canonical Jacobi seeds in standardized detector columns

This file is the detector-facing composition of the closed-horocycle
analysis with the reusable canonical-root theorem.

For a selected bidirectionally recurrent validity orbit and a detector
column `j`, write

```text
  aⱼ = π / ωⱼ,
  zⱼ(t) = linkedColumnⱼ(aⱼ t).
```

The modular clock of `zⱼ` is exactly `π i`.  Its elliptic clock is real,
so we name the corresponding real frequency `νⱼ` by

```text
  π νⱼ = aⱼ (ωⱼ + Nⱼ)/2.
```

The automatic closed-chart theorem and the two detector moments select a
unit-speed infinity-cusp chart.  The reusable modular result then gives
an exact canonical coefficient seed at time zero.  Finally the two
Jacobi quadrics and reciprocal residual allow pointwise theta saturation
and global ODE continuation.  Thus the entire standardized Jacobi column
is one regular affine Jacobi--Bloch trajectory.
-/

namespace
  HGAS.NormalizedCorrectedFixedDetectorCanonicalRootSeed

open HGAS
open HGAS.Modular
open UpperHalfPlane hiding I
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorBidirectionalValidityOrbit
open NormalizedCorrectedFixedDetectorColumnTrajectory
open NormalizedCorrectedFixedDetectorColumnRecurrence
open NormalizedCorrectedFixedDetectorColumnStandardization
open NormalizedCorrectedFixedDetectorFiniteClosedBranchSelection
open NormalizedCorrectedFixedDetectorFiniteClosedHeightSelection
open NormalizedCorrectedFixedDetectorDifferentiableClosedChart
open
  NormalizedCorrectedFixedDetectorColumnTrajectory.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorColumnRecurrence.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorColumnStandardization.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorFiniteClosedBranchSelection.SelectedBidirectionalValidityOrbit
open
  NormalizedCorrectedFixedDetectorFiniteClosedHeightSelection.SelectedBidirectionalValidityOrbit
open
  NormalizedCorrectedFixedDetectorDifferentiableClosedChart.SelectedBidirectionalValidityOrbit

noncomputable section

variable {eqs vars : ℕ}
variable
  {u :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      eqs vars}

/-- Real elliptic frequency of a standardized detector column. -/
def standardizedColumnNu
    (O : SelectedTwoSidedValidityOrbit u)
    (j : Fin vars) : ℝ :=
  columnStandardScale O j *
      ((columnOmega O j + columnNumber O j) / 2) /
    Real.pi

namespace SelectedTwoSidedValidityOrbit

variable (O : SelectedTwoSidedValidityOrbit u)

/-- The standardized elliptic clock is literally `π νⱼ`. -/
theorem standardizedColumnKappaZ_eq_pi_mul_nu
    (j : Fin vars) :
    ((columnStandardScale O j : ℝ) : ℂ) *
        columnKappaZ O j =
      (Real.pi : ℂ) * (standardizedColumnNu O j : ℂ) := by
  unfold standardizedColumnNu columnKappaZ
  push_cast
  field_simp [Real.pi_ne_zero]

/-- The standardized modular clock is literally `π i`. -/
theorem standardizedColumnKappaPhi_eq_standard
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (j : Fin vars) :
    ((columnStandardScale O j : ℝ) : ℂ) *
        columnKappaPhi O j =
      modularIndependentVariableClock := by
  unfold columnKappaPhi modularIndependentVariableClock
  calc
    ((columnStandardScale O j : ℝ) : ℂ) *
        (Complex.I * (columnOmega O j : ℂ)) =
        ((columnStandardScale O j *
          columnOmega O j : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    _ = (Real.pi : ℂ) * Complex.I := by
      rw [columnStandardScale_mul_omega O hscale hp j]

/-- Complete standardized linked trajectory in the exact
`(πνⱼ,πi)` clock convention used by affine Bloch continuation. -/
theorem standardizedLinkedColumn_isPiScaledTrajectory
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (j : Fin vars) :
    IsScaledLinkedJacobiTrajectory
      ((Real.pi : ℂ) * (standardizedColumnNu O j : ℂ))
      modularIndependentVariableClock
      (standardizedLinkedColumn O j) := by
  have h :=
    standardizedLinkedColumn_isScaledTrajectory
      O hscale hp j
  rw [
    standardizedColumnKappaZ_eq_pi_mul_nu O j,
    standardizedColumnKappaPhi_eq_standard O hscale hp j]
    at h
  exact h

end SelectedTwoSidedValidityOrbit

open
  HGAS.NormalizedCorrectedFixedDetectorCanonicalRootSeed.SelectedTwoSidedValidityOrbit

namespace SelectedBidirectionalValidityOrbit

variable (O : SelectedBidirectionalValidityOrbit u)

private abbrev B :
    SelectedTwoSidedValidityOrbit u :=
  O.toSelectedTwoSidedValidityOrbit

/-- Every selected standardized detector column has a modulus at time
zero whose four Jacobi coefficient coordinates are exactly the canonical
theta-square roots. -/
theorem standardizedLinkedColumn_exists_canonicalRootSeed
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (j : Fin vars) :
    ∃ τ : ℍ,
      (standardizedLinkedColumn (B O) j 0).jacobi.p2 =
          (canonicalUnaryRoots τ).p2 ∧
      (standardizedLinkedColumn (B O) j 0).jacobi.p3 =
          (canonicalUnaryRoots τ).p3 ∧
      (standardizedLinkedColumn (B O) j 0).jacobi.p4 =
          (canonicalUnaryRoots τ).p4 ∧
      (standardizedLinkedColumn (B O) j 0).jacobi.H =
          (canonicalUnaryRoots τ).H := by
  obtain
      ⟨T, c, selection, _hT, _hlambda, _hTdiff,
        _hcusp, _hamplitude, _hyScale, _hp4Scale⟩ :=
    standardizedUnaryColumn_exists_finiteClosedSelectionData
      O hscale hp j
  have hs :
      closedChartSpeed c = 1 :=
    closedChartSpeed_eq_one_of_selection
      O j T c selection
  have hz :
      IsScaledLinkedJacobiTrajectory
        ((Real.pi : ℂ) *
          (standardizedColumnNu (B O) j : ℂ))
        modularIndependentVariableClock
        (standardizedLinkedColumn (B O) j) :=
    standardizedLinkedColumn_isPiScaledTrajectory
      (B O) hscale hp j
  have hresidual :
      ∀ t (r : LinkedJacobiResidualIndex),
        linkedJacobiResidual r
          (standardizedLinkedColumn (B O) j t) = 0 := by
    intro t r
    exact
      linkedColumn_residual_zero
        (B O) hscale j
        (columnStandardScale (B O) j * t) r
  exact
    exists_canonicalRootSeed_of_finiteClosedSelection
      hz selection hs hresidual

/-- The selected closed chart also has the exact compiler gauge height.
This corollary records that the root seed above comes from the same
canonical-height normalization used in the quantitative bounds. -/
theorem standardizedUnaryColumn_exists_thetaGaugeClosedChart
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (j : Fin vars) :
    ∃ (T : ℝ → ℍ)
        (c :
          ClosedUnaryHorocycleChart
            (standardizedUnaryColumn (B O) j) T),
      Continuous T ∧
      (∀ t,
        UnaryModularState.lambdaCoordinate
            (standardizedUnaryColumn (B O) j t) =
          canonicalLambda (T t)) ∧
      (∀ t, ∃ w : ℂ,
        HasDerivAt (fun s : ℝ ↦ (T s : ℂ)) w t) ∧
      closedChartHeight c = thetaGaugeHeight := by
  obtain
      ⟨T, c, _selection, hT, hlambda, hTdiff,
        _hcusp, _hamplitude, _hyScale, _hp4Scale⟩ :=
    standardizedUnaryColumn_exists_finiteClosedSelectionData
      O hscale hp j
  refine ⟨T, c, hT, hlambda, hTdiff, ?_⟩
  exact
    standardizedFiniteClosedBranch_height_eq_thetaGaugeHeight
      O hscale hp j T c hlambda hTdiff

/-- **Affine Bloch classification of a standardized detector column.**

All geometric choices are discharged internally.  The result returns a
globally regular affine Bloch parameterization of the full ten-coordinate
Jacobi block, with its literal real detector frequency `νⱼ` and unit
modular speed. -/
theorem standardizedJacobiColumn_exists_affineBlochParameters
    (hscale :
      0 <
        ((NormalizedCorrectedFixedDetectorCompactSourceCode.accumulatorScale
          u).decode : ℝ))
    (hp :
      ∀ i,
        (1 : ℝ) <
          (RationalCode.decode
            (NormalizedCorrectedFixedDetectorCompactSourceCode.parameters
              u i) : ℝ))
    (j : Fin vars) :
    ∃ (τ : ℍ) (p : AffineBlochParameters),
      p.nu = standardizedColumnNu (B O) j ∧
      p.kappa = 1 ∧
      p.tau 0 = τ ∧
      p.w 0 = 0 ∧
      (∀ t,
        jacobiTheta1 (p.xi t) (p.tau t : ℂ) ≠ 0) ∧
      (fun t ↦
        (standardizedLinkedColumn (B O) j t).jacobi) =
          p.jacobiBlochPath := by
  let z : ℝ → JacobiState ℂ :=
    fun t ↦
      (standardizedLinkedColumn (B O) j t).jacobi
  have hzLinked :=
    standardizedLinkedColumn_isPiScaledTrajectory
      (B O) hscale hp j
  have hz :
      IsScaledJacobiTrajectory
        ((Real.pi : ℂ) *
          (standardizedColumnNu (B O) j : ℂ))
        ((Real.pi : ℂ) * Complex.I * ((1 : ℝ) : ℂ))
        z := by
    simpa only [
      z, modularIndependentVariableClock,
      Complex.ofReal_one, mul_one] using
      hzLinked.jacobi
  have hresidual :
      ∀ t (r : LinkedJacobiResidualIndex),
        linkedJacobiResidual r
          (standardizedLinkedColumn (B O) j t) = 0 := by
    intro t r
    exact
      linkedColumn_residual_zero
        (B O) hscale j
        (columnStandardScale (B O) j * t) r
  obtain ⟨τ, hp2, hp3, hp4, hH⟩ :=
    standardizedLinkedColumn_exists_canonicalRootSeed
      O hscale hp j
  have hR1 :
      JacobiState.residualR1 (z 0) = 0 := by
    simpa only [linkedJacobiResidual, z] using
      hresidual 0 .thetaQuadricOne
  have hR2 :
      JacobiState.residualR2 (z 0) = 0 := by
    simpa only [linkedJacobiResidual, z] using
      hresidual 0 .thetaQuadricTwo
  have hreciprocal :
      ∀ t, (z t).U * (z t).T1 = 1 := by
    intro t
    have h :=
      hresidual t .reciprocalChart
    change
      JacobiState.residualRU (z t) = 0 at h
    exact sub_eq_zero.mp h
  obtain
      ⟨p, hpnu, hpkappa, hptau, hpw,
        hpregular, hpath⟩ :=
    exists_affineBlochParameters_eq_of_canonical_residual_at
      τ 0 (standardizedColumnNu (B O) j) 1 0
      hz hp2 hp3 hp4 hH hR1 hR2 hreciprocal
  exact
    ⟨τ, p, hpnu, hpkappa, hptau, hpw,
      hpregular, hpath⟩

end SelectedBidirectionalValidityOrbit

end

end
  HGAS.NormalizedCorrectedFixedDetectorCanonicalRootSeed
