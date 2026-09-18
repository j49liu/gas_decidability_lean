import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorBidirectionalColumnRecurrence
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorColumnGenericity
import HGAS.Modular.RecurrentLiftExactFrame
import HGAS.Modular.RecurrentLiftExactGammaTwo
import HGAS.Modular.UnaryConstantTimeRescaling
import Mathlib.Tactic

/-!
# Exact standardization of a signed detector column

The private modular frequency of detector column `j` is a nonzero signed
real number `ω_j`, while the modular reconstruction theorem uses the
standard clock `π i`.  The only possible constant time change is

```text
                         a_j = π / ω_j.
```

The ODE rescales algebraically for either sign.  Recurrence requires more
care:

* if `ω_j > 0`, then `a_j > 0` and forward recurrence rescales directly;
* if `ω_j < 0`, then `-a_j > 0`; we first use recurrence of the reversed
  complete column and then rescale by `-a_j`.

Thus no unjustified implication from forward recurrence to backward
recurrence is used.
-/

namespace HGAS.NormalizedCorrectedFixedDetectorColumnStandardization

open HGAS
open HGAS.Modular
open UpperHalfPlane hiding I
open NormalizedCorrectedFixedDetectorTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorBidirectionalValidityOrbit
open NormalizedCorrectedFixedDetectorColumnTrajectory
open NormalizedCorrectedFixedDetectorColumnRecurrence
open NormalizedCorrectedFixedDetectorColumnGenericity
open NormalizedCorrectedFixedDetectorBidirectionalColumnRecurrence
open NormalizedCorrectedFixedDetectorColumnTrajectory.SelectedTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorColumnRecurrence.SelectedTwoSidedValidityOrbit
open NormalizedCorrectedFixedDetectorColumnGenericity.SelectedTwoSidedValidityOrbit
open
  NormalizedCorrectedFixedDetectorBidirectionalColumnRecurrence.SelectedBidirectionalValidityOrbit

noncomputable section

variable {eqs vars : ℕ}
variable
  {u :
    NormalizedCorrectedFixedDetectorCompactSourceCode.CompilerInput
      eqs vars}

/-- Literal real time factor converting the signed detector frequency
`ω_j` to the standard modular frequency `π`. -/
def columnStandardScale
    (O : SelectedTwoSidedValidityOrbit u)
    (j : Fin vars) : ℝ :=
  Real.pi / columnOmega O j

/-- Standardized unary trajectory of column `j`. -/
def standardizedUnaryColumn
    (O : SelectedTwoSidedValidityOrbit u)
    (j : Fin vars)
    (t : ℝ) :
    UnaryModularState ℂ :=
  (linkedColumn O j (columnStandardScale O j * t)).unary

/-- The exact geometric alternative produced by the recurrent generic
unary reconstruction theorem. -/
def HasHorizontalOrExactGammaTwoLift
    (z : ℝ → UnaryModularState ℂ) : Prop :=
  ∃ T : ℝ → ℍ,
    Continuous T ∧
    (∀ t,
      UnaryModularState.lambdaCoordinate (z t) =
        canonicalLambda (T t)) ∧
    ((∃ x y s : ℝ, ∃ hy : 0 < y,
        ∀ t,
          T t = horizontalLine x y s hy t) ∨
      ∃ q : GammaTwoFrameQuotient, ∃ σ : ℝ,
        σ ≠ 0 ∧
        ∀ t : ℝ,
          lambdaModularQuotientMk (T t) =
            gammaTwoFrameBaseProjection
              (scaledGammaTwoHorocycleFlow σ t q))

/-- Frame-valued version of the exact alternative.  It retains the
actual real frame needed for cusp normalization. -/
def HasHorizontalOrExactHorocycleFrameLift
    (z : ℝ → UnaryModularState ℂ) : Prop :=
  ∃ T : ℝ → ℍ,
    Continuous T ∧
    (∀ t,
      UnaryModularState.lambdaCoordinate (z t) =
        canonicalLambda (T t)) ∧
    ((∃ x y s : ℝ, ∃ hy : 0 < y,
        ∀ t,
          T t = horizontalLine x y s hy t) ∨
      ∃ g : RealModularFrame, ∃ σ : ℝ,
        σ ≠ 0 ∧
        ∀ t : ℝ,
          T t =
            realModularFrameBasePoint
              (g * upperUnipotent (σ * t)))

namespace SelectedTwoSidedValidityOrbit

variable (O : SelectedTwoSidedValidityOrbit u)

/-- The standardizing factor is nonzero. -/
theorem columnStandardScale_ne_zero
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
    columnStandardScale O j ≠ 0 :=
  div_ne_zero Real.pi_ne_zero
    (columnOmega_ne_zero O hscale hp j)

/-- The real scale has exactly the required normalization:
`a_j ω_j = π`. -/
theorem columnStandardScale_mul_omega
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
    columnStandardScale O j * columnOmega O j = Real.pi := by
  unfold columnStandardScale
  field_simp [columnOmega_ne_zero O hscale hp j]

/-- Constant rescaling by `π/ω_j` changes the actual signed unary clock
`iω_j` into the literal standard clock `πi`. -/
theorem standardizedUnaryColumn_isScaledTrajectory
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
    IsScaledUnaryModularTrajectory
      modularIndependentVariableClock
      (standardizedUnaryColumn O j) := by
  have htrajectory :=
    (linkedColumn_isScaledTrajectory O hscale hp j).unary.rescale
      (columnStandardScale O j)
  have hclock :
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
  rw [← hclock]
  simpa only [standardizedUnaryColumn] using htrajectory

end SelectedTwoSidedValidityOrbit

namespace SelectedBidirectionalValidityOrbit

variable (O : SelectedBidirectionalValidityOrbit u)

/-- The standardized unary column is forward recurrent, for either sign
of its private frequency. -/
theorem standardizedUnaryColumn_forwardRecurrentAt_nonempty
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
    Nonempty
      (ForwardRecurrentUnaryModularAt
        (standardizedUnaryColumn
          O.toSelectedTwoSidedValidityOrbit j) 0) := by
  let B := O.toSelectedTwoSidedValidityOrbit
  let a := columnStandardScale B j
  have hω : columnOmega B j ≠ 0 :=
    columnOmega_ne_zero B hscale hp j
  rcases lt_or_gt_of_ne hω with hωneg | hωpos
  · have haNeg : a < 0 := by
      exact div_neg_of_pos_of_neg Real.pi_pos hωneg
    have hrec :=
      (unaryColumn_reverse_forwardRecurrentAt O j).rescale_zero
        (neg_pos.mpr haNeg)
    exact ⟨by
      simpa only [standardizedUnaryColumn, a, B, neg_mul,
        neg_neg] using hrec⟩
  · have haPos : 0 < a := by
      exact div_pos Real.pi_pos hωpos
    have hrec :=
      (unaryColumn_forwardRecurrentAt B j).rescale_zero haPos
    exact ⟨by
      simpa only [standardizedUnaryColumn, a, B] using hrec⟩

/-- Chosen common return sequence for the standardized column.  The
choice is harmless: the theorem above proves that such a sequence
exists, and later arguments use only its stated convergence properties. -/
noncomputable def standardizedUnaryColumn_forwardRecurrentAt
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
    ForwardRecurrentUnaryModularAt
      (standardizedUnaryColumn
        O.toSelectedTwoSidedValidityOrbit j) 0 :=
  Classical.choice
    (standardizedUnaryColumn_forwardRecurrentAt_nonempty
      O hscale hp j)

/-- Standardization does not change the initial state, so the three
moment exclusions remain valid. -/
theorem standardizedUnaryColumn_generic
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
    (standardizedUnaryColumn
        O.toSelectedTwoSidedValidityOrbit j 0).A ≠ 0 ∧
      (standardizedUnaryColumn
        O.toSelectedTwoSidedValidityOrbit j 0).C ≠ 0 ∧
      UnaryModularState.B
        (standardizedUnaryColumn
          O.toSelectedTwoSidedValidityOrbit j 0) ≠ 0 := by
  simpa only [standardizedUnaryColumn, mul_zero] using
    linkedColumn_unary_generic
      O.toSelectedTwoSidedValidityOrbit hscale hp j

/-- Every detector column, after its exact signed time normalization,
has a canonical-lambda lift which is either horizontal or the base
projection of a literal nontrivial scaled `Γ(2)` horocycle orbit. -/
theorem standardizedUnaryColumn_hasHorizontalOrExactGammaTwoLift
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
    HasHorizontalOrExactGammaTwoLift
      (standardizedUnaryColumn
        O.toSelectedTwoSidedValidityOrbit j) := by
  have hgeneric :=
    standardizedUnaryColumn_generic O hscale hp j
  exact
    recurrentGenericUnaryTrajectory_exists_horizontal_or_exactGammaTwoHorocycle
      (SelectedTwoSidedValidityOrbit.standardizedUnaryColumn_isScaledTrajectory
        O.toSelectedTwoSidedValidityOrbit hscale hp j)
      hgeneric.1 hgeneric.2.1 hgeneric.2.2
      (standardizedUnaryColumn_forwardRecurrentAt O hscale hp j)

/-- Frame-valued sibling of the quotient theorem.  The nonhorizontal
branch retains literal witnesses `g` and `σ` and the pointwise equality
`T(t) = basePoint (g * u(σt))`. -/
theorem standardizedUnaryColumn_hasHorizontalOrExactHorocycleFrameLift
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
    HasHorizontalOrExactHorocycleFrameLift
      (standardizedUnaryColumn
        O.toSelectedTwoSidedValidityOrbit j) := by
  have hgeneric :=
    standardizedUnaryColumn_generic O hscale hp j
  exact
    recurrentGenericUnaryTrajectory_exists_horizontal_or_exactHorocycleFrame
      (SelectedTwoSidedValidityOrbit.standardizedUnaryColumn_isScaledTrajectory
        O.toSelectedTwoSidedValidityOrbit hscale hp j)
      hgeneric.1 hgeneric.2.1 hgeneric.2.2
      (standardizedUnaryColumn_forwardRecurrentAt O hscale hp j)

/-- Consolidated exact certificate: the exposed scale is nonzero,
normalizes the frequency exactly, gives the standard unary ODE, preserves
recurrence, and reaches the literal `Γ(2)` geometric alternative. -/
theorem standardizedUnaryColumn_exactGammaTwoCertificate
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
    columnStandardScale O.toSelectedTwoSidedValidityOrbit j ≠ 0 ∧
      columnStandardScale O.toSelectedTwoSidedValidityOrbit j *
          columnOmega O.toSelectedTwoSidedValidityOrbit j =
        Real.pi ∧
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock
        (standardizedUnaryColumn
          O.toSelectedTwoSidedValidityOrbit j) ∧
      Nonempty
        (ForwardRecurrentUnaryModularAt
          (standardizedUnaryColumn
            O.toSelectedTwoSidedValidityOrbit j) 0) ∧
      HasHorizontalOrExactGammaTwoLift
        (standardizedUnaryColumn
          O.toSelectedTwoSidedValidityOrbit j) := by
  refine
    ⟨SelectedTwoSidedValidityOrbit.columnStandardScale_ne_zero
        O.toSelectedTwoSidedValidityOrbit hscale hp j,
      SelectedTwoSidedValidityOrbit.columnStandardScale_mul_omega
        O.toSelectedTwoSidedValidityOrbit hscale hp j,
      SelectedTwoSidedValidityOrbit.standardizedUnaryColumn_isScaledTrajectory
        O.toSelectedTwoSidedValidityOrbit hscale hp j,
      standardizedUnaryColumn_forwardRecurrentAt_nonempty
        O hscale hp j,
      standardizedUnaryColumn_hasHorizontalOrExactGammaTwoLift
        O hscale hp j⟩

end SelectedBidirectionalValidityOrbit

end

end HGAS.NormalizedCorrectedFixedDetectorColumnStandardization
