import HGAS.Analysis.LatticeSummability
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Tactic

/-!
# The Fourier series of the Poisson kernel

This file isolates the elementary one-dimensional identity behind the
Poisson factors in the arithmetic detector.  If `0 ≤ η < 1` and `w` lies
on the complex unit circle, then

```text
             ∑       η^|s| w^s
           s ∈ ℤ

                      1 - η²
        =  --------------------------------- .
           (1 - η w) (1 - η w⁻¹)
```

The proof is deliberately split into reusable pieces.  Absolute convergence
is a direct comparison with the two-sided real geometric series.  The sum is
then partitioned into the nonnegative indices `0, 1, ...` and the negative
indices `-1, -2, ...`; both pieces are ordinary geometric series.

The final lemmas connect the scalar identity to multivariate Fourier
characters on `UnitAddTorus`.  They let downstream detector modules use the
identity without reopening any convergence or geometric-series arguments.
-/

noncomputable section

open scoped BigOperators

namespace HGAS.Analysis

/-- The `s`-th Fourier term of the Poisson kernel with radial parameter
`η` and unit-circle coordinate `w`. -/
def poissonKernelFourierTerm (η : ℝ) (w : ℂ) (s : ℤ) : ℂ :=
  ((η ^ s.natAbs : ℝ) : ℂ) * w ^ s

/-- On the unit circle, the norm of a Poisson Fourier term is exactly its
two-sided geometric weight. -/
theorem norm_poissonKernelFourierTerm
    {η : ℝ} (hη0 : 0 ≤ η) {w : ℂ} (hw : ‖w‖ = 1) (s : ℤ) :
    ‖poissonKernelFourierTerm η w s‖ = η ^ s.natAbs := by
  simp [poissonKernelFourierTerm, norm_zpow, hw,
    abs_of_nonneg hη0]

/-- Absolute summability of the complex Poisson Fourier series.  We state
this in the norm-valued form used by later termwise-integration arguments. -/
theorem summable_norm_poissonKernelFourierTerm
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    {w : ℂ} (hw : ‖w‖ = 1) :
    Summable (fun s : ℤ ↦ ‖poissonKernelFourierTerm η w s‖) := by
  simpa only [norm_poissonKernelFourierTerm hη0 hw,
    geometricIntWeight] using
      (summable_geometricIntWeight hη0 hη1)

/-- Absolute summability implies summability of the complex-valued series. -/
theorem summable_poissonKernelFourierTerm
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    {w : ℂ} (hw : ‖w‖ = 1) :
    Summable (poissonKernelFourierTerm η w) :=
  (summable_norm_poissonKernelFourierTerm hη0 hη1 hw).of_norm

/-- The nonnegative half of the two-sided series is the geometric series
with ratio `η w`. -/
theorem poissonKernelFourierTerm_ofNat
    (η : ℝ) (w : ℂ) (n : ℕ) :
    poissonKernelFourierTerm η w (n : ℤ) =
      (((η : ℂ) * w) ^ n) := by
  simp [poissonKernelFourierTerm, mul_pow]

/-- The negative half, enumerated as `-1, -2, ...`, is the positive-degree
tail of the geometric series with ratio `η w⁻¹`. -/
theorem poissonKernelFourierTerm_negSucc
    (η : ℝ) (w : ℂ) (n : ℕ) :
    poissonKernelFourierTerm η w (-(n + 1 : ℤ)) =
      (((η : ℂ) * w⁻¹) ^ (n + 1)) := by
  have hs : -(n + 1 : ℤ) = Int.negSucc n := by
    omega
  rw [hs]
  simp [poissonKernelFourierTerm, mul_pow]

/-- The complete two-sided Fourier identity for the Poisson kernel. -/
theorem tsum_poissonKernelFourierTerm
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    {w : ℂ} (hw : ‖w‖ = 1) :
    ∑' s : ℤ, poissonKernelFourierTerm η w s =
      ((1 - η ^ 2 : ℝ) : ℂ) /
        ((1 - (η : ℂ) * w) * (1 - (η : ℂ) * w⁻¹)) := by
  let a : ℂ := (η : ℂ) * w
  let b : ℂ := (η : ℂ) * w⁻¹
  have hηnorm : ‖(η : ℂ)‖ = η := by
    simp [abs_of_nonneg hη0]
  have haNorm : ‖a‖ < 1 := by
    simp only [a, norm_mul, hηnorm, hw, mul_one]
    exact hη1
  have hbNorm : ‖b‖ < 1 := by
    simp only [b, norm_mul, hηnorm, norm_inv, hw, inv_one, mul_one]
    exact hη1
  have hpos :
      Summable (fun n : ℕ ↦ poissonKernelFourierTerm η w (n : ℤ)) := by
    simpa only [poissonKernelFourierTerm_ofNat, a] using
      (summable_geometric_of_norm_lt_one haNorm)
  have hneg :
      Summable
        (fun n : ℕ ↦ poissonKernelFourierTerm η w (-(n + 1 : ℤ))) := by
    have hbase : Summable (fun n : ℕ ↦ b ^ n) :=
      summable_geometric_of_norm_lt_one hbNorm
    have hscaled : Summable (fun n : ℕ ↦ b * b ^ n) :=
      hbase.mul_left b
    convert hscaled using 1
    funext n
    simp only [poissonKernelFourierTerm_negSucc, b, pow_succ']
  have hposSum :
      ∑' n : ℕ, poissonKernelFourierTerm η w (n : ℤ) =
        (1 - a)⁻¹ := by
    calc
      ∑' n : ℕ, poissonKernelFourierTerm η w (n : ℤ) =
          ∑' n : ℕ, a ^ n := by
            apply tsum_congr
            intro n
            simp only [poissonKernelFourierTerm_ofNat, a]
      _ = (1 - a)⁻¹ := tsum_geometric_of_norm_lt_one haNorm
  have hnegSum :
      ∑' n : ℕ, poissonKernelFourierTerm η w (-(n + 1 : ℤ)) =
        b * (1 - b)⁻¹ := by
    calc
      ∑' n : ℕ, poissonKernelFourierTerm η w (-(n + 1 : ℤ)) =
          ∑' n : ℕ, b * b ^ n := by
            apply tsum_congr
            intro n
            simp only [poissonKernelFourierTerm_negSucc, b, pow_succ']
      _ = b * ∑' n : ℕ, b ^ n := tsum_mul_left
      _ = b * (1 - b)⁻¹ := by
        rw [tsum_geometric_of_norm_lt_one hbNorm]
  have hw0 : w ≠ 0 := by
    intro hwz
    subst w
    simp at hw
  have ha1 : a ≠ 1 := by
    intro ha
    have hnorm := congrArg norm ha
    rw [norm_one] at hnorm
    linarith
  have hb1 : b ≠ 1 := by
    intro hb
    have hnorm := congrArg norm hb
    rw [norm_one] at hnorm
    linarith
  have hA : 1 - a ≠ 0 := sub_ne_zero.mpr ha1.symm
  have hB : 1 - b ≠ 0 := sub_ne_zero.mpr hb1.symm
  have hab : a * b = ((η ^ 2 : ℝ) : ℂ) := by
    dsimp only [a, b]
    field_simp [hw0]
    simp [pow_two]
  have halgebra :
      (1 - a)⁻¹ + b * (1 - b)⁻¹ =
        (1 - a * b) / ((1 - a) * (1 - b)) := by
    field_simp [hA, hB]
    ring
  rw [tsum_of_nat_of_neg_add_one hpos hneg, hposSum, hnegSum]
  rw [halgebra, hab]
  push_cast
  rfl

/-! ## Interface with torus characters -/

variable {d : Type*} [Fintype d]

/-- Multiplying the integer frequency of a circle character by `s`
raises the character value to the integer power `s`. -/
theorem fourier_int_mul
    (s n : ℤ) (x : UnitAddCircle) :
    fourier (s * n) x = (fourier n x) ^ s := by
  rw [fourier_apply, mul_zsmul, AddCircle.toCircle_zsmul]
  rfl

/-- Multivariate version of `fourier_int_mul`.  This is the algebraic bridge
used by factorized detector Fourier terms: scaling every exponent by `s`
raises the whole torus character to the power `s`. -/
theorem mFourier_int_mul
    (s : ℤ) (n : d → ℤ) (x : UnitAddTorus d) :
    UnitAddTorus.mFourier (fun i ↦ s * n i) x =
      (UnitAddTorus.mFourier n x) ^ s := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    fourier_int_mul]
  exact Finset.prod_zpow (fun i ↦ fourier (n i) (x i))
    Finset.univ s

/-- Every multivariate Fourier character takes values on the complex unit
circle. -/
theorem norm_mFourier_apply
    (n : d → ℤ) (x : UnitAddTorus d) :
    ‖UnitAddTorus.mFourier n x‖ = 1 := by
  simp [UnitAddTorus.mFourier, fourier_apply]

/-- A Poisson Fourier term written in the exponent-vector form occurring in
torus Fourier expansions. -/
def torusPoissonFourierTerm
    (η : ℝ) (n : d → ℤ) (x : UnitAddTorus d) (s : ℤ) : ℂ :=
  ((η ^ s.natAbs : ℝ) : ℂ) *
    UnitAddTorus.mFourier (fun i ↦ s * n i) x

/-- The exponent-vector term is exactly the scalar Poisson term evaluated
at the base character `mFourier n x`. -/
theorem torusPoissonFourierTerm_eq
    (η : ℝ) (n : d → ℤ) (x : UnitAddTorus d) (s : ℤ) :
    torusPoissonFourierTerm η n x s =
      poissonKernelFourierTerm η (UnitAddTorus.mFourier n x) s := by
  rw [torusPoissonFourierTerm, poissonKernelFourierTerm,
    mFourier_int_mul]

/-- Absolute summability in the exponent-vector presentation. -/
theorem summable_norm_torusPoissonFourierTerm
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    (n : d → ℤ) (x : UnitAddTorus d) :
    Summable (fun s : ℤ ↦ ‖torusPoissonFourierTerm η n x s‖) := by
  simpa only [torusPoissonFourierTerm_eq] using
    (summable_norm_poissonKernelFourierTerm hη0 hη1
      (norm_mFourier_apply n x))

/-- The Poisson identity in the exact exponent-vector presentation needed
by multivariate torus Fourier series. -/
theorem tsum_torusPoissonFourierTerm
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    (n : d → ℤ) (x : UnitAddTorus d) :
    ∑' s : ℤ, torusPoissonFourierTerm η n x s =
      ((1 - η ^ 2 : ℝ) : ℂ) /
        ((1 - (η : ℂ) * UnitAddTorus.mFourier n x) *
          (1 - (η : ℂ) * (UnitAddTorus.mFourier n x)⁻¹)) := by
  simpa only [torusPoissonFourierTerm_eq] using
    (tsum_poissonKernelFourierTerm hη0 hη1
      (norm_mFourier_apply n x))

end HGAS.Analysis
