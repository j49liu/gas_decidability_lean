import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Constant-term extraction on a finite torus

The arithmetic detector is ultimately integrated over a finite product of
unit circles.  This module isolates the Fourier fact used there.

For an exponent vector `n : d → ℤ`, `UnitAddTorus.mFourier n` is the
character

```
x ↦ ∏ i, exp(2π i nᵢ xᵢ).
```

Normalized Haar integration gives one for the zero exponent and zero for
every other exponent.  We prove the same extraction formula first for a
single monomial, then for an arbitrary absolutely summable family of
monomials.  The latter theorem justifies termwise Haar integration whenever
the coefficient norms are summable.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators BoundedContinuousFunction ComplexConjugate ENNReal

namespace HGAS.Analysis

/-! We use the same probability normalization as
`Mathlib.Analysis.Fourier.AddCircleMulti`. -/

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

/-- The integral of one circle character is its constant coefficient. -/
theorem integral_fourier_unitAddCircle (n : ℤ) :
    (∫ x : UnitAddCircle, fourier n x) =
      if n = 0 then 1 else 0 := by
  have horth :=
    (orthonormal_iff_ite.mp
      (@orthonormal_fourier 1 (Fact.mk zero_lt_one)))
      0 n
  simpa only [ContinuousMap.inner_toLp, fourier_zero,
    ContinuousMap.one_apply, RCLike.inner_apply, map_one,
    one_mul, mul_one, Int.reduceNeg, neg_zero, eq_comm] using horth

/-- Multivariate character orthogonality: normalized Haar integration keeps
exactly the zero exponent vector. -/
theorem integral_mFourier (n : d → ℤ) :
    (∫ x : UnitAddTorus d, UnitAddTorus.mFourier n x) =
      if n = 0 then 1 else 0 := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [UnitAddTorus.mFourier_zero]
  · rw [if_neg hn]
    rw [UnitAddTorus.mFourier, ContinuousMap.coe_mk,
      MeasureTheory.integral_fintype_prod_volume_eq_prod]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hn
    have hni : n i ≠ 0 := by
      simpa using hi
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [integral_fourier_unitAddCircle]
    exact if_neg hni

/-- One scalar-weighted character integrates to its scalar coefficient
precisely in degree zero. -/
theorem integral_const_mul_mFourier
    (c : ℂ) (n : d → ℤ) :
    (∫ x : UnitAddTorus d,
      c * UnitAddTorus.mFourier n x) =
        if n = 0 then c else 0 := by
  rw [integral_const_mul, integral_mFourier]
  split_ifs <;> simp_all

/-- A scalar-weighted torus character. -/
def torusSeriesTerm {ι : Type*}
    (coefficient : ι → ℂ) (exponent : ι → d → ℤ)
    (i : ι) (x : UnitAddTorus d) : ℂ :=
  coefficient i * UnitAddTorus.mFourier (exponent i) x

/-- Pointwise norm of a weighted torus character. -/
theorem norm_torusSeriesTerm {ι : Type*}
    (coefficient : ι → ℂ) (exponent : ι → d → ℤ)
    (i : ι) (x : UnitAddTorus d) :
    ‖torusSeriesTerm coefficient exponent i x‖ =
      ‖coefficient i‖ := by
  simp only [torusSeriesTerm, norm_mul, UnitAddTorus.mFourier,
    ContinuousMap.coe_mk, norm_prod, fourier_apply,
    Circle.norm_coe, Finset.prod_const_one, mul_one]

/-- Every weighted character is integrable on the probability torus. -/
theorem integrable_torusSeriesTerm {ι : Type*}
    (coefficient : ι → ℂ) (exponent : ι → d → ℤ)
    (i : ι) :
    Integrable (torusSeriesTerm coefficient exponent i)
      (volume : Measure (UnitAddTorus d)) := by
  let f : UnitAddTorus d →ᵇ ℂ :=
    BoundedContinuousFunction.mkOfCompact
      ⟨torusSeriesTerm coefficient exponent i, by
        apply Continuous.mul continuous_const
        exact (UnitAddTorus.mFourier (exponent i)).continuous⟩
  exact BoundedContinuousFunction.integrable
    (volume : Measure (UnitAddTorus d)) f

/-- The integral of the norm of a weighted character is its coefficient
norm. -/
theorem integral_norm_torusSeriesTerm {ι : Type*}
    (coefficient : ι → ℂ) (exponent : ι → d → ℤ)
    (i : ι) :
    (∫ x : UnitAddTorus d,
      ‖torusSeriesTerm coefficient exponent i x‖) =
        ‖coefficient i‖ := by
  simp only [norm_torusSeriesTerm, integral_const, probReal_univ,
    one_smul]

/-- Absolute convergence permits termwise Haar integration, and normalized
Haar integration extracts exactly the zero-exponent subseries. -/
theorem integral_tsum_torusSeriesTerm_eq_constantTerms
    {ι : Type*} [Countable ι]
    (coefficient : ι → ℂ) (exponent : ι → d → ℤ)
    (hsummable : Summable fun i ↦ ‖coefficient i‖) :
    (∫ x : UnitAddTorus d,
      ∑' i, torusSeriesTerm coefficient exponent i x) =
        ∑' i, if exponent i = 0 then coefficient i else 0 := by
  have hintegrable :
      ∀ i, Integrable (torusSeriesTerm coefficient exponent i)
        (volume : Measure (UnitAddTorus d)) :=
    integrable_torusSeriesTerm coefficient exponent
  have hintegralNorm :
      Summable fun i ↦
        ∫ x : UnitAddTorus d,
          ‖torusSeriesTerm coefficient exponent i x‖ := by
    simpa only [integral_norm_torusSeriesTerm] using hsummable
  rw [← integral_tsum_of_summable_integral_norm
    hintegrable hintegralNorm]
  apply tsum_congr
  intro i
  exact integral_const_mul_mFourier
    (coefficient i) (exponent i)

end HGAS.Analysis
