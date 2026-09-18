import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic

/-!
# From a zero nonnegative integral to pointwise vanishing on the support

Suppose that a continuous nonnegative observable `f` has integral zero
against a measure `μ`.  Nonnegativity first gives `f = 0` almost
everywhere.  That conclusion alone does **not** mention every point of the
topological support.  The missing observation is that the zero set of a
continuous function is closed.  Since it is also conull, the support of
`μ` is contained in it.

The second half of this file packages the form used by the modular--Jacobi
selector.  For finitely many continuous complex residuals `r i`, set

```
                    V(x) = ∑ i, |r i x|².
```

Here `|z|²` is represented by `Complex.normSq z`, so `V` is a real
polynomial whenever the residuals are complex polynomials in real
coordinates.  If `∫ V ∂μ = 0`, then every residual vanishes at every point
of `μ.support`.

No invariance hypothesis is needed in this module.  In applications,
invariance is what proves that the displayed integral is zero.
-/

namespace HGAS.Dynamics

open Filter MeasureTheory Set
open scoped BigOperators

noncomputable section

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  {μ : Measure X}

/-- A continuous nonnegative real observable with zero integral vanishes
at every point of the topological support of the measure. -/
theorem eq_zero_on_support_of_continuous_nonneg_of_integral_eq_zero
    {f : X → ℝ}
    (hf : Continuous f)
    (hnonneg : ∀ x, 0 ≤ f x)
    (hfi : Integrable f μ)
    (hint : ∫ x, f x ∂μ = 0) :
    ∀ x ∈ μ.support, f x = 0 := by
  have hae : f =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg hnonneg hfi).mp hint
  have hzeroConull : {x | f x = 0} ∈ ae μ := by
    filter_upwards [hae] with x hx
    exact hx
  have hzeroClosed : IsClosed {x | f x = 0} :=
    isClosed_eq hf continuous_const
  exact fun x hx ↦
    Measure.support_subset_of_isClosed hzeroClosed hzeroConull hx

variable {ι : Type*} [Fintype ι]

/-- Sum of squared complex moduli of a finite family of residuals. -/
def complexResidualEnergy
    (r : ι → X → ℂ) (x : X) : ℝ :=
  ∑ i, Complex.normSq (r i x)

omit [MeasurableSpace X] in
/-- A finite residual energy is continuous when all residuals are
continuous. -/
theorem continuous_complexResidualEnergy
    {r : ι → X → ℂ}
    (hr : ∀ i, Continuous (r i)) :
    Continuous (complexResidualEnergy r) := by
  apply continuous_finsetSum
  intro i _
  exact Complex.continuous_normSq.comp (hr i)

omit [TopologicalSpace X] [MeasurableSpace X] in
/-- A finite residual energy is pointwise nonnegative. -/
theorem complexResidualEnergy_nonneg
    (r : ι → X → ℂ) (x : X) :
    0 ≤ complexResidualEnergy r x := by
  apply Finset.sum_nonneg
  intro i _
  exact Complex.normSq_nonneg _

omit [TopologicalSpace X] [MeasurableSpace X] in
/-- The residual energy is zero exactly when every constituent residual
is zero. -/
theorem complexResidualEnergy_eq_zero_iff
    (r : ι → X → ℂ) (x : X) :
    complexResidualEnergy r x = 0 ↔ ∀ i, r i x = 0 := by
  constructor
  · intro henergy i
    have hterm : Complex.normSq (r i x) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ Complex.normSq_nonneg (r j x))).mp
          henergy i (Finset.mem_univ i)
    exact Complex.normSq_eq_zero.mp hterm
  · intro hresidual
    simp [complexResidualEnergy, hresidual]

/-- **Finite residual support principle.**

If the integral of the sum of squared moduli of finitely many continuous
complex residuals is zero, every residual vanishes pointwise on the
measure support. -/
theorem complexResiduals_eq_zero_on_support_of_integral_energy_eq_zero
    {r : ι → X → ℂ}
    (hr : ∀ i, Continuous (r i))
    (henergyIntegrable : Integrable (complexResidualEnergy r) μ)
    (henergyIntegral :
      ∫ x, complexResidualEnergy r x ∂μ = 0) :
    ∀ x ∈ μ.support, ∀ i, r i x = 0 := by
  intro x hx
  apply (complexResidualEnergy_eq_zero_iff r x).mp
  exact eq_zero_on_support_of_continuous_nonneg_of_integral_eq_zero
    (continuous_complexResidualEnergy hr)
    (complexResidualEnergy_nonneg r)
    henergyIntegrable henergyIntegral x hx

end

end HGAS.Dynamics
