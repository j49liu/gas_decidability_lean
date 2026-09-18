import HGAS.Analysis.CesaroExponentialSeries
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

/-!
# The quadratic resonance calculation in the Jacobi selector

After the modular and Jacobi differential equations have classified a
regular recurrent leaf, its observed output has a Fourier expansion whose
`n`-th temporal frequency is proportional to

```
                       qρ(n+a) = (n+a)(n+a+ρ).
```

Here `a` is the real Bloch shift and `ρ` is the ratio of the two clock
rates.  Multiplication by the moment character indexed by an integer `r`
subtracts `qρ(r)`.  The elementary factorization

```
             qρ(m) - qρ(r) = (m-r)(m+r+ρ)
```

therefore gives exactly two possible resonances:

```
                         m = r   or   m = -ρ-r.
```

This file proves that calculation, the three rows `r=0,1,-1` used in the
paper, the two possible Bloch classes forced by the mean-one moment, and
the fact that an irrational `ρ` lets an affine integer lattice contain at
most one root in each row.  Finally it combines these facts with the
general Cesàro theorem in `Analysis.CesaroExponentialSeries`.

The result is an unconditional and reusable selector interface.  Its input
is an absolutely summable classified Bloch expansion.  Supplying that
expansion for every accepted recurrent state is the separate
modular/Jacobi saturation problem.
-/

noncomputable section

open Filter Topology

namespace HGAS.Modular

/-- The quadratic dispersion relation of the two-clock Jacobi trace. -/
def quadraticDispersion (ρ m : ℝ) : ℝ :=
  m * (m + ρ)

/-- Exact factorization of the difference of two dispersion values. -/
theorem quadraticDispersion_sub
    (ρ m r : ℝ) :
    quadraticDispersion ρ m - quadraticDispersion ρ r =
      (m - r) * (m + r + ρ) := by
  simp only [quadraticDispersion]
  ring

/-- A frequency equals the `r`-th moment frequency exactly at the direct
root `r` or at its reflected root `-ρ-r`. -/
theorem quadraticDispersion_eq_iff
    (ρ m r : ℝ) :
    quadraticDispersion ρ m = quadraticDispersion ρ r ↔
      m = r ∨ m = -ρ - r := by
  rw [← sub_eq_zero, quadraticDispersion_sub, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl (sub_eq_zero.mpr h)
    · exact Or.inr (by linarith)

/-- Physical frequency of the term with lattice index `n`, after twisting
by the moment character whose direct resonance is the integer `r`. -/
def quadraticMomentFrequency
    (Ω ρ a : ℝ) (r n : ℤ) : ℝ :=
  Ω * (quadraticDispersion ρ ((n : ℝ) + a) -
    quadraticDispersion ρ (r : ℝ))

/-- With nonzero private clock rate, the complete resonance table is the
two-root factorization above. -/
theorem quadraticMomentFrequency_eq_zero_iff
    {Ω : ℝ} (hΩ : Ω ≠ 0)
    (ρ a : ℝ) (r n : ℤ) :
    quadraticMomentFrequency Ω ρ a r n = 0 ↔
      (n : ℝ) + a = (r : ℝ) ∨
        (n : ℝ) + a = -ρ - (r : ℝ) := by
  rw [quadraticMomentFrequency, mul_eq_zero,
    or_iff_right hΩ, sub_eq_zero,
    quadraticDispersion_eq_iff]

/-- The mean row `r=0` has resonances `m=0,-ρ`. -/
theorem meanMomentFrequency_eq_zero_iff
    {Ω : ℝ} (hΩ : Ω ≠ 0)
    (ρ a : ℝ) (n : ℤ) :
    quadraticMomentFrequency Ω ρ a 0 n = 0 ↔
      (n : ℝ) + a = 0 ∨ (n : ℝ) + a = -ρ := by
  simpa using
    quadraticMomentFrequency_eq_zero_iff hΩ ρ a 0 n

/-- The `(1,1)` row has resonances `m=1,-1-ρ`. -/
theorem plusMomentFrequency_eq_zero_iff
    {Ω : ℝ} (hΩ : Ω ≠ 0)
    (ρ a : ℝ) (n : ℤ) :
    quadraticMomentFrequency Ω ρ a 1 n = 0 ↔
      (n : ℝ) + a = 1 ∨ (n : ℝ) + a = -1 - ρ := by
  rw [quadraticMomentFrequency_eq_zero_iff hΩ]
  constructor <;> rintro (h | h)
  · left
    norm_num at h ⊢
    exact h
  · right
    norm_num at h ⊢
    linarith
  · left
    norm_num at h ⊢
    exact h
  · right
    norm_num at h ⊢
    linarith

/-- The `(1,-1)` row has resonances `m=-1,1-ρ`. -/
theorem minusMomentFrequency_eq_zero_iff
    {Ω : ℝ} (hΩ : Ω ≠ 0)
    (ρ a : ℝ) (n : ℤ) :
    quadraticMomentFrequency Ω ρ a (-1) n = 0 ↔
      (n : ℝ) + a = -1 ∨ (n : ℝ) + a = 1 - ρ := by
  rw [quadraticMomentFrequency_eq_zero_iff hΩ]
  constructor <;> rintro (h | h)
  · left
    norm_num at h ⊢
    exact h
  · exact Or.inr (by norm_num at h ⊢; linarith)
  · left
    norm_num at h ⊢
    exact h
  · exact Or.inr (by norm_num at h ⊢; linarith)

/-- The ordinary Bloch class: `a` differs from zero by an integer. -/
def IsIntegralBlochClass (a : ℝ) : Prop :=
  ∃ k : ℤ, a = (k : ℝ)

/-- The reflected Bloch class: `a` differs from `-ρ` by an integer. -/
def IsReflectedBlochClass (ρ a : ℝ) : Prop :=
  ∃ k : ℤ, a = -ρ + (k : ℝ)

/-- A lattice term resonates with the mean if and only if `a` belongs to
one of the two Bloch classes. -/
theorem exists_mean_resonance_iff_blochClasses
    (ρ a : ℝ) :
    (∃ n : ℤ,
      quadraticDispersion ρ ((n : ℝ) + a) = 0) ↔
      IsIntegralBlochClass a ∨
        IsReflectedBlochClass ρ a := by
  constructor
  · rintro ⟨n, hn⟩
    have hroots :
        (n : ℝ) + a = 0 ∨ (n : ℝ) + a = -ρ := by
      rcases (mul_eq_zero.mp hn) with hzero | hreflected
      · exact Or.inl hzero
      · exact Or.inr (by
          simp only [quadraticDispersion] at hn
          linarith)
    rcases hroots with hzero | hreflected
    · left
      refine ⟨-n, ?_⟩
      push_cast
      linarith
    · right
      refine ⟨-n, ?_⟩
      push_cast
      linarith
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · refine ⟨-k, ?_⟩
      rw [hk]
      push_cast
      simp [quadraticDispersion]
    · refine ⟨-k, ?_⟩
      rw [hk]
      push_cast
      simp [quadraticDispersion]

/-- For irrational clock ratio the ordinary and reflected Bloch classes
are disjoint. -/
theorem integral_reflected_blochClasses_disjoint
    {ρ : ℝ} (hρ : Irrational ρ) (a : ℝ) :
    ¬(IsIntegralBlochClass a ∧
      IsReflectedBlochClass ρ a) := by
  rintro ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
  apply hρ.ne_int (l - k)
  push_cast
  linarith

/-- Irrational clock ratio implies that the affine integer lattice
`a + ℤ` contains at most one of the two roots in any moment row. -/
theorem quadraticResonance_index_unique
    {ρ : ℝ} (hρ : Irrational ρ)
    (a : ℝ) (r n₁ n₂ : ℤ)
    (h₁ :
      quadraticDispersion ρ ((n₁ : ℝ) + a) =
        quadraticDispersion ρ (r : ℝ))
    (h₂ :
      quadraticDispersion ρ ((n₂ : ℝ) + a) =
        quadraticDispersion ρ (r : ℝ)) :
    n₁ = n₂ := by
  have hr₁ :=
    (quadraticDispersion_eq_iff
      ρ ((n₁ : ℝ) + a) (r : ℝ)).mp h₁
  have hr₂ :=
    (quadraticDispersion_eq_iff
      ρ ((n₂ : ℝ) + a) (r : ℝ)).mp h₂
  rcases hr₁ with h₁direct | h₁reflected
  · rcases hr₂ with h₂direct | h₂reflected
    · exact_mod_cast (by linarith :
        (n₁ : ℝ) = (n₂ : ℝ))
    · exfalso
      apply hρ.ne_int (n₁ - n₂ - 2 * r)
      push_cast
      linarith
  · rcases hr₂ with h₂direct | h₂reflected
    · exfalso
      apply hρ.ne_int (n₂ - n₁ - 2 * r)
      push_cast
      linarith
    · exact_mod_cast (by linarith :
        (n₁ : ℝ) = (n₂ : ℝ))

/-- The classified Bloch exponential series for one moment row. -/
def quadraticMomentSeries
    (coefficient : ℤ → ℂ)
    (Ω ρ a : ℝ) (r : ℤ) (t : ℝ) : ℂ :=
  HGAS.Analysis.exponentialSeries coefficient
    (quadraticMomentFrequency Ω ρ a r) t

/-- The zero-frequency coefficient sum in the mean row. -/
def meanResonantCoefficientSum
    (coefficient : ℤ → ℂ) (ρ a : ℝ) : ℂ :=
  ∑' n : ℤ,
    if (n : ℝ) + a = 0 ∨ (n : ℝ) + a = -ρ then
      coefficient n
    else 0

/-- A nonzero mean-resonant coefficient sum forces one of the two Bloch
classes.  No nonvanishing assumption on individual coefficients is
needed. -/
theorem blochClasses_of_meanResonantCoefficientSum_ne_zero
    (coefficient : ℤ → ℂ) (ρ a : ℝ)
    (hne :
      meanResonantCoefficientSum coefficient ρ a ≠ 0) :
    IsIntegralBlochClass a ∨
      IsReflectedBlochClass ρ a := by
  by_contra hclasses
  have hnone (n : ℤ) :
      ¬((n : ℝ) + a = 0 ∨
        (n : ℝ) + a = -ρ) := by
    intro hroot
    apply hclasses
    apply
      (exists_mean_resonance_iff_blochClasses
        ρ a).mp
    refine ⟨n, ?_⟩
    rcases hroot with hzero | hreflected
    · simp [quadraticDispersion, hzero]
    · simp [quadraticDispersion, hreflected]
  apply hne
  rw [meanResonantCoefficientSum]
  have hzero :
      (fun n : ℤ ↦
        if (n : ℝ) + a = 0 ∨
            (n : ℝ) + a = -ρ then
          coefficient n
        else 0) = 0 := by
    funext n
    simp [hnone n]
  rw [hzero]
  exact tsum_zero (α := ℂ) (β := ℤ)

/-- **Reusable three-moment extraction interface.**  For every absolutely
summable classified Bloch expansion, Cesàro averaging of the `r`-th
moment retains exactly the direct and reflected resonant lattice terms. -/
theorem naturalCesaroMean_quadraticMomentSeries_tendsto
    (coefficient : ℤ → ℂ)
    (hsum : Summable fun n ↦ ‖coefficient n‖)
    {Ω : ℝ} (hΩ : Ω ≠ 0)
    (ρ a : ℝ) (r : ℤ) :
    Tendsto
      (fun N ↦ HGAS.Analysis.naturalCesaroMean
        (quadraticMomentSeries coefficient Ω ρ a r) N)
      atTop
      (𝓝 (∑' n : ℤ,
        if (n : ℝ) + a = (r : ℝ) ∨
            (n : ℝ) + a = -ρ - (r : ℝ) then
          coefficient n
        else 0)) := by
  simpa only [quadraticMomentSeries,
    quadraticMomentFrequency_eq_zero_iff hΩ] using
    HGAS.Analysis.naturalCesaroMean_exponentialSeries_tendsto
      coefficient (quadraticMomentFrequency Ω ρ a r) hsum

/-- Mean-row specialization of the extraction interface. -/
theorem naturalCesaroMean_meanMomentSeries_tendsto
    (coefficient : ℤ → ℂ)
    (hsum : Summable fun n ↦ ‖coefficient n‖)
    {Ω : ℝ} (hΩ : Ω ≠ 0)
    (ρ a : ℝ) :
    Tendsto
      (fun N ↦ HGAS.Analysis.naturalCesaroMean
        (quadraticMomentSeries coefficient Ω ρ a 0) N)
      atTop
      (𝓝 (∑' n : ℤ,
        if (n : ℝ) + a = 0 ∨
            (n : ℝ) + a = -ρ then
          coefficient n
        else 0)) := by
  simpa using
    naturalCesaroMean_quadraticMomentSeries_tendsto
      coefficient hsum hΩ ρ a 0

/-- If the mean-row Cesàro average is normalized to one, then the Bloch
shift belongs to one of the two classes in equation (8.20) of the paper. -/
theorem blochClasses_of_meanMoment_tendsto_one
    (coefficient : ℤ → ℂ)
    (hsum : Summable fun n ↦ ‖coefficient n‖)
    {Ω : ℝ} (hΩ : Ω ≠ 0)
    (ρ a : ℝ)
    (hone :
      Tendsto
        (fun N ↦ HGAS.Analysis.naturalCesaroMean
          (quadraticMomentSeries coefficient Ω ρ a 0) N)
        atTop (𝓝 1)) :
    IsIntegralBlochClass a ∨
      IsReflectedBlochClass ρ a := by
  have hextract :=
    naturalCesaroMean_meanMomentSeries_tendsto
      coefficient hsum hΩ ρ a
  have hsum_eq :
      meanResonantCoefficientSum coefficient ρ a = 1 := by
    exact tendsto_nhds_unique hextract hone
  apply
    blochClasses_of_meanResonantCoefficientSum_ne_zero
      coefficient ρ a
  rw [hsum_eq]
  norm_num

/-- `(1,1)`-row specialization of the extraction interface. -/
theorem naturalCesaroMean_plusMomentSeries_tendsto
    (coefficient : ℤ → ℂ)
    (hsum : Summable fun n ↦ ‖coefficient n‖)
    {Ω : ℝ} (hΩ : Ω ≠ 0)
    (ρ a : ℝ) :
    Tendsto
      (fun N ↦ HGAS.Analysis.naturalCesaroMean
        (quadraticMomentSeries coefficient Ω ρ a 1) N)
      atTop
      (𝓝 (∑' n : ℤ,
        if (n : ℝ) + a = 1 ∨
            (n : ℝ) + a = -1 - ρ then
          coefficient n
        else 0)) := by
  convert
    naturalCesaroMean_quadraticMomentSeries_tendsto
      coefficient hsum hΩ ρ a 1 using 1
  apply congrArg 𝓝
  apply tsum_congr
  intro n
  congr 1
  apply propext
  constructor <;> rintro (h | h)
  · left
    norm_num at h ⊢
    exact h
  · right
    norm_num at h ⊢
    linarith
  · left
    norm_num at h ⊢
    exact h
  · right
    norm_num at h ⊢
    linarith

/-- `(1,-1)`-row specialization of the extraction interface. -/
theorem naturalCesaroMean_minusMomentSeries_tendsto
    (coefficient : ℤ → ℂ)
    (hsum : Summable fun n ↦ ‖coefficient n‖)
    {Ω : ℝ} (hΩ : Ω ≠ 0)
    (ρ a : ℝ) :
    Tendsto
      (fun N ↦ HGAS.Analysis.naturalCesaroMean
        (quadraticMomentSeries coefficient Ω ρ a (-1)) N)
      atTop
      (𝓝 (∑' n : ℤ,
        if (n : ℝ) + a = -1 ∨
            (n : ℝ) + a = 1 - ρ then
          coefficient n
        else 0)) := by
  convert
    naturalCesaroMean_quadraticMomentSeries_tendsto
      coefficient hsum hΩ ρ a (-1) using 1
  apply congrArg 𝓝
  apply tsum_congr
  intro n
  congr 1
  apply propext
  constructor <;> rintro (h | h)
  · left
    norm_num at h ⊢
    exact h
  · exact Or.inr (by norm_num at h ⊢; linarith)
  · left
    norm_num at h ⊢
    exact h
  · exact Or.inr (by norm_num at h ⊢; linarith)

end HGAS.Modular
