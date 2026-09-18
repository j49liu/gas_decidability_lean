import HGAS.Modular.JacobiMomentResonanceArbitraryHorizon
import HGAS.Modular.QuadraticGeometricSequence
import Mathlib.Tactic

/-!
# Three noncolliding moments determine an arbitrary quadratic target trace

This is a phase-free version of Jacobi--Bloch three-moment rigidity.
Instead of choosing real lifts of the two initial torus angles, it records
only that the source and target coefficient families are
quadratic--geometric after the relevant integer reindexing.  This is the
right interface for a detector orbit with arbitrary initial clock phases.

For an irrational clock ratio, the mean row leaves the integral and
reflected Bloch classes.  In either class the two first moments identify
the coefficients at the neighbouring indices `1` and `-1`.  A normalized
quadratic--geometric sequence is determined by those two neighbours, so
the complete trace follows, including the reflected reindexing.

The irrationality assumption is essential here.  At ratio zero the two
first rows have the same two resonant terms and no longer identify the
neighbours separately.
-/

noncomputable section

open Filter Topology

namespace HGAS.Modular

/-- A coefficient family is a nondegenerate scaled
quadratic--geometric sequence. -/
def IsScaledQuadraticGeometric
    (coefficient : ℤ → ℂ) : Prop :=
  ∃ C R S : ℂ,
    R ≠ 0 ∧ S ≠ 0 ∧
      ∀ k : ℤ,
        coefficient k =
          C * quadraticGeometricSequence R S k

/-- A normalized nondegenerate quadratic--geometric sequence. -/
def IsQuadraticGeometric
    (coefficient : ℤ → ℂ) : Prop :=
  ∃ R S : ℂ,
    R ≠ 0 ∧ S ≠ 0 ∧
      coefficient = quadraticGeometricSequence R S

theorem IsQuadraticGeometric.zero
    {coefficient : ℤ → ℂ}
    (h : IsQuadraticGeometric coefficient) :
    coefficient 0 = 1 := by
  obtain ⟨R, S, _hR, _hS, rfl⟩ := h
  exact quadraticGeometricSequence_zero R S

/-- Mean normalization removes the scale of a scaled
quadratic--geometric sequence. -/
theorem IsScaledQuadraticGeometric.normalized_of_zero_eq_one
    {coefficient : ℤ → ℂ}
    (h : IsScaledQuadraticGeometric coefficient)
    (hzero : coefficient 0 = 1) :
    IsQuadraticGeometric coefficient := by
  obtain ⟨C, R, S, hR, hS, hformula⟩ := h
  have hC : C = 1 := by
    have := hformula 0
    rw [quadraticGeometricSequence_zero, mul_one] at this
    exact this.symm.trans hzero
  refine ⟨R, S, hR, hS, ?_⟩
  funext k
  rw [hformula k, hC, one_mul]

/-- Two normalized quadratic--geometric families which agree at `1` and
`-1` agree at every integer. -/
theorem IsQuadraticGeometric.eq_of_neighbors
    {coefficient target : ℤ → ℂ}
    (hc : IsQuadraticGeometric coefficient)
    (ht : IsQuadraticGeometric target)
    (hone : coefficient 1 = target 1)
    (hneg : coefficient (-1) = target (-1)) :
    coefficient = target := by
  obtain ⟨R, S, hR, hS, hcoefficient⟩ := hc
  obtain ⟨R', S', _hR', hS', htarget⟩ := ht
  subst coefficient
  subst target
  funext k
  exact
    quadraticGeometricSequence_eq_of_neighbors
      R S R' S' hR hS hS' hone hneg k

/-! ## Irrational resonant sums -/

private theorem integral_resonant_sum
    (coefficient : ℤ → ℂ)
    {ρ : ℝ} (hρ : Irrational ρ)
    (l r : ℤ) :
    (∑' n : ℤ,
      if (n : ℝ) + (l : ℝ) = (r : ℝ) ∨
          (n : ℝ) + (l : ℝ) =
            -ρ - (r : ℝ) then
        coefficient n
      else 0) =
      coefficient (r - l) := by
  have hpred (n : ℤ) :
      ((n : ℝ) + (l : ℝ) = (r : ℝ) ∨
          (n : ℝ) + (l : ℝ) =
            -ρ - (r : ℝ)) ↔
        n = r - l := by
    constructor
    · rintro (hdirect | hreflected)
      · have hz : n + l = r := by exact_mod_cast hdirect
        omega
      · exfalso
        apply hρ.ne_int (-(n + l + r))
        push_cast
        linarith
    · rintro rfl
      left
      push_cast
      ring
  calc
    (∑' n : ℤ,
      if (n : ℝ) + (l : ℝ) = (r : ℝ) ∨
          (n : ℝ) + (l : ℝ) =
            -ρ - (r : ℝ) then
        coefficient n
      else 0) =
        ∑' n : ℤ,
          if n = r - l then coefficient n else 0 := by
      apply tsum_congr
      intro n
      simp only [hpred n]
    _ = coefficient (r - l) := tsum_ite_eq _ _

private theorem reflected_resonant_sum
    (coefficient : ℤ → ℂ)
    {ρ : ℝ} (hρ : Irrational ρ)
    (l r : ℤ) :
    (∑' n : ℤ,
      if (n : ℝ) + (-ρ + (l : ℝ)) = (r : ℝ) ∨
          (n : ℝ) + (-ρ + (l : ℝ)) =
            -ρ - (r : ℝ) then
        coefficient n
      else 0) =
      coefficient (-r - l) := by
  have hpred (n : ℤ) :
      ((n : ℝ) + (-ρ + (l : ℝ)) = (r : ℝ) ∨
          (n : ℝ) + (-ρ + (l : ℝ)) =
            -ρ - (r : ℝ)) ↔
        n = -r - l := by
    constructor
    · rintro (hdirect | hreflected)
      · exfalso
        apply hρ.ne_int (n + l - r)
        push_cast
        linarith
      · have hz : n + l = -r := by
          exact_mod_cast (by linarith :
            (n : ℝ) + (l : ℝ) = -(r : ℝ))
        omega
    · rintro rfl
      right
      push_cast
      ring
  calc
    (∑' n : ℤ,
      if (n : ℝ) + (-ρ + (l : ℝ)) = (r : ℝ) ∨
          (n : ℝ) + (-ρ + (l : ℝ)) =
            -ρ - (r : ℝ) then
        coefficient n
      else 0) =
        ∑' n : ℤ,
          if n = -r - l then coefficient n else 0 := by
      apply tsum_congr
      intro n
      simp only [hpred n]
    _ = coefficient (-r - l) := tsum_ite_eq _ _

/-! ## Reindexing the complete time trace -/

private theorem integral_trace_eq_of_reindex
    (coefficient target : ℤ → ℂ)
    (Ω ρ : ℝ) (l : ℤ)
    (hreindex :
      ∀ k : ℤ, coefficient (k - l) = target k)
    (t : ℝ) :
    quadraticMomentSeries coefficient
        Ω ρ (l : ℝ) 0 t =
      quadraticMomentSeries target Ω ρ 0 0 t := by
  unfold quadraticMomentSeries HGAS.Analysis.exponentialSeries
  rw [← (Equiv.addRight (-l : ℤ)).tsum_eq]
  apply tsum_congr
  intro k
  unfold HGAS.Analysis.exponentialSeriesTerm
  simp only [Equiv.coe_addRight, ← sub_eq_add_neg]
  rw [hreindex k]
  congr 1
  unfold quadraticMomentFrequency quadraticDispersion
  push_cast
  ring

private theorem reflected_trace_eq_of_reindex
    (coefficient target : ℤ → ℂ)
    (Ω ρ : ℝ) (l : ℤ)
    (hreindex :
      ∀ k : ℤ, coefficient (-k - l) = target k)
    (t : ℝ) :
    quadraticMomentSeries coefficient
        Ω ρ (-ρ + (l : ℝ)) 0 t =
      quadraticMomentSeries target Ω ρ 0 0 t := by
  unfold quadraticMomentSeries HGAS.Analysis.exponentialSeries
  rw [← ((Equiv.neg ℤ).trans
    (Equiv.addRight (-l : ℤ))).tsum_eq]
  apply tsum_congr
  intro k
  unfold HGAS.Analysis.exponentialSeriesTerm
  simp only [Equiv.trans_apply, Equiv.neg_apply,
    Equiv.coe_addRight, ← sub_eq_add_neg]
  rw [hreindex k]
  congr 1
  unfold quadraticMomentFrequency quadraticDispersion
  push_cast
  ring

/-! ## Main phase-free rigidity theorem -/

/-- **Target-valued three-moment rigidity at irrational clock ratio.**

The source coefficient family need only be quadratic--geometric after
the two possible mean-resonant reindexings.  The target may have arbitrary
initial phases.  The two twisting constants are correspondingly arbitrary
nonzero complex numbers; their only role is to cancel from the comparison
of the two neighbouring coefficients. -/
theorem quadraticTrace_eq_target_of_three_moments
    (coefficient target : ℤ → ℂ)
    (Ω ρ a : ℝ)
    (hΩ : Ω ≠ 0)
    (hρ : Irrational ρ)
    (hsum : Summable fun n : ℤ ↦ ‖coefficient n‖)
    (hIntegral :
      ∀ l : ℤ,
        IsScaledQuadraticGeometric
          (fun k : ℤ ↦ coefficient (k - l)))
    (hReflected :
      ∀ l : ℤ,
        IsScaledQuadraticGeometric
          (fun k : ℤ ↦ coefficient (-k - l)))
    (hTarget : IsQuadraticGeometric target)
    (cPlus cMinus : ℂ)
    (hcPlus : cPlus ≠ 0)
    (hcMinus : cMinus ≠ 0)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    (hmean :
      Tendsto
        (fun N ↦ HGAS.Analysis.cesaroMeanAt
          (quadraticMomentSeries coefficient Ω ρ a 0)
          (T N))
        atTop (𝓝 1))
    (hplus :
      Tendsto
        (fun N ↦ HGAS.Analysis.cesaroMeanAt
          (quadraticMomentSeries
            (fun n ↦ cPlus * coefficient n)
            Ω ρ a 1)
          (T N))
        atTop (𝓝 (cPlus * target 1)))
    (hminus :
      Tendsto
        (fun N ↦ HGAS.Analysis.cesaroMeanAt
          (quadraticMomentSeries
            (fun n ↦ cMinus * coefficient n)
            Ω ρ a (-1))
          (T N))
        atTop (𝓝 (cMinus * target (-1)))) :
    ∀ t : ℝ,
      quadraticMomentSeries coefficient Ω ρ a 0 t =
        quadraticMomentSeries target Ω ρ 0 0 t := by
  have hsumPlus :
      Summable fun n : ℤ ↦
        ‖cPlus * coefficient n‖ :=
    (hsum.of_norm.mul_left cPlus).norm
  have hsumMinus :
      Summable fun n : ℤ ↦
        ‖cMinus * coefficient n‖ :=
    (hsum.of_norm.mul_left cMinus).norm
  have hmeanExtract :=
    cesaroMeanAt_quadraticMomentSeries_tendsto
      coefficient hsum hΩ ρ a 0 hT
  have hmeanLimit :
      (∑' n : ℤ,
        if (n : ℝ) + a = (0 : ℤ) ∨
            (n : ℝ) + a = -ρ - (0 : ℤ) then
          coefficient n
        else 0) =
        1 :=
    tendsto_nhds_unique hmeanExtract hmean
  have hclasses :
      IsIntegralBlochClass a ∨
        IsReflectedBlochClass ρ a :=
    blochClasses_of_cesaroMeanAt_meanMoment_tendsto_one
      coefficient hsum hΩ ρ a hT hmean
  have hplusExtract :=
    cesaroMeanAt_quadraticMomentSeries_tendsto
      (fun n ↦ cPlus * coefficient n)
      hsumPlus hΩ ρ a 1 hT
  have hminusExtract :=
    cesaroMeanAt_quadraticMomentSeries_tendsto
      (fun n ↦ cMinus * coefficient n)
      hsumMinus hΩ ρ a (-1) hT
  rcases hclasses with ⟨l, rfl⟩ | ⟨l, rfl⟩
  · have hzero : coefficient (-l) = 1 := by
      have hlimit := hmeanLimit
      rw [integral_resonant_sum coefficient hρ l 0] at hlimit
      simpa only [zero_sub] using hlimit
    have hone : coefficient (1 - l) = target 1 := by
      have hlimit := tendsto_nhds_unique hplusExtract hplus
      rw [integral_resonant_sum
        (fun n ↦ cPlus * coefficient n) hρ l 1] at hlimit
      exact mul_left_cancel₀ hcPlus hlimit
    have hneg : coefficient (-1 - l) = target (-1) := by
      have hlimit := tendsto_nhds_unique hminusExtract hminus
      rw [integral_resonant_sum
        (fun n ↦ cMinus * coefficient n) hρ l (-1)] at hlimit
      exact mul_left_cancel₀ hcMinus hlimit
    have hsource :
        IsQuadraticGeometric
          (fun k : ℤ ↦ coefficient (k - l)) :=
      (hIntegral l).normalized_of_zero_eq_one (by
        simpa only [zero_sub] using hzero)
    have hreindex :
        (fun k : ℤ ↦ coefficient (k - l)) = target :=
      hsource.eq_of_neighbors hTarget
        (by simpa only using hone)
        (by simpa only using hneg)
    exact integral_trace_eq_of_reindex
      coefficient target Ω ρ l (congrFun hreindex)
  · have hzero : coefficient (-l) = 1 := by
      have hlimit := hmeanLimit
      rw [reflected_resonant_sum coefficient hρ l 0] at hlimit
      simpa only [neg_zero, zero_sub] using hlimit
    have hone : coefficient (-1 - l) = target 1 := by
      have hlimit := tendsto_nhds_unique hplusExtract hplus
      rw [reflected_resonant_sum
        (fun n ↦ cPlus * coefficient n) hρ l 1] at hlimit
      exact mul_left_cancel₀ hcPlus hlimit
    have hneg : coefficient (1 - l) = target (-1) := by
      have hlimit := tendsto_nhds_unique hminusExtract hminus
      rw [reflected_resonant_sum
        (fun n ↦ cMinus * coefficient n) hρ l (-1)] at hlimit
      exact mul_left_cancel₀ hcMinus hlimit
    have hsource :
        IsQuadraticGeometric
          (fun k : ℤ ↦ coefficient (-k - l)) :=
      (hReflected l).normalized_of_zero_eq_one (by
        simpa only [neg_zero, zero_sub] using hzero)
    have hreindex :
        (fun k : ℤ ↦ coefficient (-k - l)) = target :=
      hsource.eq_of_neighbors hTarget
        (by simpa only using hone)
        (by simpa only using hneg)
    exact reflected_trace_eq_of_reindex
      coefficient target Ω ρ l (congrFun hreindex)

end HGAS.Modular
