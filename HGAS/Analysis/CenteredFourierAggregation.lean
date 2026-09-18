import HGAS.Analysis.FourierExponentAggregation
import Mathlib.Tactic

/-!
# Centering an absolutely summable Fourier expression

This small adapter represents `Σᵢ cᵢ χ_{aᵢ} - C` by adjoining one
constant term to the raw index type.  Its main theorem says that if the
sum of all raw zero-exponent coefficients is `C`, then the collected
coefficient at exponent zero is exactly zero.

The theorem is intentionally stated with `HasSum`, so explicit resonance
calculations can name their finite sum without first proving convergence
of the entire Fourier series.
-/

noncomputable section

namespace HGAS.Analysis

universe u v

variable {d : Type u} {ι : Type v}

/-- A distinguished constant term together with a raw Fourier family. -/
abbrev CenteredFourierIndex (ι : Type v) :=
  Unit ⊕ ι

/-- Coefficient family for `Σᵢ coefficient i - center`. -/
def centeredFourierCoefficient
    (center : ℂ) (coefficient : ι → ℂ) :
    CenteredFourierIndex ι → ℂ
  | Sum.inl _ => -center
  | Sum.inr i => coefficient i

/-- The adjoined centering term has exponent zero. -/
def centeredFourierExponent
    (exponent : ι → d → ℤ) :
    CenteredFourierIndex ι → d → ℤ
  | Sum.inl _ => 0
  | Sum.inr i => exponent i

/-- If the aggregate raw coefficient at exponent zero equals `center`,
then adjoining `-center` kills the collected zero mode. -/
theorem aggregate_centeredFourierCoefficient_zero
    [Fintype d]
    (center : ℂ)
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (hresonant :
      HasSum
        (fun i : ι ↦
          if exponent i = 0 then coefficient i else 0)
        center) :
    aggregateFourierCoefficient
        (centeredFourierCoefficient center coefficient)
        (centeredFourierExponent exponent) 0 = 0 := by
  classical
  let zeroFiber : Set (CenteredFourierIndex ι) :=
    {i | centeredFourierExponent exponent i = 0}
  have hleft :
      HasSum
        (fun u : Unit ↦
          zeroFiber.indicator
            (centeredFourierCoefficient center coefficient)
            (Sum.inl u))
        (-center) := by
    convert
      hasSum_fintype
        (fun u : Unit ↦
          zeroFiber.indicator
            (centeredFourierCoefficient center coefficient)
            (Sum.inl u)) using 1
    simp [zeroFiber, centeredFourierExponent,
      centeredFourierCoefficient]
  have hright :
      HasSum
        (fun i : ι ↦
          zeroFiber.indicator
            (centeredFourierCoefficient center coefficient)
            (Sum.inr i))
        center := by
    apply hresonant.congr
    intro s
    apply Finset.sum_congr rfl
    intro i _
    simp only [zeroFiber, Set.indicator,
      Set.mem_setOf_eq, centeredFourierExponent,
      centeredFourierCoefficient]
  have htotal :
      HasSum
        (zeroFiber.indicator
          (centeredFourierCoefficient center coefficient))
        (-center + center) :=
    HasSum.sum
      (f := zeroFiber.indicator
        (centeredFourierCoefficient center coefficient))
      hleft hright
  calc
    aggregateFourierCoefficient
        (centeredFourierCoefficient center coefficient)
        (centeredFourierExponent exponent) 0 =
      ∑' i : CenteredFourierIndex ι,
        zeroFiber.indicator
          (centeredFourierCoefficient center coefficient) i :=
      tsum_subtype zeroFiber
        (centeredFourierCoefficient center coefficient)
    _ = -center + center := htotal.tsum_eq
    _ = 0 := by ring

end HGAS.Analysis
