import HGAS.Analysis.CenteredFourierAggregation
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic

/-!
# Elementary operations on absolutely convergent torus Fourier series

The canonical detector moments repeatedly use three operations:

1. subtract one constant Fourier mode;
2. multiply a series by one torus character; and
3. square a one-dimensional theta series.

This file proves those identities once for arbitrary finite tori and
arbitrary countable index types.  The statements are pointwise and keep
the exact coefficient/exponent families visible, which makes them useful
both for the human proof and for later coefficient aggregation.
-/

noncomputable section

namespace HGAS.Analysis

universe u v

variable {d : Type u} [Fintype d]
variable {ι : Type v}

/-- Adjoining the constant coefficient `-center` represents literal
subtraction of `center`. -/
theorem torusFourierSeries_centered
    (center : ℂ)
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (hcoefficient : Summable fun i ↦ ‖coefficient i‖)
    (phase : UnitAddTorus d) :
    torusFourierSeries
        (centeredFourierCoefficient center coefficient)
        (centeredFourierExponent exponent) phase =
      torusFourierSeries coefficient exponent phase - center := by
  let rawTerm : ι → ℂ :=
    fun i ↦ torusSeriesTerm coefficient exponent i phase
  have hraw : Summable rawTerm :=
    hcoefficient.of_norm_bounded fun i ↦ by
      rw [norm_torusSeriesTerm]
  let centeredTerm : CenteredFourierIndex ι → ℂ :=
    fun i ↦
      torusSeriesTerm
        (centeredFourierCoefficient center coefficient)
        (centeredFourierExponent exponent) i phase
  have hleft :
      HasSum (fun u : Unit ↦ centeredTerm (Sum.inl u)) (-center) := by
    convert hasSum_fintype
      (fun u : Unit ↦ centeredTerm (Sum.inl u)) using 1
    simp [centeredTerm, torusSeriesTerm,
      centeredFourierCoefficient, centeredFourierExponent,
      UnitAddTorus.mFourier_zero]
  have hright :
      HasSum (fun i : ι ↦ centeredTerm (Sum.inr i))
        (torusFourierSeries coefficient exponent phase) := by
    have h := hraw.hasSum
    unfold torusFourierSeries
    exact h.congr fun i ↦ by
      rfl
  have hsum :
      HasSum centeredTerm
        (-center + torusFourierSeries coefficient exponent phase) :=
    HasSum.sum hleft hright
  unfold torusFourierSeries
  change (∑' i, centeredTerm i) =
    torusFourierSeries coefficient exponent phase - center
  rw [hsum.tsum_eq]
  ring

/-- Multiplying a Fourier series by one character translates every
exponent by that character. -/
theorem torusFourierSeries_mul_mFourier
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (twist : d → ℤ)
    (phase : UnitAddTorus d) :
  torusFourierSeries coefficient exponent phase *
        UnitAddTorus.mFourier twist phase =
      torusFourierSeries coefficient
        (fun i ↦ exponent i + twist) phase := by
  unfold torusFourierSeries
  rw [← tsum_mul_right]
  apply tsum_congr
  intro i
  unfold torusSeriesTerm
  rw [UnitAddTorus.mFourier_add]
  ring

/-- Symmetric left-multiplication form. -/
theorem mFourier_mul_torusFourierSeries
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (twist : d → ℤ)
    (phase : UnitAddTorus d) :
    UnitAddTorus.mFourier twist phase *
        torusFourierSeries coefficient exponent phase =
      torusFourierSeries coefficient
        (fun i ↦ twist + exponent i) phase := by
  calc
    UnitAddTorus.mFourier twist phase *
          torusFourierSeries coefficient exponent phase =
        torusFourierSeries coefficient exponent phase *
          UnitAddTorus.mFourier twist phase := by ring
    _ =
        torusFourierSeries coefficient
          (fun i ↦ exponent i + twist) phase :=
      torusFourierSeries_mul_mFourier
        coefficient exponent twist phase
    _ =
        torusFourierSeries coefficient
          (fun i ↦ twist + exponent i) phase := by
      congr 1
      funext i x
      exact add_comm (exponent i x) (twist x)

/-- The square of an absolutely convergent Fourier series is the double
series with product coefficients and summed exponents. -/
theorem torusFourierSeries_sq
    (coefficient : ι → ℂ)
    (exponent : ι → d → ℤ)
    (hcoefficient : Summable fun i ↦ ‖coefficient i‖)
    (phase : UnitAddTorus d) :
    torusFourierSeries coefficient exponent phase ^ 2 =
      torusFourierSeries
        (fun ij : ι × ι ↦ coefficient ij.1 * coefficient ij.2)
        (fun ij : ι × ι ↦ exponent ij.1 + exponent ij.2)
        phase := by
  let term : ι → ℂ :=
    fun i ↦ torusSeriesTerm coefficient exponent i phase
  have htermNorm : Summable fun i ↦ ‖term i‖ := by
    simpa only [term, norm_torusSeriesTerm] using hcoefficient
  unfold torusFourierSeries
  rw [pow_two, tsum_mul_tsum_of_summable_norm htermNorm htermNorm]
  apply tsum_congr
  intro ij
  unfold term torusSeriesTerm
  rw [UnitAddTorus.mFourier_add]
  ring

end HGAS.Analysis
