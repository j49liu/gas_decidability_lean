import HGAS.Modular.UnaryMomentResonance

/-!
# Finite-moment selection for unary theta expansions

`UnaryMomentResonance` computes the exact Cesàro limits of the mean and
first Fourier moment of the three unary theta characteristics.  This file
turns those computations into the logical implications used by the
selector.

The point is deliberately elementary and reusable.  Once a global
classification theorem has represented a recurrent trajectory by an
absolutely summable integer-square or half-square expansion:

* its ordinary mean determines the constant coefficient;
* a half-square characteristic cannot have a nonzero mean;
* reversed orientation cannot have a nonzero first moment; and
* among the two unit orientations, a nonzero first moment selects the
  forward orientation.

Thus the dynamical classification and the finite algebraic selector are
kept logically separate.
-/

namespace HGAS.Modular

open Filter Topology

noncomputable section

/-- If an integer-square expansion has a prescribed mean limit, that
limit is exactly its constant coefficient. -/
theorem constantCoefficient_eq_of_integerSquareMean_tendsto
    (coefficient : ℤ → ℂ)
    (hsum : Summable fun n ↦ ‖coefficient n‖)
    {Ω s : ℝ} (hΩ : Ω ≠ 0) (hs : s ≠ 0)
    {L : ℂ}
    (hL :
      Tendsto
        (fun N ↦ HGAS.Analysis.naturalCesaroMean
          (integerSquareMomentSeries coefficient Ω s 0) N)
        atTop (𝓝 L)) :
    coefficient 0 = L := by
  exact tendsto_nhds_unique
    (naturalCesaroMean_integerSquareMean_tendsto
      coefficient hsum hΩ hs)
    hL

/-- A half-square characteristic cannot satisfy a nonzero mean
normalization. -/
theorem halfSquareMean_ne_nonzero
    (coefficient : ℤ → ℂ)
    (hsum : Summable fun n ↦ ‖coefficient n‖)
    {Ω s : ℝ} (hΩ : Ω ≠ 0) (hs : s ≠ 0)
    {L : ℂ} (hL : L ≠ 0) :
    ¬ Tendsto
        (fun N ↦ HGAS.Analysis.naturalCesaroMean
          (halfSquareMomentSeries coefficient Ω s 0) N)
        atTop (𝓝 L) := by
  intro hlimit
  have hzero : (0 : ℂ) = L :=
    tendsto_nhds_unique
      (naturalCesaroMean_halfSquareMean_tendsto_zero
        coefficient hsum hΩ hs)
      hlimit
  exact hL hzero.symm

/-- Reversed orientation cannot satisfy a nonzero first-moment
normalization. -/
theorem reversedOrientationFirstMoment_ne_nonzero
    (coefficient : ℤ → ℂ)
    (hsum : Summable fun n ↦ ‖coefficient n‖)
    {Ω : ℝ} (hΩ : Ω ≠ 0)
    {L : ℂ} (hL : L ≠ 0) :
    ¬ Tendsto
        (fun N ↦ HGAS.Analysis.naturalCesaroMean
          (integerSquareMomentSeries coefficient Ω (-1) 1) N)
        atTop (𝓝 L) := by
  intro hlimit
  have hzero : (0 : ℂ) = L :=
    tendsto_nhds_unique
      (naturalCesaroMean_integerSquareFirst_neg_tendsto_zero
        coefficient hsum hΩ)
      hlimit
  exact hL hzero.symm

/-- The first-moment limit of a forward unit-orientation expansion is
the sum of precisely its two resonant coefficients. -/
theorem firstResonantSum_eq_of_forwardMoment_tendsto
    (coefficient : ℤ → ℂ)
    (hsum : Summable fun n ↦ ‖coefficient n‖)
    {Ω : ℝ} (hΩ : Ω ≠ 0)
    {L : ℂ}
    (hL :
      Tendsto
        (fun N ↦ HGAS.Analysis.naturalCesaroMean
          (integerSquareMomentSeries coefficient Ω 1 1) N)
        atTop (𝓝 L)) :
    (∑' n : ℤ,
      if n = 1 ∨ n = -1 then coefficient n else 0) = L := by
  exact tendsto_nhds_unique
    (naturalCesaroMean_integerSquareFirst_one_tendsto
      coefficient hsum hΩ)
    hL

/-- A real scalar whose square is one has one of the two unit
orientations. -/
theorem eq_one_or_neg_one_of_sq_eq_one
    {s : ℝ} (hs : s ^ 2 = 1) :
    s = 1 ∨ s = -1 :=
  sq_eq_one_iff.mp hs

/-- Among the two unit orientations, a nonzero first-moment
normalization forces the forward orientation. -/
theorem forwardOrientation_of_unit_and_nonzero_firstMoment
    (coefficient : ℤ → ℂ)
    (hsum : Summable fun n ↦ ‖coefficient n‖)
    {Ω s : ℝ} (hΩ : Ω ≠ 0)
    (hs : s = 1 ∨ s = -1)
    {L : ℂ} (hL : L ≠ 0)
    (hlimit :
      Tendsto
        (fun N ↦ HGAS.Analysis.naturalCesaroMean
          (integerSquareMomentSeries coefficient Ω s 1) N)
        atTop (𝓝 L)) :
    s = 1 := by
  rcases hs with hs | hs
  · exact hs
  · subst s
    exact False.elim
      (reversedOrientationFirstMoment_ne_nonzero
        coefficient hsum hΩ hL hlimit)

end

end HGAS.Modular
