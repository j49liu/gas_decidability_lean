import Stability.Selection.OrdinaryTimeRadicalFourierBudget
import HGAS.Clocks.ScaledRadicalClock

/-!
# The actual cohomological equation for radical clocks

The primitive uses the Haar coefficients of the original function.
Its derivative in physical time is the original function minus its
constant coefficient; the zero-mode condition is not presumed.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace Stability.Selection

open HGAS.Analysis HGAS.Clocks

/-- With no integer resonances, deleting resonant Fourier terms subtracts
exactly the actual constant coefficient. -/
theorem nonresonant_fourierSeries_eq_sub_zero {d : Type*} [Fintype d]
    (f : UnitAddTorus d → ℂ) (hc : Continuous f)
    (hf : Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff f a‖)
    (ω : d → ℝ) (hω : RadicalIndependence.HasNoNontrivialIntegerCharacter ω)
    (x : UnitAddTorus d) :
    torusFourierSeries (nonresonantCoefficient (UnitAddTorus.mFourierCoeff f) id ω) id x =
      f x - UnitAddTorus.mFourierCoeff f 0 := by
  have hz (a : d → ℤ) : RadicalClock.frequencyPairing a ω = 0 ↔ a = 0 := by
    constructor
    · exact hω a
    · rintro rfl
      simp [RadicalClock.frequencyPairing]
  let term := fun a ↦ torusSeriesTerm (UnitAddTorus.mFourierCoeff f) id a x
  have hs : Summable term := hf.of_norm_bounded fun a ↦
    (norm_torusSeriesTerm _ _ _ _).le
  have hsplit := hs.tsum_eq_add_tsum_ite 0
  have hzero : term 0 = UnitAddTorus.mFourierCoeff f 0 := by
    simp [term, torusSeriesTerm, UnitAddTorus.mFourier_zero]
  have hfull : (∑' a, term a) = f x :=
    congrFun (torusFourierSeries_fourierCoeff f hc hf) x
  rw [hzero, hfull] at hsplit
  have he (a : d → ℤ) :
      torusSeriesTerm (nonresonantCoefficient (UnitAddTorus.mFourierCoeff f) id ω) id a x =
        if a = 0 then 0 else term a := by
    by_cases ha : a = 0
    · simp [torusSeriesTerm, nonresonantCoefficient, hz, ha]
    · simp [torusSeriesTerm, nonresonantCoefficient, hz, ha, term]
  change (∑' a, torusSeriesTerm
    (nonresonantCoefficient (UnitAddTorus.mFourierCoeff f) id ω) id a x) = _
  rw [tsum_congr he]
  exact eq_sub_iff_add_eq.mpr (by rw [add_comm]; exact hsplit.symm)

/-- The actual Fourier primitive satisfies the centered cohomological
equation along every physical signed-prime-root orbit. -/
theorem radicalFourierPrimitive_hasDerivAt {d : Type*} [Fintype d]
    (p : d → ℕ) (hp : ∀ i, (p i).Prime) (hinjective : Function.Injective p)
    (sign : d → ℤ) (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (m : ℕ) (hm : 0 < m) (f : UnitAddTorus d → ℂ) (hc : Continuous f)
    (hf : Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff f a‖ *
      (1 + 1 / (m : ℝ)) ^ (∑ i, |(a i : ℝ)|))
    (x : UnitAddTorus d) (t : ℝ) :
    let ω := ScaledRadicalClock.scaledSignedPrimeSqrtFrequency (1 / (2 * Real.pi)) p sign
    HasDerivAt (fun s ↦ radicalFourierPrimitive p sign f
      (RadicalClock.torusTranslationFlow ω s x))
      (f (RadicalClock.torusTranslationFlow ω t x) - UnitAddTorus.mFourierCoeff f 0) t := by
  dsimp only
  have hρ : 1 ≤ 1 + 1 / (m : ℝ) := le_add_of_nonneg_right (by positivity)
  have hs := summable_norm_fourierCoeff_of_weighted f _
    (fun a ↦ Real.one_le_rpow hρ (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)) hf
  have hp' := (summable_primitiveCoefficient_of_exponential p hp hinjective sign hsign
    m hm (UnitAddTorus.mFourierCoeff f) id hf).1
  have hd := torusCohomologicalPrimitive_hasDerivAt (UnitAddTorus.mFourierCoeff f) id
    (ScaledRadicalClock.scaledSignedPrimeSqrtFrequency (1 / (2 * Real.pi)) p sign) hs hp' x t
  rw [nonresonant_fourierSeries_eq_sub_zero f hc hs _
    (ScaledRadicalClock.turnsNormalizedSignedPrimeSqrt_hasNoCharacter
      p hp hinjective sign hsign)] at hd
  exact hd

/-- Real functions give conjugate-symmetric actual Haar coefficients. -/
theorem fourierCoeff_real_neg {d : Type*} [Fintype d]
    (f : UnitAddTorus d → ℝ) (a : d → ℤ) :
    UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) (-a) =
      conj (UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) a) := by
  simpa only [Complex.conj_ofReal, neg_neg] using
    fourierCoeff_conj (fun x ↦ (f x : ℂ)) (-a)

/-- Division by the purely imaginary angular frequency preserves the
conjugate symmetry needed for a real primitive. -/
theorem primitiveCoefficient_conj {d : Type*} [Fintype d]
    (c : (d → ℤ) → ℂ) (hc : ∀ a, c (-a) = conj (c a))
    (ω : d → ℝ) (a : d → ℤ) :
    conj (cohomologicalPrimitiveCoefficient c id ω a) =
      cohomologicalPrimitiveCoefficient c id ω (-a) := by
  have hp : RadicalClock.frequencyPairing (-a) ω = -RadicalClock.frequencyPairing a ω := by
    simp [RadicalClock.frequencyPairing, Pi.neg_apply, Int.cast_neg,
      neg_mul, Finset.sum_neg_distrib]
  have ha : conj (torusAngularFrequency a ω) = torusAngularFrequency (-a) ω := by
    simp only [torusAngularFrequency, hp, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  by_cases h : RadicalClock.frequencyPairing a ω = 0
  · simp [cohomologicalPrimitiveCoefficient, hp, h]
  · simp [cohomologicalPrimitiveCoefficient, hp, h, ← hc a, ha]

/-- The primitive of a real-valued function is itself real-valued, not
merely a chosen real part of some complex solution. -/
theorem radicalFourierPrimitive_im_eq_zero {d : Type*} [Fintype d]
    (p : d → ℕ) (sign : d → ℤ) (f : UnitAddTorus d → ℝ)
    (x : UnitAddTorus d) :
    (radicalFourierPrimitive p sign (fun x ↦ (f x : ℂ)) x).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  unfold radicalFourierPrimitive torusCohomologicalPrimitive torusFourierSeries
  rw [Complex.conj_tsum]
  have he (a : d → ℤ) :
      conj (torusSeriesTerm
        (cohomologicalPrimitiveCoefficient (UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ))) id
          (fun i ↦ 1 / (2 * Real.pi) *
            RadicalIndependence.signedPrimeSqrtFrequency p sign i)) id a x) =
      torusSeriesTerm
        (cohomologicalPrimitiveCoefficient (UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ))) id
          (fun i ↦ 1 / (2 * Real.pi) *
            RadicalIndependence.signedPrimeSqrtFrequency p sign i)) id (-a) x := by
    simp only [torusSeriesTerm, id_eq, map_mul,
      primitiveCoefficient_conj _ (fourierCoeff_real_neg f), ← UnitAddTorus.mFourier_neg]
  rw [tsum_congr he]
  exact (Equiv.neg (d → ℤ)).tsum_eq (fun a ↦ torusSeriesTerm
    (cohomologicalPrimitiveCoefficient (UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ))) id
      (fun i ↦ 1 / (2 * Real.pi) *
        RadicalIndependence.signedPrimeSqrtFrequency p sign i)) id a x)

end Stability.Selection
