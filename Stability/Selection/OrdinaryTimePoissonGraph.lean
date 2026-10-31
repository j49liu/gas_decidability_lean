import Stability.Selection.OrdinaryTimeFourierInverse
import HGAS.Arithmetic.DetectorCharacterCode

/-!
# The reciprocal Poisson coordinates on the intended torus graph

The fourth-power clock convention makes each reciprocal a geometric
series in one integer character. Section 9's bound is exactly four when
the weighted character ratio is at most `3/4`.
-/

noncomputable section

open scoped BigOperators

namespace Stability.Selection

open HGAS

variable {eqs vars : ℕ}

/-- The two literal Poisson reciprocal coordinates are the cases
`sign = 1` and `sign = -1`. -/
def poissonReciprocalGraph (I : DQLSystem eqs vars) (j : Fin vars) (sign : ℤ)
    (x : UnitAddTorus (Fin (vars + eqs))) : ℂ :=
  (1 - (1 / 2 : ℂ) * UnitAddTorus.mFourier
    (fun i ↦ sign * DetectorCharacterCode.flattenCharacter
      (DetectorCharacterCode.poissonArgumentCharacter I j) i) x)⁻¹

private theorem poisson_denominator_ne_zero
    (I : DQLSystem eqs vars) (j : Fin vars) (sign : ℤ)
    (x : UnitAddTorus (Fin (vars + eqs))) :
    1 - (1 / 2 : ℂ) * UnitAddTorus.mFourier
      (fun i ↦ sign * DetectorCharacterCode.flattenCharacter
        (DetectorCharacterCode.poissonArgumentCharacter I j) i) x ≠ 0 := by
  intro hz
  have hn := congrArg norm (sub_eq_zero.mp hz)
  simp only [norm_one, norm_mul, norm_div, Complex.norm_ofNat,
    UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply,
    Circle.norm_coe, Finset.prod_const_one, mul_one] at hn
  norm_num at hn

theorem continuous_poissonReciprocalGraph
    (I : DQLSystem eqs vars) (j : Fin vars) (sign : ℤ) :
    Continuous (poissonReciprocalGraph I j sign) :=
  (continuous_const.sub (continuous_const.mul
    (UnitAddTorus.mFourier _).continuous)).inv₀ (poisson_denominator_ne_zero I j sign)

/-- The actual inverse graph relation holds at every torus phase. -/
theorem poissonReciprocalGraph_identity
    (I : DQLSystem eqs vars) (j : Fin vars) (sign : ℤ)
    (x : UnitAddTorus (Fin (vars + eqs))) :
    (1 - (1 / 2 : ℂ) * UnitAddTorus.mFourier
      (fun i ↦ sign * DetectorCharacterCode.flattenCharacter
        (DetectorCharacterCode.poissonArgumentCharacter I j) i) x) *
      poissonReciprocalGraph I j sign x = 1 :=
  mul_inv_cancel₀ (poisson_denominator_ne_zero I j sign x)

private theorem poissonExponent_length
    (I : DQLSystem eqs vars) (j : Fin vars) (sign : ℤ) (hsign : |(sign : ℝ)| = 1) :
    (∑ i, |((sign * DetectorCharacterCode.flattenCharacter
      (DetectorCharacterCode.poissonArgumentCharacter I j) i : ℤ) : ℝ)|) =
      4 + 4 * ∑ row, |(I.quadratic row j : ℝ)| := by
  classical
  simp only [Int.cast_mul, abs_mul, hsign, one_mul]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp [DetectorCharacterCode.flattenCharacter, DetectorCharacterCode.poissonArgumentCharacter,
    DetectorCharacterCode.privateCharacter, DetectorCharacterCode.quadraticCharacter,
    abs_mul, Finset.mul_sum, apply_ite abs]

/-- Both literal reciprocal coordinates have genuine weighted Fourier
norm at most four under the manuscript's columnwise sufficient bound. -/
theorem poissonReciprocalGraph_weightedFourier_bound
    (I : DQLSystem eqs vars) (j : Fin vars) (sign : ℤ) (hsign : |(sign : ℝ)| = 1)
    {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hratio : (1 / 2 : ℝ) * ρ ^ (4 + 4 * ∑ row, |(I.quadratic row j : ℝ)|) ≤ 3 / 4) :
    Summable (fun a : Fin (vars + eqs) → ℤ ↦
      ‖UnitAddTorus.mFourierCoeff (poissonReciprocalGraph I j sign) a‖ *
        ρ ^ (∑ i, |(a i : ℝ)|)) ∧
    (∑' a : Fin (vars + eqs) → ℤ,
      ‖UnitAddTorus.mFourierCoeff (poissonReciprocalGraph I j sign) a‖ *
        ρ ^ (∑ i, |(a i : ℝ)|)) ≤ 4 := by
  have hlength := poissonExponent_length I j sign hsign
  obtain ⟨hs, hb⟩ := exponential_fourierCoeff_reciprocal_character
    (fun i ↦ sign * DetectorCharacterCode.flattenCharacter
      (DetectorCharacterCode.poissonArgumentCharacter I j) i)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hρ (by rw [hlength]; linarith)
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hs hb
  refine ⟨hs, hb.trans ?_⟩
  rw [hlength]
  have hpos : 0 < 1 - (1 / 2 : ℝ) *
      ρ ^ (4 + 4 * ∑ row, |(I.quadratic row j : ℝ)|) := by linarith
  rw [← one_div]
  apply (div_le_iff₀ hpos).2
  linarith

end Stability.Selection
