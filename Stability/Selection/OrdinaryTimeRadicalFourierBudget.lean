import Stability.Selection.OrdinaryTimeSourcePolynomialBudget
import HGAS.Analysis.RadicalFourierPrimitiveBounds
import HGAS.Clocks.ExplicitRadicalDegreeBound

/-!
# Exponential Fourier bounds for radical-clock primitives

An explicit polynomial-versus-exponential estimate absorbs the radical
small divisor. Frequencies are measured in fundamental turns, so the
physical signed square-root clock uses the factor `1/(2π)`.
-/

noncomputable section

open scoped BigOperators

namespace Stability.Selection

open HGAS.Analysis HGAS.Clocks

/-- A factorial/binomial bound valid also at degree zero and index zero. -/
theorem polynomial_le_geometric_radius (m s n : ℕ) (hm : 0 < m) :
    (1 + (n : ℝ)) ^ s ≤ (s.factorial * (2 * m) ^ s : ℕ) *
      (1 + 1 / (m : ℝ)) ^ n := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hr : 1 + 1 / (m : ℝ) ≤ 2 := by
    have hi : 1 / (m : ℝ) ≤ 1 := (div_le_one hm0).2 hm1
    linarith
  have hchoose : ((n + s).choose s : ℝ) * (1 / (m : ℝ)) ^ s ≤
      (1 + 1 / (m : ℝ)) ^ (n + s) := by
    rw [add_pow]
    have ht := Finset.single_le_sum
      (s := Finset.range (n + s + 1))
      (f := fun k ↦ (1 : ℝ) ^ k * (1 / (m : ℝ)) ^ (n + s - k) *
        ((n + s).choose k : ℝ))
      (fun _ _ ↦ by positivity) (show n ∈ Finset.range (n + s + 1) by simp)
    simpa only [one_pow, one_mul, Nat.add_sub_cancel_left, Nat.choose_symm_add,
      mul_comm] using ht
  have hchoose' : ((n + s).choose s : ℝ) ≤
      (m : ℝ) ^ s * (1 + 1 / (m : ℝ)) ^ (n + s) := by
    have h := mul_le_mul_of_nonneg_left hchoose (pow_nonneg hm0.le s)
    have hcancel : (m : ℝ) ^ s * (1 / (m : ℝ)) ^ s = 1 := by
      rw [← mul_pow, mul_one_div_cancel hm0.ne', one_pow]
    calc
      _ = (m : ℝ) ^ s * (((n + s).choose s : ℝ) * (1 / (m : ℝ)) ^ s) := by
        rw [mul_left_comm, hcancel, mul_one]
      _ ≤ _ := h
  have hnat : (n + 1) ^ s ≤ s.factorial * (n + s).choose s :=
    (Nat.pow_succ_le_ascFactorial (n + 1) s).trans_eq
      (Nat.ascFactorial_eq_factorial_mul_choose n s)
  have hpoly : (1 + (n : ℝ)) ^ s ≤ (s.factorial : ℝ) * ((n + s).choose s : ℝ) := by
    exact_mod_cast (by simpa only [add_comm] using hnat)
  calc
    _ ≤ (s.factorial : ℝ) * ((m : ℝ) ^ s * (1 + 1 / (m : ℝ)) ^ (n + s)) :=
      hpoly.trans (mul_le_mul_of_nonneg_left hchoose' (Nat.cast_nonneg _))
    _ = (s.factorial : ℝ) * (m : ℝ) ^ s * (1 + 1 / (m : ℝ)) ^ s *
        (1 + 1 / (m : ℝ)) ^ n := by rw [pow_add]; ring
    _ ≤ (s.factorial : ℝ) * (m : ℝ) ^ s * 2 ^ s *
        (1 + 1 / (m : ℝ)) ^ n := by
      gcongr
    _ = _ := by push_cast; rw [mul_pow]; ring

/-- A computable small-divisor multiplier at radius `1+1/m`. -/
def radicalFourierBudget {d : Type*} [Fintype d] (p : d → ℕ) (m : ℕ) : ℕ :=
  let s := 2 ^ Fintype.card d - 1
  (1 + ∑ i, p i) ^ s * (s.factorial * (2 * m) ^ s)

/-- The exact algebraic height power is bounded by an explicit
exponential lattice weight. No field-degree computation is required. -/
theorem radical_height_power_le_exponential {d : Type*} [Fintype d]
    (p : d → ℕ) (m : ℕ) (hm : 0 < m) (a : d → ℤ) :
    RadicalSmallDivisor.radicalConjugateHeight p a ^
        (RadicalSmallDivisor.radicalDegree p - 1) ≤
      (radicalFourierBudget p m : ℝ) *
        (1 + 1 / (m : ℝ)) ^ (∑ i, |(a i : ℝ)|) := by
  let R : ℕ := 1 + ∑ i, p i
  let n : ℕ := ∑ i, (a i).natAbs
  let s : ℕ := 2 ^ Fintype.card d - 1
  have hR : (1 : ℝ) ≤ R := by
    dsimp [R]
    exact_mod_cast (show 1 ≤ 1 + ∑ i, p i by omega)
  have hn : (n : ℝ) = ∑ i, |(a i : ℝ)| := by
    simp [n, Nat.cast_sum, Nat.cast_natAbs, Int.cast_abs]
  have hroot (i : d) : Real.sqrt (p i : ℝ) ≤ R := by
    have hsingle : p i ≤ ∑ j, p j :=
      Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    have hp : (p i : ℝ) + 1 ≤ R := by dsimp [R]; exact_mod_cast (by omega : p i + 1 ≤ 1 + ∑ j, p j)
    refine (show Real.sqrt (p i : ℝ) ≤ (p i : ℝ) + 1 from ?_).trans hp
    apply (Real.sqrt_le_left (by positivity)).2
    nlinarith [sq_nonneg (p i : ℝ), show (0 : ℝ) ≤ p i by positivity]
  have hheight : RadicalSmallDivisor.radicalConjugateHeight p a ≤ (R : ℝ) * n := by
    rw [hn, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hroot i) (abs_nonneg (a i : ℝ))
  have hheight' : RadicalSmallDivisor.radicalConjugateHeight p a ≤ (R : ℝ) * (1 + n) := by
    nlinarith [show 0 ≤ (R : ℝ) by positivity]
  have hbase : 1 ≤ (R : ℝ) * (1 + n) :=
    one_le_mul_of_one_le_of_one_le hR (by linarith [show (0 : ℝ) ≤ n by positivity])
  have hdegree : RadicalSmallDivisor.radicalDegree p - 1 ≤ s :=
    Nat.sub_le_sub_right (RadicalSmallDivisor.radicalDegree_le_two_pow_card p) 1
  calc
    _ ≤ ((R : ℝ) * (1 + n)) ^ (RadicalSmallDivisor.radicalDegree p - 1) :=
      pow_le_pow_left₀ (RadicalSmallDivisor.radicalConjugateHeight_nonneg p a) hheight' _
    _ ≤ ((R : ℝ) * (1 + n)) ^ s := pow_le_pow_right₀ hbase hdegree
    _ = (R : ℝ) ^ s * (1 + (n : ℝ)) ^ s := mul_pow _ _ _
    _ ≤ (R : ℝ) ^ s * ((s.factorial * (2 * m) ^ s : ℕ) *
        (1 + 1 / (m : ℝ)) ^ n) :=
      mul_le_mul_of_nonneg_left (polynomial_le_geometric_radius m s n hm) (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast (1 + 1 / (m : ℝ)) n, hn]
      simp only [radicalFourierBudget, R, s, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
        Nat.cast_one, Nat.cast_sum]
      ring

/-- At the physical angular normalization, the primitive coefficient
is controlled by a wholly arithmetic multiple of the exponential weight. -/
theorem primitiveCoefficient_le_exponential {d : Type*} [Fintype d]
    (p : d → ℕ) (hp : ∀ i, (p i).Prime) (hinjective : Function.Injective p)
    (sign : d → ℤ) (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (m : ℕ) (hm : 0 < m) (c : ℂ) (a : d → ℤ) :
    ‖cohomologicalPrimitiveCoefficient (fun _ : Unit ↦ c) (fun _ : Unit ↦ a)
      (fun i ↦ (1 / (2 * Real.pi)) *
        RadicalIndependence.signedPrimeSqrtFrequency p sign i) ()‖ ≤
      (radicalFourierBudget p m : ℝ) *
        (‖c‖ * (1 + 1 / (m : ℝ)) ^ (∑ i, |(a i : ℝ)|)) := by
  have h := norm_cohomologicalPrimitiveCoefficient_le_radicalMajorant
    (1 / (2 * Real.pi)) (by positivity) p hp hinjective sign hsign c a
  have hden : 2 * Real.pi * |1 / (2 * Real.pi)| = 1 := by
    rw [abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
    field_simp [Real.pi_ne_zero]
  dsimp only [radicalPrimitiveCoefficientMajorant] at h
  rw [hden, div_one] at h
  refine h.trans ?_
  have hb := mul_le_mul_of_nonneg_left (radical_height_power_le_exponential p m hm a)
    (norm_nonneg c)
  simpa only [mul_left_comm] using hb

/-- Exponential absolute summability controls the actual inverse-frequency
coefficients and their full sum by the explicit arithmetic budget. -/
theorem summable_primitiveCoefficient_of_exponential {d ι : Type*} [Fintype d]
    (p : d → ℕ) (hp : ∀ i, (p i).Prime) (hinjective : Function.Injective p)
    (sign : d → ℤ) (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (m : ℕ) (hm : 0 < m) (c : ι → ℂ) (e : ι → d → ℤ)
    (hc : Summable fun k ↦ ‖c k‖ *
      (1 + 1 / (m : ℝ)) ^ (∑ i, |(e k i : ℝ)|)) :
    Summable (fun k ↦ ‖cohomologicalPrimitiveCoefficient c e
      (fun i ↦ (1 / (2 * Real.pi)) *
        RadicalIndependence.signedPrimeSqrtFrequency p sign i) k‖) ∧
    (∑' k, ‖cohomologicalPrimitiveCoefficient c e
      (fun i ↦ (1 / (2 * Real.pi)) *
        RadicalIndependence.signedPrimeSqrtFrequency p sign i) k‖) ≤
      (radicalFourierBudget p m : ℝ) *
        ∑' k, ‖c k‖ * (1 + 1 / (m : ℝ)) ^ (∑ i, |(e k i : ℝ)|) := by
  have hb (k) := primitiveCoefficient_le_exponential p hp hinjective sign hsign m hm (c k) (e k)
  have hs := hc.mul_left (radicalFourierBudget p m : ℝ)
  have ht := hs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hb
  refine ⟨ht, ?_⟩
  exact (ht.tsum_le_tsum hb hs).trans_eq tsum_mul_left

/-- The literal primitive of the actual Haar coefficients, in physical
time rather than an independently rescaled recurrence parameter. -/
def radicalFourierPrimitive {d : Type*} [Fintype d]
    (p : d → ℕ) (sign : d → ℤ) (f : UnitAddTorus d → ℂ) : UnitAddTorus d → ℂ :=
  torusCohomologicalPrimitive (UnitAddTorus.mFourierCoeff f) id
    (fun i ↦ (1 / (2 * Real.pi)) * RadicalIndependence.signedPrimeSqrtFrequency p sign i)

/-- The actual Fourier primitive is continuous and has a numerical
bound in terms of the exponential Fourier norm. -/
theorem radicalFourierPrimitive_continuous_bound {d : Type*} [Fintype d]
    (p : d → ℕ) (hp : ∀ i, (p i).Prime) (hinjective : Function.Injective p)
    (sign : d → ℤ) (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (m : ℕ) (hm : 0 < m) (f : UnitAddTorus d → ℂ)
    (hf : Summable fun a ↦ ‖UnitAddTorus.mFourierCoeff f a‖ *
      (1 + 1 / (m : ℝ)) ^ (∑ i, |(a i : ℝ)|)) :
    Continuous (radicalFourierPrimitive p sign f) ∧ ∀ x,
      ‖radicalFourierPrimitive p sign f x‖ ≤ (radicalFourierBudget p m : ℝ) *
        ∑' a, ‖UnitAddTorus.mFourierCoeff f a‖ *
          (1 + 1 / (m : ℝ)) ^ (∑ i, |(a i : ℝ)|) := by
  obtain ⟨hs, hb⟩ := summable_primitiveCoefficient_of_exponential p hp hinjective sign hsign
    m hm (UnitAddTorus.mFourierCoeff f) id hf
  exact ⟨continuous_torusCohomologicalPrimitive _ _ _ hs,
    fun x ↦ (norm_torusCohomologicalPrimitive_le _ _ _ hs x).trans hb⟩

end Stability.Selection
