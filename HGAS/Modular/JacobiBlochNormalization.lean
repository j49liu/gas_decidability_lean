import HGAS.Modular.JacobiReflectedTrace
import Mathlib.Tactic

/-!
# Normalization of the reflected Jacobi Bloch coefficients

The mean and first twisted moment equations leave a reflected Bloch
class.  After reindexing its Bloch shift to `-ρ`, the two scalar
normalizations in equation (8.22) of the paper are

```
D = exp (-q ρ²) exp (i ρ χ),
B = exp (2 q ρ) exp (-2 i χ),
```

where `q = log λ`.  The `k`-th constant coefficient is then

```
D exp (q (k-ρ)²) B^k exp (i (k-ρ)χ)
  = exp (q k²) exp (-i kχ).
```

This file proves that cancellation exactly and combines it with the
already formalized reflection `k ↦ -k`.  We write `B^k` in its selected
exponential form; this avoids an irrelevant branch choice for a complex
logarithm.
-/

namespace HGAS.Modular

noncomputable section

/-- The positive Gaussian coefficient with logarithmic nome `q`. -/
def jacobiGaussianCoefficient (q x : ℝ) : ℂ :=
  (Real.exp (q * x ^ 2) : ℝ)

@[simp]
theorem jacobiUnitPhase_add (x y : ℝ) :
    jacobiUnitPhase (x + y) =
      jacobiUnitPhase x * jacobiUnitPhase y := by
  simp only [jacobiUnitPhase,
    HGAS.Analysis.realFrequencyExponential]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp]
theorem jacobiUnitPhase_zero :
    jacobiUnitPhase 0 = 1 := by
  simp [jacobiUnitPhase,
    HGAS.Analysis.realFrequencyExponential]

@[simp]
theorem jacobiUnitPhase_neg (x : ℝ) :
    jacobiUnitPhase (-x) =
      (jacobiUnitPhase x)⁻¹ := by
  simp [jacobiUnitPhase,
    HGAS.Analysis.realFrequencyExponential,
    Complex.exp_neg]

/-- The selected scalar `D` of the reflected branch. -/
def reflectedBlochAmplitude (q ρ χ : ℝ) : ℂ :=
  (Real.exp (-q * ρ ^ 2) : ℝ) *
    jacobiUnitPhase (ρ * χ)

/-- The selected elliptic multiplier
`B = exp(2qρ) exp(-2iχ)` from equation (8.22). -/
def reflectedBlochMultiplier (q ρ χ : ℝ) : ℂ :=
  (Real.exp (2 * q * ρ) : ℝ) *
    jacobiUnitPhase (-2 * χ)

/-- The `k`-th power of the selected elliptic multiplier `B`, written
without choosing a complex logarithm. -/
def reflectedBlochMultiplierPower
    (q ρ χ : ℝ) (k : ℤ) : ℂ :=
  (Real.exp (2 * q * ρ * (k : ℝ)) : ℝ) *
    jacobiUnitPhase (-2 * (k : ℝ) * χ)

theorem jacobiUnitPhase_ne_zero (θ : ℝ) :
    jacobiUnitPhase θ ≠ 0 := by
  intro hzero
  have hnorm := norm_jacobiUnitPhase θ
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

theorem jacobiGaussianCoefficient_ne_zero
    (q x : ℝ) :
    jacobiGaussianCoefficient q x ≠ 0 := by
  unfold jacobiGaussianCoefficient
  exact Complex.ofReal_ne_zero.mpr
    (Real.exp_ne_zero (q * x ^ 2))

theorem reflectedBlochAmplitude_ne_zero
    (q ρ χ : ℝ) :
    reflectedBlochAmplitude q ρ χ ≠ 0 := by
  exact
    mul_ne_zero
      (by
        exact Complex.ofReal_ne_zero.mpr
          (Real.exp_ne_zero (-q * ρ ^ 2)))
      (jacobiUnitPhase_ne_zero (ρ * χ))

theorem reflectedBlochMultiplier_ne_zero
    (q ρ χ : ℝ) :
    reflectedBlochMultiplier q ρ χ ≠ 0 := by
  exact
    mul_ne_zero
      (by
        exact_mod_cast
          Real.exp_ne_zero (2 * q * ρ))
      (jacobiUnitPhase_ne_zero (-2 * χ))

@[simp]
theorem reflectedBlochMultiplierPower_one
    (q ρ χ : ℝ) :
    reflectedBlochMultiplierPower q ρ χ 1 =
      reflectedBlochMultiplier q ρ χ := by
  simp only [reflectedBlochMultiplierPower,
    reflectedBlochMultiplier, Int.cast_one, mul_one]

@[simp]
theorem reflectedBlochMultiplierPower_neg_one
    (q ρ χ : ℝ) :
    reflectedBlochMultiplierPower q ρ χ (-1) =
      (reflectedBlochMultiplier q ρ χ)⁻¹ := by
  rw [reflectedBlochMultiplierPower,
    reflectedBlochMultiplier]
  push_cast
  rw [mul_inv_rev]
  simp [Complex.exp_neg, jacobiUnitPhase_neg]
  ring

/-- The unique reflected-class coefficient that survives the mean row
after reindexing `a₀=-ρ`. -/
def reflectedMeanMomentCoefficient
    (q ρ χ : ℝ) (D : ℂ) : ℂ :=
  D *
    (jacobiGaussianCoefficient q (-ρ) *
      jacobiUnitPhase (-ρ * χ))

/-- The unique reflected root in the `(1,1)` row is `k=-1`.  Twisting by
`exp(-i(α+β))` contributes the additional constant phase `exp(-iχ)`. -/
def reflectedPlusOneMomentCoefficient
    (q ρ χ : ℝ) (D B : ℂ) : ℂ :=
  (D *
      jacobiGaussianCoefficient q (-1 - ρ) *
      jacobiUnitPhase ((-1 - ρ) * χ) *
      jacobiUnitPhase (-χ)) *
    B⁻¹

/-- Mean-one coefficient equation on the reindexed reflected branch. -/
def ReflectedMeanCoefficientEquation
    (q ρ χ : ℝ) (D : ℂ) : Prop :=
  reflectedMeanMomentCoefficient q ρ χ D = 1

/-- The reflected `(1,1)` coefficient equation.  The right side is
`exp(q)`, i.e. `λ` when `q=log λ`. -/
def ReflectedPlusOneCoefficientEquation
    (q ρ χ : ℝ) (D B : ℂ) : Prop :=
  reflectedPlusOneMomentCoefficient q ρ χ D B =
    jacobiGaussianCoefficient q 1

/-- The complete time-independent coefficient of the reindexed reflected
Bloch term. -/
def normalizedReflectedBlochCoefficient
    (q ρ χ : ℝ) (k : ℤ) : ℂ :=
  reflectedBlochAmplitude q ρ χ *
    jacobiGaussianCoefficient q ((k : ℝ) - ρ) *
    reflectedBlochMultiplierPower q ρ χ k *
    jacobiUnitPhase (((k : ℝ) - ρ) * χ)

/-- Exact coefficient cancellation in equation (8.22). -/
theorem normalizedReflectedBlochCoefficient_eq
    (q ρ χ : ℝ) (k : ℤ) :
    normalizedReflectedBlochCoefficient q ρ χ k =
      jacobiGaussianCoefficient q (k : ℝ) *
        jacobiUnitPhase (-(k : ℝ) * χ) := by
  have hamplitude :
      Real.exp (-q * ρ ^ 2) *
          Real.exp (q * ((k : ℝ) - ρ) ^ 2) *
          Real.exp (2 * q * ρ * (k : ℝ)) =
        Real.exp (q * (k : ℝ) ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hphase :
      jacobiUnitPhase (ρ * χ) *
          jacobiUnitPhase (-2 * (k : ℝ) * χ) *
          jacobiUnitPhase (((k : ℝ) - ρ) * χ) =
        jacobiUnitPhase (-(k : ℝ) * χ) := by
    rw [← jacobiUnitPhase_add, ← jacobiUnitPhase_add]
    congr 1
    ring
  have hamplitudeComplex :
      (Real.exp (-q * ρ ^ 2) : ℂ) *
          (Real.exp (q * ((k : ℝ) - ρ) ^ 2) : ℂ) *
          (Real.exp (2 * q * ρ * (k : ℝ)) : ℂ) =
        (Real.exp (q * (k : ℝ) ^ 2) : ℂ) := by
    exact_mod_cast hamplitude
  unfold normalizedReflectedBlochCoefficient
    reflectedBlochAmplitude
    reflectedBlochMultiplierPower
    jacobiGaussianCoefficient
  calc
    ((Real.exp (-q * ρ ^ 2) : ℂ) *
          jacobiUnitPhase (ρ * χ)) *
        (Real.exp (q * ((k : ℝ) - ρ) ^ 2) : ℂ) *
        ((Real.exp (2 * q * ρ * (k : ℝ)) : ℂ) *
          jacobiUnitPhase (-2 * (k : ℝ) * χ)) *
        jacobiUnitPhase (((k : ℝ) - ρ) * χ) =
      ((Real.exp (-q * ρ ^ 2) : ℂ) *
          (Real.exp (q * ((k : ℝ) - ρ) ^ 2) : ℂ) *
          (Real.exp (2 * q * ρ * (k : ℝ)) : ℂ)) *
        (jacobiUnitPhase (ρ * χ) *
          jacobiUnitPhase (-2 * (k : ℝ) * χ) *
          jacobiUnitPhase (((k : ℝ) - ρ) * χ)) := by
            ring
    _ =
      (Real.exp (q * (k : ℝ) ^ 2) : ℂ) *
        jacobiUnitPhase (-(k : ℝ) * χ) := by
          rw [hamplitudeComplex, hphase]

/-! ## The moment equations force the selected parameters -/

/-- The displayed amplitude satisfies the mean-one coefficient equation. -/
theorem reflectedMeanCoefficientEquation_amplitude
    (q ρ χ : ℝ) :
    ReflectedMeanCoefficientEquation q ρ χ
      (reflectedBlochAmplitude q ρ χ) := by
  have h :=
    normalizedReflectedBlochCoefficient_eq
      q ρ χ 0
  rw [ReflectedMeanCoefficientEquation]
  calc
    reflectedMeanMomentCoefficient q ρ χ
          (reflectedBlochAmplitude q ρ χ) =
        normalizedReflectedBlochCoefficient
          q ρ χ 0 := by
      unfold reflectedMeanMomentCoefficient
        normalizedReflectedBlochCoefficient
        reflectedBlochMultiplierPower
      simp [jacobiUnitPhase_zero]
      ring
    _ =
        jacobiGaussianCoefficient q (0 : ℝ) *
          jacobiUnitPhase (-(0 : ℝ) * χ) := by
      simpa using h
    _ = 1 := by
      simp [jacobiGaussianCoefficient]

/-- The mean equation does not merely accept the displayed amplitude: it
forces it uniquely. -/
theorem reflectedMeanCoefficientEquation_iff
    (q ρ χ : ℝ) (D : ℂ) :
    ReflectedMeanCoefficientEquation q ρ χ D ↔
      D = reflectedBlochAmplitude q ρ χ := by
  let factor : ℂ :=
    jacobiGaussianCoefficient q (-ρ) *
      jacobiUnitPhase (-ρ * χ)
  have hfactor : factor ≠ 0 := by
    exact
      mul_ne_zero
        (jacobiGaussianCoefficient_ne_zero q (-ρ))
        (jacobiUnitPhase_ne_zero (-ρ * χ))
  constructor
  · intro hD
    apply mul_right_cancel₀ hfactor
    calc
      D * factor = 1 := by
        simpa only [ReflectedMeanCoefficientEquation,
          reflectedMeanMomentCoefficient, factor] using hD
      _ =
          reflectedBlochAmplitude q ρ χ *
            factor := by
        symm
        simpa only [ReflectedMeanCoefficientEquation,
          reflectedMeanMomentCoefficient, factor] using
            reflectedMeanCoefficientEquation_amplitude
              q ρ χ
  · rintro rfl
    exact reflectedMeanCoefficientEquation_amplitude q ρ χ

/-- The displayed amplitude and elliptic multiplier satisfy the reflected
`(1,1)` coefficient equation. -/
theorem reflectedPlusOneCoefficientEquation_selected
    (q ρ χ : ℝ) :
    ReflectedPlusOneCoefficientEquation q ρ χ
      (reflectedBlochAmplitude q ρ χ)
      (reflectedBlochMultiplier q ρ χ) := by
  have h :=
    normalizedReflectedBlochCoefficient_eq
      q ρ χ (-1)
  have hnormalized :
      normalizedReflectedBlochCoefficient q ρ χ (-1) *
          jacobiUnitPhase (-χ) =
        jacobiGaussianCoefficient q 1 := by
    rw [h]
    simp only [Int.cast_neg, Int.cast_one,
      neg_neg, one_mul]
    calc
      jacobiGaussianCoefficient q (-1) *
            jacobiUnitPhase χ *
            jacobiUnitPhase (-χ) =
          jacobiGaussianCoefficient q (-1) *
            (jacobiUnitPhase χ *
              jacobiUnitPhase (-χ)) := by ring
      _ =
          jacobiGaussianCoefficient q (-1) *
            jacobiUnitPhase (χ + -χ) := by
              rw [jacobiUnitPhase_add]
      _ = jacobiGaussianCoefficient q 1 := by
        simp [jacobiGaussianCoefficient]
  rw [ReflectedPlusOneCoefficientEquation,
    reflectedPlusOneMomentCoefficient]
  rw [← hnormalized]
  unfold normalizedReflectedBlochCoefficient
  rw [reflectedBlochMultiplierPower_neg_one]
  ring_nf

/-- The mean and reflected `(1,1)` equations jointly force exactly the
parameters displayed in equation (8.22). -/
theorem reflectedMean_plusOneCoefficientEquations_iff
    (q ρ χ : ℝ) (D B : ℂ) :
    (ReflectedMeanCoefficientEquation q ρ χ D ∧
      ReflectedPlusOneCoefficientEquation q ρ χ D B) ↔
    (D = reflectedBlochAmplitude q ρ χ ∧
      B = reflectedBlochMultiplier q ρ χ) := by
  constructor
  · rintro ⟨hmean, hplus⟩
    have hD :=
      (reflectedMeanCoefficientEquation_iff
        q ρ χ D).mp hmean
    refine ⟨hD, ?_⟩
    subst D
    let prefactor : ℂ :=
      reflectedBlochAmplitude q ρ χ *
        jacobiGaussianCoefficient q (-1 - ρ) *
        jacobiUnitPhase ((-1 - ρ) * χ) *
        jacobiUnitPhase (-χ)
    have hprefactor : prefactor ≠ 0 := by
      dsimp only [prefactor]
      exact
        mul_ne_zero
          (mul_ne_zero
            (mul_ne_zero
              (reflectedBlochAmplitude_ne_zero q ρ χ)
              (jacobiGaussianCoefficient_ne_zero
                q (-1 - ρ)))
            (jacobiUnitPhase_ne_zero
              ((-1 - ρ) * χ)))
          (jacobiUnitPhase_ne_zero (-χ))
    have hinv :
        B⁻¹ =
          (reflectedBlochMultiplier q ρ χ)⁻¹ := by
      apply mul_left_cancel₀ hprefactor
      calc
        prefactor * B⁻¹ =
            jacobiGaussianCoefficient q 1 := by
          simpa only [ReflectedPlusOneCoefficientEquation,
            reflectedPlusOneMomentCoefficient,
            prefactor] using hplus
        _ =
            prefactor *
              (reflectedBlochMultiplier q ρ χ)⁻¹ := by
          symm
          simpa only [ReflectedPlusOneCoefficientEquation,
            reflectedPlusOneMomentCoefficient,
            prefactor] using
              reflectedPlusOneCoefficientEquation_selected
                q ρ χ
    exact inv_injective hinv
  · rintro ⟨rfl, rfl⟩
    exact
      ⟨reflectedMeanCoefficientEquation_amplitude q ρ χ,
        reflectedPlusOneCoefficientEquation_selected q ρ χ⟩

/-- Once the mean row has fixed the reflected amplitude, the `(1,1)`
coefficient equation is equivalent to the displayed elliptic
multiplier. -/
theorem reflectedPlusOneCoefficientEquation_iff
    (q ρ χ : ℝ) (B : ℂ) :
    ReflectedPlusOneCoefficientEquation q ρ χ
        (reflectedBlochAmplitude q ρ χ) B ↔
      B = reflectedBlochMultiplier q ρ χ := by
  constructor
  · intro hplus
    exact
      ((reflectedMean_plusOneCoefficientEquations_iff
        q ρ χ (reflectedBlochAmplitude q ρ χ) B).mp
        ⟨reflectedMeanCoefficientEquation_amplitude q ρ χ,
          hplus⟩).2
  · rintro rfl
    exact reflectedPlusOneCoefficientEquation_selected q ρ χ

/-- The complete reflected Bloch term after imposing the two scalar
moment normalizations. -/
def normalizedReflectedBlochTerm
    (q ρ χ α : ℝ) (k : ℤ) : ℂ :=
  normalizedReflectedBlochCoefficient q ρ χ k *
    jacobiUnitPhase
      ((((k : ℝ) ^ 2) - ρ * (k : ℝ)) * α)

/-- A selected reflected Bloch term is exactly the abstract reflected
trace term with Gaussian coefficient. -/
theorem normalizedReflectedBlochTerm_eq_reflected
    (q ρ χ α : ℝ) (k : ℤ) :
    normalizedReflectedBlochTerm q ρ χ α k =
      reflectedJacobiTraceTerm
        (fun j : ℤ ↦
          jacobiGaussianCoefficient q (j : ℝ))
        ρ χ α k := by
  rw [normalizedReflectedBlochTerm,
    normalizedReflectedBlochCoefficient_eq]
  unfold reflectedJacobiTraceTerm
  calc
    jacobiGaussianCoefficient q (k : ℝ) *
          jacobiUnitPhase (-(k : ℝ) * χ) *
        jacobiUnitPhase
          ((((k : ℝ) ^ 2) - ρ * (k : ℝ)) * α) =
      jacobiGaussianCoefficient q (k : ℝ) *
        (jacobiUnitPhase (-(k : ℝ) * χ) *
          jacobiUnitPhase
            ((((k : ℝ) ^ 2) - ρ * (k : ℝ)) * α)) := by
              ring
    _ =
      jacobiGaussianCoefficient q (k : ℝ) *
        jacobiUnitPhase
          (-(k : ℝ) * χ +
            (((k : ℝ) ^ 2 - ρ * (k : ℝ)) * α)) := by
              rw [jacobiUnitPhase_add]

/-- The Gaussian coefficient is even on integer indices. -/
theorem jacobiGaussianCoefficient_int_even
    (q : ℝ) (k : ℤ) :
    jacobiGaussianCoefficient q ((-k : ℤ) : ℝ) =
      jacobiGaussianCoefficient q (k : ℝ) := by
  unfold jacobiGaussianCoefficient
  push_cast
  rw [neg_sq]

/-- Pointwise elimination of the fully normalized reflected branch. -/
theorem normalizedReflectedBlochTerm_eq_canonical_neg
    (q ρ χ α : ℝ) (k : ℤ) :
    normalizedReflectedBlochTerm q ρ χ α k =
      canonicalJacobiTraceTerm
        (fun j : ℤ ↦
          jacobiGaussianCoefficient q (j : ℝ))
        ρ χ α (-k) := by
  rw [normalizedReflectedBlochTerm_eq_reflected]
  exact
    reflectedJacobiTraceTerm_eq_canonical_neg
      (fun j : ℤ ↦
        jacobiGaussianCoefficient q (j : ℝ))
      (jacobiGaussianCoefficient_int_even q)
      ρ χ α k

/-- The sum of all fully normalized reflected Bloch terms is the
canonical Jacobi trace. -/
theorem tsum_normalizedReflectedBlochTerm_eq_canonical
    (q ρ χ α : ℝ) :
    (∑' k : ℤ,
        normalizedReflectedBlochTerm q ρ χ α k) =
      canonicalJacobiTrace
        (fun j : ℤ ↦
          jacobiGaussianCoefficient q (j : ℝ))
        ρ χ α := by
  rw [← (Equiv.neg ℤ).tsum_eq]
  apply tsum_congr
  intro k
  simpa only [Equiv.neg_apply, neg_neg] using
    normalizedReflectedBlochTerm_eq_canonical_neg
      q ρ χ α (-k)

end

end HGAS.Modular
