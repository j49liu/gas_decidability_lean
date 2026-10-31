import Stability.Selection.OrdinaryTimeRadicalPrimitive

/-!
# Polynomial primitives on the literal source graph

The resource constants are rational and independent of the arithmetic
RHS. The cohomological equation retains the actual constant Fourier mode
until arithmetic vanishing has been proved separately.
-/

noncomputable section

open scoped BigOperators

namespace Stability.Selection

open HGAS HGAS.Analysis HGAS.Clocks

/-- Rational coefficient mass of a polynomial, after cancellation. -/
def rationalPolynomialMass {n : ℕ} (P : MvPolynomial (Fin n) ℚ) : ℚ :=
  ∑ e ∈ P.support, |P.coeff e|

theorem rationalPolynomialMass_nonneg {n : ℕ} (P : MvPolynomial (Fin n) ℚ) :
    0 ≤ rationalPolynomialMass P := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

theorem rationalPolynomialMass_cast {n : ℕ} (P : MvPolynomial (Fin n) ℚ) :
    (rationalPolynomialMass P : ℝ) = ∑ e ∈ P.support, ‖((P.coeff e : ℚ) : ℂ)‖ := by
  simp [rationalPolynomialMass, Complex.norm_ratCast]

/-- The actual real polynomial evaluated on the actual encoded graph. -/
def sourcePolynomialFunction {eqs vars : ℕ} (I : DQLSystem eqs vars)
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (P : MvPolynomial (Fin (FixedDetectorPolynomialCode.dimension eqs vars)) ℚ)
    (x : UnitAddTorus (Fin (vars + eqs))) : ℝ :=
  MvPolynomial.eval₂ (algebraMap ℚ ℝ) (intendedSourceGraph I controller x) P

theorem sourcePolynomialFunction_complex {eqs vars : ℕ} (I : DQLSystem eqs vars)
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (P : MvPolynomial (Fin (FixedDetectorPolynomialCode.dimension eqs vars)) ℚ)
    (x : UnitAddTorus (Fin (vars + eqs))) :
    (sourcePolynomialFunction I controller P x : ℂ) =
      MvPolynomial.eval₂ (algebraMap ℚ ℂ)
        (fun i ↦ (intendedSourceGraph I controller x i : ℂ)) P := by
  exact MvPolynomial.eval₂_comp_left Complex.ofRealHom (algebraMap ℚ ℝ)
    (intendedSourceGraph I controller x) P

theorem continuous_sourcePolynomialFunction {eqs vars : ℕ} (I : DQLSystem eqs vars)
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (P : MvPolynomial (Fin (FixedDetectorPolynomialCode.dimension eqs vars)) ℚ) :
    Continuous (sourcePolynomialFunction I controller P) := by
  classical
  unfold sourcePolynomialFunction
  simp_rw [MvPolynomial.eval₂_eq]
  have hc (i : Fin (FixedDetectorPolynomialCode.dimension eqs vars)) :=
    (continuous_apply i).comp (continuous_intendedSourceGraph I controller)
  fun_prop

/-- A common degree bound controls each real source polynomial by a
rational coefficient mass and the prescribed RHS exponential factor. -/
theorem sourcePolynomialFunction_weightedFourier_bound {eqs vars : ℕ}
    (I : DQLSystem eqs vars) (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (hcontroller : ∀ i, |(controller i).r| ≤ 1 ∧ |(controller i).s| ≤ 1)
    {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hθ : (1 / 256 : ℝ) * ρ ^
      (4 + 4 * ∑ row, ∑ j, |(I.linear row j : ℝ)|) ≤ 1 / 8)
    (hP : (1 / 2 : ℝ) * ρ ^
      (4 + 4 * ∑ row, ∑ j, |(I.quadratic row j : ℝ)|) ≤ 3 / 4)
    (P : MvPolynomial (Fin (FixedDetectorPolynomialCode.dimension eqs vars)) ℚ)
    (D : ℕ) (hD : P.totalDegree ≤ D) :
    Summable (fun a : Fin (vars + eqs) → ℤ ↦
      ‖UnitAddTorus.mFourierCoeff (fun x ↦ (sourcePolynomialFunction I controller P x : ℂ)) a‖ *
        ρ ^ (∑ k, |(a k : ℝ)|)) ∧
    (∑' a : Fin (vars + eqs) → ℤ,
      ‖UnitAddTorus.mFourierCoeff (fun x ↦ (sourcePolynomialFunction I controller P x : ℂ)) a‖ *
        ρ ^ (∑ k, |(a k : ℝ)|)) ≤
      (rationalPolynomialMass P : ℝ) * (sourceCoordinateFourierBudget : ℝ) ^ D *
        ρ ^ (4 * (D : ℝ) * ∑ row, |(I.rhs row : ℝ)|) := by
  simp_rw [sourcePolynomialFunction_complex]
  obtain ⟨hs, hb⟩ := intendedSourceGraph_polynomial_weightedFourier_bound
    I controller hcontroller hρ hθ hP P
  refine ⟨hs, hb.trans ?_⟩
  rw [rationalPolynomialMass_cast]
  have hC : (1 : ℝ) ≤ sourceCoordinateFourierBudget := by
    exact_mod_cast (Nat.succ_le_iff.mpr sourceCoordinateFourierBudget_pos)
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC hD)
      (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  · apply Real.rpow_le_rpow_of_exponent_le hρ
    have hd : (P.totalDegree : ℝ) ≤ D := by exact_mod_cast hD
    exact mul_le_mul_of_nonneg_right (by linarith)
      (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
  · positivity
  · positivity

/-- An explicit rational primitive budget for a finite polynomial family. -/
def sourcePrimitiveBudget {eqs vars outputs : ℕ}
    (p : Fin (vars + eqs) → ℕ) (m D : ℕ)
    (P : Fin outputs → MvPolynomial (Fin (FixedDetectorPolynomialCode.dimension eqs vars)) ℚ) : ℚ :=
  1 + (radicalFourierBudget p m : ℚ) * (∑ i, rationalPolynomialMass (P i)) *
    (sourceCoordinateFourierBudget : ℚ) ^ D

theorem sourcePrimitiveBudget_pos {eqs vars outputs : ℕ}
    (p : Fin (vars + eqs) → ℕ) (m D : ℕ)
    (P : Fin outputs → MvPolynomial (Fin (FixedDetectorPolynomialCode.dimension eqs vars)) ℚ) :
    0 < sourcePrimitiveBudget p m D P := by
  unfold sourcePrimitiveBudget
  have hs : 0 ≤ ∑ i, rationalPolynomialMass (P i) :=
    Finset.sum_nonneg fun i _ ↦ rationalPolynomialMass_nonneg (P i)
  have h := mul_nonneg (mul_nonneg
    (Nat.cast_nonneg (radicalFourierBudget p m) : (0 : ℚ) ≤ radicalFourierBudget p m) hs)
    (by positivity : (0 : ℚ) ≤ (sourceCoordinateFourierBudget : ℚ) ^ D)
  linarith

/-- The real primitive vector; each complex coordinate before taking its
real part is already real by `radicalFourierPrimitive_im_eq_zero`. -/
def sourcePolynomialPrimitive {eqs vars outputs : ℕ} (I : DQLSystem eqs vars)
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (p : Fin (vars + eqs) → ℕ) (sign : Fin (vars + eqs) → ℤ)
    (P : Fin outputs → MvPolynomial (Fin (FixedDetectorPolynomialCode.dimension eqs vars)) ℚ)
    (x : UnitAddTorus (Fin (vars + eqs))) : Fin outputs → ℝ :=
  fun i ↦ (radicalFourierPrimitive p sign
    (fun y ↦ (sourcePolynomialFunction I controller (P i) y : ℂ)) x).re

/-- A finite polynomial family has a continuous real primitive with a
rational `K₀`, the exact RHS exponent, and the centered physical-time
cohomological equation. Squared Euclidean norm is used explicitly. -/
theorem sourcePolynomialPrimitive_resources {eqs vars outputs : ℕ}
    (I : DQLSystem eqs vars) (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (hcontroller : ∀ i, |(controller i).r| ≤ 1 ∧ |(controller i).s| ≤ 1)
    (p : Fin (vars + eqs) → ℕ) (hp : ∀ i, (p i).Prime) (hinjective : Function.Injective p)
    (sign : Fin (vars + eqs) → ℤ) (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (m : ℕ) (hm : 0 < m)
    (hθ : (1 / 256 : ℝ) * (1 + 1 / (m : ℝ)) ^
      (4 + 4 * ∑ row, ∑ j, |(I.linear row j : ℝ)|) ≤ 1 / 8)
    (hP : (1 / 2 : ℝ) * (1 + 1 / (m : ℝ)) ^
      (4 + 4 * ∑ row, ∑ j, |(I.quadratic row j : ℝ)|) ≤ 3 / 4)
    (P : Fin outputs → MvPolynomial (Fin (FixedDetectorPolynomialCode.dimension eqs vars)) ℚ)
    (D : ℕ) (hD : ∀ i, (P i).totalDegree ≤ D) :
    Continuous (sourcePolynomialPrimitive I controller p sign P) ∧
    (∀ x, normSq (sourcePolynomialPrimitive I controller p sign P x) ≤
      ((sourcePrimitiveBudget p m D P : ℝ) *
        (1 + 1 / (m : ℝ)) ^ (4 * (D : ℝ) * ∑ row, |(I.rhs row : ℝ)|)) ^ 2) ∧
    ∀ x t i,
      let ω := ScaledRadicalClock.scaledSignedPrimeSqrtFrequency (1 / (2 * Real.pi)) p sign
      HasDerivAt (fun s ↦ sourcePolynomialPrimitive I controller p sign P
        (RadicalClock.torusTranslationFlow ω s x) i)
        (sourcePolynomialFunction I controller (P i) (RadicalClock.torusTranslationFlow ω t x) -
          (UnitAddTorus.mFourierCoeff
            (fun y ↦ (sourcePolynomialFunction I controller (P i) y : ℂ)) 0).re) t := by
  let ρ : ℝ := 1 + 1 / (m : ℝ)
  let E : ℝ := ρ ^ (4 * (D : ℝ) * ∑ row, |(I.rhs row : ℝ)|)
  have hρ : 1 ≤ ρ := le_add_of_nonneg_right (by positivity)
  have hs (i) := sourcePolynomialFunction_weightedFourier_bound I controller hcontroller
    hρ hθ hP (P i) D (hD i)
  have hb (i) := radicalFourierPrimitive_continuous_bound p hp hinjective sign hsign m hm
    (fun x ↦ (sourcePolynomialFunction I controller (P i) x : ℂ)) (hs i).1
  refine ⟨?_, ?_, ?_⟩
  · apply continuous_pi
    intro i
    exact Complex.continuous_re.comp (hb i).1
  · intro x
    have hi (i) : |sourcePolynomialPrimitive I controller p sign P x i| ≤
        (radicalFourierBudget p m : ℝ) *
          ((rationalPolynomialMass (P i) : ℝ) * (sourceCoordinateFourierBudget : ℝ) ^ D * E) :=
      (Complex.abs_re_le_norm _).trans (((hb i).2 x).trans
        (mul_le_mul_of_nonneg_left (hs i).2 (Nat.cast_nonneg _)))
    have hsum : (∑ i, |sourcePolynomialPrimitive I controller p sign P x i|) ≤
        (sourcePrimitiveBudget p m D P : ℝ) * E := by
      refine (Finset.sum_le_sum (fun i _ ↦ hi i)).trans ?_
      have he : (∑ i, (radicalFourierBudget p m : ℝ) *
          ((rationalPolynomialMass (P i) : ℝ) * (sourceCoordinateFourierBudget : ℝ) ^ D * E)) =
          (radicalFourierBudget p m : ℝ) * (∑ i, (rationalPolynomialMass (P i) : ℝ)) *
            (sourceCoordinateFourierBudget : ℝ) ^ D * E := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [he]
      simp only [sourcePrimitiveBudget, Rat.cast_add, Rat.cast_one, Rat.cast_mul,
        Rat.cast_natCast, Rat.cast_sum, Rat.cast_pow]
      have hE : 0 ≤ E := by dsimp [E]; positivity
      nlinarith
    calc
      normSq (sourcePolynomialPrimitive I controller p sign P x) =
          ∑ i, |sourcePolynomialPrimitive I controller p sign P x i| ^ 2 := by
        unfold normSq dot
        apply Finset.sum_congr rfl
        intro i _
        rw [sq_abs, pow_two]
      _ ≤ (∑ i, |sourcePolynomialPrimitive I controller p sign P x i|) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ ↦ abs_nonneg _)
      _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) hsum 2
  · intro x t i
    have hd := radicalFourierPrimitive_hasDerivAt p hp hinjective sign hsign m hm
      (fun y ↦ (sourcePolynomialFunction I controller (P i) y : ℂ))
      (Complex.continuous_ofReal.comp (continuous_sourcePolynomialFunction I controller (P i)))
      (hs i).1 x t
    simpa only [sourcePolynomialPrimitive, Complex.sub_re, Complex.ofReal_re] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd

end Stability.Selection
