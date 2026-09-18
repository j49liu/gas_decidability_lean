import HGAS.Clocks.ControllerPhaseProductCharacterCode
import HGAS.Clocks.ControllerPhaseProductFlowPolynomial
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Tactic

/-!
# Differential semantics of controller--phase characters

The polynomial character compiler is useful dynamically only after its
formal velocity has been identified with the actual derivative along the
controller--phase flow.  This file proves that bridge.

The proof is deliberately split into two reusable pieces.  First, a signed
integral power of an arbitrary complex phase satisfying

```
                         ζ' = i ω ζ
```

satisfies the expected signed-power equation.  Negative powers are
represented by conjugates, exactly as in the polynomial compiler.  Second,
the finite product rule combines those equations into the logarithmic
derivative of a character.  No division is used: the product with one
factor removed is multiplied back by that factor.  Consequently the proof
also covers zero phase coordinates algebraically, although the intended
flow stays on unit circles.
-/

namespace HGAS.Clocks.ControllerPhaseProductCharacterDynamics

open Complex
open scoped BigOperators

noncomputable section

private theorem pow_velocity
    (z : ℂ) (ω : ℝ) (n : ℕ) :
    (n : ℂ) * z ^ (n - 1) *
          (Complex.I * (ω : ℂ) * z) =
      Complex.I * (((n : ℝ) * ω : ℝ) : ℂ) * z ^ n := by
  cases n with
  | zero => simp
  | succ n =>
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel,
        pow_succ]
      push_cast
      ring

/-- The conjugate of a rotating phase rotates with the opposite angular
velocity. -/
theorem hasDerivAt_star_of_rotating
    (ζ : ℝ → ℂ) (ω : ℝ) (t : ℝ)
    (hζ :
      HasDerivAt ζ
        (Complex.I * (ω : ℂ) * ζ t) t) :
    HasDerivAt (fun u ↦ star (ζ u))
      (Complex.I * ((-ω : ℝ) : ℂ) * star (ζ t)) t := by
  convert hζ.star using 1
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im]

/-- Differential equation for the signed-power convention used by the
polynomial character compiler. -/
theorem hasDerivAt_signedPower
    (ζ : ℝ → ℂ) (ω : ℝ) (e : ℤ) (t : ℝ)
    (hζ :
      HasDerivAt ζ
        (Complex.I * (ω : ℂ) * ζ t) t) :
    HasDerivAt
      (fun u ↦
        if e < 0 then
          star (ζ u) ^ e.natAbs
        else
          ζ u ^ e.natAbs)
      (Complex.I * (((e : ℝ) * ω : ℝ) : ℂ) *
        (if e < 0 then
          star (ζ t) ^ e.natAbs
        else
          ζ t ^ e.natAbs)) t := by
  by_cases he : e < 0
  · simp only [he, if_true]
    have hpow :=
      (hasDerivAt_star_of_rotating ζ ω t hζ).pow e.natAbs
    convert hpow using 1
    rw [pow_velocity]
    have heInt :
        (e.natAbs : ℤ) = -e :=
      Int.ofNat_natAbs_of_nonpos he.le
    have heReal :
        ((e.natAbs : ℕ) : ℝ) = -(e : ℝ) := by
      have h :=
        congrArg (fun k : ℤ ↦ (k : ℝ)) heInt
      norm_num at h ⊢
      exact h
    have hecast :
        (e : ℝ) = -(e.natAbs : ℕ) := by
      linarith
    rw [hecast]
    push_cast
    ring
  · simp only [he, if_false]
    have hpow := hζ.pow e.natAbs
    convert hpow using 1
    rw [pow_velocity]
    have heInt :
        (e.natAbs : ℤ) = e :=
      Int.natAbs_of_nonneg (le_of_not_gt he)
    have hecast :
        (e : ℝ) = (e.natAbs : ℕ) := by
      have h :=
        congrArg (fun k : ℤ ↦ (k : ℝ)) heInt.symm
      norm_num at h ⊢
      exact h
    rw [hecast]

private noncomputable def signedPowerFunction
    (ζ : ℝ → ℂ) (e : ℤ) (t : ℝ) : ℂ :=
  if e < 0 then
    star (ζ t) ^ e.natAbs
  else
    ζ t ^ e.natAbs

/-- Product form of the character differential equation.  This theorem is
independent of the controller implementation and can be reused for any
finite family of rotating complex phases. -/
theorem hasDerivAt_characterProduct
    {q : ℕ}
    (ζ : Fin q → ℝ → ℂ)
    (ω : Fin q → ℝ)
    (exponents : Fin q → ℤ)
    (t : ℝ)
    (hζ : ∀ i,
      HasDerivAt (ζ i)
        (Complex.I * (ω i : ℂ) * ζ i t) t) :
    HasDerivAt
      (fun u ↦
        ∏ i : Fin q,
          signedPowerFunction (ζ i) (exponents i) u)
      (Complex.I *
          ((∑ i : Fin q,
            (exponents i : ℝ) * ω i : ℝ) : ℂ) *
        ∏ i : Fin q,
          signedPowerFunction (ζ i) (exponents i) t) t := by
  let f : Fin q → ℝ → ℂ :=
    fun i u ↦ signedPowerFunction (ζ i) (exponents i) u
  let f' : Fin q → ℂ :=
    fun i ↦
      Complex.I *
        (((exponents i : ℝ) * ω i : ℝ) : ℂ) *
          f i t
  have hfactor :
      ∀ i : Fin q, HasDerivAt (f i) (f' i) t := by
    intro i
    exact hasDerivAt_signedPower
      (ζ i) (ω i) (exponents i) t (hζ i)
  have hproduct :=
    HasDerivAt.fun_finsetProd
      (u := Finset.univ)
      (fun i _ ↦ hfactor i)
  convert hproduct using 1
  simp only [f']
  symm
  calc
      ∑ i : Fin q,
          (∏ j ∈ Finset.univ.erase i, f j t) •
            (Complex.I *
              (((exponents i : ℝ) * ω i : ℝ) : ℂ) *
                f i t) =
          ∑ i : Fin q,
            Complex.I *
              (((exponents i : ℝ) * ω i : ℝ) : ℂ) *
                ∏ j : Fin q, f j t := by
          apply Finset.sum_congr rfl
          intro i _
          rw [smul_eq_mul]
          calc
            (∏ j ∈ Finset.univ.erase i, f j t) *
                  (Complex.I *
                    (((exponents i : ℝ) * ω i : ℝ) : ℂ) *
                      f i t) =
                Complex.I *
                  (((exponents i : ℝ) * ω i : ℝ) : ℂ) *
                    ((∏ j ∈ Finset.univ.erase i, f j t) *
                      f i t) := by
                ring
            _ =
                Complex.I *
                  (((exponents i : ℝ) * ω i : ℝ) : ℂ) *
                    ∏ j : Fin q, f j t := by
                rw [Finset.prod_erase_mul
                  Finset.univ (fun j ↦ f j t)
                  (Finset.mem_univ i)]
      _ =
          Complex.I *
            ((∑ i : Fin q,
              (exponents i : ℝ) * ω i : ℝ) : ℂ) *
              ∏ j : Fin q, f j t := by
          push_cast
          rw [Finset.mul_sum]
          rw [Finset.sum_mul]

/-! ## Specialization to the coupled controller--phase flow -/

/-- Read an analytic product of controller and phase circles as the
structured real state expected by the polynomial character compiler. -/
def analyticStateFamily
    {q : ℕ}
    (z : ControllerPhaseFlow.State (Fin q)) :
    ControllerPhaseProductPolynomialCode.StateFamily q ℝ :=
  fun i ↦
    { controller :=
        ControllerFlow.circleControllerState (z.1 i)
      phase :=
        PhaseClockFlow.circlePhaseState (z.2 i) }

@[simp]
theorem phaseValue_analyticStateFamily
    {q : ℕ}
    (z : ControllerPhaseFlow.State (Fin q))
    (i : Fin q) :
    ControllerPhaseProductCharacterCode.phaseValue
        (analyticStateFamily z) i =
      (z.2 i : ℂ) := by
  apply Complex.ext <;>
    simp [ControllerPhaseProductCharacterCode.phaseValue,
      analyticStateFamily, PhaseClockFlow.circlePhaseState]

@[simp]
theorem frequencyValue_analyticStateFamily
    {q : ℕ}
    (parameters : Fin q → RationalCode)
    (exponents : Fin q → ℤ)
    (z : ControllerPhaseFlow.State (Fin q)) :
    ControllerPhaseProductCharacterCode.frequencyValue
        parameters exponents (analyticStateFamily z) =
      ∑ i : Fin q,
        (exponents i : ℝ) *
          (RationalCode.decode (parameters i) : ℝ) *
          (z.1 i : ℂ).re := by
  simp [ControllerPhaseProductCharacterCode.frequencyValue,
    analyticStateFamily,
    ControllerFlow.circleControllerState]

/-- Along the literal global coupled clock flow, the character value has
the derivative emitted by `derivativeCode`.  In particular, this theorem
identifies the actual instantaneous character frequency with the compiled
rational linear readout. -/
theorem characterValue_controllerPhaseFlow_hasDerivAt
    {q : ℕ}
    (parameters : Fin q → RationalCode)
    (hp : ∀ i,
      (1 : ℝ) <
        (RationalCode.decode (parameters i) : ℝ))
    (exponents : Fin q → ℤ)
    (z₀ : ControllerPhaseFlow.State (Fin q))
    (t : ℝ) :
    HasDerivAt
      (fun u ↦
        ControllerPhaseProductCharacterCode.characterValue
          exponents
          (analyticStateFamily
            (ControllerPhaseFlow.controllerPhaseFlow
              (fun i ↦
                (RationalCode.decode (parameters i) : ℝ))
              hp u z₀)))
      (Complex.I *
          (ControllerPhaseProductCharacterCode.frequencyValue
            parameters exponents
            (analyticStateFamily
              (ControllerPhaseFlow.controllerPhaseFlow
                (fun i ↦
                  (RationalCode.decode (parameters i) : ℝ))
                hp t z₀)) : ℂ) *
        ControllerPhaseProductCharacterCode.characterValue
          exponents
          (analyticStateFamily
            (ControllerPhaseFlow.controllerPhaseFlow
              (fun i ↦
                (RationalCode.decode (parameters i) : ℝ))
              hp t z₀))) t := by
  let p : Fin q → ℝ :=
    fun i ↦ (RationalCode.decode (parameters i) : ℝ)
  let orbit : ℝ → ControllerPhaseFlow.State (Fin q) :=
    fun u ↦
      ControllerPhaseFlow.controllerPhaseFlow p hp u z₀
  let ζ : Fin q → ℝ → ℂ :=
    fun i u ↦ (orbit u).2 i
  let ω : Fin q → ℝ :=
    fun i ↦ p i * ((orbit t).1 i : ℂ).re
  have hζ : ∀ i,
      HasDerivAt (ζ i)
        (Complex.I * (ω i : ℂ) * ζ i t) t := by
    intro i
    have h :=
      ControllerPhaseFlow.controllerPhaseFlow_solves_lockedPhaseField
        p hp z₀ i t
    convert h using 1
    simp only [ζ, ω, p, orbit,
      Controller.lockedPhaseField,
      Controller.lockedFrequency,
      PhaseClockFlow.phaseStateComplex_phaseField,
      PhaseClockFlow.phaseStateComplex_circlePhaseState,
      ControllerFlow.circleControllerState_r]
    push_cast
    ring
  have hcharacter :=
    hasDerivAt_characterProduct ζ ω exponents t hζ
  simpa only [
    ControllerPhaseProductCharacterCode.characterValue,
    List.prod_ofFn,
    ControllerPhaseProductCharacterCode.signedPowerValue,
    phaseValue_analyticStateFamily,
    signedPowerFunction,
    frequencyValue_analyticStateFamily,
    p, orbit, ζ, ω, mul_assoc] using hcharacter

/-- Code-level form of the preceding theorem: the actual derivative is
literally the evaluation of `derivativeCode` at the current flattened
polynomial state. -/
theorem characterValue_controllerPhaseFlow_hasDerivAt_derivativeCode
    {q : ℕ}
    (parameters : Fin q → RationalCode)
    (hp : ∀ i,
      (1 : ℝ) <
        (RationalCode.decode (parameters i) : ℝ))
    (exponents : Fin q → ℤ)
    (z₀ : ControllerPhaseFlow.State (Fin q))
    (t : ℝ) :
    HasDerivAt
      (fun u ↦
        ControllerPhaseProductCharacterCode.characterValue
          exponents
          (analyticStateFamily
            (ControllerPhaseFlow.controllerPhaseFlow
              (fun i ↦
                (RationalCode.decode (parameters i) : ℝ))
              hp u z₀)))
      (ControllerPhaseProductCharacterCode.evalPair
        (ControllerPhaseProductCharacterCode.derivativeCode
          parameters exponents)
        (ControllerPhaseProductPolynomialCode.point
          (analyticStateFamily
            (ControllerPhaseFlow.controllerPhaseFlow
              (fun i ↦
                (RationalCode.decode (parameters i) : ℝ))
              hp t z₀)))) t := by
  simpa only [
    ControllerPhaseProductCharacterCode.evalPair_derivativeCode] using
    characterValue_controllerPhaseFlow_hasDerivAt
      parameters hp exponents z₀ t

end

end HGAS.Clocks.ControllerPhaseProductCharacterDynamics
