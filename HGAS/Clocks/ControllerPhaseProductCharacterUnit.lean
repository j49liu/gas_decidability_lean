import HGAS.Clocks.ControllerPhaseProductCharacterCode
import Mathlib.Analysis.Complex.Circle
import Mathlib.Tactic

/-!
# Unit-circle semantics of compiled controller characters

The sparse character compiler represents a negative phase power by a
conjugate.  This is a Laurent inverse precisely on the intended phase
circles.  The lemmas here isolate that semantic hypothesis and prove the
two facts repeatedly needed by gauge and Poisson specializations:

* every compiled character has norm one; and
* negating every exponent gives the multiplicative inverse character.

They are stated for structured controller--phase states and do not assume
that the controller coordinates themselves are locked.
-/

namespace HGAS.Clocks.ControllerPhaseProductCharacterCode

open HGAS
open ControllerPhaseProductPolynomialCode

noncomputable section

variable {q : ℕ}

/-- The phase coordinates of a structured state lie on their intended
unit circles. -/
def OnPhaseCircles
    (z : StateFamily q ℝ) : Prop :=
  ∀ a, ‖phaseValue z a‖ = 1

theorem norm_signedPowerValue_eq_one
    (z : StateFamily q ℝ) (a : Fin q) (e : ℤ)
    (hz : OnPhaseCircles z) :
    ‖signedPowerValue z a e‖ = 1 := by
  by_cases he : e < 0
  · simp only [signedPowerValue, if_pos he, norm_pow, norm_star]
    rw [hz a, one_pow]
  · simp only [signedPowerValue, if_neg he, norm_pow]
    rw [hz a, one_pow]

theorem signedPowerValue_neg_eq_inv
    (z : StateFamily q ℝ) (a : Fin q) (e : ℤ)
    (hz : OnPhaseCircles z) :
    signedPowerValue z a (-e) =
      (signedPowerValue z a e)⁻¹ := by
  have hconj :
      signedPowerValue z a (-e) =
        star (signedPowerValue z a e) := by
    cases e with
    | ofNat n =>
        cases n with
        | zero =>
            simp [signedPowerValue]
        | succ n =>
            have hnegative :
                signedPowerValue z a (Int.negSucc n) =
                  star (phaseValue z a) ^ (n + 1) := by
              rw [signedPowerValue,
                if_pos (Int.negSucc_lt_zero n)]
              rfl
            have hpositive :
                signedPowerValue z a (Int.ofNat (n + 1)) =
                  phaseValue z a ^ (n + 1) := by
              rw [signedPowerValue, if_neg]
              · rfl
              · exact
                  not_lt_of_ge (Int.natCast_nonneg (n + 1))
            have hnegInt :
                -(Int.ofNat (n + 1)) = Int.negSucc n := by
              simpa [Nat.succ_eq_add_one] using
                Int.neg_ofNat_succ n
            rw [hnegInt, hnegative, hpositive]
            simp
    | negSucc n =>
        have hpositive :
            signedPowerValue z a ((n + 1 : ℕ) : ℤ) =
              phaseValue z a ^ (n + 1) := by
          rw [signedPowerValue, if_neg]
          · rfl
          · exact
              not_lt_of_ge (Int.natCast_nonneg (n + 1))
        have hnegative :
            signedPowerValue z a (Int.negSucc n) =
              star (phaseValue z a) ^ (n + 1) := by
          rw [signedPowerValue,
            if_pos (Int.negSucc_lt_zero n)]
          rfl
        rw [Int.neg_negSucc, hpositive, hnegative]
        simp
  rw [hconj]
  exact (Complex.inv_eq_conj
    (norm_signedPowerValue_eq_one z a e hz)).symm

theorem norm_characterValue_eq_one
    (exponents : Fin q → ℤ)
    (z : StateFamily q ℝ)
    (hz : OnPhaseCircles z) :
    ‖characterValue exponents z‖ = 1 := by
  let indices : List (Fin q) :=
    List.ofFn fun a : Fin q ↦ a
  unfold characterValue
  have hindices :
      List.ofFn
          (fun a : Fin q ↦
            signedPowerValue z a (exponents a)) =
        indices.map
          (fun a ↦ signedPowerValue z a (exponents a)) := by
    simp [indices, Function.comp_def]
  rw [hindices]
  induction indices with
  | nil => simp
  | cons a indices ih =>
      simp [norm_signedPowerValue_eq_one z a (exponents a) hz, ih]

theorem characterValue_neg_eq_inv
    (exponents : Fin q → ℤ)
    (z : StateFamily q ℝ)
    (hz : OnPhaseCircles z) :
    characterValue (fun i ↦ -exponents i) z =
      (characterValue exponents z)⁻¹ := by
  let indices : List (Fin q) :=
    List.ofFn fun a : Fin q ↦ a
  unfold characterValue
  have hnegative :
      List.ofFn
          (fun a : Fin q ↦
            signedPowerValue z a (-exponents a)) =
        indices.map
          (fun a ↦ signedPowerValue z a (-exponents a)) := by
    simp [indices, Function.comp_def]
  have hpositive :
      List.ofFn
          (fun a : Fin q ↦
            signedPowerValue z a (exponents a)) =
        indices.map
          (fun a ↦ signedPowerValue z a (exponents a)) := by
    simp [indices, Function.comp_def]
  rw [hnegative, hpositive]
  change
    (indices.map
        (fun a ↦ signedPowerValue z a (-exponents a))).prod =
      (indices.map
        (fun a ↦ signedPowerValue z a (exponents a))).prod⁻¹
  induction indices with
  | nil => simp
  | cons a indices ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [signedPowerValue_neg_eq_inv z a (exponents a) hz, ih]
      rw [mul_inv_rev]
      exact mul_comm _ _

end

end HGAS.Clocks.ControllerPhaseProductCharacterCode
