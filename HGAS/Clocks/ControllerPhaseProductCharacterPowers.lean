import HGAS.Clocks.ControllerPhaseProductCharacterCode
import Mathlib.Tactic

/-!
# Power identities for controller-product characters

The Laurent-character compiler represents negative exponents by powers of
the conjugate phase coordinate.  Scaling every integral exponent by four
therefore agrees exactly with taking the fourth power of the compiled
character value.  The identity is algebraic and does not require a
unit-circle hypothesis.

This small module isolates the fact needed by fourth-root gauge
constructions, without tying it to the DQL detector.
-/

namespace HGAS.Clocks.ControllerPhaseProductCharacterCode

open HGAS
open ControllerPhaseProductPolynomialCode

noncomputable section

variable {q : ℕ}

/-- Multiplying one signed exponent by four is the same as taking the
fourth power of its signed-power value. -/
theorem signedPowerValue_four_mul
    (z : StateFamily q ℝ) (a : Fin q) (e : ℤ) :
    signedPowerValue z a (4 * e) =
      signedPowerValue z a e ^ 4 := by
  cases e with
  | ofNat n =>
      have hn : ¬(Int.ofNat n) < 0 :=
        not_lt_of_ge (Int.natCast_nonneg n)
      have hfour : ¬4 * Int.ofNat n < 0 := by omega
      simp only [signedPowerValue, if_neg hn, if_neg hfour]
      norm_num [Int.natAbs_mul]
      rw [Nat.mul_comm, pow_mul]
  | negSucc n =>
      have hn : Int.negSucc n < 0 :=
        Int.negSucc_lt_zero n
      have hfour : 4 * Int.negSucc n < 0 := by omega
      simp only [signedPowerValue, if_pos hn, if_pos hfour]
      norm_num [Int.natAbs_mul]
      rw [Nat.mul_comm, pow_mul]

/-- Multiplying every exponent of a finite character by four is exactly
the fourth power of the character value. -/
theorem characterValue_four_mul
    (exponents : Fin q → ℤ)
    (z : StateFamily q ℝ) :
    characterValue (fun i => 4 * exponents i) z =
      characterValue exponents z ^ 4 := by
  let indices : List (Fin q) :=
    List.ofFn fun i : Fin q => i
  unfold characterValue
  have hscaled :
      List.ofFn
          (fun i : Fin q =>
            signedPowerValue z i (4 * exponents i)) =
        indices.map
          (fun i =>
            signedPowerValue z i (4 * exponents i)) := by
    simp [indices, Function.comp_def]
  have hroot :
      List.ofFn
          (fun i : Fin q =>
            signedPowerValue z i (exponents i)) =
        indices.map
          (fun i =>
            signedPowerValue z i (exponents i)) := by
    simp [indices, Function.comp_def]
  rw [hscaled, hroot]
  induction indices with
  | nil => simp
  | cons i indices ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [signedPowerValue_four_mul, ih, mul_pow]

end

end HGAS.Clocks.ControllerPhaseProductCharacterCode
