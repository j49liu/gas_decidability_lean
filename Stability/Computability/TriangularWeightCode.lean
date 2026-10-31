import Stability.Computability.PolynomialCodeOperations
import Stability.Simulation.TriangularErrorWeights

/-!
# Effective triangular error weights

The code follows the same finite prefix recursion as the polynomial
construction. Its loop length and coordinate indices are fixed compiler
parameters; the coefficient polynomials remain genuine raw inputs.
-/

namespace Stability.TriangularWeightCode

open HGAS
open scoped BigOperators

variable {n J : ℕ}

def step (C : Fin J → Fin J → PolynomialCode n)
    (previous : Fin J → PolynomialCode n) (j : Fin J) : PolynomialCode n :=
  PolynomialCode.add PolynomialCode.one (PolynomialCode.sumCodes (List.ofFn fun i ↦
    if i.val < j.val then PolynomialCode.mul (C j i) (previous i) else PolynomialCode.zero))

def weightPrefix (C : Fin J → Fin J → PolynomialCode n) : ℕ → Fin J → PolynomialCode n
  | 0 => fun _ ↦ PolynomialCode.zero
  | count + 1 =>
      let previous := weightPrefix C count
      if h : count < J then Function.update previous ⟨count, h⟩
        (step C previous ⟨count, h⟩) else previous

def weights (C : Fin J → Fin J → PolynomialCode n) : Fin J → PolynomialCode n :=
  weightPrefix C J

theorem decode_step {τ : Type*} (r : τ → Fin n)
    (C : Fin J → Fin J → PolynomialCode n) (previous : Fin J → PolynomialCode n)
    (A : Fin J → Fin J → MvPolynomial τ ℚ) (p : Fin J → MvPolynomial τ ℚ)
    (hC : ∀ j i, PolynomialCode.decode (C j i) = MvPolynomial.rename r (A j i))
    (hp : ∀ i, PolynomialCode.decode (previous i) = MvPolynomial.rename r (p i))
    (j : Fin J) :
    PolynomialCode.decode (step C previous j) =
      MvPolynomial.rename r (Simulation.TriangularErrorWeights.step A p j) := by
  simp only [step, PolynomialCode.decode_add_code, PolynomialCode.decode_one_code,
    PolynomialCode.decode_sumCodes, List.map_ofFn, List.sum_ofFn,
    Simulation.TriangularErrorWeights.step, map_add, map_one, map_sum, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [Function.comp_apply]
  split_ifs
  · simp only [PolynomialCode.decode_mul_code, hC, hp, map_mul]
  · exact PolynomialCode.decode_zero_code

theorem decode_weightPrefix {τ : Type*} (r : τ → Fin n)
    (C : Fin J → Fin J → PolynomialCode n) (A : Fin J → Fin J → MvPolynomial τ ℚ)
    (hC : ∀ j i, PolynomialCode.decode (C j i) = MvPolynomial.rename r (A j i))
    (count : ℕ) (j : Fin J) :
    PolynomialCode.decode (weightPrefix C count j) =
      MvPolynomial.rename r (Simulation.TriangularErrorWeights.weightPrefix A count j) := by
  induction count generalizing j with
  | zero => simp [weightPrefix, Simulation.TriangularErrorWeights.weightPrefix]
  | succ count ih =>
    simp only [weightPrefix, Simulation.TriangularErrorWeights.weightPrefix]
    split_ifs with h
    · by_cases hj : j = ⟨count, h⟩
      · subst j
        rw [Function.update_self, Function.update_self]
        exact decode_step r C _ A _ hC ih _
      · rw [Function.update_of_ne hj, Function.update_of_ne hj]
        exact ih j
    · exact ih j

theorem decode_weights {τ : Type*} (r : τ → Fin n)
    (C : Fin J → Fin J → PolynomialCode n) (A : Fin J → Fin J → MvPolynomial τ ℚ)
    (hC : ∀ j i, PolynomialCode.decode (C j i) = MvPolynomial.rename r (A j i))
    (j : Fin J) :
    PolynomialCode.decode (weights C j) =
      MvPolynomial.rename r (Simulation.TriangularErrorWeights.weights A j) :=
  decode_weightPrefix r C A hC J j

theorem step_primrec {α : Type*} [Primcodable α]
    (C : α → Fin J → Fin J → PolynomialCode n)
    (previous : α → Fin J → PolynomialCode n)
    (hC : ∀ j i, Primrec (fun a ↦ C a j i))
    (hp : ∀ i, Primrec (fun a ↦ previous a i)) (j : Fin J) :
    Primrec (fun a ↦ step (C a) (previous a) j) := by
  apply PolynomialCode.add_primrec.comp (Primrec.const _)
  apply PolynomialCode.sumCodes_primrec.comp
  apply Primrec.list_ofFn
  intro i
  by_cases hi : i.val < j.val
  · simpa only [hi, ↓reduceIte] using PolynomialCode.mul_primrec.comp (hC j i) (hp i)
  · simpa only [hi, ↓reduceIte] using (Primrec.const PolynomialCode.zero :
      Primrec (fun _ : α ↦ (PolynomialCode.zero : PolynomialCode n)))

theorem weightPrefix_primrec {α : Type*} [Primcodable α]
    (C : α → Fin J → Fin J → PolynomialCode n)
    (hC : ∀ j i, Primrec (fun a ↦ C a j i)) (count : ℕ) (j : Fin J) :
    Primrec (fun a ↦ weightPrefix (C a) count j) := by
  induction count generalizing j with
  | zero => exact Primrec.const _
  | succ count ih =>
    by_cases h : count < J
    · by_cases hj : j = ⟨count, h⟩
      · subst j
        simpa only [weightPrefix, h, ↓reduceDIte, Function.update_self] using
          step_primrec C (fun a ↦ weightPrefix (C a) count) hC ih ⟨count, h⟩
      · simpa only [weightPrefix, h, ↓reduceDIte, Function.update_of_ne hj] using ih j
    · simpa only [weightPrefix, h, ↓reduceDIte] using ih j

theorem weights_at_primrec {α : Type*} [Primcodable α]
    (C : α → Fin J → Fin J → PolynomialCode n)
    (hC : ∀ j i, Primrec (fun a ↦ C a j i)) (j : Fin J) :
    Primrec (fun a ↦ weights (C a) j) := weightPrefix_primrec C hC J j

end Stability.TriangularWeightCode
