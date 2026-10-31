import Stability.Computability.PolynomialFractionCode
import Stability.Simulation.TriangularLift

/-!
# Effective recursive auxiliary velocities

This is the literal finite prefix construction of the rational radical
lift. Each step differentiates the supplied radicand along the already
constructed coordinate fractions and divides by four times that same
radicand. The decoding statements preserve numerator and denominator
polynomials, without requiring positivity or triangularity assumptions.
-/

namespace Stability.TriangularLiftCode

open HGAS Simulation PolynomialFractionCode

noncomputable section

variable {σ : Type*} [Fintype σ] {n J : ℕ}

def rootStep (e : (σ ⊕ Fin J) ≃ Fin n) (D : Fin J → PolynomialCode n)
    (F : σ → PolynomialFractionCode n) (roots : Fin J → PolynomialFractionCode n)
    (j : Fin J) : PolynomialFractionCode n :=
  mulPolynomial (PolynomialCode.varCode (e (.inr j)))
    (divPolynomial (directional e (D j) (Sum.elim F roots))
      (PolynomialCode.mul (PolynomialCode.constant (RationalCode.ofNat 4)) (D j)))

def velocityPrefix (e : (σ ⊕ Fin J) ≃ Fin n) (D : Fin J → PolynomialCode n)
    (F : σ → PolynomialFractionCode n) : ℕ → Fin J → PolynomialFractionCode n
  | 0 => fun _ ↦ ofPolynomial PolynomialCode.zero
  | count + 1 =>
      let previous := velocityPrefix e D F count
      if h : count < J then Function.update previous ⟨count, h⟩
        (rootStep e D F previous ⟨count, h⟩) else previous

def rootVelocity (e : (σ ⊕ Fin J) ≃ Fin n) (D : Fin J → PolynomialCode n)
    (F : σ → PolynomialFractionCode n) : Fin J → PolynomialFractionCode n :=
  velocityPrefix e D F J

def field (e : (σ ⊕ Fin J) ≃ Fin n) (D : Fin J → PolynomialCode n)
    (F : σ → PolynomialFractionCode n) : σ ⊕ Fin J → PolynomialFractionCode n :=
  Sum.elim F (rootVelocity e D F)

theorem decode_rootStep (e : (σ ⊕ Fin J) ≃ Fin n) (D : Fin J → PolynomialCode n)
    (F : σ → PolynomialFractionCode n) (roots : Fin J → PolynomialFractionCode n)
    (P : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (W : σ → PolynomialFraction (σ ⊕ Fin J))
    (previous : Fin J → PolynomialFraction (σ ⊕ Fin J))
    (hD : ∀ j, PolynomialCode.decode (D j) = MvPolynomial.rename e (P j))
    (hF : ∀ i, decode (F i) = rename e (W i))
    (hroots : ∀ j, decode (roots j) = rename e (previous j)) (j : Fin J) :
    decode (rootStep e D F roots j) = rename e (TriangularLift.rootStep P W previous j) := by
  have hV : ∀ i, decode (Sum.elim F roots i) = rename e (Sum.elim W previous i) := by
    intro i
    cases i with
    | inl i => exact hF i
    | inr i => exact hroots i
  simp only [rootStep, decode_mulPolynomial, decode_divPolynomial,
    PolynomialCode.decode_varCode, PolynomialCode.decode_mul_code,
    PolynomialCode.decode_constant, RationalCode.decode_ofNat, hD]
  rw [decode_directional e _ _ (hD j) _ _ hV]
  simp [TriangularLift.rootStep]

theorem decode_velocityPrefix (e : (σ ⊕ Fin J) ≃ Fin n) (D : Fin J → PolynomialCode n)
    (F : σ → PolynomialFractionCode n) (P : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (W : σ → PolynomialFraction (σ ⊕ Fin J))
    (hD : ∀ j, PolynomialCode.decode (D j) = MvPolynomial.rename e (P j))
    (hF : ∀ i, decode (F i) = rename e (W i)) (count : ℕ) (j : Fin J) :
    decode (velocityPrefix e D F count j) =
      rename e (TriangularLift.velocityPrefix P W count j) := by
  induction count generalizing j with
  | zero => simp [velocityPrefix, TriangularLift.velocityPrefix]
  | succ count ih =>
    simp only [velocityPrefix, TriangularLift.velocityPrefix]
    split_ifs with h
    · by_cases hj : j = ⟨count, h⟩
      · subst j
        rw [Function.update_self, Function.update_self]
        exact decode_rootStep e D F _ P W _ hD hF ih _
      · rw [Function.update_of_ne hj, Function.update_of_ne hj]
        exact ih j
    · exact ih j

theorem decode_field (e : (σ ⊕ Fin J) ≃ Fin n) (D : Fin J → PolynomialCode n)
    (F : σ → PolynomialFractionCode n) (P : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (W : σ → PolynomialFraction (σ ⊕ Fin J))
    (hD : ∀ j, PolynomialCode.decode (D j) = MvPolynomial.rename e (P j))
    (hF : ∀ i, decode (F i) = rename e (W i)) (i : σ ⊕ Fin J) :
    decode (field e D F i) = rename e (TriangularLift.field P W i) := by
  cases i with
  | inl i => exact hF i
  | inr j => exact decode_velocityPrefix e D F P W hD hF J j

theorem rootStep_primrec {α : Type*} [Primcodable α] (e : (σ ⊕ Fin J) ≃ Fin n)
    (D : α → Fin J → PolynomialCode n) (F : α → σ → PolynomialFractionCode n)
    (roots : α → Fin J → PolynomialFractionCode n)
    (hD : ∀ j, Primrec (fun a ↦ D a j)) (hF : ∀ i, Primrec (fun a ↦ F a i))
    (hroots : ∀ j, Primrec (fun a ↦ roots a j)) (j : Fin J) :
    Primrec (fun a ↦ rootStep e (D a) (F a) (roots a) j) := by
  apply mulPolynomial_primrec.comp (Primrec.const _)
  apply divPolynomial_primrec.comp
  · apply directional_primrec e _ _ (hD j)
    intro i
    cases i with
    | inl i => exact hF i
    | inr i => exact hroots i
  · exact PolynomialCode.mul_primrec.comp (Primrec.const _) (hD j)

theorem velocityPrefix_primrec {α : Type*} [Primcodable α] (e : (σ ⊕ Fin J) ≃ Fin n)
    (D : α → Fin J → PolynomialCode n) (F : α → σ → PolynomialFractionCode n)
    (hD : ∀ j, Primrec (fun a ↦ D a j)) (hF : ∀ i, Primrec (fun a ↦ F a i))
    (count : ℕ) (j : Fin J) : Primrec (fun a ↦ velocityPrefix e (D a) (F a) count j) := by
  induction count generalizing j with
  | zero => exact Primrec.const _
  | succ count ih =>
    by_cases h : count < J
    · by_cases hj : j = ⟨count, h⟩
      · subst j
        simpa only [velocityPrefix, h, ↓reduceDIte, Function.update_self] using
          rootStep_primrec e D F (fun a ↦ velocityPrefix e (D a) (F a) count) hD hF ih ⟨count, h⟩
      · simpa only [velocityPrefix, h, ↓reduceDIte, Function.update_of_ne hj] using ih j
    · simpa only [velocityPrefix, h, ↓reduceDIte] using ih j

theorem field_primrec {α : Type*} [Primcodable α] (e : (σ ⊕ Fin J) ≃ Fin n)
    (D : α → Fin J → PolynomialCode n) (F : α → σ → PolynomialFractionCode n)
    (hD : ∀ j, Primrec (fun a ↦ D a j)) (hF : ∀ i, Primrec (fun a ↦ F a i))
    (i : σ ⊕ Fin J) : Primrec (fun a ↦ field e (D a) (F a) i) := by
  cases i with
  | inl i => exact hF i
  | inr j => exact velocityPrefix_primrec e D F hD hF J j

end

end Stability.TriangularLiftCode
