import Stability.Computability.PolynomialErrorWeightCode

/-!
# Error-weight decoding across an equal root count

The executable code uses one fixed root space. The semantic radical
family may present an equal count through an input-dependent expression.
Eliminating that equality transports the established decoding theorems;
no permutation of the triangular root order is introduced.
-/

namespace Stability.PolynomialErrorWeightCode

open HGAS
open scoped BigOperators

noncomputable section

variable {σ : Type*} {n J K M : ℕ}

def rootCoordinateCast (h : J = K) (e : (σ ⊕ Fin K) ≃ Fin n) :
    (σ ⊕ Fin J) ≃ Fin n :=
  (Equiv.sumCongr (Equiv.refl σ) (finCongr h)).trans e

@[simp]
theorem rootCoordinateCast_refl (e : (σ ⊕ Fin J) ≃ Fin n) :
    rootCoordinateCast rfl e = e := by
  ext i
  cases i <;> rfl

variable [Fintype σ]

theorem decode_familyWeight_cast (h : J = K) (e : (σ ⊕ Fin K) ≃ Fin n)
    (D : Fin K → PolynomialCode n) (P : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (hD : ∀ j, PolynomialCode.decode (D j) =
      MvPolynomial.rename (rootCoordinateCast h e) (P (j.cast h.symm)))
    (outputs : Fin M → PolynomialCode n) (Q : Fin M → MvPolynomial (σ ⊕ Fin J) ℚ)
    (hQ : ∀ i, PolynomialCode.decode (outputs i) =
      MvPolynomial.rename (rootCoordinateCast h e) (Q i)) :
    PolynomialCode.decode (familyWeight e D outputs) =
      MvPolynomial.rename (rootCoordinateCast h e)
        (1 + ∑ i, Simulation.RadicalDefectBounds.polynomialWeight P (Q i)) := by
  subst K
  simp only [rootCoordinateCast_refl, Fin.cast_refl] at hD hQ ⊢
  exact decode_familyWeight e D P hD outputs Q hQ

theorem decode_penalty_cast (h : J = K) (e : (σ ⊕ Fin K) ≃ Fin n) (clock : σ)
    (D : Fin K → PolynomialCode n) (P : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (hD : ∀ j, PolynomialCode.decode (D j) =
      MvPolynomial.rename (rootCoordinateCast h e) (P (j.cast h.symm)))
    (outputs : Fin M → PolynomialCode n) (Q : Fin M → MvPolynomial (σ ⊕ Fin J) ℚ)
    (hQ : ∀ i, PolynomialCode.decode (outputs i) =
      MvPolynomial.rename (rootCoordinateCast h e) (Q i)) :
    PolynomialCode.decode (penalty e clock D outputs) =
      MvPolynomial.rename (rootCoordinateCast h e) ((1 + MvPolynomial.X (.inl clock) ^ 2) *
        (1 + ∑ i, Simulation.RadicalDefectBounds.polynomialWeight P (Q i)) ^ 2 *
        Simulation.RadicalDefectBounds.defectEnergy P) := by
  subst K
  simp only [rootCoordinateCast_refl, Fin.cast_refl] at hD hQ ⊢
  exact decode_penalty e clock D P hD outputs Q hQ

end

end Stability.PolynomialErrorWeightCode
