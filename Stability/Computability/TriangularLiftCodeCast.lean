import Stability.Computability.TriangularLiftCode
import Stability.Computability.PolynomialErrorWeightCast
import Stability.Computability.PolynomialDefectCode

/-!
# Literal radical-lift decoding across equal root counts

Only equality casts are used, so the fixed order of fraction sums and of
the triangular velocity recursion is unchanged.
-/

namespace Stability

open HGAS Simulation PolynomialErrorWeightCode

noncomputable section

variable {σ : Type*} {n J K : ℕ}

theorem PolynomialDefectCode.decode_squareCode_cast (h : J = K)
    (e : (σ ⊕ Fin K) ≃ Fin n) (p : PolynomialCode n)
    (P : MvPolynomial (σ ⊕ Fin J) ℚ)
    (hp : PolynomialCode.decode p = MvPolynomial.rename (rootCoordinateCast h e) P) :
    PolynomialCode.decode (PolynomialDefectCode.squareCode e p) =
      MvPolynomial.rename (rootCoordinateCast h e) (RadicalProgram.squareRootsPolynomial P) := by
  subst K
  simp only [rootCoordinateCast_refl] at hp ⊢
  exact PolynomialDefectCode.decode_squareCode e p P hp

variable [Fintype σ]

theorem TriangularLiftCode.decode_field_cast (h : J = K) (e : (σ ⊕ Fin K) ≃ Fin n)
    (D : Fin K → PolynomialCode n) (F : σ → PolynomialFractionCode n)
    (P : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (W : σ → PolynomialFraction (σ ⊕ Fin J))
    (hD : ∀ j, PolynomialCode.decode (D j) =
      MvPolynomial.rename (rootCoordinateCast h e) (P (j.cast h.symm)))
    (hF : ∀ i, PolynomialFractionCode.decode (F i) =
      PolynomialFractionCode.rename (rootCoordinateCast h e) (W i)) (i : σ ⊕ Fin K) :
    PolynomialFractionCode.decode (TriangularLiftCode.field e D F i) =
      PolynomialFractionCode.rename (rootCoordinateCast h e)
        (TriangularLift.field P W
          ((Equiv.sumCongr (Equiv.refl σ) (finCongr h)).symm i)) := by
  subst K
  simp only [rootCoordinateCast_refl, Fin.cast_refl, finCongr_refl,
    Equiv.sumCongr_refl, Equiv.refl_symm, Equiv.refl_apply] at hD hF ⊢
  exact TriangularLiftCode.decode_field e D F P W hD hF i

end

end Stability
