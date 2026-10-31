import Stability.Computability.PolynomialCodeRealization
import Stability.Dynamics.FiniteOutputConjugacy

/-!
# Decoded polynomial codes and finite-coordinate conjugacy

An exact polynomial renaming identity supplies both the vector-field
conjugacy and the scalar-output identity. Thus finite output bounds can
be transferred from the semantic monitor's coordinate type to the fixed
`Fin n` space of its generated code without changing the ODE convention.
-/

namespace Stability.PolynomialCodeRealization

open HGAS

noncomputable section

variable {σ : Type*} {n : ℕ}

def coordinateLinearEquiv (e : σ ≃ Fin n) : (σ → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ ↦ ℝ) e

@[simp] theorem coordinateLinearEquiv_apply (e : σ ≃ Fin n) (x : σ → ℝ) (i : Fin n) :
    coordinateLinearEquiv e x i = x (e.symm i) := by
  change (Equiv.piCongrLeft (fun _ ↦ ℝ) e) x i = _
  rw [Equiv.piCongrLeft_apply]
  simp

@[simp] theorem coordinateLinearEquiv_symm_apply (e : σ ≃ Fin n)
    (x : Fin n → ℝ) (i : σ) : (coordinateLinearEquiv e).symm x i = x (e i) := rfl

theorem realize_eq_conjugateField [Fintype σ] (e : σ ≃ Fin n) (F : PolynomialFieldCode n)
    (P : σ → MvPolynomial σ ℚ)
    (hF : ∀ i, PolynomialCode.decode (F i) = MvPolynomial.rename e (P (e.symm i))) :
    PolynomialFieldCode.realize F = HGAS.conjugateField (coordinateLinearEquiv e)
      (fun x i ↦ Simulation.AbsFormula.polynomialValue x (P i)) := by
  funext x i
  simp only [PolynomialFieldCode.realize_apply, hF, MvPolynomial.eval₂Hom_rename,
    HGAS.conjugateField, coordinateLinearEquiv_apply, Simulation.AbsFormula.polynomialValue]
  rfl

theorem output_eq_conjugate (e : σ ≃ Fin n) (b : PolynomialCode n) (p : MvPolynomial σ ℚ)
    (hb : PolynomialCode.decode b = MvPolynomial.rename e p) :
    (fun x ↦ MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x (PolynomialCode.decode b)) =
      fun x ↦ Simulation.AbsFormula.polynomialValue ((coordinateLinearEquiv e).symm x) p := by
  funext x
  rw [hb, MvPolynomial.eval₂Hom_rename]
  rfl

theorem hasBoundedFiniteOutput_codes_iff [Fintype σ] (e : σ ≃ Fin n) (F : PolynomialFieldCode n)
    (b : PolynomialCode n) (P : σ → MvPolynomial σ ℚ) (p : MvPolynomial σ ℚ)
    (hF : ∀ i, PolynomialCode.decode (F i) = MvPolynomial.rename e (P (e.symm i)))
    (hb : PolynomialCode.decode b = MvPolynomial.rename e p) :
    HasBoundedFiniteOutput (PolynomialFieldCode.realize F)
        (fun x ↦ MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x (PolynomialCode.decode b)) ↔
      HasBoundedFiniteOutput (fun x i ↦ Simulation.AbsFormula.polynomialValue x (P i))
        (fun x ↦ Simulation.AbsFormula.polynomialValue x p) := by
  rw [realize_eq_conjugateField e F P hF, output_eq_conjugate e b p hb]
  exact (hasBoundedFiniteOutput_iff_conjugateField (coordinateLinearEquiv e)
    (F := fun x i ↦ Simulation.AbsFormula.polynomialValue x (P i))
    (g := fun x ↦ Simulation.AbsFormula.polynomialValue x p)).symm

end

end Stability.PolynomialCodeRealization
