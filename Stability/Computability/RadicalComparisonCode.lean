import Stability.Computability.RadicalMajorantCode

/-!
# Effective polynomial comparison weights

The code uses the full-space cube radius from the actual radical-error
proof and the coefficient mass of each actual formal partial derivative.
In particular, it does not replace a missing partial by an arbitrary
positive bound: the decoded comparison polynomial is exactly the original.
-/

namespace Stability.RadicalComparisonCode

open HGAS PolynomialWeightCode PolynomialCodeRealization

noncomputable section

variable {σ : Type*} [Fintype σ] {n J : ℕ}

def rootBound (e : (σ ⊕ Fin J) ≃ Fin n) (D : Fin J → PolynomialCode n) (i : Fin J) :
    PolynomialCode n :=
  PolynomialCode.add (PolynomialCode.pow (PolynomialCode.varCode (e (.inr i))) 2)
    (RadicalMajorantCode.majorants e D i)

def cubeRadius (e : (σ ⊕ Fin J) ≃ Fin n) (D : Fin J → PolynomialCode n) :
    PolynomialCode n := radiusCode (envelopeCode e) (rootBound e D)

def weight (e : (σ ⊕ Fin J) ≃ Fin n) (D : Fin J → PolynomialCode n)
    (p : PolynomialCode n) (i : Fin J) : PolynomialCode n :=
  PolynomialCode.mul
    (PolynomialCode.constant
      (PolynomialCode.cubeAbsBoundCode (PolynomialCode.pderiv (e (.inr i)) p)))
    (PolynomialCode.pow (cubeRadius e D) (degree p))

theorem decode_rootBound (e : (σ ⊕ Fin J) ≃ Fin n) (D : Fin J → PolynomialCode n)
    (P : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (hD : ∀ j, PolynomialCode.decode (D j) = MvPolynomial.rename e (P j)) (i : Fin J) :
    PolynomialCode.decode (rootBound e D i) =
      MvPolynomial.rename e (Simulation.RadicalComparison.rootBound P i) := by
  simp [rootBound, RadicalMajorantCode.decode_majorants e D P hD,
    Simulation.RadicalComparison.rootBound]

theorem decode_cubeRadius (e : (σ ⊕ Fin J) ≃ Fin n) (D : Fin J → PolynomialCode n)
    (P : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (hD : ∀ j, PolynomialCode.decode (D j) = MvPolynomial.rename e (P j)) :
    PolynomialCode.decode (cubeRadius e D) =
      MvPolynomial.rename e (Simulation.RadicalComparison.cubeRadius P) :=
  decode_radiusCode e _ _ (decode_rootBound e D P hD)

theorem decode_weight (e : (σ ⊕ Fin J) ≃ Fin n) (D : Fin J → PolynomialCode n)
    (P : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (hD : ∀ j, PolynomialCode.decode (D j) = MvPolynomial.rename e (P j))
    (p : PolynomialCode n) (Q : MvPolynomial (σ ⊕ Fin J) ℚ)
    (hp : PolynomialCode.decode p = MvPolynomial.rename e Q) (i : Fin J) :
    PolynomialCode.decode (weight e D p i) =
      MvPolynomial.rename e (Simulation.RadicalComparison.weight P Q i) := by
  rw [weight, PolynomialCode.decode_mul_code, PolynomialCode.decode_constant,
    PolynomialCode.decode_pow_code, decode_cubeAbsBoundCode, PolynomialCode.decode_pderiv,
    degree_eq_totalDegree, hp, pderiv_rename_equiv, coefficientMass_rename_equiv,
    totalDegree_rename_equiv, decode_cubeRadius e D P hD]
  simp [Simulation.RadicalComparison.weight]

theorem rootBound_primrec {α : Type*} [Primcodable α]
    (e : (σ ⊕ Fin J) ≃ Fin n) (D : α → Fin J → PolynomialCode n)
    (hD : ∀ j, Primrec (fun a ↦ D a j)) (i : Fin J) :
    Primrec (fun a ↦ rootBound e (D a) i) :=
  PolynomialCode.add_primrec.comp (Primrec.const _)
    (RadicalMajorantCode.majorants_at_primrec e D hD i)

theorem cubeRadius_primrec {α : Type*} [Primcodable α]
    (e : (σ ⊕ Fin J) ≃ Fin n) (D : α → Fin J → PolynomialCode n)
    (hD : ∀ j, Primrec (fun a ↦ D a j)) : Primrec (fun a ↦ cubeRadius e (D a)) :=
  radiusCode_primrec _ (fun a ↦ rootBound e (D a)) (rootBound_primrec e D hD)

theorem weight_primrec {α : Type*} [Primcodable α]
    (e : (σ ⊕ Fin J) ≃ Fin n) (D : α → Fin J → PolynomialCode n) (p : α → PolynomialCode n)
    (hD : ∀ j, Primrec (fun a ↦ D a j)) (hp : Primrec p) (i : Fin J) :
    Primrec (fun a ↦ weight e (D a) (p a) i) := by
  apply PolynomialCode.mul_primrec.comp
  · exact PolynomialCode.constant_primrec.comp (PolynomialCode.cubeAbsBoundCode_primrec.comp
      (PolynomialCode.pderiv_primrec.comp (Primrec.const _) hp))
  · exact PolynomialCode.pow_primrec.comp (cubeRadius_primrec e D hD) ((degree_primrec n).comp hp)

end

end Stability.RadicalComparisonCode
