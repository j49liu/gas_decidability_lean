import Stability.Computability.RadicalComparisonCode
import Stability.Computability.TriangularWeightCode
import Stability.Computability.PolynomialDefectCode

/-!
# Effective polynomial error weights and the clock penalty

The literal comparison coefficients feed the finite triangular recursion.
Their resulting root weights give polynomial and finite-family error
weights. The penalty multiplies the squared family weight by the clock
factor and the quartic defect energy. Every operation is performed on
raw polynomial codes, with exact decoding and primitive-recursion proofs.
-/

namespace Stability.PolynomialErrorWeightCode

open HGAS
open scoped BigOperators

noncomputable section

variable {σ : Type*} [Fintype σ] {n J M : ℕ}

def coefficients (e : (σ ⊕ Fin J) ≃ Fin n) (D : Fin J → PolynomialCode n)
    (j i : Fin J) : PolynomialCode n :=
  RadicalComparisonCode.weight e D (D j) i

def rootWeights (e : (σ ⊕ Fin J) ≃ Fin n) (D : Fin J → PolynomialCode n) :
    Fin J → PolynomialCode n :=
  TriangularWeightCode.weights (coefficients e D)

def polynomialWeight (e : (σ ⊕ Fin J) ≃ Fin n) (D : Fin J → PolynomialCode n)
    (p : PolynomialCode n) : PolynomialCode n :=
  PolynomialCode.sumCodes (List.ofFn fun i ↦
    PolynomialCode.mul (RadicalComparisonCode.weight e D p i) (rootWeights e D i))

def familyWeight (e : (σ ⊕ Fin J) ≃ Fin n) (D : Fin J → PolynomialCode n)
    (outputs : Fin M → PolynomialCode n) : PolynomialCode n :=
  PolynomialCode.add PolynomialCode.one
    (PolynomialCode.sumCodes (List.ofFn fun i ↦ polynomialWeight e D (outputs i)))

def penalty (e : (σ ⊕ Fin J) ≃ Fin n) (clock : σ) (D : Fin J → PolynomialCode n)
    (outputs : Fin M → PolynomialCode n) : PolynomialCode n :=
  PolynomialCode.mul
    (PolynomialCode.mul
      (PolynomialCode.add PolynomialCode.one
        (PolynomialCode.pow (PolynomialCode.varCode (e (.inl clock))) 2))
      (PolynomialCode.pow (familyWeight e D outputs) 2))
    (PolynomialDefectCode.energyCode e D)

section Decoding

theorem decode_coefficients (e : (σ ⊕ Fin J) ≃ Fin n)
    (D : Fin J → PolynomialCode n) (P : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (hD : ∀ j, PolynomialCode.decode (D j) = MvPolynomial.rename e (P j)) (j i : Fin J) :
    PolynomialCode.decode (coefficients e D j i) =
      MvPolynomial.rename e (Simulation.RadicalDefectBounds.coefficients P j i) :=
  RadicalComparisonCode.decode_weight e D P hD (D j) (P j) (hD j) i

theorem decode_rootWeights (e : (σ ⊕ Fin J) ≃ Fin n)
    (D : Fin J → PolynomialCode n) (P : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (hD : ∀ j, PolynomialCode.decode (D j) = MvPolynomial.rename e (P j)) (j : Fin J) :
    PolynomialCode.decode (rootWeights e D j) =
      MvPolynomial.rename e (Simulation.RadicalDefectBounds.rootWeights P j) :=
  TriangularWeightCode.decode_weights e (coefficients e D)
    (Simulation.RadicalDefectBounds.coefficients P) (decode_coefficients e D P hD) j

theorem decode_polynomialWeight (e : (σ ⊕ Fin J) ≃ Fin n)
    (D : Fin J → PolynomialCode n) (P : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (hD : ∀ j, PolynomialCode.decode (D j) = MvPolynomial.rename e (P j))
    (p : PolynomialCode n) (Q : MvPolynomial (σ ⊕ Fin J) ℚ)
    (hp : PolynomialCode.decode p = MvPolynomial.rename e Q) :
    PolynomialCode.decode (polynomialWeight e D p) =
      MvPolynomial.rename e (Simulation.RadicalDefectBounds.polynomialWeight P Q) := by
  simp only [polynomialWeight, PolynomialCode.decode_sumCodes, List.map_ofFn, List.sum_ofFn,
    Function.comp_apply, PolynomialCode.decode_mul_code,
    RadicalComparisonCode.decode_weight e D P hD p Q hp, decode_rootWeights e D P hD,
    Simulation.RadicalDefectBounds.polynomialWeight, map_sum, map_mul]

theorem decode_familyWeight (e : (σ ⊕ Fin J) ≃ Fin n)
    (D : Fin J → PolynomialCode n) (P : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (hD : ∀ j, PolynomialCode.decode (D j) = MvPolynomial.rename e (P j))
    (outputs : Fin M → PolynomialCode n) (Q : Fin M → MvPolynomial (σ ⊕ Fin J) ℚ)
    (hQ : ∀ i, PolynomialCode.decode (outputs i) = MvPolynomial.rename e (Q i)) :
    PolynomialCode.decode (familyWeight e D outputs) =
      MvPolynomial.rename e (1 + ∑ i, Simulation.RadicalDefectBounds.polynomialWeight P (Q i)) := by
  simp only [familyWeight, PolynomialCode.decode_add_code, PolynomialCode.decode_one_code,
    PolynomialCode.decode_sumCodes, List.map_ofFn, List.sum_ofFn, Function.comp_apply,
    decode_polynomialWeight e D P hD _ _ (hQ _), map_add, map_one, map_sum]

theorem decode_penalty (e : (σ ⊕ Fin J) ≃ Fin n) (clock : σ)
    (D : Fin J → PolynomialCode n) (P : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (hD : ∀ j, PolynomialCode.decode (D j) = MvPolynomial.rename e (P j))
    (outputs : Fin M → PolynomialCode n) (Q : Fin M → MvPolynomial (σ ⊕ Fin J) ℚ)
    (hQ : ∀ i, PolynomialCode.decode (outputs i) = MvPolynomial.rename e (Q i)) :
    PolynomialCode.decode (penalty e clock D outputs) =
      MvPolynomial.rename e ((1 + MvPolynomial.X (.inl clock) ^ 2) *
        (1 + ∑ i, Simulation.RadicalDefectBounds.polynomialWeight P (Q i)) ^ 2 *
        Simulation.RadicalDefectBounds.defectEnergy P) := by
  simp only [penalty, PolynomialCode.decode_mul_code, PolynomialCode.decode_add_code,
    PolynomialCode.decode_one_code, PolynomialCode.decode_pow_code,
    PolynomialCode.decode_varCode, decode_familyWeight e D P hD outputs Q hQ,
    PolynomialDefectCode.decode_energyCode e D P hD, map_mul, map_add, map_pow, map_one,
    MvPolynomial.rename_X]

end Decoding

section Computability

variable {α : Type*} [Primcodable α]

theorem coefficients_primrec (e : (σ ⊕ Fin J) ≃ Fin n)
    (D : α → Fin J → PolynomialCode n) (hD : ∀ j, Primrec (fun a ↦ D a j)) (j i : Fin J) :
    Primrec (fun a ↦ coefficients e (D a) j i) :=
  RadicalComparisonCode.weight_primrec e D (fun a ↦ D a j) hD (hD j) i

theorem rootWeights_primrec (e : (σ ⊕ Fin J) ≃ Fin n)
    (D : α → Fin J → PolynomialCode n) (hD : ∀ j, Primrec (fun a ↦ D a j)) (j : Fin J) :
    Primrec (fun a ↦ rootWeights e (D a) j) :=
  TriangularWeightCode.weights_at_primrec (fun a ↦ coefficients e (D a))
    (coefficients_primrec e D hD) j

theorem polynomialWeight_primrec (e : (σ ⊕ Fin J) ≃ Fin n)
    (D : α → Fin J → PolynomialCode n) (p : α → PolynomialCode n)
    (hD : ∀ j, Primrec (fun a ↦ D a j)) (hp : Primrec p) :
    Primrec (fun a ↦ polynomialWeight e (D a) (p a)) := by
  apply PolynomialCode.sumCodes_primrec.comp
  exact Primrec.list_ofFn fun i ↦ PolynomialCode.mul_primrec.comp
    (RadicalComparisonCode.weight_primrec e D p hD hp i) (rootWeights_primrec e D hD i)

theorem familyWeight_primrec (e : (σ ⊕ Fin J) ≃ Fin n)
    (D : α → Fin J → PolynomialCode n) (outputs : α → Fin M → PolynomialCode n)
    (hD : ∀ j, Primrec (fun a ↦ D a j)) (hQ : ∀ i, Primrec (fun a ↦ outputs a i)) :
    Primrec (fun a ↦ familyWeight e (D a) (outputs a)) := by
  apply PolynomialCode.add_primrec.comp (Primrec.const _)
  apply PolynomialCode.sumCodes_primrec.comp
  exact Primrec.list_ofFn fun i ↦ polynomialWeight_primrec e D (fun a ↦ outputs a i) hD (hQ i)

theorem penalty_primrec (e : (σ ⊕ Fin J) ≃ Fin n) (clock : σ)
    (D : α → Fin J → PolynomialCode n) (outputs : α → Fin M → PolynomialCode n)
    (hD : ∀ j, Primrec (fun a ↦ D a j)) (hQ : ∀ i, Primrec (fun a ↦ outputs a i)) :
    Primrec (fun a ↦ penalty e clock (D a) (outputs a)) :=
  PolynomialCode.mul_primrec.comp
    (PolynomialCode.mul_primrec.comp (Primrec.const _)
      (PolynomialCode.pow_primrec.comp (familyWeight_primrec e D outputs hD hQ)
        (Primrec.const 2)))
    (PolynomialDefectCode.energyCode_primrec e D hD)

end Computability

end

end Stability.PolynomialErrorWeightCode
