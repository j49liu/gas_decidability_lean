import Stability.Computability.PolynomialCodeOperations
import Stability.Simulation.RadicalDefectBounds

/-!
# Effective quartic defects and their energy

The auxiliary coordinates are squared by literal coded substitution.
Subtracting the resulting radicands from fourth powers and summing their
squares gives the exact defect energy, including an empty root family.
-/

namespace Stability.PolynomialDefectCode

open HGAS
open scoped BigOperators

variable {σ : Type*} {n J : ℕ}

def squareVariable (e : (σ ⊕ Fin J) ≃ Fin n) (i : Fin n) : PolynomialCode n :=
  match e.symm i with
  | .inl j => PolynomialCode.varCode (e (.inl j))
  | .inr j => PolynomialCode.pow (PolynomialCode.varCode (e (.inr j))) 2

def squareCode (e : (σ ⊕ Fin J) ≃ Fin n) (p : PolynomialCode n) : PolynomialCode n :=
  PolynomialCodeOperations.substitute (squareVariable e) p

theorem decode_squareCode (e : (σ ⊕ Fin J) ≃ Fin n) (p : PolynomialCode n)
    (P : MvPolynomial (σ ⊕ Fin J) ℚ)
    (hp : PolynomialCode.decode p = MvPolynomial.rename e P) :
    PolynomialCode.decode (squareCode e p) =
      MvPolynomial.rename e (Simulation.RadicalProgram.squareRootsPolynomial P) := by
  rw [squareCode, PolynomialCodeOperations.decode_substitute, hp,
    Simulation.RadicalProgram.squareRootsPolynomial,
    MvPolynomial.bind₁_rename, MvPolynomial.rename_bind₁]
  congr 1
  congr 1
  funext i
  cases i <;> simp [squareVariable, Simulation.RadicalProgram.squareRootVariable]

def defectCode (e : (σ ⊕ Fin J) ≃ Fin n) (D : Fin J → PolynomialCode n)
    (j : Fin J) : PolynomialCode n :=
  PolynomialCode.sub (PolynomialCode.pow (PolynomialCode.varCode (e (.inr j))) 4)
    (squareCode e (D j))

def energyCode (e : (σ ⊕ Fin J) ≃ Fin n) (D : Fin J → PolynomialCode n) :
    PolynomialCode n :=
  PolynomialCode.sumCodes (List.ofFn fun j ↦ PolynomialCode.pow (defectCode e D j) 2)

theorem decode_defectCode (e : (σ ⊕ Fin J) ≃ Fin n)
    (D : Fin J → PolynomialCode n) (P : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (hD : ∀ j, PolynomialCode.decode (D j) = MvPolynomial.rename e (P j)) (j : Fin J) :
    PolynomialCode.decode (defectCode e D j) =
      MvPolynomial.rename e (Simulation.RadicalDefectBounds.defect P j) := by
  simp [defectCode, decode_squareCode e (D j) (P j) (hD j),
    Simulation.RadicalDefectBounds.defect]

theorem decode_energyCode (e : (σ ⊕ Fin J) ≃ Fin n)
    (D : Fin J → PolynomialCode n) (P : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (hD : ∀ j, PolynomialCode.decode (D j) = MvPolynomial.rename e (P j)) :
    PolynomialCode.decode (energyCode e D) =
      MvPolynomial.rename e (Simulation.RadicalDefectBounds.defectEnergy P) := by
  simp [energyCode, PolynomialCode.decode_sumCodes, List.map_ofFn, List.sum_ofFn,
    decode_defectCode e D P hD, Simulation.RadicalDefectBounds.defectEnergy]

theorem squareCode_primrec (e : (σ ⊕ Fin J) ≃ Fin n) : Primrec (squareCode e) :=
  PolynomialCodeOperations.substitute_primrec.comp (Primrec.const _) Primrec.id

theorem defectCode_primrec {α : Type*} [Primcodable α]
    (e : (σ ⊕ Fin J) ≃ Fin n) (D : α → Fin J → PolynomialCode n)
    (hD : ∀ j, Primrec (fun a ↦ D a j)) (j : Fin J) :
    Primrec (fun a ↦ defectCode e (D a) j) :=
  PolynomialCode.sub_primrec.comp (Primrec.const _) ((squareCode_primrec e).comp (hD j))

theorem energyCode_primrec {α : Type*} [Primcodable α]
    (e : (σ ⊕ Fin J) ≃ Fin n) (D : α → Fin J → PolynomialCode n)
    (hD : ∀ j, Primrec (fun a ↦ D a j)) : Primrec (fun a ↦ energyCode e (D a)) := by
  apply PolynomialCode.sumCodes_primrec.comp
  exact Primrec.list_ofFn fun j ↦
    PolynomialCode.pow_primrec.comp (defectCode_primrec e D hD j) (Primrec.const 2)

end Stability.PolynomialDefectCode
