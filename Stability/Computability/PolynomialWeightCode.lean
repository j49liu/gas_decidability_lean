import Stability.Computability.PolynomialCodeOperations
import Stability.Simulation.RadicalComparison

/-!
# Polynomial envelope and comparison-weight codes

All polynomial operations are performed on finite rational sparse codes.
Coordinate maps and finite enumeration orders are fixed parameters, not
choices made from the input. Decoding identifies the resulting codes
with the actual polynomial majorants used in the global defect estimates.
-/

namespace Stability.PolynomialWeightCode

open HGAS
open scoped BigOperators

noncomputable section

variable {n J : ℕ} {τ : Type*} [Fintype τ]

def envelopeCode (r : τ → Fin n) : PolynomialCode n :=
  PolynomialCode.add PolynomialCode.one (PolynomialCode.sumCodes (List.ofFn
    fun i : Fin (Fintype.card τ) ↦
      PolynomialCode.pow (PolynomialCode.varCode (r ((Fintype.equivFin τ).symm i))) 2))

theorem decode_envelopeCode (r : τ → Fin n) :
    PolynomialCode.decode (envelopeCode r) =
      MvPolynomial.rename r (Simulation.AbsFormula.coordinateEnvelope (σ := τ)) := by
  simp only [envelopeCode, PolynomialCode.decode_add_code, PolynomialCode.decode_one_code,
    PolynomialCode.decode_sumCodes, List.map_ofFn, List.sum_ofFn, Function.comp_apply,
    PolynomialCode.decode_pow_code, PolynomialCode.decode_varCode,
    Simulation.AbsFormula.coordinateEnvelope, map_add, map_one, map_sum, map_pow,
    MvPolynomial.rename_X]
  congr 1
  exact Equiv.sum_comp (Fintype.equivFin τ).symm (fun i ↦ MvPolynomial.X (r i) ^ 2)

def radiusCode (envelope : PolynomialCode n) (bounds : Fin J → PolynomialCode n) :
    PolynomialCode n :=
  PolynomialCode.add envelope (PolynomialCode.sumCodes
    (List.ofFn fun i ↦ PolynomialCode.pow (bounds i) 2))

theorem decode_radiusCode (r : τ → Fin n) (bounds : Fin J → PolynomialCode n)
    (p : Fin J → MvPolynomial τ ℚ)
    (hp : ∀ i, PolynomialCode.decode (bounds i) = MvPolynomial.rename r (p i)) :
    PolynomialCode.decode (radiusCode (envelopeCode r) bounds) =
      MvPolynomial.rename r (Simulation.RadicalMajorant.radius p) := by
  simp [radiusCode, decode_envelopeCode, PolynomialCode.decode_sumCodes,
    List.map_ofFn, List.sum_ofFn, hp, Simulation.RadicalMajorant.radius]

theorem radiusCode_primrec {α : Type*} [Primcodable α]
    (envelope : PolynomialCode n) (bounds : α → Fin J → PolynomialCode n)
    (hb : ∀ i, Primrec (fun a ↦ bounds a i)) :
    Primrec (fun a ↦ radiusCode envelope (bounds a)) := by
  apply PolynomialCode.add_primrec.comp (Primrec.const _)
  apply PolynomialCode.sumCodes_primrec.comp
  exact Primrec.list_ofFn fun i ↦ PolynomialCode.pow_primrec.comp (hb i) (Primrec.const 2)

end

end Stability.PolynomialWeightCode
