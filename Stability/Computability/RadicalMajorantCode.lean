import Stability.Computability.PolynomialWeightCode
import Stability.Computability.PolynomialCodeRealization

/-!
# Effective polynomial majorants for the radical graph

The base-variable majorants are stored in the full extended coordinate
space. Their construction uses the actual decoded coefficient masses and
degrees, computed by exact sparse-code algorithms. The fixed prefix loop
is the same loop as the semantic triangular majorant construction.
-/

namespace Stability.RadicalMajorantCode

open HGAS PolynomialWeightCode PolynomialCodeRealization

noncomputable section

variable {σ : Type*} [Fintype σ] {n J : ℕ}

def step (e : (σ ⊕ Fin J) ≃ Fin n) (D previous : Fin J → PolynomialCode n)
    (j : Fin J) : PolynomialCode n :=
  PolynomialCode.add PolynomialCode.one (PolynomialCode.mul
    (PolynomialCode.constant (PolynomialCode.cubeAbsBoundCode (D j)))
    (PolynomialCode.pow (radiusCode (envelopeCode (fun i ↦ e (.inl i))) previous)
      (degree (D j))))

def boundPrefix (e : (σ ⊕ Fin J) ≃ Fin n) (D : Fin J → PolynomialCode n) :
    ℕ → Fin J → PolynomialCode n
  | 0 => fun _ ↦ PolynomialCode.zero
  | count + 1 =>
      let previous := boundPrefix e D count
      if h : count < J then Function.update previous ⟨count, h⟩
        (step e D previous ⟨count, h⟩) else previous

def majorants (e : (σ ⊕ Fin J) ≃ Fin n) (D : Fin J → PolynomialCode n) :
    Fin J → PolynomialCode n := boundPrefix e D J

theorem decode_step (e : (σ ⊕ Fin J) ≃ Fin n) (D previous : Fin J → PolynomialCode n)
    (P : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ) (p : Fin J → MvPolynomial σ ℚ)
    (hD : ∀ j, PolynomialCode.decode (D j) = MvPolynomial.rename e (P j))
    (hp : ∀ i, PolynomialCode.decode (previous i) =
      MvPolynomial.rename (fun i ↦ e (.inl i)) (p i)) (j : Fin J) :
    PolynomialCode.decode (step e D previous j) =
      MvPolynomial.rename (fun i ↦ e (.inl i)) (Simulation.RadicalMajorant.step P p j) := by
  rw [step, PolynomialCode.decode_add_code, PolynomialCode.decode_one_code,
    PolynomialCode.decode_mul_code, PolynomialCode.decode_constant,
    PolynomialCode.decode_pow_code, decode_radiusCode _ previous p hp,
    decode_cubeAbsBoundCode, degree_eq_totalDegree, hD j,
    coefficientMass_rename_equiv, totalDegree_rename_equiv]
  simp [Simulation.RadicalMajorant.step]

theorem decode_boundPrefix (e : (σ ⊕ Fin J) ≃ Fin n) (D : Fin J → PolynomialCode n)
    (P : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (hD : ∀ j, PolynomialCode.decode (D j) = MvPolynomial.rename e (P j))
    (count : ℕ) (j : Fin J) :
    PolynomialCode.decode (boundPrefix e D count j) =
      MvPolynomial.rename (fun i ↦ e (.inl i))
        (Simulation.RadicalMajorant.boundPrefix P count j) := by
  induction count generalizing j with
  | zero => simp [boundPrefix, Simulation.RadicalMajorant.boundPrefix]
  | succ count ih =>
    simp only [boundPrefix, Simulation.RadicalMajorant.boundPrefix]
    split_ifs with h
    · by_cases hj : j = ⟨count, h⟩
      · subst j
        rw [Function.update_self, Function.update_self]
        exact decode_step e D _ P _ hD ih _
      · rw [Function.update_of_ne hj, Function.update_of_ne hj]
        exact ih j
    · exact ih j

theorem decode_majorants (e : (σ ⊕ Fin J) ≃ Fin n) (D : Fin J → PolynomialCode n)
    (P : Fin J → MvPolynomial (σ ⊕ Fin J) ℚ)
    (hD : ∀ j, PolynomialCode.decode (D j) = MvPolynomial.rename e (P j)) (j : Fin J) :
    PolynomialCode.decode (majorants e D j) =
      MvPolynomial.rename e
        (MvPolynomial.rename Sum.inl (Simulation.RadicalMajorant.majorants P j)) := by
  rw [MvPolynomial.rename_rename]
  exact decode_boundPrefix e D P hD J j

theorem step_primrec {α : Type*} [Primcodable α]
    (e : (σ ⊕ Fin J) ≃ Fin n) (D previous : α → Fin J → PolynomialCode n)
    (hD : ∀ j, Primrec (fun a ↦ D a j)) (hp : ∀ j, Primrec (fun a ↦ previous a j))
    (j : Fin J) : Primrec (fun a ↦ step e (D a) (previous a) j) := by
  apply PolynomialCode.add_primrec.comp (Primrec.const _)
  apply PolynomialCode.mul_primrec.comp
  · exact PolynomialCode.constant_primrec.comp
      (PolynomialCode.cubeAbsBoundCode_primrec.comp (hD j))
  · exact PolynomialCode.pow_primrec.comp (radiusCode_primrec _ previous hp)
      ((degree_primrec n).comp (hD j))

theorem boundPrefix_primrec {α : Type*} [Primcodable α]
    (e : (σ ⊕ Fin J) ≃ Fin n) (D : α → Fin J → PolynomialCode n)
    (hD : ∀ j, Primrec (fun a ↦ D a j)) (count : ℕ) (j : Fin J) :
    Primrec (fun a ↦ boundPrefix e (D a) count j) := by
  induction count generalizing j with
  | zero => exact Primrec.const _
  | succ count ih =>
    by_cases h : count < J
    · by_cases hj : j = ⟨count, h⟩
      · subst j
        simpa only [boundPrefix, h, ↓reduceDIte, Function.update_self] using
          step_primrec e D (fun a ↦ boundPrefix e (D a) count) hD ih ⟨count, h⟩
      · simpa only [boundPrefix, h, ↓reduceDIte, Function.update_of_ne hj] using ih j
    · simpa only [boundPrefix, h, ↓reduceDIte] using ih j

theorem majorants_at_primrec {α : Type*} [Primcodable α]
    (e : (σ ⊕ Fin J) ≃ Fin n) (D : α → Fin J → PolynomialCode n)
    (hD : ∀ j, Primrec (fun a ↦ D a j)) (j : Fin J) :
    Primrec (fun a ↦ majorants e (D a) j) := boundPrefix_primrec e D hD J j

end

end Stability.RadicalMajorantCode
