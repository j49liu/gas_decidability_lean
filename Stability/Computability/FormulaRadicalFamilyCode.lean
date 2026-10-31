import Stability.Computability.FormulaRadicalCode
import Stability.Simulation.FormulaRadicalFamily

/-!
# Effective shared radical extraction for a fixed formula family

Every output retains its original position, and every radicand retains
its extraction order. Fresh root offsets are computed from the fixed
syntax, so they are independent of the input constants.
-/

namespace Stability.FormulaTemplate

open HGAS Simulation

variable {α σ : Type*} {n : ℕ}

abbrev FamilyExpansionCode (n : ℕ) := List (PolynomialCode n) × List (PowerFractionCode n)

def extractFamilyCode (r : σ → Fin n) (roots : ℕ → PolynomialCode n)
    (L : α → PolynomialCode n) : List (FormulaTemplate α σ) → ℕ → α → FamilyExpansionCode n
  | [], _, _ => ([], [])
  | e :: es, start, x =>
      let E := extractCode r roots L e start x
      let F := extractFamilyCode r roots L es (start + e.rootCount) x
      (E.1 ++ F.1, E.2 :: F.2)

theorem extractFamilyCode_lengths (r : σ → Fin n) (roots : ℕ → PolynomialCode n)
    (L : α → PolynomialCode n) (es : List (FormulaTemplate α σ)) (start : ℕ) (x : α) :
    (extractFamilyCode r roots L es start x).1.length = (es.map rootCount).sum ∧
      (extractFamilyCode r roots L es start x).2.length = es.length := by
  induction es generalizing start with
  | nil => simp [extractFamilyCode]
  | cons e es ih => simp [extractFamilyCode, extractCode_length, ih]

/-- The decoded lists equal the actual ordered extraction after the
specified polynomial coordinate homomorphism. -/
theorem decode_extractFamilyCode (r : σ → Fin n) (roots : ℕ → PolynomialCode n)
    (L : α → PolynomialCode n) (P : α → MvPolynomial σ ℚ)
    (φ : MvPolynomial (σ ⊕ ℕ) ℚ →ₐ[ℚ] MvPolynomial (Fin n) ℚ)
    (hbase : ∀ i, φ (MvPolynomial.X (Sum.inl i)) = MvPolynomial.X (r i))
    (hroots : ∀ j, φ (MvPolynomial.X (Sum.inr j)) = PolynomialCode.decode (roots j))
    (hL : ∀ x, PolynomialCode.decode (L x) = φ (RadicalProgram.basePolynomial (P x)))
    (es : List (FormulaTemplate α σ)) (start : ℕ) (x : α) :
    let E := extractFamilyCode r roots L es start x
    let F := AbsFormula.extractRadicalFamily (P x) (es.map (instantiate · x)) start
    E.1.map PolynomialCode.decode = F.program.map φ ∧
      E.2.map (fun f ↦ (PolynomialCode.decode f.1, f.2)) =
        F.results.map (fun f ↦ (φ f.numerator, f.exponent)) := by
  induction es generalizing start with
  | nil => simp [extractFamilyCode, AbsFormula.extractRadicalFamily]
  | cons e es ih =>
    obtain ⟨hprog, hnum, hexp⟩ := decode_extractCode r roots L P φ hbase hroots hL e start x
    simp only [extractFamilyCode, List.map_cons, AbsFormula.extractRadicalFamily,
      AbsFormula.extractRadicals_length, radicalCount_instantiate,
      List.map_append, hprog, hnum, hexp, (ih (start + e.rootCount)).1,
      (ih (start + e.rootCount)).2, and_self]

theorem extractFamilyCode_primrec [Primcodable α] (r : σ → Fin n)
    (roots : ℕ → PolynomialCode n) (L : α → PolynomialCode n) (hL : Primrec L)
    (es : List (FormulaTemplate α σ)) (he : ∀ e ∈ es, PrimitiveConstants e) (start : ℕ) :
    Primrec (extractFamilyCode r roots L es start) := by
  induction es generalizing start with
  | nil => exact Primrec.const _
  | cons e es ih =>
    have hE := extractCode_primrec r roots L hL e (he e (by simp)) start
    have hF := ih (fun e he' ↦ he e (List.mem_cons_of_mem _ he')) (start + e.rootCount)
    exact Primrec.pair
      (Primrec.list_append.comp (Primrec.fst.comp hE) (Primrec.fst.comp hF))
      (Primrec.list_cons.comp (Primrec.snd.comp hE) (Primrec.snd.comp hF))

end Stability.FormulaTemplate
