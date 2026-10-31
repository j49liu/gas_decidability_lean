import Stability.Computability.FormulaTemplate
import Stability.Computability.PowerFractionCode
import Stability.Simulation.FormulaRadicals

/-!
# Effective ordered radical extraction in a fixed target dimension

Root positions depend only on the template, not on the input constants.
The target may replace out-of-range roots by zero; hence the compiler
also covers zero roots without choosing an element of an empty type.
The decoding theorem is an identity with the actual extraction followed
by a polynomial algebra homomorphism.
-/

namespace Stability.FormulaTemplate

open HGAS Simulation

variable {α σ : Type*} {n : ℕ}

abbrev ExpansionCode (n : ℕ) := List (PolynomialCode n) × PowerFractionCode n

/-- Compile directly into the final coordinate space. `roots j` is a
fixed raw code, including the zero fallback for unavailable root indices. -/
def extractCode (r : σ → Fin n) (roots : ℕ → PolynomialCode n)
    (L : α → PolynomialCode n) : FormulaTemplate α σ → ℕ → α → ExpansionCode n
  | .coordinate i, _, _ => ([], PowerFractionCode.ofPolynomial (PolynomialCode.varCode (r i)))
  | .constant c, _, x => ([], PowerFractionCode.ofPolynomial (PolynomialCode.constant (c x)))
  | .add e f, start, x =>
      let E := extractCode r roots L e start x
      let F := extractCode r roots L f (start + e.rootCount) x
      (E.1 ++ F.1, PowerFractionCode.add (L x) E.2 F.2)
  | .mul e f, start, x =>
      let E := extractCode r roots L e start x
      let F := extractCode r roots L f (start + e.rootCount) x
      (E.1 ++ F.1, PowerFractionCode.mul E.2 F.2)
  | .abs e, start, x =>
      let E := extractCode r roots L e start x
      (E.1 ++ [PowerFractionCode.smoothingRadicand (L x) E.2],
        (roots (start + e.rootCount), E.2.2 + 1))

@[simp]
theorem extractCode_length (r : σ → Fin n) (roots : ℕ → PolynomialCode n)
    (L : α → PolynomialCode n) (e : FormulaTemplate α σ) (start : ℕ) (x : α) :
    (extractCode r roots L e start x).1.length = e.rootCount := by
  induction e generalizing start <;> simp_all [extractCode, rootCount]

/-- Exact numerator, exponent, and ordered radicand identities. The
homomorphism can be finite-root restriction followed by coordinate renaming. -/
theorem decode_extractCode (r : σ → Fin n) (roots : ℕ → PolynomialCode n)
    (L : α → PolynomialCode n) (P : α → MvPolynomial σ ℚ)
    (φ : MvPolynomial (σ ⊕ ℕ) ℚ →ₐ[ℚ] MvPolynomial (Fin n) ℚ)
    (hbase : ∀ i, φ (MvPolynomial.X (Sum.inl i)) = MvPolynomial.X (r i))
    (hroots : ∀ j, φ (MvPolynomial.X (Sum.inr j)) = PolynomialCode.decode (roots j))
    (hL : ∀ x, PolynomialCode.decode (L x) = φ (RadicalProgram.basePolynomial (P x)))
    (e : FormulaTemplate α σ) (start : ℕ) (x : α) :
    let E := extractCode r roots L e start x
    let F := AbsFormula.extractRadicals (P x) (e.instantiate x) start
    E.1.map PolynomialCode.decode = F.program.map φ ∧
      PolynomialCode.decode E.2.1 = φ F.result.numerator ∧ E.2.2 = F.result.exponent := by
  induction e generalizing start with
  | coordinate i =>
    simp [extractCode, instantiate, AbsFormula.extractRadicals,
      PowerFractionCode.ofPolynomial, PowerFraction.ofPolynomial, hbase]
  | constant c =>
    simp [extractCode, instantiate, AbsFormula.extractRadicals,
      PowerFractionCode.ofPolynomial, PowerFraction.ofPolynomial]
  | add e f ihE ihF =>
    simp only [extractCode, instantiate, AbsFormula.extractRadicals,
      AbsFormula.extractRadicals_length, radicalCount_instantiate, List.map_append,
      PowerFractionCode.add, PowerFraction.add, PolynomialCode.decode_add_code,
      PolynomialCode.decode_mul_code, PolynomialCode.decode_pow_code,
      map_add, map_mul, map_pow, (ihE start).1, (ihE start).2.1, (ihE start).2.2,
      (ihF (start + e.rootCount)).1, (ihF (start + e.rootCount)).2.1,
      (ihF (start + e.rootCount)).2.2, hL, and_self]
  | mul e f ihE ihF =>
    simp only [extractCode, instantiate, AbsFormula.extractRadicals,
      AbsFormula.extractRadicals_length, radicalCount_instantiate, List.map_append,
      PowerFractionCode.mul, PowerFraction.mul, PolynomialCode.decode_mul_code, map_mul,
      (ihE start).1, (ihE start).2.1, (ihE start).2.2,
      (ihF (start + e.rootCount)).1, (ihF (start + e.rootCount)).2.1,
      (ihF (start + e.rootCount)).2.2, and_self]
  | abs e ih =>
    simp [extractCode, instantiate, AbsFormula.extractRadicals,
      AbsFormula.extractRadicals_length, radicalCount_instantiate, hroots,
      PowerFractionCode.smoothingRadicand, PowerFraction.smoothingRadicand,
      (ih start).1, (ih start).2.1, (ih start).2.2, hL]

/-- A fixed template and fixed allocation offset yield primitive-recursive
codes from primitive-recursive constants and precision codes. -/
theorem extractCode_primrec [Primcodable α] (r : σ → Fin n)
    (roots : ℕ → PolynomialCode n) (L : α → PolynomialCode n) (hL : Primrec L)
    (e : FormulaTemplate α σ) (he : PrimitiveConstants e) (start : ℕ) :
    Primrec (extractCode r roots L e start) := by
  induction e generalizing start with
  | coordinate i => exact Primrec.const _
  | constant c =>
    exact Primrec.pair (Primrec.const []) (PowerFractionCode.ofPolynomial_primrec.comp
      (PolynomialCode.constant_primrec.comp he))
  | add e f ihE ihF =>
    have hE := ihE he.1 start
    have hF := ihF he.2 (start + e.rootCount)
    exact Primrec.pair (Primrec.list_append.comp (Primrec.fst.comp hE) (Primrec.fst.comp hF))
      (PowerFractionCode.add_primrec.comp
        (Primrec.pair hL (Primrec.pair (Primrec.snd.comp hE) (Primrec.snd.comp hF))))
  | mul e f ihE ihF =>
    have hE := ihE he.1 start
    have hF := ihF he.2 (start + e.rootCount)
    exact Primrec.pair (Primrec.list_append.comp (Primrec.fst.comp hE) (Primrec.fst.comp hF))
      (PowerFractionCode.mul_primrec.comp (Primrec.snd.comp hE) (Primrec.snd.comp hF))
  | abs e ih =>
    have hE := ih he start
    exact Primrec.pair
      (Primrec.list_append.comp (Primrec.fst.comp hE)
        (Primrec.list_cons.comp (PowerFractionCode.smoothingRadicand_primrec.comp hL
          (Primrec.snd.comp hE)) (Primrec.const [])))
      (Primrec.pair (Primrec.const _) (Primrec.nat_add.comp
        (Primrec.snd.comp (Primrec.snd.comp hE)) (Primrec.const 1)))

end Stability.FormulaTemplate
