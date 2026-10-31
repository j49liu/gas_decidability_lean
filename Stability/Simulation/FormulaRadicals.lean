import Stability.Simulation.RadicalProgram

/-!
# Extracting an ordered radical program from a smoothed formula

The compiler traverses a formula from the inside out. Every absolute-value
node appends one polynomial radicand and replaces its square root by a
fresh root variable divided by a power of the common precision. Constants
are never simplified, so the number of roots is exactly the syntactic
absolute-value count.
-/

namespace Stability.Simulation

/-- A finite root program and the rational expression for its output. -/
structure RadicalExpansion (σ : Type*) where
  program : RadicalProgram.Program σ
  result : PowerFraction (σ ⊕ ℕ)

namespace AbsFormula

noncomputable section

open RadicalProgram

variable {σ : Type*}

/-- Extract radicals using fresh root indices starting at `start`.
All denominators remain powers of the specified precision polynomial. -/
def extractRadicals (L : MvPolynomial σ ℚ) : AbsFormula σ → ℕ → RadicalExpansion σ
  | .coordinate i, _ => ⟨[], PowerFraction.ofPolynomial (MvPolynomial.X (Sum.inl i))⟩
  | .constant c, _ => ⟨[], PowerFraction.ofPolynomial (MvPolynomial.C c)⟩
  | .add e f, start =>
      let E := extractRadicals L e start
      let F := extractRadicals L f (start + E.program.length)
      ⟨E.program ++ F.program, PowerFraction.add (basePolynomial L) E.result F.result⟩
  | .mul e f, start =>
      let E := extractRadicals L e start
      let F := extractRadicals L f (start + E.program.length)
      ⟨E.program ++ F.program, PowerFraction.mul E.result F.result⟩
  | .abs e, start =>
      let E := extractRadicals L e start
      ⟨E.program ++ [PowerFraction.smoothingRadicand (basePolynomial L) E.result],
        ⟨MvPolynomial.X (Sum.inr (start + E.program.length)), E.result.exponent + 1⟩⟩

/-- The compiler keeps exactly one root per absolute-value node, including
nodes whose values happen to simplify at special coefficients. -/
theorem extractRadicals_length (L : MvPolynomial σ ℚ) (e : AbsFormula σ) (start : ℕ) :
    (extractRadicals L e start).program.length = radicalCount e := by
  induction e generalizing start with
  | coordinate i => rfl
  | constant c => rfl
  | add e f he hf => simp [extractRadicals, radicalCount, he, hf]
  | mul e f he hf => simp [extractRadicals, radicalCount, he, hf]
  | abs e he => simp [extractRadicals, radicalCount, he]

/-- Every generated radicand uses only earlier roots, and the final
numerator uses only roots allocated by the program or its prefix. -/
theorem extractRadicals_wellFormed (L : MvPolynomial σ ℚ) (e : AbsFormula σ) (start : ℕ) :
    Triangular (extractRadicals L e start).program start ∧
      DependsBelow (extractRadicals L e start).result.numerator
        (start + (extractRadicals L e start).program.length) := by
  induction e generalizing start with
  | coordinate i => exact ⟨trivial, dependsBelow_X_base i start⟩
  | constant c => exact ⟨trivial, dependsBelow_C c start⟩
  | add e f he hf =>
      let E := extractRadicals L e start
      let F := extractRadicals L f (start + E.program.length)
      obtain ⟨hE, hEnum⟩ := he start
      change DependsBelow E.result.numerator (start + E.program.length) at hEnum
      obtain ⟨hF, hFnum⟩ := hf (start + E.program.length)
      change Triangular (E.program ++ F.program) start ∧ _
      refine ⟨(triangular_append _ _ _).mpr ⟨hE, hF⟩, ?_⟩
      change DependsBelow
        (E.result.numerator * basePolynomial L ^ F.result.exponent +
          F.result.numerator * basePolynomial L ^ E.result.exponent)
        (start + (E.program ++ F.program).length)
      have hE' : DependsBelow E.result.numerator (start + (E.program ++ F.program).length) :=
        hEnum.mono (by simp only [List.length_append]; omega)
      have hF' : DependsBelow F.result.numerator (start + (E.program ++ F.program).length) := by
        simpa only [List.length_append, Nat.add_assoc] using hFnum
      exact (hE'.mul ((dependsBelow_basePolynomial L _).pow _)).add
        (hF'.mul ((dependsBelow_basePolynomial L _).pow _))
  | mul e f he hf =>
      let E := extractRadicals L e start
      let F := extractRadicals L f (start + E.program.length)
      obtain ⟨hE, hEnum⟩ := he start
      change DependsBelow E.result.numerator (start + E.program.length) at hEnum
      obtain ⟨hF, hFnum⟩ := hf (start + E.program.length)
      change Triangular (E.program ++ F.program) start ∧ _
      refine ⟨(triangular_append _ _ _).mpr ⟨hE, hF⟩, ?_⟩
      change DependsBelow (E.result.numerator * F.result.numerator)
        (start + (E.program ++ F.program).length)
      apply (hEnum.mono (by simp only [List.length_append]; omega)).mul
      simpa only [List.length_append, Nat.add_assoc] using hFnum
  | abs e he =>
      let E := extractRadicals L e start
      obtain ⟨hE, hEnum⟩ := he start
      change Triangular
        (E.program ++ [PowerFraction.smoothingRadicand (basePolynomial L) E.result]) start ∧ _
      refine ⟨(triangular_append _ _ _).mpr ⟨hE, ?_⟩, ?_⟩
      · refine ⟨?_, trivial⟩
        exact ((hEnum.pow 2).mul ((dependsBelow_basePolynomial L _).pow 2)).add
          ((dependsBelow_basePolynomial L _).pow _)
      · apply dependsBelow_X_root
        change start + E.program.length < start + (E.program ++ [_]).length
        simp only [List.length_append, List.length_singleton]
        omega

/-- Under the actual generated root equations, the extracted rational
expression is exactly the inside-out smoothed formula. The next theorem
constructs such a root assignment by sequential evaluation. -/
theorem extractRadicals_value (L : MvPolynomial σ ℚ) (e : AbsFormula σ) (start : ℕ)
    (x : σ → ℝ) (roots : ℕ → ℝ) (hL : 0 < polynomialValue x L)
    (hsat : Satisfies x roots (extractRadicals L e start).program start) :
    PowerFraction.value (polynomialValue x L) (point x roots)
      (extractRadicals L e start).result = smoothEval (polynomialValue x L) x e := by
  have hbase : polynomialValue (point x roots) (basePolynomial L) = polynomialValue x L :=
    basePolynomial_value L x roots
  induction e generalizing start with
  | coordinate i => simp [extractRadicals, PowerFraction.value, PowerFraction.ofPolynomial,
      polynomialValue, point, smoothEval]
  | constant c => simp [extractRadicals, PowerFraction.value, PowerFraction.ofPolynomial,
      polynomialValue, smoothEval]
  | add e f he hf =>
      let E := extractRadicals L e start
      let F := extractRadicals L f (start + E.program.length)
      obtain ⟨hsE, hsF⟩ := (satisfies_append E.program F.program start x roots).mp hsat
      have hsum := PowerFraction.value_add (basePolynomial L) E.result F.result
        (point x roots) (by rw [hbase]; exact ne_of_gt hL)
      rw [hbase] at hsum
      change PowerFraction.value _ _ (PowerFraction.add _ E.result F.result) = _
      rw [hsum, he start hsE, hf (start + E.program.length) hsF]
      rfl
  | mul e f he hf =>
      let E := extractRadicals L e start
      let F := extractRadicals L f (start + E.program.length)
      obtain ⟨hsE, hsF⟩ := (satisfies_append E.program F.program start x roots).mp hsat
      change PowerFraction.value _ _ (PowerFraction.mul E.result F.result) = _
      rw [PowerFraction.value_mul, he start hsE, hf (start + E.program.length) hsF]
      rfl
  | abs e he =>
      let E := extractRadicals L e start
      let D := PowerFraction.smoothingRadicand (basePolynomial L) E.result
      obtain ⟨hsE, hsD⟩ := (satisfies_append E.program [D] start x roots).mp hsat
      have hroot : roots (start + E.program.length) =
          Real.sqrt (RadicalProgram.polynomialValue x roots D) := hsD.1
      change polynomialValue (point x roots) (MvPolynomial.X (Sum.inr (start + E.program.length))) /
          (polynomialValue x L) ^ (E.result.exponent + 1) = _
      have hX : polynomialValue (point x roots)
          (MvPolynomial.X (Sum.inr (start + E.program.length))) =
            roots (start + E.program.length) := by
        simp [polynomialValue, point]
      rw [hX, hroot]
      have hrad := PowerFraction.sqrt_smoothingRadicand_div_eq (basePolynomial L) E.result
        (point x roots) (by rw [hbase]; exact hL)
      rw [hbase] at hrad
      change Real.sqrt (polynomialValue (point x roots)
        (PowerFraction.smoothingRadicand (basePolynomial L) E.result)) /
          (polynomialValue x L) ^ (E.result.exponent + 1) = _
      rw [hrad, he start hsE]
      rfl

/-- Every radicand is at least one at every extended real state whenever
the precision is at least one. No root equations are needed for this
global denominator bound. -/
theorem extractRadicals_radicands_one_le (L : MvPolynomial σ ℚ)
    (e : AbsFormula σ) (start : ℕ) (x : σ → ℝ) (roots : ℕ → ℝ)
    (hL : 1 ≤ polynomialValue x L) :
    ∀ D ∈ (extractRadicals L e start).program,
      1 ≤ RadicalProgram.polynomialValue x roots D := by
  induction e generalizing start with
  | coordinate i => simp [extractRadicals]
  | constant c => simp [extractRadicals]
  | add e f he hf =>
      intro D hD
      rcases List.mem_append.mp hD with hD | hD
      · exact he start D hD
      · exact hf _ D hD
  | mul e f he hf =>
      intro D hD
      rcases List.mem_append.mp hD with hD | hD
      · exact he start D hD
      · exact hf _ D hD
  | abs e he =>
      intro D hD
      rcases List.mem_append.mp hD with hD | hD
      · exact he start D hD
      · have hD' : D = PowerFraction.smoothingRadicand (basePolynomial L)
            (extractRadicals L e start).result := List.mem_singleton.mp hD
        subst D
        exact PowerFraction.one_le_smoothingRadicand _ _ _
          (by
            have hbase : polynomialValue (point x roots) (basePolynomial L) =
                polynomialValue x L := basePolynomial_value L x roots
            rw [hbase]
            exact hL)

/-- With the uncancelled common-denominator convention, the final
denominator exponent also equals the absolute-value count. -/
theorem extractRadicals_exponent (L : MvPolynomial σ ℚ) (e : AbsFormula σ) (start : ℕ) :
    (extractRadicals L e start).result.exponent = radicalCount e := by
  induction e generalizing start with
  | coordinate i => rfl
  | constant c => rfl
  | add e f he hf => simp [extractRadicals, PowerFraction.add, radicalCount, he, hf]
  | mul e f he hf => simp [extractRadicals, PowerFraction.mul, radicalCount, he, hf]
  | abs e he => simp [extractRadicals, radicalCount, he]

/-- Sequential evaluation of the extracted finite program produces the
correct smoothed value. No root equations or representation are assumed. -/
theorem extractRadicals_run_value (L : MvPolynomial σ ℚ) (e : AbsFormula σ) (start : ℕ)
    (x : σ → ℝ) (initialRoots : ℕ → ℝ) (hL : 0 < polynomialValue x L) :
    PowerFraction.value (polynomialValue x L)
      (point x (run (extractRadicals L e start).program start x initialRoots))
      (extractRadicals L e start).result = smoothEval (polynomialValue x L) x e :=
  extractRadicals_value L e start x _ hL
    (run_satisfies _ start x initialRoots (extractRadicals_wellFormed L e start).1)

end

end AbsFormula

end Stability.Simulation
