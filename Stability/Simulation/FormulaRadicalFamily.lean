import Stability.Simulation.FormulaRadicalResources

/-!
# A shared radical program for a finite family

The compiler places the programs for consecutive formulas one after
another. Each formula gets fresh root coordinates, and every output uses
the same precision polynomial. The final evaluator therefore represents
all smoothed coordinates simultaneously, including an additional output
formula if one is included in the list.
-/

namespace Stability.Simulation

/-- A shared finite root program with one rational output per formula. -/
structure RadicalFamilyExpansion (σ : Type*) where
  program : RadicalProgram.Program σ
  results : List (PowerFraction (σ ⊕ ℕ))

namespace AbsFormula

noncomputable section

open RadicalProgram

variable {σ : Type*}

/-- Extract a family in order, allocating disjoint consecutive root ranges. -/
def extractRadicalFamily (L : MvPolynomial σ ℚ) :
    List (AbsFormula σ) → ℕ → RadicalFamilyExpansion σ
  | [], _ => ⟨[], []⟩
  | e :: es, start =>
      let E := extractRadicals L e start
      let F := extractRadicalFamily L es (start + E.program.length)
      ⟨E.program ++ F.program, E.result :: F.results⟩

theorem extractRadicalFamily_lengths (L : MvPolynomial σ ℚ)
    (es : List (AbsFormula σ)) (start : ℕ) :
    (extractRadicalFamily L es start).program.length = (es.map radicalCount).sum ∧
      (extractRadicalFamily L es start).results.length = es.length := by
  induction es generalizing start with
  | nil => simp [extractRadicalFamily]
  | cons e es ih =>
      simp [extractRadicalFamily, extractRadicals_length, ih]

/-- The shared program is triangular and all output numerators use only
the roots in its finite range, together with any supplied prefix. -/
theorem extractRadicalFamily_wellFormed (L : MvPolynomial σ ℚ)
    (es : List (AbsFormula σ)) (start : ℕ) :
    Triangular (extractRadicalFamily L es start).program start ∧
      ∀ result ∈ (extractRadicalFamily L es start).results,
        DependsBelow result.numerator
          (start + (extractRadicalFamily L es start).program.length) := by
  induction es generalizing start with
  | nil => simp [extractRadicalFamily, Triangular]
  | cons e es ih =>
      let E := extractRadicals L e start
      let F := extractRadicalFamily L es (start + E.program.length)
      obtain ⟨hE, hEnum⟩ := extractRadicals_wellFormed L e start
      change DependsBelow E.result.numerator (start + E.program.length) at hEnum
      obtain ⟨hF, hFnum⟩ := ih (start + E.program.length)
      change Triangular (E.program ++ F.program) start ∧ _
      refine ⟨(triangular_append _ _ _).mpr ⟨hE, hF⟩, ?_⟩
      intro result hresult
      change result ∈ E.result :: F.results at hresult
      change DependsBelow result.numerator (start + (E.program ++ F.program).length)
      rcases List.mem_cons.mp hresult with hresult | hresult
      · subst result
        exact hEnum.mono (by simp only [List.length_append]; omega)
      · simpa only [List.length_append, Nat.add_assoc] using hFnum _ hresult

/-- Every output is correct under the equations of the shared program.
The following theorem supplies these equations by actual evaluation. -/
theorem extractRadicalFamily_values (L : MvPolynomial σ ℚ)
    (es : List (AbsFormula σ)) (start : ℕ) (x : σ → ℝ) (roots : ℕ → ℝ)
    (hL : 0 < polynomialValue x L)
    (hsat : Satisfies x roots (extractRadicalFamily L es start).program start) :
    ((extractRadicalFamily L es start).results.map
      (PowerFraction.value (polynomialValue x L) (point x roots))) =
        es.map (smoothEval (polynomialValue x L) x) := by
  induction es generalizing start with
  | nil => rfl
  | cons e es ih =>
      let E := extractRadicals L e start
      let F := extractRadicalFamily L es (start + E.program.length)
      obtain ⟨hsE, hsF⟩ := (satisfies_append E.program F.program start x roots).mp hsat
      change PowerFraction.value _ _ E.result :: F.results.map _ = _ :: _
      rw [extractRadicals_value L e start x roots hL hsE,
        ih (start + E.program.length) hsF]

/-- A single sequential evaluation gives all smoothed formula values,
for arbitrary initial values of every root coordinate. -/
theorem extractRadicalFamily_run_values (L : MvPolynomial σ ℚ)
    (es : List (AbsFormula σ)) (start : ℕ) (x : σ → ℝ) (initialRoots : ℕ → ℝ)
    (hL : 0 < polynomialValue x L) :
    ((extractRadicalFamily L es start).results.map
      (PowerFraction.value (polynomialValue x L)
        (point x (run (extractRadicalFamily L es start).program start x initialRoots)))) =
        es.map (smoothEval (polynomialValue x L) x) :=
  extractRadicalFamily_values L es start x _ hL
    (run_satisfies _ start x initialRoots (extractRadicalFamily_wellFormed L es start).1)

/-- Positivity holds everywhere in the extended state space, not merely
on the graph obtained by evaluating the root program. -/
theorem extractRadicalFamily_radicands_one_le (L : MvPolynomial σ ℚ)
    (es : List (AbsFormula σ)) (start : ℕ) (x : σ → ℝ) (roots : ℕ → ℝ)
    (hL : 1 ≤ polynomialValue x L) :
    ∀ D ∈ (extractRadicalFamily L es start).program,
      1 ≤ RadicalProgram.polynomialValue x roots D := by
  induction es generalizing start with
  | nil => simp [extractRadicalFamily]
  | cons e es ih =>
      intro D hD
      rcases List.mem_append.mp hD with hD | hD
      · exact extractRadicals_radicands_one_le L e start x roots hL D hD
      · exact ih _ D hD

/-- A common degree bound for the finite family, independent of constants. -/
def radicalFamilyDegreeBound (precisionDegree : ℕ) : List (AbsFormula σ) → ℕ
  | [] => 0
  | e :: es => max (radicalDegreeBound precisionDegree e)
      (radicalFamilyDegreeBound precisionDegree es)

theorem radicalFamilyDegreeBound_eraseConstants (d : ℕ) (es : List (AbsFormula σ)) :
    radicalFamilyDegreeBound d (es.map eraseConstants) = radicalFamilyDegreeBound d es := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [radicalFamilyDegreeBound, radicalDegreeBound_eraseConstants, ih]

/-- All numerator and radicand degrees are bounded before evaluating
coefficients or roots. Root indices do not contribute to the bound. -/
theorem extractRadicalFamily_totalDegree_le (L : MvPolynomial σ ℚ) {d : ℕ}
    (hL : L.totalDegree ≤ d) (es : List (AbsFormula σ)) (start : ℕ) :
    (∀ result ∈ (extractRadicalFamily L es start).results,
      result.numerator.totalDegree ≤ radicalFamilyDegreeBound d es) ∧
    (∀ D ∈ (extractRadicalFamily L es start).program,
      D.totalDegree ≤ radicalFamilyDegreeBound d es) := by
  induction es generalizing start with
  | nil => simp [extractRadicalFamily]
  | cons e es ih =>
      let E := extractRadicals L e start
      let F := extractRadicalFamily L es (start + E.program.length)
      obtain ⟨hE, hEp⟩ := extractRadicals_totalDegree_le L hL e start
      obtain ⟨hF, hFp⟩ := ih (start + E.program.length)
      constructor
      · intro result hresult
        rcases List.mem_cons.mp hresult with hresult | hresult
        · subst result
          exact hE.trans (Nat.le_max_left _ _)
        · exact (hF _ hresult).trans (Nat.le_max_right _ _)
      · intro D hD
        rcases List.mem_append.mp hD with hD | hD
        · exact (hEp D hD).trans (Nat.le_max_left _ _)
        · exact (hFp D hD).trans (Nat.le_max_right _ _)

end

end AbsFormula

end Stability.Simulation
