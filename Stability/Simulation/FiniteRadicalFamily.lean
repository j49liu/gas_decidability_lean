import Stability.Simulation.FormulaRadicalFamily
import Stability.Simulation.RadicalFiniteCoordinates

/-!
# A finite-coordinate realization of a smoothed formula family

The resulting object consists of actual rational polynomials in the base
coordinates and finitely many root coordinates. Its root graph is defined
by sequential evaluation, not by choosing a solution of implicit equations.
The generated graph satisfies every finite radicand equation, and every
output equals its smoothed formula on that graph.
-/

namespace Stability.Simulation

/-- Finite polynomial radicands and rational outputs with one shared precision. -/
structure FiniteRadicalExpansion (σ : Type*) where
  rootCount : ℕ
  radicands : Fin rootCount → MvPolynomial (σ ⊕ Fin rootCount) ℚ
  outputs : List (PowerFraction (σ ⊕ Fin rootCount))

namespace AbsFormula

noncomputable section

open RadicalProgram

variable {σ : Type*}

def finiteFraction (bound : ℕ) (f : PowerFraction (σ ⊕ ℕ)) :
    PowerFraction (σ ⊕ Fin bound) := ⟨finitePolynomial bound f.numerator, f.exponent⟩

/-- The finite tuple of polynomials obtained by the explicit family compiler. -/
def finiteRadicalFamily (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ)) :
    FiniteRadicalExpansion σ :=
  let E := extractRadicalFamily L es 0
  ⟨E.program.length, fun i ↦ finitePolynomial E.program.length (E.program.get i),
    E.results.map (finiteFraction E.program.length)⟩

/-- The canonical finite root graph, obtained by running the program from zero. -/
def finiteRadicalRoots (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ)) (x : σ → ℝ) :
    Fin (finiteRadicalFamily L es).rootCount → ℝ :=
  fun i ↦ run (extractRadicalFamily L es 0).program 0 x (fun _ ↦ 0) i.val

theorem finiteRadicalFamily_counts (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ)) :
    (finiteRadicalFamily L es).rootCount = (es.map radicalCount).sum ∧
      (finiteRadicalFamily L es).outputs.length = es.length := by
  simpa [finiteRadicalFamily] using extractRadicalFamily_lengths L es 0

/-- Every generated finite root satisfies its actual polynomial equation. -/
theorem finiteRadicalRoots_equation (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ))
    (x : σ → ℝ) (i : Fin (finiteRadicalFamily L es).rootCount) :
    finiteRadicalRoots L es x i = Real.sqrt
      (polynomialValue (Sum.elim x (finiteRadicalRoots L es x))
        ((finiteRadicalFamily L es).radicands i)) := by
  let E := extractRadicalFamily L es 0
  have htri : Triangular E.program 0 := (extractRadicalFamily_wellFormed L es 0).1
  have hbound : DependsBelow (E.program.get i) E.program.length := by
    simpa using htri.dependsBelow_end _ (List.get_mem _ i)
  change run E.program 0 x (fun _ ↦ 0) i.val = Real.sqrt
    (polynomialValue (Sum.elim x (fun j : Fin E.program.length ↦
      run E.program 0 x (fun _ ↦ 0) j.val))
        (finitePolynomial E.program.length (E.program.get i)))
  rw [finitePolynomial_value_restrict hbound]
  simpa using (run_satisfies E.program 0 x (fun _ ↦ 0) htri).get i

theorem finiteFraction_value {bound : ℕ} {f : PowerFraction (σ ⊕ ℕ)}
    (hf : DependsBelow f.numerator bound) (L : ℝ) (x : σ → ℝ) (roots : ℕ → ℝ) :
    PowerFraction.value L (Sum.elim x (fun i : Fin bound ↦ roots i.val))
      (finiteFraction bound f) = PowerFraction.value L (point x roots) f := by
  unfold PowerFraction.value finiteFraction
  rw [finitePolynomial_value_restrict hf]
  rfl

/-- The finite graph represents every smoothed output simultaneously. -/
theorem finiteRadicalFamily_values (L : MvPolynomial σ ℚ) (es : List (AbsFormula σ))
    (x : σ → ℝ) (hL : 0 < polynomialValue x L) :
    ((finiteRadicalFamily L es).outputs.map
      (PowerFraction.value (polynomialValue x L)
        (Sum.elim x (finiteRadicalRoots L es x)))) =
      es.map (smoothEval (polynomialValue x L) x) := by
  let E := extractRadicalFamily L es 0
  let roots := run E.program 0 x (fun _ ↦ 0)
  have hbound : ∀ f ∈ E.results, DependsBelow f.numerator E.program.length := by
    simpa using (extractRadicalFamily_wellFormed L es 0).2
  change (E.results.map (finiteFraction E.program.length)).map
    (PowerFraction.value _ (Sum.elim x (fun i : Fin E.program.length ↦ roots i.val))) = _
  rw [List.map_map]
  calc
    _ = E.results.map (PowerFraction.value (polynomialValue x L) (point x roots)) := by
      apply List.map_congr_left
      intro f hf
      exact finiteFraction_value (hbound f hf) _ x roots
    _ = _ := extractRadicalFamily_run_values L es 0 x (fun _ ↦ 0) hL

/-- Every finite radicand is globally at least one, without a graph condition. -/
theorem finiteRadicalFamily_radicands_one_le (L : MvPolynomial σ ℚ)
    (es : List (AbsFormula σ)) (x : σ → ℝ)
    (roots : Fin (finiteRadicalFamily L es).rootCount → ℝ)
    (hL : 1 ≤ polynomialValue x L) (i : Fin (finiteRadicalFamily L es).rootCount) :
    1 ≤ polynomialValue (Sum.elim x roots) ((finiteRadicalFamily L es).radicands i) := by
  let E := extractRadicalFamily L es 0
  have hbound : DependsBelow (E.program.get i) E.program.length := by
    simpa using (extractRadicalFamily_wellFormed L es 0).1.dependsBelow_end _
      (List.get_mem _ i)
  change 1 ≤ polynomialValue (Sum.elim x roots)
    (finitePolynomial E.program.length (E.program.get i))
  calc
    1 ≤ RadicalProgram.polynomialValue x (extendRoots roots) (E.program.get i) :=
      extractRadicalFamily_radicands_one_le L es 0 x (extendRoots roots) hL _
        (List.get_mem _ i)
    _ = _ := (finitePolynomial_value hbound x roots).symm

/-- Finite coordinate restriction preserves the proved shape-dependent bounds. -/
theorem finiteRadicalFamily_totalDegree_le (L : MvPolynomial σ ℚ) {d : ℕ}
    (hL : L.totalDegree ≤ d) (es : List (AbsFormula σ)) :
    (∀ i, ((finiteRadicalFamily L es).radicands i).totalDegree ≤
      radicalFamilyDegreeBound d es) ∧
    (∀ f ∈ (finiteRadicalFamily L es).outputs,
      f.numerator.totalDegree ≤ radicalFamilyDegreeBound d es) := by
  let E := extractRadicalFamily L es 0
  obtain ⟨hresults, hprogram⟩ := extractRadicalFamily_totalDegree_le L hL es 0
  obtain ⟨htri, hbound⟩ := extractRadicalFamily_wellFormed L es 0
  constructor
  · intro i
    change (finitePolynomial E.program.length (E.program.get i)).totalDegree ≤ _
    rw [finitePolynomial_totalDegree (by
      simpa using htri.dependsBelow_end _ (List.get_mem _ i))]
    exact hprogram _ (List.get_mem _ i)
  · intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    change (finitePolynomial E.program.length g.numerator).totalDegree ≤ _
    rw [finitePolynomial_totalDegree (by simpa using hbound g hg)]
    exact hresults g hg

end

end AbsFormula

end Stability.Simulation
