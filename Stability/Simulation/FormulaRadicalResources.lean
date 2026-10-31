import Stability.Simulation.FormulaRadicals

/-!
# Shape-dependent degrees for the extracted radical program

One recursive integer bounds both the final numerator and every radicand.
It depends on the formula tree and a degree bound for the precision, not
on the rational constants. The bound is deliberately coarse; its role is
to prove fixed algebraic resources as input coefficients vary.
-/

namespace Stability.Simulation.AbsFormula

open RadicalProgram

variable {σ : Type*}

/-- A common bound for all polynomials produced by radical extraction. -/
def radicalDegreeBound (precisionDegree : ℕ) : AbsFormula σ → ℕ
  | .coordinate _ => 1
  | .constant _ => 0
  | .add e f => radicalDegreeBound precisionDegree e + radicalDegreeBound precisionDegree f +
      precisionDegree * (radicalCount e + radicalCount f)
  | .mul e f => radicalDegreeBound precisionDegree e + radicalDegreeBound precisionDegree f
  | .abs e => 1 + 2 * radicalDegreeBound precisionDegree e +
      2 * precisionDegree * (radicalCount e + 1)

theorem radicalDegreeBound_eraseConstants (d : ℕ) (e : AbsFormula σ) :
    radicalDegreeBound d (eraseConstants e) = radicalDegreeBound d e := by
  induction e <;> simp_all [radicalDegreeBound, eraseConstants, radicalCount_eraseConstants]

/-- Every polynomial in the actual extracted program obeys the same
shape-dependent bound. This includes all radicands, not only the output. -/
theorem extractRadicals_totalDegree_le (L : MvPolynomial σ ℚ) {d : ℕ}
    (hL : L.totalDegree ≤ d) (e : AbsFormula σ) (start : ℕ) :
    (extractRadicals L e start).result.numerator.totalDegree ≤ radicalDegreeBound d e ∧
      ∀ D ∈ (extractRadicals L e start).program, D.totalDegree ≤ radicalDegreeBound d e := by
  have hbase : (basePolynomial L).totalDegree ≤ d :=
    (MvPolynomial.totalDegree_rename_le Sum.inl L).trans hL
  have hpower (k : ℕ) : ((basePolynomial L) ^ k).totalDegree ≤ k * d :=
    (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left k hbase)
  induction e generalizing start with
  | coordinate i => simp [extractRadicals, PowerFraction.ofPolynomial, radicalDegreeBound]
  | constant c => simp [extractRadicals, PowerFraction.ofPolynomial, radicalDegreeBound]
  | add e f he hf =>
      let E := extractRadicals L e start
      let F := extractRadicals L f (start + E.program.length)
      obtain ⟨hE, hEp⟩ := he start
      obtain ⟨hF, hFp⟩ := hf (start + E.program.length)
      change E.result.numerator.totalDegree ≤ radicalDegreeBound d e at hE
      change F.result.numerator.totalDegree ≤ radicalDegreeBound d f at hF
      change (E.result.numerator * basePolynomial L ^ F.result.exponent +
          F.result.numerator * basePolynomial L ^ E.result.exponent).totalDegree ≤ _ ∧ _
      constructor
      · apply (MvPolynomial.totalDegree_add _ _).trans
        apply max_le
        · have hmul := (MvPolynomial.totalDegree_mul _ _).trans
            (Nat.add_le_add hE (hpower F.result.exponent))
          have hfexp : F.result.exponent = radicalCount f := extractRadicals_exponent L f _
          rw [hfexp] at hmul
          rw [hfexp]
          unfold radicalDegreeBound
          nlinarith
        · have hmul := (MvPolynomial.totalDegree_mul _ _).trans
            (Nat.add_le_add hF (hpower E.result.exponent))
          have heexp : E.result.exponent = radicalCount e := extractRadicals_exponent L e _
          rw [heexp] at hmul
          rw [heexp]
          unfold radicalDegreeBound
          nlinarith
      · intro D hD
        rcases List.mem_append.mp hD with hD | hD
        · have h := hEp D hD
          change D.totalDegree ≤ radicalDegreeBound d e + radicalDegreeBound d f + _
          omega
        · have h := hFp D hD
          change D.totalDegree ≤ radicalDegreeBound d e + radicalDegreeBound d f + _
          omega
  | mul e f he hf =>
      let E := extractRadicals L e start
      let F := extractRadicals L f (start + E.program.length)
      obtain ⟨hE, hEp⟩ := he start
      obtain ⟨hF, hFp⟩ := hf (start + E.program.length)
      change (E.result.numerator * F.result.numerator).totalDegree ≤ _ ∧ _
      refine ⟨(MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hE hF), ?_⟩
      intro D hD
      rcases List.mem_append.mp hD with hD | hD
      · exact (hEp D hD).trans (Nat.le_add_right _ _)
      · exact (hFp D hD).trans (Nat.le_add_left _ _)
  | abs e he =>
      let E := extractRadicals L e start
      obtain ⟨hE, hEp⟩ := he start
      change E.result.numerator.totalDegree ≤ radicalDegreeBound d e at hE
      constructor
      · change (MvPolynomial.X (Sum.inr (start + E.program.length)) :
          RadicalProgram.Polynomial σ).totalDegree ≤ _
        simp only [MvPolynomial.totalDegree_X, radicalDegreeBound]
        omega
      · intro D hD
        rcases List.mem_append.mp hD with hD | hD
        · have h := hEp D hD
          change D.totalDegree ≤ 1 + 2 * radicalDegreeBound d e + _
          omega
        · have hD' : D = PowerFraction.smoothingRadicand (basePolynomial L) E.result :=
            List.mem_singleton.mp hD
          subst D
          apply (MvPolynomial.totalDegree_add _ _).trans
          apply max_le
          · have hp := (MvPolynomial.totalDegree_pow E.result.numerator 2).trans
              (Nat.mul_le_mul_left 2 hE)
            have hmul := (MvPolynomial.totalDegree_mul _ _).trans
              (Nat.add_le_add hp (hpower 2))
            change _ ≤ 1 + 2 * radicalDegreeBound d e + 2 * d * (radicalCount e + 1)
            nlinarith
          · have heexp : E.result.exponent = radicalCount e := extractRadicals_exponent L e _
            have hpow := hpower (2 * E.result.exponent)
            rw [heexp] at hpow
            change _ ≤ 1 + 2 * radicalDegreeBound d e + 2 * d * (radicalCount e + 1)
            rw [heexp]
            nlinarith

end Stability.Simulation.AbsFormula
