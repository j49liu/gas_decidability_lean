import Stability.Simulation.PolynomialDifferenceBounds
import Stability.Simulation.RationalDirectionalDerivative
import Stability.Simulation.PositiveDenominatorClearing

/-!
# Degrees of literal polynomial-fraction arithmetic

These estimates concern the stored numerators and denominators, before
any cancellation. Addition accumulates denominator factors; finite sums
therefore have bounds proportional to the actual number of summands.
The same estimates apply to the explicit positive common denominator.
-/

namespace Stability.Simulation.PolynomialFraction

noncomputable section

variable {σ ι : Type*}

/-- A common upper bound for the two stored polynomial degrees. -/
def DegreesLE (f : PolynomialFraction σ) (b : ℕ) : Prop :=
  f.numerator.totalDegree ≤ b ∧ f.denominator.totalDegree ≤ b

theorem DegreesLE.mono {f : PolynomialFraction σ} {a b : ℕ}
    (hf : DegreesLE f a) (hab : a ≤ b) : DegreesLE f b :=
  ⟨hf.1.trans hab, hf.2.trans hab⟩

theorem ofPolynomial_degreesLE (p : MvPolynomial σ ℚ) :
    DegreesLE (ofPolynomial p) p.totalDegree := by
  exact ⟨le_rfl, by simp [ofPolynomial]⟩

theorem add_degreesLE {f g : PolynomialFraction σ} {a b : ℕ}
    (hf : DegreesLE f a) (hg : DegreesLE g b) : DegreesLE (add f g) (a + b) := by
  constructor
  · apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hf.1 hg.2)
    · exact (MvPolynomial.totalDegree_mul _ _).trans
        ((Nat.add_le_add hg.1 hf.2).trans_eq (Nat.add_comm _ _))
  · exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hf.2 hg.2)

theorem mulPolynomial_degreesLE (p : MvPolynomial σ ℚ)
    {f : PolynomialFraction σ} {a d : ℕ} (hf : DegreesLE f a) (hp : p.totalDegree ≤ d) :
    DegreesLE (mulPolynomial p f) (d + a) :=
  ⟨(MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hp hf.1),
    hf.2.trans (Nat.le_add_left _ _)⟩

theorem divPolynomial_degreesLE (p : MvPolynomial σ ℚ)
    {f : PolynomialFraction σ} {a d : ℕ} (hf : DegreesLE f a) (hp : p.totalDegree ≤ d) :
    DegreesLE (divPolynomial f p) (a + d) :=
  ⟨hf.1.trans (Nat.le_add_right _ _),
    (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hf.2 hp)⟩

/-- Empty sums have degree zero, so this bound needs no positivity
assumption on either the summand count or the degree budget. -/
theorem sum_degreesLE (fs : List (PolynomialFraction σ)) {b : ℕ}
    (hfs : ∀ f ∈ fs, DegreesLE f b) : DegreesLE (sum fs) (fs.length * b) := by
  induction fs with
  | nil => simp [sum, DegreesLE, ofPolynomial]
  | cons f fs ih =>
      have h := add_degreesLE (hfs f (List.mem_cons_self))
        (ih (fun g hg ↦ hfs g (List.mem_cons_of_mem _ hg)))
      simpa only [sum, List.length_cons, Nat.add_mul, one_mul, Nat.add_comm] using h

theorem sumOver_degreesLE [Fintype ι] (fs : ι → PolynomialFraction σ) {b : ℕ}
    (hfs : ∀ i, DegreesLE (fs i) b) : DegreesLE (sumOver fs) (Fintype.card ι * b) := by
  have h := sum_degreesLE (Finset.univ.toList.map fs) (fun f hf ↦ by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hf
    exact hfs i)
  simpa [sumOver] using h

theorem directional_degreesLE [Fintype σ] (p : MvPolynomial σ ℚ)
    (V : σ → PolynomialFraction σ) {d b : ℕ} (hp : p.totalDegree ≤ d)
    (hV : ∀ i, DegreesLE (V i) b) :
    DegreesLE (directional p V) (Fintype.card σ * (d + b)) := by
  apply sumOver_degreesLE
  intro i
  exact mulPolynomial_degreesLE _ (hV i) ((AbsFormula.pderiv_totalDegree_le p i).trans hp)

theorem commonDenominator_degree_le [Fintype ι]
    (fs : ι → PolynomialFraction σ) {b : ℕ} (hfs : ∀ i, DegreesLE (fs i) b) :
    (commonDenominator fs).totalDegree ≤ Fintype.card ι * b := by
  apply (commonDenominator_totalDegree_le fs).trans
  calc
    (∑ i, (fs i).denominator.totalDegree) ≤ ∑ _ : ι, b :=
      Finset.sum_le_sum fun i _ ↦ (hfs i).2
    _ = _ := by simp

/-- Joint denominator clearing costs at most one degree budget for each
member of the family, including the selected numerator. -/
theorem clearedNumerator_degree_le [Fintype ι] [DecidableEq ι]
    (fs : ι → PolynomialFraction σ) {b : ℕ} (hfs : ∀ i, DegreesLE (fs i) b) (i : ι) :
    (clearedNumerator fs i).totalDegree ≤ Fintype.card ι * b := by
  apply (clearedNumerator_totalDegree_le fs i).trans
  have hsum : (∑ j ∈ Finset.univ.erase i, (fs j).denominator.totalDegree) ≤
      (Finset.univ.erase i).card * b := by
    calc
      _ ≤ ∑ _ ∈ Finset.univ.erase i, b := Finset.sum_le_sum fun j _ ↦ (hfs j).2
      _ = _ := by simp
  have hcard : (Finset.univ.erase i).card + 1 = Fintype.card ι := by
    simpa using Finset.card_erase_add_one (Finset.mem_univ i)
  calc
    _ ≤ b + (Finset.univ.erase i).card * b := Nat.add_le_add (hfs i).1 hsum
    _ = ((Finset.univ.erase i).card + 1) * b := by ring
    _ = _ := by rw [hcard]

end

end Stability.Simulation.PolynomialFraction
