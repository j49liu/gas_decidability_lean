import Stability.Selection.OrdinaryTimeRadiusChoice

/-!
# The least positive gain denominator

The printed inequality is checked by integer arithmetic on a rational
code. It has a witness for every code, including zero and negative
numerators. The resulting gain has the required quadratic error budget.
-/

namespace Stability.Selection

open HGAS

def gainAdmissible (M : ℕ) (c : RationalCode) (k : ℕ) : Prop :=
  0 < k ∧ 4 * c.1.2 ^ 2 * (M + 1) ≤ k ^ 2 * (c.2 + 1) ^ 2

instance (M : ℕ) (c : RationalCode) (k : ℕ) : Decidable (gainAdmissible M c k) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem exists_gainAdmissible (M : ℕ) (c : RationalCode) : ∃ k, gainAdmissible M c k := by
  let C := 4 * c.1.2 ^ 2 * (M + 1)
  refine ⟨C + 1, Nat.zero_lt_succ _, ?_⟩
  change C ≤ (C + 1) ^ 2 * (c.2 + 1) ^ 2
  have hC : C ≤ (C + 1) ^ 2 := by nlinarith
  exact hC.trans (Nat.le_mul_of_pos_right _ (by positivity))

def gainDenominator (M : ℕ) (c : RationalCode) : ℕ := Nat.find (exists_gainAdmissible M c)

theorem gainDenominator_spec (M : ℕ) (c : RationalCode) :
    gainAdmissible M c (gainDenominator M c) := Nat.find_spec (exists_gainAdmissible M c)

theorem gainDenominator_pos (M : ℕ) (c : RationalCode) : 0 < gainDenominator M c :=
  (gainDenominator_spec M c).1

theorem gainDenominator_min (M : ℕ) (c : RationalCode) (k : ℕ)
    (hk : gainAdmissible M c k) : gainDenominator M c ≤ k :=
  Nat.find_min' (exists_gainAdmissible M c) hk

theorem rationalCode_sq (c : RationalCode) :
    RationalCode.decode c ^ 2 = (c.1.2 : ℚ) ^ 2 / (c.2 + 1 : ℚ) ^ 2 := by
  rcases c with ⟨⟨s, a⟩, b⟩
  cases s <;> simp [RationalCode.decode, SignedMagnitudeCode.decode,
    Rat.divInt_eq_div, div_pow]

def graphWeightBudget (M : ℕ) : ℚ := 1 / (1 + (M : ℚ))

theorem graphWeightBudget_pos (M : ℕ) : 0 < graphWeightBudget M := by
  unfold graphWeightBudget
  positivity

theorem gainAdmissible_iff (M : ℕ) (c : RationalCode) (k : ℕ) :
    gainAdmissible M c k ↔
      0 < k ∧ 4 * RationalCode.decode c ^ 2 ≤ (k : ℚ) ^ 2 * graphWeightBudget M := by
  simp only [gainAdmissible, rationalCode_sq, graphWeightBudget]
  rw [← mul_div_assoc, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  norm_cast
  simp only [Nat.add_comm M 1]

def graphGain (M : ℕ) (c : RationalCode) : ℚ := 1 / (gainDenominator M c : ℚ)

theorem graphGain_pos (M : ℕ) (c : RationalCode) : 0 < graphGain M c := by
  have hk : (0 : ℚ) < gainDenominator M c := by exact_mod_cast gainDenominator_pos M c
  exact one_div_pos.mpr hk

theorem graphGain_quadratic_bound (M : ℕ) (c : RationalCode) :
    graphGain M c ^ 2 * RationalCode.decode c ^ 2 ≤ graphWeightBudget M / 4 := by
  have h := ((gainAdmissible_iff M c _).mp (gainDenominator_spec M c)).2
  have hk : (0 : ℚ) < gainDenominator M c := by exact_mod_cast gainDenominator_pos M c
  unfold graphGain
  rw [div_pow, one_pow, div_mul_eq_mul_div, div_le_div_iff₀ (pow_pos hk 2) (by norm_num)]
  simpa only [one_mul, mul_comm] using h

theorem gainDenominator_min_rational (M : ℕ) (c : RationalCode) (k : ℕ) (hk : 0 < k)
    (hb : 4 * RationalCode.decode c ^ 2 ≤ (k : ℚ) ^ 2 * graphWeightBudget M) :
    gainDenominator M c ≤ k := gainDenominator_min M c k ((gainAdmissible_iff M c k).mpr ⟨hk, hb⟩)

theorem gainAdmissible_primrec :
    PrimrecPred (fun x : (ℕ × RationalCode) × ℕ ↦ gainAdmissible x.1.1 x.1.2 x.2) := by
  have hnum : Primrec (fun x : (ℕ × RationalCode) × ℕ ↦ x.1.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have hden : Primrec (fun x : (ℕ × RationalCode) × ℕ ↦ x.1.2.2 + 1) :=
    Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hM : Primrec (fun x : (ℕ × RationalCode) × ℕ ↦ x.1.1 + 1) :=
    Primrec.succ.comp (Primrec.fst.comp Primrec.fst)
  have hleft := Primrec.nat_mul.comp
    (Primrec.nat_mul.comp (Primrec.const 4) (Primrec.nat_mul.comp hnum hnum)) hM
  have hright : Primrec (fun x : (ℕ × RationalCode) × ℕ ↦ x.2 * x.2 *
      ((x.1.2.2 + 1) * (x.1.2.2 + 1))) :=
    Primrec.nat_mul.comp (Primrec.nat_mul.comp Primrec.snd Primrec.snd)
      (Primrec.nat_mul.comp hden hden)
  simpa only [gainAdmissible, pow_two] using
    (Primrec.nat_lt.comp (Primrec.const 0) Primrec.snd).and (Primrec.nat_le.comp hleft hright)

theorem gainDenominator_computable : Computable₂ gainDenominator :=
  Computable.find gainAdmissible_primrec.computablePred
    (fun x : ℕ × RationalCode ↦ exists_gainAdmissible x.1 x.2)

def graphGainCode (M : ℕ) (c : RationalCode) : RationalCode :=
  RationalCode.unitFraction (gainDenominator M c)

theorem decode_graphGainCode (M : ℕ) (c : RationalCode) :
    RationalCode.decode (graphGainCode M c) = graphGain M c :=
  RationalCode.decode_unitFraction (gainDenominator_pos M c)

theorem graphGainCode_computable : Computable₂ graphGainCode :=
  RationalCode.unitFraction_primrec.to_comp.comp gainDenominator_computable

/-- The last reward estimate is ordinary real arithmetic. The graph
weight, scaled primitive, and epsilon bounds are stated explicitly. -/
theorem graph_reward_lower_bound {w wstar h2 ε : ℝ}
    (hw : wstar ≤ w) (hh : h2 ≤ wstar / 4) (hε : ε = wstar / 4) :
    5 * wstar / 4 ≤ 2 * w - 2 * h2 - ε := by
  linarith

end Stability.Selection
