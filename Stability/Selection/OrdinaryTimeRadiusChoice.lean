import Stability.Selection.OrdinaryTimeSourcePrimitive
import HGAS.Lyapunov.ExactGridPositivityComputability
import Mathlib.Computability.RE

/-!
# The least positive Fourier-radius denominator

The search tests integer inequalities equivalent to the two rational
ratio conditions. Convergence to one proves termination; minimization
is therefore a total computable operation, not an oracle for a real test.
-/

namespace Stability.Selection

open Filter Topology

def radiusAdmissible (B A m : ℕ) : Prop :=
  0 < m ∧ (m + 1) ^ B ≤ 32 * m ^ B ∧ 2 * (m + 1) ^ A ≤ 3 * m ^ A

instance (B A m : ℕ) : Decidable (radiusAdmissible B A m) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem radiusAdmissible_iff (B A m : ℕ) (hm : 0 < m) :
    radiusAdmissible B A m ↔
      (1 / 256 : ℚ) * (1 + 1 / (m : ℚ)) ^ B ≤ 1 / 8 ∧
      (1 / 2 : ℚ) * (1 + 1 / (m : ℚ)) ^ A ≤ 3 / 4 := by
  have hm0 : (0 : ℚ) < m := by exact_mod_cast hm
  have he (K : ℕ) : (1 + 1 / (m : ℚ)) ^ K = ((m + 1 : ℕ) : ℚ) ^ K / (m : ℚ) ^ K := by
    rw [← div_pow]
    congr 1
    push_cast
    field_simp
  have hB : (m + 1) ^ B ≤ 32 * m ^ B ↔ (1 + 1 / (m : ℚ)) ^ B ≤ 32 := by
    rw [he, div_le_iff₀ (pow_pos hm0 B)]
    norm_cast
  have hA : 2 * (m + 1) ^ A ≤ 3 * m ^ A ↔ 2 * (1 + 1 / (m : ℚ)) ^ A ≤ 3 := by
    rw [he, ← mul_div_assoc, div_le_iff₀ (pow_pos hm0 A)]
    norm_cast
  simp only [radiusAdmissible, hm, true_and, hB, hA]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem exists_radiusAdmissible (B A : ℕ) : ∃ m, radiusAdmissible B A m := by
  have ht : Tendsto (fun m : ℕ ↦ 1 + 1 / (m : ℚ)) atTop (𝓝 1) := by
    simpa only [add_zero] using
      (tendsto_const_nhds (x := (1 : ℚ))).add tendsto_one_div_atTop_nhds_zero_nat
  have hB : ∀ᶠ m : ℕ in atTop, (1 / 256 : ℚ) * (1 + 1 / (m : ℚ)) ^ B < 1 / 8 :=
    (show Tendsto (fun m : ℕ ↦ (1 / 256 : ℚ) * (1 + 1 / (m : ℚ)) ^ B)
      atTop (𝓝 (1 / 256)) by simpa using tendsto_const_nhds.mul (ht.pow B)).eventually_lt_const
        (by norm_num)
  have hA : ∀ᶠ m : ℕ in atTop, (1 / 2 : ℚ) * (1 + 1 / (m : ℚ)) ^ A < 3 / 4 :=
    (show Tendsto (fun m : ℕ ↦ (1 / 2 : ℚ) * (1 + 1 / (m : ℚ)) ^ A)
      atTop (𝓝 (1 / 2)) by simpa using tendsto_const_nhds.mul (ht.pow A)).eventually_lt_const
        (by norm_num)
  obtain ⟨m, hm, hb, ha⟩ := ((eventually_gt_atTop 0).and (hB.and hA)).exists
  exact ⟨m, (radiusAdmissible_iff B A m hm).mpr ⟨hb.le, ha.le⟩⟩

def radiusIndex (B A : ℕ) : ℕ := Nat.find (exists_radiusAdmissible B A)

theorem radiusIndex_spec (B A : ℕ) : radiusAdmissible B A (radiusIndex B A) :=
  Nat.find_spec (exists_radiusAdmissible B A)

theorem radiusIndex_pos (B A : ℕ) : 0 < radiusIndex B A := (radiusIndex_spec B A).1

theorem radiusIndex_min (B A m : ℕ) (hm : radiusAdmissible B A m) : radiusIndex B A ≤ m :=
  Nat.find_min' (exists_radiusAdmissible B A) hm

def fourierRadius (B A : ℕ) : ℚ := 1 + 1 / (radiusIndex B A : ℚ)

theorem fourierRadius_gt_one (B A : ℕ) : 1 < fourierRadius B A := by
  have hm : (0 : ℚ) < radiusIndex B A := by exact_mod_cast radiusIndex_pos B A
  unfold fourierRadius
  linarith [one_div_pos.mpr hm]

theorem fourierRadius_bounds (B A : ℕ) :
    (1 / 256 : ℚ) * fourierRadius B A ^ B ≤ 1 / 8 ∧
      (1 / 2 : ℚ) * fourierRadius B A ^ A ≤ 3 / 4 :=
  (radiusAdmissible_iff B A _ (radiusIndex_pos B A)).mp (radiusIndex_spec B A)

private theorem natPower_primrec : Primrec₂ (fun n k : ℕ ↦ n ^ k) := by
  have hstep : Primrec₂ (fun n : ℕ ↦ fun state : ℕ × ℕ ↦ state.2 * n) :=
    Primrec.nat_mul.comp₂ (Primrec.snd.comp₂ Primrec₂.right) Primrec₂.left
  exact (Primrec.nat_rec (Primrec.const 1) hstep).of_eq fun n k ↦ by
    induction k with
    | zero => rfl
    | succ k ih => simpa [pow_succ] using congrArg (· * n) ih

theorem radiusAdmissible_primrec :
    PrimrecPred (fun x : (ℕ × ℕ) × ℕ ↦ radiusAdmissible x.1.1 x.1.2 x.2) := by
  have hB : Primrec (fun x : (ℕ × ℕ) × ℕ ↦ (x.2 + 1) ^ x.1.1) :=
    natPower_primrec.comp (Primrec.succ.comp Primrec.snd)
    (Primrec.fst.comp Primrec.fst)
  have hB' : Primrec (fun x : (ℕ × ℕ) × ℕ ↦ x.2 ^ x.1.1) :=
    natPower_primrec.comp Primrec.snd (Primrec.fst.comp Primrec.fst)
  have hA : Primrec (fun x : (ℕ × ℕ) × ℕ ↦ (x.2 + 1) ^ x.1.2) :=
    natPower_primrec.comp (Primrec.succ.comp Primrec.snd)
    (Primrec.snd.comp Primrec.fst)
  have hA' : Primrec (fun x : (ℕ × ℕ) × ℕ ↦ x.2 ^ x.1.2) :=
    natPower_primrec.comp Primrec.snd (Primrec.snd.comp Primrec.fst)
  exact (Primrec.nat_lt.comp (Primrec.const 0) Primrec.snd).and
    ((Primrec.nat_le.comp hB (Primrec.nat_mul.comp (Primrec.const 32) hB')).and
      (Primrec.nat_le.comp (Primrec.nat_mul.comp (Primrec.const 2) hA)
        (Primrec.nat_mul.comp (Primrec.const 3) hA')))

theorem radiusIndex_computable : Computable₂ radiusIndex :=
  Computable.find radiusAdmissible_primrec.computablePred
    (fun x : ℕ × ℕ ↦ exists_radiusAdmissible x.1 x.2)

def fourierRadiusCode (B A : ℕ) : HGAS.RationalCode :=
  HGAS.RationalCode.add HGAS.RationalCode.one
    (HGAS.RationalCode.unitFraction (radiusIndex B A))

theorem decode_fourierRadiusCode (B A : ℕ) :
    HGAS.RationalCode.decode (fourierRadiusCode B A) = fourierRadius B A := by
  simp [fourierRadiusCode, fourierRadius,
    HGAS.RationalCode.decode_unitFraction (radiusIndex_pos B A)]

theorem fourierRadiusCode_computable : Computable₂ fourierRadiusCode :=
  HGAS.RationalCode.add_primrec.to_comp.comp (Computable.const _)
    (HGAS.RationalCode.unitFraction_primrec.to_comp.comp radiusIndex_computable)

def linearRadiusExponent {eqs vars : ℕ} (I : HGAS.DQLSystem eqs vars) : ℕ :=
  4 + 4 * ∑ row, ∑ j, (I.linear row j).natAbs

def quadraticRadiusExponent {eqs vars : ℕ} (I : HGAS.DQLSystem eqs vars) : ℕ :=
  4 + 4 * ∑ row, ∑ j, (I.quadratic row j).natAbs

def sourceRadiusIndex {eqs vars : ℕ} (I : HGAS.DQLSystem eqs vars) : ℕ :=
  radiusIndex (linearRadiusExponent I) (quadraticRadiusExponent I)

theorem sourceRadiusIndex_pos {eqs vars : ℕ} (I : HGAS.DQLSystem eqs vars) :
    0 < sourceRadiusIndex I := radiusIndex_pos _ _

theorem sourceRadiusIndex_bounds {eqs vars : ℕ} (I : HGAS.DQLSystem eqs vars) :
    (1 / 256 : ℝ) * (1 + 1 / (sourceRadiusIndex I : ℝ)) ^
      (4 + 4 * ∑ row, ∑ j, |(I.linear row j : ℝ)|) ≤ 1 / 8 ∧
    (1 / 2 : ℝ) * (1 + 1 / (sourceRadiusIndex I : ℝ)) ^
      (4 + 4 * ∑ row, ∑ j, |(I.quadratic row j : ℝ)|) ≤ 3 / 4 := by
  have heB : (linearRadiusExponent I : ℝ) =
      4 + 4 * ∑ row, ∑ j, |(I.linear row j : ℝ)| := by
    simp [linearRadiusExponent, Nat.cast_sum, Nat.cast_natAbs, Int.cast_abs]
  have heA : (quadraticRadiusExponent I : ℝ) =
      4 + 4 * ∑ row, ∑ j, |(I.quadratic row j : ℝ)| := by
    simp [quadraticRadiusExponent, Nat.cast_sum, Nat.cast_natAbs, Int.cast_abs]
  rw [← heB, ← heA, Real.rpow_natCast, Real.rpow_natCast]
  have h := fourierRadius_bounds (linearRadiusExponent I) (quadraticRadiusExponent I)
  simpa only [fourierRadius, sourceRadiusIndex, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast] using
    (show (1 / 256 : ℝ) * (fourierRadius (linearRadiusExponent I)
        (quadraticRadiusExponent I) : ℝ) ^ linearRadiusExponent I ≤ 1 / 8 ∧
      (1 / 2 : ℝ) * (fourierRadius (linearRadiusExponent I)
        (quadraticRadiusExponent I) : ℝ) ^ quadraticRadiusExponent I ≤ 3 / 4 by
      constructor
      · convert (Rat.cast_le (K := ℝ)).mpr h.1 using 1 <;> push_cast <;> norm_num
      · convert (Rat.cast_le (K := ℝ)).mpr h.2 using 1 <;> push_cast <;> norm_num)

end Stability.Selection
