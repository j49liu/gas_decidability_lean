import HGAS.Modular.GammaTwoPrimitiveRowDynamics
import Mathlib.Tactic

/-!
# Periodic level-two horocycles and horizontal primitive rows

`GammaTwoPrimitiveRowDynamics` proves that a horizontal primitive lattice
row produces a periodic horocycle.  Here we prove the converse.

If

```
                 [g u(T)] = [g],       T > 0,
```

then an integral level-two matrix `γ` satisfies
`γg = gu(T)`.  The first column of `g` is therefore a fixed vector of the
nonidentity integral matrix `γ`.  A nonzero row of `γ-I` is an integral
row perpendicular to that column.  Dividing the row by its gcd makes it
primitive without changing the perpendicularity relation.

This elementary equivalence is the precise cusp-normalization input for
the closed-horocycle selector.
-/

namespace HGAS.Modular

open Matrix Set
open scoped MatrixGroups

noncomputable section

/-- Dividing a nonzero integral relation by the gcd gives a primitive
integral row with the same real orthogonality relation. -/
private theorem exists_primitiveIntegralRow_of_integer_relation
    {a c : ℝ} {r s : ℤ}
    (hrs : r ≠ 0 ∨ s ≠ 0)
    (hrel : (r : ℝ) * a + (s : ℝ) * c = 0) :
    ∃ v : PrimitiveIntegralRow,
      (v.1 0 : ℝ) * a + (v.1 1 : ℝ) * c = 0 := by
  have hgcdpos : 0 < r.gcd s :=
    Int.gcd_pos_iff.mpr hrs
  obtain ⟨r', s', hgcd, hr, hs⟩ :=
    Int.exists_gcd_one hgcdpos
  let row : Fin 2 → ℤ := ![r', s']
  have hrow :
      row ∈ EisensteinSeries.gammaSet 1 1
        (0 : Fin 2 → ZMod 1) := by
    rw [EisensteinSeries.gammaSet_one_mem_iff]
    simpa [row] using hgcd
  let v : PrimitiveIntegralRow := ⟨row, hrow⟩
  refine ⟨v, ?_⟩
  have hgcdreal :
      (0 : ℝ) <
        ((r.gcd s : ℕ) : ℝ) := by
    exact_mod_cast hgcdpos
  have hfactor :
      (((r.gcd s : ℕ) : ℝ)) *
          ((r' : ℝ) * a + (s' : ℝ) * c) =
        0 := by
    have hrcast :
        (r : ℝ) =
          (r' : ℝ) * ((r.gcd s : ℕ) : ℝ) := by
      exact_mod_cast hr
    have hscast :
        (s : ℝ) =
          (s' : ℝ) * ((r.gcd s : ℕ) : ℝ) := by
      exact_mod_cast hs
    rw [hrcast, hscast] at hrel
    calc
      (((r.gcd s : ℕ) : ℝ)) *
            ((r' : ℝ) * a + (s' : ℝ) * c) =
          ((r' : ℝ) *
                ((r.gcd s : ℕ) : ℝ)) * a +
            ((s' : ℝ) *
                ((r.gcd s : ℕ) : ℝ)) * c := by ring
      _ = 0 := hrel
  have hprimitive :
      (r' : ℝ) * a + (s' : ℝ) * c = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hgcdreal.ne'
  simpa [v, row] using hprimitive

/-- A positive period forces the deck matrix witnessing it to be
nonidentity. -/
private theorem period_deck_ne_one
    (g : RealModularFrame) {T : ℝ} (hT : 0 < T)
    (γ : GammaTwo)
    (hγ :
      γ • g = g * upperUnipotent T) :
    γ ≠ 1 := by
  intro hγone
  subst γ
  simp only [one_smul] at hγ
  have hu : upperUnipotent T = 1 := by
    apply mul_left_cancel (a := g)
    simpa only [mul_one] using hγ.symm
  have hentry :=
    congrArg
      (fun A : RealModularFrame ↦
        (A : Matrix (Fin 2) (Fin 2) ℝ) 0 1)
      hu
  norm_num [upperUnipotent] at hentry
  exact hT.ne' hentry

/-- The first column of a periodic frame is fixed by its period deck
matrix. -/
private theorem period_deck_firstColumn_relations
    (g : RealModularFrame) {T : ℝ}
    (γ : GammaTwo)
    (hγ :
      γ • g = g * upperUnipotent T) :
    (((γ.1 0 0 - 1 : ℤ) : ℝ) * g 0 0 +
        (γ.1 0 1 : ℝ) * g 1 0 = 0) ∧
      ((γ.1 1 0 : ℝ) * g 0 0 +
        ((γ.1 1 1 - 1 : ℤ) : ℝ) * g 1 0 = 0) := by
  have h0 :=
    congrArg
      (fun A : RealModularFrame ↦
        (A : Matrix (Fin 2) (Fin 2) ℝ) 0 0)
      hγ
  have h1 :=
    congrArg
      (fun A : RealModularFrame ↦
        (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0)
      hγ
  simp only [gammaTwo_smul_realFrame,
    Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two,
    upperUnipotent_coe, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_one, mul_zero, add_zero] at h0 h1
  have hcast :
      ∀ i j : Fin 2,
        (gammaTwoToRealFrame γ :
            Matrix (Fin 2) (Fin 2) ℝ) i j =
          (γ.1 i j : ℝ) := by
    intro i j
    simp [gammaTwoToRealFrame,
      Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply]
  rw [hcast 0 0, hcast 0 1] at h0
  rw [hcast 1 0, hcast 1 1] at h1
  constructor
  · push_cast
    linear_combination h0
  · push_cast
    linear_combination h1

/-- **Converse periodic-row criterion.**  Every periodic level-two
horocycle has a primitive integral row whose first moving coordinate
vanishes. -/
theorem exists_primitiveRowMul_fst_eq_zero_of_isPeriodicHorocyclePoint
    (g : RealModularFrame)
    (hperiodic :
      IsPeriodicHorocyclePoint 1
        (gammaTwoFrameQuotientMk g)) :
    ∃ v : PrimitiveIntegralRow,
      primitiveIntegralRowMul v g 0 = 0 := by
  obtain ⟨T, hT, hperiod⟩ := hperiodic
  rw [scaledGammaTwoHorocycleFlow_one] at hperiod
  change
    gammaTwoFrameQuotientMk (g * upperUnipotent T) =
      gammaTwoFrameQuotientMk g at hperiod
  have horbit := Quotient.exact hperiod
  change
    g * upperUnipotent T ∈
      MulAction.orbit GammaTwo g at horbit
  obtain ⟨γ, hγ⟩ :=
    MulAction.mem_orbit_iff.mp horbit
  have hγne : γ ≠ 1 :=
    period_deck_ne_one g hT γ hγ
  have hrelations :=
    period_deck_firstColumn_relations g γ hγ
  by_cases hrow0 :
      γ.1 0 0 - 1 ≠ 0 ∨ γ.1 0 1 ≠ 0
  · obtain ⟨v, hv⟩ :=
      exists_primitiveIntegralRow_of_integer_relation
        hrow0 hrelations.1
    refine ⟨v, ?_⟩
    simpa only [primitiveIntegralRowMul,
      Fin.sum_univ_two] using hv
  · push Not at hrow0
    have h00 : γ.1 0 0 = 1 :=
      sub_eq_zero.mp hrow0.1
    have hrow1 :
        γ.1 1 0 ≠ 0 ∨ γ.1 1 1 - 1 ≠ 0 := by
      by_contra h
      push Not at h
      have h11 : γ.1 1 1 = 1 :=
        sub_eq_zero.mp h.2
      apply hγne
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [h00, hrow0.2, h.1, h11]
    obtain ⟨v, hv⟩ :=
      exists_primitiveIntegralRow_of_integer_relation
        hrow1 hrelations.2
    refine ⟨v, ?_⟩
    simpa only [primitiveIntegralRowMul,
      Fin.sum_univ_two] using hv

/-- Periodicity is equivalent to the existence of a horizontal primitive
lattice row. -/
theorem isPeriodicHorocyclePoint_iff_exists_primitiveRowMul_fst_eq_zero
    (g : RealModularFrame) :
    IsPeriodicHorocyclePoint 1
        (gammaTwoFrameQuotientMk g) ↔
      ∃ v : PrimitiveIntegralRow,
        primitiveIntegralRowMul v g 0 = 0 := by
  constructor
  · exact
      exists_primitiveRowMul_fst_eq_zero_of_isPeriodicHorocyclePoint g
  · rintro ⟨v, hv⟩
    exact
      isPeriodicHorocyclePoint_of_primitiveRowMul_fst_eq_zero
        v g hv

end

end HGAS.Modular
