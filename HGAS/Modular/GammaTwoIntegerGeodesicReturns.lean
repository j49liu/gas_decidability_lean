import HGAS.Modular.GammaTwoShearFlowBoxes
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Integer good-return lengths for nonperiodic horocycles

The geometric recurrence theorem produces real geodesic return times
`Lₙ → ∞`, whereas the project's pointwise ergodic theorem is formulated
for integer averaging lengths.  This module bridges the two without an
approximation error in the orbit average.

Set

```text
  Nₙ = ceil(exp(Lₙ)).
```

Then `Nₙ → ∞`, every `Nₙ` is positive, and

```text
  dₙ = log(Nₙ) - Lₙ
```

lies in the fixed interval `[0, log 2]`.  Indeed,

```text
  exp(Lₙ) ≤ Nₙ < exp(Lₙ) + 1 ≤ 2 exp(Lₙ),
```

because the chosen return times satisfy `Lₙ ≥ n ≥ 0`.
Consequently the adjusted geodesic points at time `log Nₙ` lie in a
fixed compact thickening of the `1/3` Mahler core.

These integer lengths are the exact durations used in the formal
Hubbard--Miller good-times argument.
-/

namespace HGAS.Modular

open Filter Function _root_.MeasureTheory Set Topology
open scoped MatrixGroups

noncomputable section

/-- A compact thickening of the `1/3` Mahler core by geodesic times in
`[0, log 2]`. -/
def gammaTwoIntegerReturnCompactCore :
    Set GammaTwoFrameQuotient :=
  (fun p : GammaTwoFrameQuotient × ℝ ↦
    gammaTwoFrameRightMul (geodesicFrame p.2) p.1) ''
      (gammaTwoMahlerCompactCore (1 / 3 : ℝ) ×ˢ
        Icc 0 (Real.log 2))

theorem isCompact_gammaTwoIntegerReturnCompactCore :
    IsCompact gammaTwoIntegerReturnCompactCore := by
  apply IsCompact.image
  · exact
      (isCompact_gammaTwoMahlerCompactCore (1 / 3 : ℝ)).prod
        isCompact_Icc
  · exact gammaTwoFrameRightMul_joint_continuous.comp
      ((geodesicFrame_continuous.comp continuous_snd).prodMk
        continuous_fst)

/-- A nonperiodic horocycle has integer lengths tending to infinity such
that the geodesic point at logarithmic time lies in one fixed compact
set. -/
theorem exists_integer_gammaTwoGeodesic_return_lengths
    (q : GammaTwoFrameQuotient)
    (hnonperiodic :
      ¬ IsPeriodicHorocyclePoint 1 q) :
    ∃ N : ℕ → ℕ,
      Tendsto N atTop atTop ∧
      (∀ n, 0 < N n) ∧
      ∀ n,
        gammaTwoFrameRightMul
            (geodesicFrame (Real.log (N n : ℝ))) q ∈
          gammaTwoIntegerReturnCompactCore := by
  induction q using Quotient.inductionOn with
  | _ g =>
      choose L hLge hLthick using
        fun n : ℕ ↦
          exists_geodesic_thick_return_time_ge
            g hnonperiodic (n : ℝ)
      let N : ℕ → ℕ :=
        fun n ↦ ⌈Real.exp (L n)⌉₊
      have hLtop : Tendsto L atTop atTop :=
        tendsto_atTop_mono hLge
          tendsto_natCast_atTop_atTop
      have hNtop : Tendsto N atTop atTop :=
        tendsto_nat_ceil_atTop.comp
          (Real.tendsto_exp_atTop.comp hLtop)
      have hNpos (n : ℕ) : 0 < N n := by
        exact Nat.ceil_pos.mpr (Real.exp_pos (L n))
      refine ⟨N, hNtop, hNpos, ?_⟩
      intro n
      let d : ℝ := Real.log (N n : ℝ) - L n
      have hLnonneg : 0 ≤ L n :=
        (Nat.cast_nonneg n).trans (hLge n)
      have hNrealPos : 0 < (N n : ℝ) := by
        exact_mod_cast hNpos n
      have hexp_le_N :
          Real.exp (L n) ≤ (N n : ℝ) :=
        Nat.le_ceil _
      have hdnonneg : 0 ≤ d := by
        dsimp only [d]
        have hlog :=
          Real.log_le_log (Real.exp_pos (L n)) hexp_le_N
        rw [Real.log_exp] at hlog
        linarith
      have hNlt :
          (N n : ℝ) < 2 * Real.exp (L n) := by
        calc
          (N n : ℝ) <
              Real.exp (L n) + 1 :=
            Nat.ceil_lt_add_one (Real.exp_pos (L n)).le
          _ ≤ Real.exp (L n) + Real.exp (L n) := by
            gcongr
            exact Real.one_le_exp hLnonneg
          _ = 2 * Real.exp (L n) := by ring_nf
      have hdle : d ≤ Real.log 2 := by
        have hloglt :=
          Real.log_lt_log hNrealPos hNlt
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
          (Real.exp_ne_zero (L n)), Real.log_exp] at hloglt
        dsimp only [d]
        linarith
      refine
        ⟨(gammaTwoFrameQuotientMk
              (g * geodesicFrame (L n)), d),
          ⟨?_, hdnonneg, hdle⟩, ?_⟩
      · exact gammaTwoFrameQuotientMk_mem_mahlerCompactCore
          (by norm_num) _ (hLthick n)
      · change
          gammaTwoFrameRightMul (geodesicFrame d)
              (gammaTwoFrameQuotientMk
                (g * geodesicFrame (L n))) =
            gammaTwoFrameQuotientMk
              (g * geodesicFrame (Real.log (N n : ℝ)))
        rw [gammaTwoFrameRightMul_mk]
        congr 1
        rw [mul_assoc, ← geodesicFrame_add]
        congr 1
        dsimp only [d]
        ring_nf

end

end HGAS.Modular
