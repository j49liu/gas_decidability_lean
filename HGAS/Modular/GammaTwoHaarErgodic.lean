import HGAS.Modular.GammaTwoHaarProbabilityUnique
import HGAS.Modular.HorocycleShearingAlgebra
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Tactic

/-!
# Ergodicity of Haar measure for the level-two horocycle flow

This module gives a self-contained formal proof of Hedlund's ergodicity
theorem in the concrete space `Γ(2) \ SL(2,ℝ)`.  The proof is the
elementary Mautner argument.

For a right-invariant probability `ν`, right translation defines a
strongly continuous isometric representation on `L²(ν)`.  If a vector is
fixed by the upper-unipotent subgroup, an exact four-factor matrix identity
forces invariance under the diagonal subgroup.  Diagonal contraction then
forces invariance under the lower-unipotent subgroup.  Explicit Gauss and
Weyl decompositions show that the vector is fixed by all of `SL(2,ℝ)`.

Applied to the indicator of a horocycle-invariant measurable set, this
shows that its normalized restriction is again right invariant.  Uniqueness
of the right-invariant probability then gives the zero-one law.

The representation-theoretic lemmas are stated for an arbitrary
right-invariant probability on the quotient and are reusable independently
of the chosen Haar construction.
-/

namespace HGAS.Modular

open Filter Function Matrix _root_.MeasureTheory Set Topology
open scoped ENNReal MatrixGroups

noncomputable section

/-- The Weyl element used in the elementary Mautner argument. -/
def mautnerWeyl : RealModularFrame :=
  upperUnipotent 1 * lowerUnipotent (-1) * upperUnipotent 1

@[simp]
theorem mautnerWeyl_coe :
    (mautnerWeyl : Matrix (Fin 2) (Fin 2) ℝ) =
      !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mautnerWeyl, upperUnipotent, lowerUnipotent,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- The determinant-one diagonal matrix with first entry `a`. -/
def mautnerDiagonal (a : ℝ) (ha : a ≠ 0) :
    RealModularFrame :=
  ⟨!![a, 0; 0, a⁻¹], by
    simp [Matrix.det_fin_two, ha]⟩

@[simp]
theorem mautnerDiagonal_coe (a : ℝ) (ha : a ≠ 0) :
    (mautnerDiagonal a ha : Matrix (Fin 2) (Fin 2) ℝ) =
      !![a, 0; 0, a⁻¹] :=
  rfl

theorem mautnerDiagonal_pos_eq_geodesic
    {a : ℝ} (ha : 0 < a) :
    mautnerDiagonal a ha.ne' =
      geodesicFrame (2 * Real.log a) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · change a = Real.exp ((2 * Real.log a) / 2)
    rw [show (2 * Real.log a) / 2 = Real.log a by ring,
      Real.exp_log ha]
  · simp [mautnerDiagonal, geodesicFrame]
  · simp [mautnerDiagonal, geodesicFrame]
  · change a⁻¹ = Real.exp (-(2 * Real.log a) / 2)
    rw [show -(2 * Real.log a) / 2 = -Real.log a by ring,
      Real.exp_neg, Real.exp_log ha]

theorem mautnerWeyl_sq_mul_geodesic
    {a : ℝ} (ha : a < 0) :
    mautnerWeyl * mautnerWeyl *
        geodesicFrame (2 * Real.log (-a)) =
      mautnerDiagonal a ha.ne := by
  have hneg : 0 < -a := neg_pos.mpr ha
  have hplus :
      Real.exp ((2 * Real.log (-a)) / 2) = -a := by
    rw [show (2 * Real.log (-a)) / 2 =
      Real.log (-a) by ring, Real.exp_log hneg]
  have hminus :
      Real.exp (-(2 * Real.log (-a)) / 2) =
        (-a)⁻¹ := by
    rw [show -(2 * Real.log (-a)) / 2 =
      -Real.log (-a) by ring, Real.exp_neg,
      Real.exp_log hneg]
  have hplus' : Real.exp (Real.log a) = -a := by
    rw [Real.exp_log_eq_abs ha.ne, abs_of_neg ha]
  have hminus' :
      Real.exp (-(2 * Real.log a) / 2) = (-a)⁻¹ := by
    rw [show -(2 * Real.log a) / 2 =
      -Real.log a by ring, Real.exp_neg, hplus']
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [mautnerWeyl, mautnerDiagonal, geodesicFrame,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, hplus, hminus, hplus', hminus']

/-- Gauss decomposition on the big cell of `SL(2,ℝ)`. -/
theorem lower_diagonal_upper_eq
    (g : RealModularFrame) (h00 : g 0 0 ≠ 0) :
    lowerUnipotent (g 1 0 / g 0 0) *
        mautnerDiagonal (g 0 0) h00 *
        upperUnipotent (g 0 1 / g 0 0) =
      g := by
  have hdet :
      g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe g
    rw [Matrix.det_fin_two] at h
    exact h
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [lowerUnipotent, mautnerDiagonal, upperUnipotent,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
  all_goals field_simp [h00]
  nlinarith

/-- The exact factorization that produces diagonal invariance from upper
unipotent invariance. -/
theorem mautner_diagonal_factorization
    (s x : ℝ) (hx : x ≠ 0) :
    lowerUnipotent
          (-((Real.exp (s / 2) - 1) /
            (Real.exp (s / 2) * x))) *
        upperUnipotent x *
        lowerUnipotent ((Real.exp (s / 2) - 1) / x) *
        upperUnipotent (-x / Real.exp (s / 2)) =
      geodesicFrame s := by
  have hexp : Real.exp (s / 2) ≠ 0 :=
    Real.exp_ne_zero _
  have hnegexp :
      Real.exp (-s / 2) = (Real.exp (s / 2))⁻¹ := by
    rw [show -s / 2 = -(s / 2) by ring,
      Real.exp_neg]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one,
      Matrix.SpecialLinearGroup.coe_mul,
      lowerUnipotent_coe, upperUnipotent_coe,
      geodesicFrame_coe, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, zero_mul, one_mul,
      mul_zero, mul_one, zero_add, add_zero,
      hnegexp]
  all_goals (field_simp [hx, hexp]; ring)

/-! ## The right regular representation on `L²` -/

/-- Right multiplication as a continuously varying continuous map of the
level-two quotient. -/
def gammaTwoFrameRightMulContinuousMap
    (a : RealModularFrame) :
    C(GammaTwoFrameQuotient, GammaTwoFrameQuotient) :=
  ⟨gammaTwoFrameRightMul a,
    gammaTwoFrameRightMul_continuous a⟩

theorem gammaTwoFrameRightMul_joint_continuous :
    Continuous
      (fun p : RealModularFrame × GammaTwoFrameQuotient ↦
        gammaTwoFrameRightMul p.1 p.2) := by
  exact
    gammaTwoFrameQuotientOppositeSMul_continuous.comp
      ((MulOpposite.continuous_op.comp continuous_fst).prodMk
        continuous_snd)

theorem gammaTwoFrameRightMulContinuousMap_continuous :
    Continuous gammaTwoFrameRightMulContinuousMap := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact gammaTwoFrameRightMul_joint_continuous

/-- Every descended right translation preserves a right-invariant frame
probability. -/
def IsRightInvariantFrameProbability.measurePreservingRightMul
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν)
    (a : RealModularFrame) :
    MeasurePreserving (gammaTwoFrameRightMul a)
      (ν : Measure GammaTwoFrameQuotient)
      (ν : Measure GammaTwoFrameQuotient) where
  measurable := (gammaTwoFrameRightMul_continuous a).measurable
  map_eq := congrArg ProbabilityMeasure.toMeasure (hν a)

/-- The Koopman operator associated to descended right multiplication. -/
def frameKoopmanL2
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν)
    (a : RealModularFrame)
    (f : Lp ℝ 2 (ν : Measure GammaTwoFrameQuotient)) :
    Lp ℝ 2 (ν : Measure GammaTwoFrameQuotient) :=
  Lp.compMeasurePreserving
    (gammaTwoFrameRightMul a)
    (hν.measurePreservingRightMul a) f

theorem frameKoopmanL2_one
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν)
    (f : Lp ℝ 2 (ν : Measure GammaTwoFrameQuotient)) :
    frameKoopmanL2 hν 1 f = f := by
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_compMeasurePreserving f
      (hν.measurePreservingRightMul 1)] with q hq
  calc
    frameKoopmanL2 hν 1 f q =
        f (gammaTwoFrameRightMul 1 q) := hq
    _ = f q := by
      rw [gammaTwoFrameRightMul_one]
      rfl

theorem frameKoopmanL2_mul
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν)
    (a b : RealModularFrame)
    (f : Lp ℝ 2 (ν : Measure GammaTwoFrameQuotient)) :
    frameKoopmanL2 hν (a * b) f =
      frameKoopmanL2 hν a (frameKoopmanL2 hν b f) := by
  simpa only [frameKoopmanL2,
    gammaTwoFrameRightMul_mul] using
      Lp.compMeasurePreserving_comp_apply
        f (hν.measurePreservingRightMul b)
        (hν.measurePreservingRightMul a)

theorem norm_frameKoopmanL2_sub
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν)
    (a : RealModularFrame)
    (f g : Lp ℝ 2 (ν : Measure GammaTwoFrameQuotient)) :
    ‖frameKoopmanL2 hν a f -
        frameKoopmanL2 hν a g‖ =
      ‖f - g‖ := by
  have hsub :
      frameKoopmanL2 hν a f -
          frameKoopmanL2 hν a g =
        frameKoopmanL2 hν a (f - g) := by
    exact
      (map_sub
        (Lp.compMeasurePreserving
          (gammaTwoFrameRightMul a)
          (hν.measurePreservingRightMul a)) f g).symm
  rw [hsub]
  exact Lp.norm_compMeasurePreserving
    (f - g) (hν.measurePreservingRightMul a)

theorem frameKoopmanL2_continuous
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν)
    (f : Lp ℝ 2 (ν : Measure GammaTwoFrameQuotient)) :
    Continuous (fun a ↦ frameKoopmanL2 hν a f) := by
  exact
    (continuous_const :
      Continuous
        (fun _ : RealModularFrame ↦
          f)).compMeasurePreservingLp
      gammaTwoFrameRightMulContinuousMap_continuous
      (fun a ↦ hν.measurePreservingRightMul a)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)

/-! ## Mautner's phenomenon for `SL(2,ℝ)` -/

/-- An `L²` vector fixed by every upper unipotent is fixed by the
geodesic diagonal subgroup.  This is the elementary factorization proof
of Mautner's phenomenon. -/
theorem frameKoopmanL2_geodesic_fixed_of_upper_fixed
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν)
    (f : Lp ℝ 2 (ν : Measure GammaTwoFrameQuotient))
    (hupper :
      ∀ t : ℝ,
        frameKoopmanL2 hν (upperUnipotent t) f = f)
    (s : ℝ) :
    frameKoopmanL2 hν (geodesicFrame s) f = f := by
  let x : ℕ → ℝ := fun n ↦ ((n + 1 : ℕ) : ℝ)
  let y : ℕ → ℝ :=
    fun n ↦ (Real.exp (s / 2) - 1) / x n
  let z : ℕ → ℝ :=
    fun n ↦
      -((Real.exp (s / 2) - 1) /
        (Real.exp (s / 2) * x n))
  have hx (n : ℕ) : x n ≠ 0 := by
    positivity
  have hy : Tendsto y atTop (𝓝 0) := by
    have h :=
      (tendsto_const_div_atTop_nhds_zero_nat
        (Real.exp (s / 2) - 1)).comp
        (tendsto_add_atTop_nat 1)
    convert h using 1
  have hz : Tendsto z atTop (𝓝 0) := by
    have hden :
        Tendsto
          (fun n : ℕ ↦
            Real.exp (s / 2) *
              (((n + 1 : ℕ) : ℝ)))
          atTop atTop :=
      (tendsto_natCast_atTop_atTop.comp
          (tendsto_add_atTop_nat 1)).const_mul_atTop
        (Real.exp_pos _)
    have h :
        Tendsto
          (fun n : ℕ ↦
            -((Real.exp (s / 2) - 1) /
              (Real.exp (s / 2) *
                (((n + 1 : ℕ) : ℝ)))))
          atTop (𝓝 0) :=
      by
        simpa only [neg_zero] using
          ((tendsto_const_nhds :
              Tendsto
                (fun _ : ℕ ↦ Real.exp (s / 2) - 1)
                atTop (𝓝 (Real.exp (s / 2) - 1)))
            |>.div_atTop hden).neg
    simpa [z, x] using h
  have hlowerY :
      Tendsto
        (fun n ↦
          frameKoopmanL2 hν (lowerUnipotent (y n)) f)
        atTop (𝓝 f) := by
    have hframe :
        Tendsto (fun n ↦ lowerUnipotent (y n))
          atTop (𝓝 (1 : RealModularFrame)) := by
      simpa only [lowerUnipotent_zero] using
        lowerUnipotent_continuous.continuousAt.tendsto.comp hy
    have hK :=
      (frameKoopmanL2_continuous hν f).continuousAt.tendsto.comp
        hframe
    simpa only [frameKoopmanL2_one] using hK
  have hupperLower :
      Tendsto
        (fun n ↦
          frameKoopmanL2 hν (upperUnipotent (x n))
            (frameKoopmanL2 hν (lowerUnipotent (y n)) f))
        atTop (𝓝 f) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hdist :=
      (tendsto_iff_dist_tendsto_zero.mp hlowerY)
    convert hdist using 1
    funext n
    calc
      dist
          (frameKoopmanL2 hν (upperUnipotent (x n))
            (frameKoopmanL2 hν (lowerUnipotent (y n)) f))
          f =
        dist
          (frameKoopmanL2 hν (upperUnipotent (x n))
            (frameKoopmanL2 hν (lowerUnipotent (y n)) f))
          (frameKoopmanL2 hν (upperUnipotent (x n)) f) := by
            rw [hupper]
      _ =
        dist
          (frameKoopmanL2 hν (lowerUnipotent (y n)) f)
          f := by
            simp only [dist_eq_norm]
            exact norm_frameKoopmanL2_sub hν _ _ _
  have hlowerZ :
      Tendsto
        (fun n ↦
          frameKoopmanL2 hν (lowerUnipotent (z n)) f)
        atTop (𝓝 f) := by
    have hframe :
        Tendsto (fun n ↦ lowerUnipotent (z n))
          atTop (𝓝 (1 : RealModularFrame)) := by
      simpa only [lowerUnipotent_zero] using
        lowerUnipotent_continuous.continuousAt.tendsto.comp hz
    have hK :=
      (frameKoopmanL2_continuous hν f).continuousAt.tendsto.comp
        hframe
    simpa only [frameKoopmanL2_one] using hK
  have hfull :
      Tendsto
        (fun n ↦
          frameKoopmanL2 hν (lowerUnipotent (z n))
            (frameKoopmanL2 hν (upperUnipotent (x n))
              (frameKoopmanL2 hν
                (lowerUnipotent (y n)) f)))
        atTop (𝓝 f) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have h₁ :=
      tendsto_iff_dist_tendsto_zero.mp hupperLower
    have h₂ :=
      tendsto_iff_dist_tendsto_zero.mp hlowerZ
    have hsum :
        Tendsto
          (fun n ↦
            dist
                (frameKoopmanL2 hν (upperUnipotent (x n))
                  (frameKoopmanL2 hν
                    (lowerUnipotent (y n)) f))
                f +
              dist
                (frameKoopmanL2 hν
                  (lowerUnipotent (z n)) f)
                f)
          atTop (𝓝 0) := by
      simpa only [zero_add] using h₁.add h₂
    refine squeeze_zero'
      (Eventually.of_forall fun n ↦ dist_nonneg)
      (Eventually.of_forall fun n ↦ ?_)
      hsum
    calc
      dist
          (frameKoopmanL2 hν (lowerUnipotent (z n))
            (frameKoopmanL2 hν (upperUnipotent (x n))
              (frameKoopmanL2 hν
                (lowerUnipotent (y n)) f)))
          f ≤
        dist
          (frameKoopmanL2 hν (lowerUnipotent (z n))
            (frameKoopmanL2 hν (upperUnipotent (x n))
              (frameKoopmanL2 hν
                (lowerUnipotent (y n)) f)))
          (frameKoopmanL2 hν (lowerUnipotent (z n)) f) +
        dist
          (frameKoopmanL2 hν (lowerUnipotent (z n)) f)
          f :=
        dist_triangle _ _ _
      _ =
        dist
          (frameKoopmanL2 hν (upperUnipotent (x n))
            (frameKoopmanL2 hν
              (lowerUnipotent (y n)) f))
          f +
        dist
          (frameKoopmanL2 hν (lowerUnipotent (z n)) f)
          f := by
        congr 1
        simp only [dist_eq_norm]
        exact norm_frameKoopmanL2_sub hν _ _ _
  have heq (n : ℕ) :
      frameKoopmanL2 hν (geodesicFrame s) f =
        frameKoopmanL2 hν (lowerUnipotent (z n))
          (frameKoopmanL2 hν (upperUnipotent (x n))
            (frameKoopmanL2 hν
              (lowerUnipotent (y n)) f)) := by
    rw [← mautner_diagonal_factorization s (x n) (hx n)]
    simp only [z, y]
    rw [frameKoopmanL2_mul, frameKoopmanL2_mul,
      frameKoopmanL2_mul, hupper]
  have hconstant :
      Tendsto
        (fun _ : ℕ ↦
          frameKoopmanL2 hν (geodesicFrame s) f)
        atTop (𝓝 f) :=
    hfull.congr' (Eventually.of_forall fun n ↦ (heq n).symm)
  exact tendsto_nhds_unique tendsto_const_nhds hconstant

/-- After diagonal invariance is known, contraction by the diagonal
subgroup forces invariance under the opposite unipotent subgroup. -/
theorem frameKoopmanL2_lower_fixed_of_upper_fixed
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν)
    (f : Lp ℝ 2 (ν : Measure GammaTwoFrameQuotient))
    (hupper :
      ∀ t : ℝ,
        frameKoopmanL2 hν (upperUnipotent t) f = f)
    (r : ℝ) :
    frameKoopmanL2 hν (lowerUnipotent r) f = f := by
  have hgeodesic :=
    frameKoopmanL2_geodesic_fixed_of_upper_fixed
      hν f hupper
  let w : ℕ → ℝ :=
    fun n ↦ Real.exp (-(n : ℝ)) * r
  have hw : Tendsto w atTop (𝓝 0) := by
    simpa only [w, Function.comp_apply, zero_mul] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        tendsto_natCast_atTop_atTop).mul_const r
  have hlower :
      Tendsto
        (fun n ↦
          frameKoopmanL2 hν (lowerUnipotent (w n)) f)
        atTop (𝓝 f) := by
    have hframe :
        Tendsto (fun n ↦ lowerUnipotent (w n))
          atTop (𝓝 (1 : RealModularFrame)) := by
      simpa only [lowerUnipotent_zero] using
        lowerUnipotent_continuous.continuousAt.tendsto.comp hw
    have hK :=
      (frameKoopmanL2_continuous hν f).continuousAt.tendsto.comp
        hframe
    simpa only [frameKoopmanL2_one] using hK
  have hdist :
      Tendsto
        (fun n ↦
          dist
            (frameKoopmanL2 hν (lowerUnipotent (w n)) f)
            f)
        atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hlower
  have heq (n : ℕ) :
      dist
          (frameKoopmanL2 hν (lowerUnipotent (w n)) f)
          f =
        dist
          (frameKoopmanL2 hν (lowerUnipotent r) f)
          f := by
    have hconj :=
      geodesicFrame_lowerUnipotent_conjugation
        (-(n : ℝ)) r
    have hwframe :
        lowerUnipotent (w n) =
          geodesicFrame (n : ℝ) *
            lowerUnipotent r *
              geodesicFrame (-(n : ℝ)) := by
      simpa only [neg_neg, w] using hconj.symm
    rw [hwframe, frameKoopmanL2_mul,
      frameKoopmanL2_mul, hgeodesic]
    calc
      dist
          (frameKoopmanL2 hν (geodesicFrame (n : ℝ))
            (frameKoopmanL2 hν (lowerUnipotent r) f))
          f =
        dist
          (frameKoopmanL2 hν (geodesicFrame (n : ℝ))
            (frameKoopmanL2 hν (lowerUnipotent r) f))
          (frameKoopmanL2 hν (geodesicFrame (n : ℝ)) f) := by
            rw [hgeodesic]
      _ =
        dist
          (frameKoopmanL2 hν (lowerUnipotent r) f)
          f := by
            simp only [dist_eq_norm]
            exact norm_frameKoopmanL2_sub hν _ _ _
  have hconstant :
      Tendsto
        (fun _ : ℕ ↦
          dist
            (frameKoopmanL2 hν (lowerUnipotent r) f)
            f)
        atTop (𝓝 0) :=
    hdist.congr' (Eventually.of_forall fun n ↦ heq n)
  have hzero :
      dist
        (frameKoopmanL2 hν (lowerUnipotent r) f)
        f = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hconstant
  exact dist_eq_zero.mp hzero

/-- Mautner's phenomenon for the right regular representation of
`SL(2,ℝ)`: upper-unipotent fixed vectors are fixed by every frame. -/
theorem frameKoopmanL2_fixed_of_upper_fixed
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν)
    (f : Lp ℝ 2 (ν : Measure GammaTwoFrameQuotient))
    (hupper :
      ∀ t : ℝ,
        frameKoopmanL2 hν (upperUnipotent t) f = f)
    (a : RealModularFrame) :
    frameKoopmanL2 hν a f = f := by
  have hgeodesic :=
    frameKoopmanL2_geodesic_fixed_of_upper_fixed
      hν f hupper
  have hlower :=
    frameKoopmanL2_lower_fixed_of_upper_fixed
      hν f hupper
  have hweyl :
      frameKoopmanL2 hν mautnerWeyl f = f := by
    rw [mautnerWeyl, frameKoopmanL2_mul,
      frameKoopmanL2_mul, hupper, hlower, hupper]
  have hweylInv :
      frameKoopmanL2 hν mautnerWeyl⁻¹ f = f := by
    have hone :=
      frameKoopmanL2_mul hν mautnerWeyl⁻¹
        mautnerWeyl f
    rw [inv_mul_cancel, frameKoopmanL2_one, hweyl] at hone
    exact hone.symm
  have hdiagonal :
      ∀ b : ℝ, ∀ hb : b ≠ 0,
        frameKoopmanL2 hν (mautnerDiagonal b hb) f = f := by
    intro b hb
    rcases lt_or_gt_of_ne hb with hbneg | hbpos
    · rw [← mautnerWeyl_sq_mul_geodesic hbneg,
        frameKoopmanL2_mul, frameKoopmanL2_mul]
      rw [hgeodesic, hweyl, hweyl]
    · rw [mautnerDiagonal_pos_eq_geodesic hbpos,
        hgeodesic]
  have hbig :
      ∀ b : RealModularFrame, b 0 0 ≠ 0 →
        frameKoopmanL2 hν b f = f := by
    intro b hb
    rw [← lower_diagonal_upper_eq b hb,
      frameKoopmanL2_mul, frameKoopmanL2_mul]
    rw [hupper, hdiagonal, hlower]
  by_cases ha00 : a 0 0 = 0
  · have ha10 : a 1 0 ≠ 0 := by
      intro ha10
      have hdet := Matrix.SpecialLinearGroup.det_coe a
      rw [Matrix.det_fin_two, ha00, ha10] at hdet
      norm_num at hdet
    let b : RealModularFrame := mautnerWeyl * a
    have hb00 : b 0 0 ≠ 0 := by
      change (mautnerWeyl * a) 0 0 ≠ 0
      simp [mautnerWeyl,
        Matrix.SpecialLinearGroup.coe_mul,
        Matrix.mul_apply, Fin.sum_univ_two,
        ha10]
    have hb := hbig b hb00
    have hab : mautnerWeyl⁻¹ * b = a := by
      simp [b]
    rw [← hab, frameKoopmanL2_mul]
    rw [hb, hweylInv]
  · exact hbig a ha00

/-! ## Haar ergodicity -/

/-- Every right-invariant frame probability on
`Γ(2) \ SL(2,ℝ)` is ergodic for the horocycle flow. -/
theorem IsRightInvariantFrameProbability.horocycleErgodic
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν) :
    HGAS.Dynamics.IsErgodicInvariantProbability
      gammaTwoHorocycleFlow ν := by
  refine ⟨hν.horocycleInvariant, ?_⟩
  intro A hA hAflow
  let f : Lp ℝ 2 (ν : Measure GammaTwoFrameQuotient) :=
    indicatorConstLp 2 hA (measure_ne_top _ _) (1 : ℝ)
  have hupper :
      ∀ t : ℝ,
        frameKoopmanL2 hν (upperUnipotent t) f = f := by
    intro t
    change
      Lp.compMeasurePreserving
          (gammaTwoFrameRightMul (upperUnipotent t))
          (hν.measurePreservingRightMul (upperUnipotent t))
          (indicatorConstLp 2 hA (measure_ne_top _ _) (1 : ℝ)) =
        indicatorConstLp 2 hA (measure_ne_top _ _) (1 : ℝ)
    rw [Lp.indicatorConstLp_compMeasurePreserving]
    apply
      (indicatorConstLp_inj _ _ _ _
        (one_ne_zero : (1 : ℝ) ≠ 0)).2
    simpa only [← gammaTwoHorocycleFlow_eq_rightMul] using
      hAflow t
  have hfixed :
      ∀ a : RealModularFrame,
        frameKoopmanL2 hν a f = f :=
    frameKoopmanL2_fixed_of_upper_fixed hν f hupper
  have hAall :
      ∀ a : RealModularFrame,
        (gammaTwoFrameRightMul a) ⁻¹' A =ᵐ[
          (ν : Measure GammaTwoFrameQuotient)] A := by
    intro a
    have ha := hfixed a
    change
      Lp.compMeasurePreserving
          (gammaTwoFrameRightMul a)
          (hν.measurePreservingRightMul a)
          (indicatorConstLp 2 hA (measure_ne_top _ _) (1 : ℝ)) =
        indicatorConstLp 2 hA (measure_ne_top _ _) (1 : ℝ) at ha
    rw [Lp.indicatorConstLp_compMeasurePreserving] at ha
    exact
      (indicatorConstLp_inj _ _ _ _
        (one_ne_zero : (1 : ℝ) ≠ 0)).1 ha
  by_cases hAzero :
      (ν : Measure GammaTwoFrameQuotient) A = 0
  · exact Or.inl hAzero
  · right
    let ρ : FiniteMeasure GammaTwoFrameQuotient :=
      ν.toFiniteMeasure.restrict A
    have hρ : ρ ≠ 0 := by
      exact
        (FiniteMeasure.restrict_nonzero_iff
          ν.toFiniteMeasure A).2
            ((ν.null_iff_toMeasure_null A).not.mpr hAzero)
    let νA : ProbabilityMeasure GammaTwoFrameQuotient :=
      ρ.normalize
    have hνA :
        IsRightInvariantFrameProbability νA := by
      intro a
      have hmapν :
          Measure.map (gammaTwoFrameRightMul a)
              (ν : Measure GammaTwoFrameQuotient) =
            (ν : Measure GammaTwoFrameQuotient) :=
        congrArg ProbabilityMeasure.toMeasure (hν a)
      have hmapRestrict :
          Measure.map (gammaTwoFrameRightMul a)
              ((ν : Measure GammaTwoFrameQuotient).restrict A) =
            (ν : Measure GammaTwoFrameQuotient).restrict A := by
        have hr :=
          Measure.restrict_map
            (μ := (ν : Measure GammaTwoFrameQuotient))
            (gammaTwoFrameRightMul_continuous a).measurable hA
        rw [hmapν,
          Measure.restrict_congr_set (hAall a)] at hr
        exact hr.symm
      apply ProbabilityMeasure.toMeasure_injective
      simp only [ProbabilityMeasure.toMeasure_map]
      rw [show
        (νA : Measure GammaTwoFrameQuotient) =
          ρ.mass⁻¹ • (ρ : Measure GammaTwoFrameQuotient) by
            exact ρ.toMeasure_normalize_eq_of_nonzero hρ]
      rw [Measure.map_smul]
      change
        ρ.mass⁻¹ •
            Measure.map (gammaTwoFrameRightMul a)
              ((ν : Measure GammaTwoFrameQuotient).restrict A) =
          ρ.mass⁻¹ •
            ((ν : Measure GammaTwoFrameQuotient).restrict A)
      rw [hmapRestrict]
    have hνAeq : νA = ν :=
      gammaTwoRightInvariantProbability_unique νA ν
        hνA hν
    have haeA :
        ∀ᵐ q ∂(νA : Measure GammaTwoFrameQuotient),
          q ∈ A := by
      exact
        HGAS.Dynamics.ae_mem_normalize_restrict
          ν.toFiniteMeasure hA hρ
    have hmassA :
        (νA : Measure GammaTwoFrameQuotient) A = 1 := by
      have h :=
        (ae_mem_iff_measure_eq hA.nullMeasurableSet).1 haeA
      simpa only [measure_univ] using h
    simpa only [hνAeq] using hmassA

end

end HGAS.Modular
