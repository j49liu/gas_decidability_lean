import HGAS.Computability.CubicLiftEffectiveGain
import HGAS.Veronese.CubicLiftShadowingBounds
import HGAS.Veronese.ShadowingPrelims
import HGAS.Stability.LinearConjugacyLyapunov
import Mathlib.Tactic

/-!
# Fixed-parameter computable gains for the Lyapunov half of cubicization

`HGAS.Computability.CubicLiftEffectiveGain` constructs, for each fixed
pair `(n,k)`, a computable gain `K = M (1 + ‖F‖₁)` satisfying the
stabilization inequalities.  The Lyapunov-stability half of the paper uses
the stronger package `CubicLiftShadowingBounds`, which additionally needs a
sup-norm Lipschitz constant `L` of the angular field and the radial rate of
the unstabilized cubic lift on `Q = 1`, and the shadowing gain condition
`2 L + 1 ≤ K c - C`.

The Lipschitz constant is again linear in the input field.  We prove this
by the same monomial-basis expansion as for the tangency and radial
constants: Lipschitz constants add under sums and scale by `|c|`.

We then

* fix, once per `(n,k)`, a natural multiplier `M` for which
  `K = M (1 + ‖F‖₁)` satisfies all the gain conditions;
* define the corresponding total primitive-recursive compiler
  `effectiveCubicLSReductionCode`, which sends malformed inputs to an
  explicit cubic field that is not Lyapunov stable;
* prove that it is a many-one reduction for `HGASQ`, and that it is a
  reduction for `HLSQ` as soon as the semantic Lyapunov-stability
  conjugacy theorem for the stabilized lift is available.

As in the GAS module, the computability statement is nonuniform in
`(n,k)`.
-/

namespace HGAS.Veronese

open Set Metric
open scoped BigOperators

noncomputable section

variable {n k : ℕ}

/-! ## Sup-norm Lipschitz bounds for the angular data of the cubic lift -/

/-- The angular field and the radial reward of the unstabilized cubic lift
of `F` are `L`-Lipschitz on `Q = 1`, for the sup norm. -/
def CubicLiftLipschitzOn
    (F : HGAS.PolynomialField n) (k : ℕ) (L : ℝ) : Prop :=
  (∀ y y' : RealVeroneseSpace n k, Q y = 1 → Q y' = 1 →
      ‖weightedAngularField (evaluatedCubicLift (k := k) F) y -
          weightedAngularField (evaluatedCubicLift (k := k) F) y'‖ ≤
        L * ‖y - y'‖) ∧
    (∀ y y' : RealVeroneseSpace n k, Q y = 1 → Q y' = 1 →
      |weightedRadialReward (evaluatedCubicLift (k := k) F) y -
          weightedRadialReward (evaluatedCubicLift (k := k) F) y'| ≤
        L * ‖y - y'‖)

private theorem mem_closedBall_of_Q_eq_one_shadow
    (y : RealVeroneseSpace n k) (hQ : Q y = 1) :
    y ∈ closedBall (0 : RealVeroneseSpace n k) 1 := by
  simpa [Metric.mem_closedBall, dist_zero_right] using
    norm_le_one_of_Q_eq_one y hQ

/-- Every cubic lift has some sup-norm Lipschitz constant on `Q = 1`. -/
theorem exists_cubicLiftLipschitzOn
    (F : HGAS.PolynomialField n) :
    ∃ L : ℝ, 0 ≤ L ∧ CubicLiftLipschitzOn F k L := by
  have hG := contDiff_evaluatedCubicLift (k := k) F
  obtain ⟨K₁, hK₁⟩ :=
    (contDiff_weightedAngularField hG).contDiffOn.exists_lipschitzOnWith
      one_ne_zero
      (convex_closedBall (0 : RealVeroneseSpace n k) 1)
      (isCompact_closedBall (0 : RealVeroneseSpace n k) 1)
  obtain ⟨K₂, hK₂⟩ :=
    (contDiff_weightedRadialReward hG).contDiffOn.exists_lipschitzOnWith
      one_ne_zero
      (convex_closedBall (0 : RealVeroneseSpace n k) 1)
      (isCompact_closedBall (0 : RealVeroneseSpace n k) 1)
  have hK₁0 : (0 : ℝ) ≤ K₁ := K₁.2
  have hK₂0 : (0 : ℝ) ≤ K₂ := K₂.2
  refine ⟨(K₁ : ℝ) + K₂, add_nonneg hK₁0 hK₂0, ?_, ?_⟩
  · intro y y' hy hy'
    have hlip :=
      hK₁.dist_le_mul y (mem_closedBall_of_Q_eq_one_shadow y hy)
        y' (mem_closedBall_of_Q_eq_one_shadow y' hy')
    rw [dist_eq_norm, dist_eq_norm] at hlip
    exact hlip.trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  · intro y y' hy hy'
    have hlip :=
      hK₂.dist_le_mul y (mem_closedBall_of_Q_eq_one_shadow y hy)
        y' (mem_closedBall_of_Q_eq_one_shadow y' hy')
    rw [Real.dist_eq, dist_eq_norm] at hlip
    exact hlip.trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

theorem CubicLiftLipschitzOn.mono
    {F : HGAS.PolynomialField n} {L L' : ℝ}
    (h : CubicLiftLipschitzOn F k L) (hLL' : L ≤ L') :
    CubicLiftLipschitzOn F k L' := by
  refine ⟨?_, ?_⟩
  · intro y y' hy hy'
    exact (h.1 y y' hy hy').trans
      (mul_le_mul_of_nonneg_right hLL' (norm_nonneg _))
  · intro y y' hy hy'
    exact (h.2 y y' hy hy').trans
      (mul_le_mul_of_nonneg_right hLL' (norm_nonneg _))

theorem cubicLiftLipschitzOn_zero :
    CubicLiftLipschitzOn (zeroPolynomialField n) k 0 := by
  have hzero :
      evaluatedCubicLift (k := k) (zeroPolynomialField n) =
        fun _ => 0 := by
    funext z
    exact evaluatedCubicLift_zero z
  refine ⟨?_, ?_⟩
  · intro y y' _ _
    rw [hzero]
    simp [weightedAngularField, weightedRadialReward, weightedInner]
  · intro y y' _ _
    rw [hzero]
    simp [weightedRadialReward, weightedInner]

private theorem norm_add_sub_add_le_shadow
    {E : Type*} [SeminormedAddCommGroup E] (a b a' b' : E) :
    ‖(a + b) - (a' + b')‖ ≤ ‖a - a'‖ + ‖b - b'‖ := by
  rw [add_sub_add_comm]
  exact norm_add_le _ _

theorem CubicLiftLipschitzOn.add
    {F G : HGAS.PolynomialField n} {L₁ L₂ : ℝ}
    (hF : CubicLiftLipschitzOn F k L₁)
    (hG : CubicLiftLipschitzOn G k L₂) :
    CubicLiftLipschitzOn (addPolynomialField F G) k (L₁ + L₂) := by
  have hfield :
      evaluatedCubicLift (k := k) (addPolynomialField F G) =
        fun z => evaluatedCubicLift (k := k) F z +
          evaluatedCubicLift (k := k) G z := by
    funext z
    exact evaluatedCubicLift_add F G z
  refine ⟨?_, ?_⟩
  · intro y y' hy hy'
    rw [hfield, weightedAngularField_add, weightedAngularField_add]
    calc
      _ ≤ ‖weightedAngularField (evaluatedCubicLift (k := k) F) y -
            weightedAngularField (evaluatedCubicLift (k := k) F) y'‖ +
          ‖weightedAngularField (evaluatedCubicLift (k := k) G) y -
            weightedAngularField (evaluatedCubicLift (k := k) G) y'‖ :=
        norm_add_sub_add_le_shadow _ _ _ _
      _ ≤ L₁ * ‖y - y'‖ + L₂ * ‖y - y'‖ :=
        add_le_add (hF.1 y y' hy hy') (hG.1 y y' hy hy')
      _ = (L₁ + L₂) * ‖y - y'‖ := by ring
  · intro y y' hy hy'
    rw [hfield, weightedRadialReward_add, weightedRadialReward_add]
    calc
      _ ≤ |weightedRadialReward (evaluatedCubicLift (k := k) F) y -
            weightedRadialReward (evaluatedCubicLift (k := k) F) y'| +
          |weightedRadialReward (evaluatedCubicLift (k := k) G) y -
            weightedRadialReward (evaluatedCubicLift (k := k) G) y'| := by
        rw [add_sub_add_comm]
        exact abs_add_le _ _
      _ ≤ L₁ * ‖y - y'‖ + L₂ * ‖y - y'‖ :=
        add_le_add (hF.2 y y' hy hy') (hG.2 y y' hy hy')
      _ = (L₁ + L₂) * ‖y - y'‖ := by ring

theorem CubicLiftLipschitzOn.scale
    {F : HGAS.PolynomialField n} {L : ℝ}
    (c : ℚ) (hF : CubicLiftLipschitzOn F k L) :
    CubicLiftLipschitzOn (scalePolynomialField c F) k
      (|(c : ℝ)| * L) := by
  have hfield :
      evaluatedCubicLift (k := k) (scalePolynomialField c F) =
        fun z => (c : ℝ) • evaluatedCubicLift (k := k) F z := by
    funext z
    exact evaluatedCubicLift_scale c F z
  refine ⟨?_, ?_⟩
  · intro y y' hy hy'
    rw [hfield, weightedAngularField_smul, weightedAngularField_smul,
      ← smul_sub, norm_smul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hF.1 y y' hy hy') (abs_nonneg _)
  · intro y y' hy hy'
    rw [hfield, weightedRadialReward_smul, weightedRadialReward_smul,
      ← mul_sub, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hF.2 y y' hy hy') (abs_nonneg _)

theorem CubicLiftLipschitzOn.cast
    {F G : HGAS.PolynomialField n} {L : ℝ}
    (h : F = G) (hF : CubicLiftLipschitzOn F k L) :
    CubicLiftLipschitzOn G k L :=
  h ▸ hF

theorem cubicLiftLipschitzOn_sum
    {ι : Type*} (s : Finset ι)
    (F : ι → HGAS.PolynomialField n) (L : ι → ℝ)
    (h : ∀ i, CubicLiftLipschitzOn (F i) k (L i)) :
    CubicLiftLipschitzOn (sumPolynomialFields s F) k
      (∑ i ∈ s, L i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hfield :
          zeroPolynomialField n = sumPolynomialFields ∅ F := by
        funext j
        simp [sumPolynomialFields, zeroPolynomialField]
      rw [Finset.sum_empty]
      exact cubicLiftLipschitzOn_zero.cast hfield
  | @insert a s ha ih =>
      have hfield :
          addPolynomialField (F a) (sumPolynomialFields s F) =
            sumPolynomialFields (insert a s) F := by
        simp only [sumPolynomialFields, Finset.sum_insert ha]
        funext j
        rfl
      rw [Finset.sum_insert ha]
      exact ((h a).add ih).cast hfield

/-! ## Uniform Lipschitz constants for the fixed monomial basis -/

/-- A chosen Lipschitz constant for the lift of one coordinate monomial
field.  There are finitely many of them for fixed `(n,k)`. -/
def basisLipschitzConstant
    (n k : ℕ) (i : Fin n) (a : MultiIndex n (2 * k + 1)) : ℝ :=
  Classical.choose
    (exists_cubicLiftLipschitzOn (k := k) (monomialBasisField i a))

theorem basisLipschitzConstant_nonneg
    (n k : ℕ) (i : Fin n) (a : MultiIndex n (2 * k + 1)) :
    0 ≤ basisLipschitzConstant n k i a :=
  (Classical.choose_spec
    (exists_cubicLiftLipschitzOn (k := k) (monomialBasisField i a))).1

theorem basisLipschitzConstant_spec
    (n k : ℕ) (i : Fin n) (a : MultiIndex n (2 * k + 1)) :
    CubicLiftLipschitzOn (monomialBasisField i a) k
      (basisLipschitzConstant n k i a) :=
  (Classical.choose_spec
    (exists_cubicLiftLipschitzOn (k := k) (monomialBasisField i a))).2

/-- The fixed Lipschitz multiplier for degree `2k+1` inputs in `n`
variables. -/
def basisLipschitzBound (n k : ℕ) (_hk : 1 ≤ k) : ℝ :=
  1 + ∑ i : Fin n, ∑ a : MultiIndex n (2 * k + 1),
    basisLipschitzConstant n k i a

theorem basisLipschitzBound_pos
    (n k : ℕ) (hk : 1 ≤ k) :
    0 < basisLipschitzBound n k hk := by
  have hmass :
      0 ≤ ∑ i : Fin n, ∑ a : MultiIndex n (2 * k + 1),
        basisLipschitzConstant n k i a :=
    Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun a _ => basisLipschitzConstant_nonneg n k i a
  unfold basisLipschitzBound
  linarith

theorem basisLipschitzConstant_le_bound
    (n k : ℕ) (hk : 1 ≤ k)
    (i : Fin n) (a : MultiIndex n (2 * k + 1)) :
    basisLipschitzConstant n k i a ≤ basisLipschitzBound n k hk := by
  have hinner :
      basisLipschitzConstant n k i a ≤
        ∑ b : MultiIndex n (2 * k + 1), basisLipschitzConstant n k i b :=
    Finset.single_le_sum
      (f := fun b => basisLipschitzConstant n k i b)
      (fun b _ => basisLipschitzConstant_nonneg n k i b)
      (Finset.mem_univ a)
  have houter :
      (∑ b : MultiIndex n (2 * k + 1), basisLipschitzConstant n k i b) ≤
        ∑ j : Fin n, ∑ b : MultiIndex n (2 * k + 1),
          basisLipschitzConstant n k j b :=
    Finset.single_le_sum
      (f := fun j => ∑ b : MultiIndex n (2 * k + 1),
        basisLipschitzConstant n k j b)
      (fun j _ => Finset.sum_nonneg fun b _ =>
        basisLipschitzConstant_nonneg n k j b)
      (Finset.mem_univ i)
  unfold basisLipschitzBound
  linarith

/-- **Linear Lipschitz bound.**  For a degree-`2k+1` homogeneous field,
the angular field and radial reward of its cubic lift are Lipschitz on
`Q = 1` (sup norm) with a constant bounded by the fixed multiplier
`basisLipschitzBound n k hk` times the coefficient `ℓ¹` norm. -/
theorem exists_cubicLiftLipschitz_uniform
    (F : HGAS.PolynomialField n)
    (hF : HGAS.IsHomogeneousOfDegree (2 * k + 1) F)
    (hk : 1 ≤ k) :
    ∃ L : ℝ, 0 ≤ L ∧
      L ≤ basisLipschitzBound n k hk *
          fieldCoefficientL1 (2 * k + 1) F ∧
      (∀ y y' : RealVeroneseSpace n k, Q y = 1 → Q y' = 1 →
        ‖weightedAngularField (evaluatedCubicLift (k := k) F) y -
            weightedAngularField (evaluatedCubicLift (k := k) F) y'‖ ≤
          L * ‖y - y'‖) ∧
      (∀ y y' : RealVeroneseSpace n k, Q y = 1 → Q y' = 1 →
        |weightedRadialReward (evaluatedCubicLift (k := k) F) y -
            weightedRadialReward (evaluatedCubicLift (k := k) F) y'| ≤
          L * ‖y - y'‖) := by
  let coeffAbs : Fin n × MultiIndex n (2 * k + 1) → ℝ := fun q =>
    |((MvPolynomial.coeff (multiIndexFinsupp q.2) (F q.1) : ℚ) : ℝ)|
  let Lq : Fin n × MultiIndex n (2 * k + 1) → ℝ := fun q =>
    coeffAbs q * basisLipschitzConstant n k q.1 q.2
  have hq :
      ∀ q : Fin n × MultiIndex n (2 * k + 1),
        CubicLiftLipschitzOn (coefficientBasisField F (2 * k + 1) q) k
          (Lq q) := fun q =>
    (basisLipschitzConstant_spec n k q.1 q.2).scale
      (MvPolynomial.coeff (multiIndexFinsupp q.2) (F q.1))
  have hsum :=
    cubicLiftLipschitzOn_sum
      (Finset.univ : Finset (Fin n × MultiIndex n (2 * k + 1)))
      (coefficientBasisField F (2 * k + 1)) Lq hq
  have hfield :
      sumPolynomialFields
          (Finset.univ : Finset (Fin n × MultiIndex n (2 * k + 1)))
          (coefficientBasisField F (2 * k + 1)) = F := by
    simpa [homogeneousFieldFlatExpansion] using
      homogeneousFieldFlatExpansion_eq F hF
  have hLip := hsum.cast hfield
  refine ⟨∑ q, Lq q, ?_, ?_, hLip.1, hLip.2⟩
  · exact Finset.sum_nonneg fun q _ =>
      mul_nonneg (abs_nonneg _) (basisLipschitzConstant_nonneg n k q.1 q.2)
  · rw [fieldCoefficientL1,
      ← Fintype.sum_prod_type
        (fun q : Fin n × MultiIndex n (2 * k + 1) =>
          |((MvPolynomial.coeff (multiIndexFinsupp q.2)
              (F q.1) : ℚ) : ℝ)|),
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q _
    simpa [Lq, coeffAbs, mul_comm] using
      (mul_le_mul_of_nonneg_left
        (basisLipschitzConstant_le_bound n k hk q.1 q.2)
        (abs_nonneg
          (((MvPolynomial.coeff (multiIndexFinsupp q.2)
            (F q.1) : ℚ) : ℝ))))

/-! ## Fixed geometric constants for the shadowing gain

As in `FixedCubicGainParameters`, all analytic constants below depend only
on the fixed pair `(n,k)`.  The angular scale condition now also absorbs
twice the Lipschitz multiplier, so that `K = M (1 + ‖F‖₁)` satisfies the
shadowing condition `2 L + 1 ≤ K c - C`.
-/

structure FixedCubicShadowGainParameters
    (n k : ℕ) (hk : 1 ≤ k) where
  c : ℝ
  η : ℝ
  M : ℕ
  c_pos : 0 < c
  η_pos : 0 < η
  M_pos : 0 < M
  morseBott :
    ∀ y : RealVeroneseSpace n k,
      Q y = 1 →
        completeToricEnergy y ≤ η →
          c * completeToricEnergy y ≤ penaltyDissipation y
  angularScale :
    basisUniformBound n k hk + 2 * basisLipschitzBound n k hk + 1 ≤
      (M : ℝ) * c
  radialScale :
    basisUniformBound n k hk + 1 ≤
      4 * (M : ℝ) * η

theorem nonempty_fixedCubicShadowGainParameters
    (n k : ℕ) (hk : 1 ≤ k) :
    Nonempty (FixedCubicShadowGainParameters n k hk) := by
  obtain ⟨c, η, hc, hη, hMorseBott⟩ :=
    exists_positive_morseBott_coercivity_constants
      (n := n) hk
  let B := basisUniformBound n k hk
  let BL := basisLipschitzBound n k hk
  let threshold : ℝ :=
    max 0 (max ((B + 2 * BL + 1) / c) ((B + 1) / (4 * η)))
  obtain ⟨M, hM⟩ := exists_nat_gt threshold
  have hM0 : (0 : ℝ) < M :=
    lt_of_le_of_lt (le_max_left _ _) hM
  have hMB : (B + 2 * BL + 1) / c < (M : ℝ) :=
    lt_of_le_of_lt
      (le_trans (le_max_left _ _)
        (le_max_right 0
          (max ((B + 2 * BL + 1) / c) ((B + 1) / (4 * η)))))
      hM
  have hMR : (B + 1) / (4 * η) < (M : ℝ) :=
    lt_of_le_of_lt
      (le_trans (le_max_right _ _)
        (le_max_right 0
          (max ((B + 2 * BL + 1) / c) ((B + 1) / (4 * η)))))
      hM
  have hAngular : B + 2 * BL + 1 ≤ (M : ℝ) * c :=
    le_of_lt ((div_lt_iff₀ hc).mp hMB)
  have hfourEta : 0 < 4 * η := mul_pos (by norm_num) hη
  have hRadial : B + 1 ≤ 4 * (M : ℝ) * η := by
    have hstrict : B + 1 < (M : ℝ) * (4 * η) :=
      (div_lt_iff₀ hfourEta).mp hMR
    nlinarith
  have hMnat : 0 < M := by
    exact_mod_cast hM0
  exact ⟨{
    c := c
    η := η
    M := M
    c_pos := hc
    η_pos := hη
    M_pos := hMnat
    morseBott := hMorseBott
    angularScale := hAngular
    radialScale := hRadial
  }⟩

noncomputable def fixedCubicShadowGainParameters
    (n k : ℕ) (hk : 1 ≤ k) :
    FixedCubicShadowGainParameters n k hk :=
  Classical.choice
    (nonempty_fixedCubicShadowGainParameters n k hk)

/-! ## The executable shadowing gain -/

/-- For each fixed `(n,k)`, the input-computable shadowing gain
`M (1 + ‖F‖₁)`, with the fixed natural multiplier `M` hard-coded. -/
def effectiveCubicShadowGainCode
    (n k : ℕ) (hk : 1 ≤ k)
    (F : HGAS.PolynomialFieldCode n) :
    HGAS.RationalCode :=
  HGAS.RationalCode.mul
    (HGAS.RationalCode.ofNat
      (fixedCubicShadowGainParameters n k hk).M)
    (fieldCoefficientScaleCode n (2 * k + 1) F)

theorem effectiveCubicShadowGainCode_primrec
    (n k : ℕ) (hk : 1 ≤ k) :
    Primrec (effectiveCubicShadowGainCode n k hk) := by
  apply HGAS.RationalCode.mul_primrec.comp
  · exact Primrec.const
      (HGAS.RationalCode.ofNat
        (fixedCubicShadowGainParameters n k hk).M)
  · exact fieldCoefficientScaleCode_primrec n (2 * k + 1)

@[simp] theorem decode_effectiveCubicShadowGainCode
    (n k : ℕ) (hk : 1 ≤ k)
    (F : HGAS.PolynomialFieldCode n) :
    HGAS.RationalCode.decode (effectiveCubicShadowGainCode n k hk F) =
      ((fixedCubicShadowGainParameters n k hk).M : ℚ) *
        (1 +
          ∑ i : Fin n,
            ∑ a : MultiIndex n (2 * k + 1),
              |MvPolynomial.coeff (multiIndexFinsupp a)
                (HGAS.PolynomialCode.decode (F i))|) := by
  simp [effectiveCubicShadowGainCode]

theorem real_decode_effectiveCubicShadowGainCode
    (n k : ℕ) (hk : 1 ≤ k)
    (F : HGAS.PolynomialFieldCode n) :
    ((HGAS.RationalCode.decode
      (effectiveCubicShadowGainCode n k hk F) : ℚ) : ℝ) =
      ((fixedCubicShadowGainParameters n k hk).M : ℝ) *
        (1 + fieldCoefficientL1 (2 * k + 1)
          (HGAS.PolynomialFieldCode.decode F)) := by
  rw [decode_effectiveCubicShadowGainCode]
  push_cast
  simp only [fieldCoefficientL1,
    HGAS.PolynomialFieldCode.decode]

theorem decode_effectiveCubicShadowGainCode_pos
    (n k : ℕ) (hk : 1 ≤ k)
    (F : HGAS.PolynomialFieldCode n) :
    0 < HGAS.RationalCode.decode
      (effectiveCubicShadowGainCode n k hk F) := by
  have hreal :
      0 <
        ((HGAS.RationalCode.decode
          (effectiveCubicShadowGainCode n k hk F) : ℚ) : ℝ) := by
    rw [real_decode_effectiveCubicShadowGainCode]
    exact mul_pos
      (by
        exact_mod_cast
          (fixedCubicShadowGainParameters n k hk).M_pos)
      (by
        linarith [fieldCoefficientL1_nonneg
          (2 * k + 1) (HGAS.PolynomialFieldCode.decode F)])
  exact_mod_cast hreal

/-- For fixed `(n,k)`, the input-computable shadowing gain satisfies all
analytic hypotheses of `CubicLiftShadowingBounds`. -/
theorem exists_effectiveCubicLiftShadowingBounds
    (Fcode : HGAS.PolynomialFieldCode n)
    (hF :
      HGAS.IsHomogeneousOfDegree (2 * k + 1)
        (HGAS.PolynomialFieldCode.decode Fcode))
    (hk : 1 ≤ k) :
    ∃ b : CubicLiftShadowingBounds
        (HGAS.PolynomialFieldCode.decode Fcode) k,
      b.K =
        HGAS.RationalCode.decode
          (effectiveCubicShadowGainCode n k hk Fcode) := by
  let F := HGAS.PolynomialFieldCode.decode Fcode
  let p := fixedCubicShadowGainParameters n k hk
  let B := basisUniformBound n k hk
  let BL := basisLipschitzBound n k hk
  let ℓ := fieldCoefficientL1 (2 * k + 1) F
  obtain ⟨b, hC, hA⟩ :=
    exists_cubicLiftLinearBounds_uniform F hF hk
  obtain ⟨L, hL0, hLle, hLang, hLrad⟩ :=
    exists_cubicLiftLipschitz_uniform F hF hk
  have hℓ : 0 ≤ ℓ :=
    fieldCoefficientL1_nonneg (2 * k + 1) F
  have hB : 0 ≤ B :=
    le_of_lt (basisUniformBound_pos n k hk)
  have hBL : 0 ≤ BL :=
    le_of_lt (basisLipschitzBound_pos n k hk)
  have hscale : 0 < 1 + ℓ := by linarith
  let K : ℚ :=
    HGAS.RationalCode.decode
      (effectiveCubicShadowGainCode n k hk Fcode)
  have hKreal :
      (K : ℝ) = (p.M : ℝ) * (1 + ℓ) := by
    simpa [K, p, ℓ, F] using
      real_decode_effectiveCubicShadowGainCode n k hk Fcode
  have hKpos : 0 < K :=
    decode_effectiveCubicShadowGainCode_pos n k hk Fcode
  have hC' : b.C ≤ B * ℓ := by simpa [B, ℓ] using hC
  have hA' : b.A ≤ B * ℓ := by simpa [B, ℓ] using hA
  have hL' : L ≤ BL * ℓ := by simpa [BL, ℓ] using hLle
  have hMc : B + 2 * BL + 1 ≤ (p.M : ℝ) * p.c := by
    simpa [B, BL, p] using p.angularScale
  have hKc :
      (B + 2 * BL + 1) * (1 + ℓ) ≤ (K : ℝ) * p.c := by
    rw [hKreal]
    calc
      (B + 2 * BL + 1) * (1 + ℓ) ≤ ((p.M : ℝ) * p.c) * (1 + ℓ) :=
        mul_le_mul_of_nonneg_right hMc hscale.le
      _ = (p.M : ℝ) * (1 + ℓ) * p.c := by ring
  have hAngular : b.C < (K : ℝ) * p.c := by
    nlinarith
  have hShadow : 2 * L + 1 ≤ (K : ℝ) * p.c - b.C := by
    nlinarith
  have hRadial : b.A + 1 ≤ 4 * (K : ℝ) * p.η := by
    calc
      b.A + 1 ≤ B * ℓ + 1 := by linarith
      _ ≤ (B + 1) * (1 + ℓ) := by nlinarith
      _ ≤ (4 * (p.M : ℝ) * p.η) * (1 + ℓ) :=
        mul_le_mul_of_nonneg_right
          (by simpa [B, p] using p.radialScale)
          (le_of_lt hscale)
      _ = 4 * (K : ℝ) * p.η := by rw [hKreal]; ring
  refine ⟨{
    c := p.c
    η := p.η
    C := b.C
    A := b.A
    K := K
    c_pos := p.c_pos
    η_pos := p.η_pos
    C_nonneg := b.C_nonneg
    A_nonneg := b.A_nonneg
    K_pos := hKpos
    morseBott := p.morseBott
    angularTangency := b.angularTangency
    radialBound := b.radialBound
    angularGain := hAngular
    radialGain := hRadial
    L := L
    L_nonneg := hL0
    angularLipschitz := hLang
    radialLipschitz := hLrad
    shadowGain := hShadow
  }, rfl⟩

/-! ## An explicit cubic field that is not Lyapunov stable

For `m ≥ 2` the cubic field `ẋ₀ = x₀ x₁²`, `ẋᵢ = 0` (`i ≠ 0`) is not
Lyapunov stable: on the line `x₁ = a` the first coordinate grows like
`a exp (a² t)`.  Malformed source codes are sent to this field.  (The zero
field used by the GAS compiler is Lyapunov stable, so it cannot serve as a
negative instance for `HLSQ`.)
-/

/-- The exponent vector of `x₀ x₁²`. -/
def unstableCubicExponent (m : ℕ) : HGAS.ExponentCode m :=
  fun j => if j.val = 0 then 1 else if j.val = 1 then 2 else 0

/-- The cubic field code `ẋ₀ = x₀ x₁²`, `ẋᵢ = 0` for `i ≠ 0`, when
`m ≥ 2`; the zero code otherwise. -/
def unstableCubicCode (m : ℕ) : HGAS.PolynomialFieldCode m :=
  if 2 ≤ m then
    fun i =>
      if i.val = 0 then
        [(unstableCubicExponent m, HGAS.RationalCode.one)]
      else []
  else zeroPolynomialFieldCode m

theorem unstableCubicCode_apply
    (m : ℕ) (hm : 2 ≤ m) (i : Fin m) :
    unstableCubicCode m i =
      if i.val = 0 then
        [(unstableCubicExponent m, HGAS.RationalCode.one)]
      else [] := by
  simp [unstableCubicCode, hm]

theorem decode_unstableCubicExponent
    (m : ℕ) (hm : 2 ≤ m) :
    HGAS.ExponentCode.decode (unstableCubicExponent m) =
      Finsupp.single (⟨0, by omega⟩ : Fin m) 1 +
        Finsupp.single (⟨1, by omega⟩ : Fin m) 2 := by
  ext j
  rcases j with ⟨j, hj⟩
  simp only [HGAS.ExponentCode.decode, Finsupp.coe_mk,
    unstableCubicExponent, Finsupp.add_apply, Finsupp.single_apply,
    Fin.mk.injEq]
  rcases j with _ | _ | j <;> simp

theorem decode_unstableCubicCode
    (m : ℕ) (hm : 2 ≤ m) (i : Fin m) :
    HGAS.PolynomialCode.decode (unstableCubicCode m i) =
      if i.val = 0 then
        MvPolynomial.monomial
          (Finsupp.single (⟨0, by omega⟩ : Fin m) 1 +
            Finsupp.single (⟨1, by omega⟩ : Fin m) 2) 1
      else 0 := by
  rw [unstableCubicCode_apply m hm i]
  split_ifs with hi
  · rw [HGAS.PolynomialCode.decode_cons,
      HGAS.PolynomialCode.decode_nil, add_zero]
    simp only [HGAS.PolynomialCode.decodeTerm,
      HGAS.RationalCode.decode_one,
      decode_unstableCubicExponent m hm]
  · rfl

theorem unstableCubicCode_homogeneous (m : ℕ) :
    HGAS.PolynomialFieldCode.homogeneous 3
      (unstableCubicCode m) = true := by
  by_cases hm : 2 ≤ m
  · rw [HGAS.PolynomialFieldCode.homogeneous_eq_true_iff]
    intro i
    rw [decode_unstableCubicCode m hm i]
    split_ifs
    · apply MvPolynomial.isHomogeneous_monomial
      simp
    · exact MvPolynomial.isHomogeneous_zero _ _ _
  · have hcode : unstableCubicCode m = zeroPolynomialFieldCode m := by
      simp [unstableCubicCode, hm]
    rw [hcode]
    exact zeroPolynomialFieldCode_homogeneous m 3

theorem realize_unstableCubicCode
    (m : ℕ) (hm : 2 ≤ m) (x : Fin m → ℝ) (i : Fin m) :
    HGAS.PolynomialFieldCode.realize (unstableCubicCode m) x i =
      if i.val = 0 then
        x ⟨0, by omega⟩ * x ⟨1, by omega⟩ ^ 2
      else 0 := by
  rw [HGAS.PolynomialFieldCode.realize_apply,
    decode_unstableCubicCode m hm i]
  split_ifs
  · rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial,
      Finsupp.prod_add_index' (by simp) (by intro _ _ _; rw [pow_add]),
      Finsupp.prod_single_index (by simp),
      Finsupp.prod_single_index (by simp)]
    simp
  · simp

/-- The explicit cubic field is not Lyapunov stable (with existence of
solutions) at the origin. -/
theorem not_lyapunovStableWithExistence_unstableCubicCode
    (m : ℕ) (hm : 2 ≤ m) :
    ¬ HGAS.LyapunovStableWithExistence
        (HGAS.PolynomialFieldCode.realize (unstableCubicCode m)) 0 := by
  intro hLS
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  let V := HGAS.PolynomialFieldCode.realize (unstableCubicCode m)
  have hV0 : ∀ x : Fin m → ℝ, V x i0 = x i0 * x i1 ^ 2 := by
    intro x
    simpa [V, i0, i1] using realize_unstableCubicCode m hm x i0
  have hV1 : ∀ x : Fin m → ℝ, V x i1 = 0 := by
    intro x
    simpa [V, i0, i1] using realize_unstableCubicCode m hm x i1
  obtain ⟨δ, hδ, hball⟩ := hLS 1 one_pos
  set a : ℝ := δ / 2 with ha_def
  have ha : 0 < a := by positivity
  let x₀ : Fin m → ℝ := fun j => if j.val ≤ 1 then a else 0
  have hx₀ : dist x₀ 0 < δ := by
    rw [dist_zero_right]
    have hnorm : ‖x₀‖ ≤ a := by
      rw [pi_norm_le_iff_of_nonneg ha.le]
      intro j
      simp only [x₀]
      split_ifs
      · simp [abs_of_pos ha]
      · simp [ha.le]
    linarith
  obtain ⟨⟨γ, hγ⟩, hbound⟩ := hball x₀ hx₀
  have hγ0 : γ 0 = x₀ := hγ.1
  have hcurve : IsIntegralCurveOn γ (fun _ => V) (Ici 0) := hγ.2
  have hcoord :
      ∀ j : Fin m, ∀ t : ℝ, 0 ≤ t →
        HasDerivWithinAt (fun s => γ s j) (V (γ t) j) (Ici t) t := by
    intro j t ht
    exact hasDerivWithinAt_pi.mp
      ((hcurve t ht).mono (Set.Ici_subset_Ici.mpr ht)) j
  have hcont :
      ∀ j : Fin m, ∀ T : ℝ,
        ContinuousOn (fun s => γ s j) (Icc 0 T) := by
    intro j T
    exact (continuous_apply j).comp_continuousOn
      (hcurve.continuousOn.mono Set.Icc_subset_Ici_self)
  -- The second coordinate stays equal to `a`.
  have hγ1 : ∀ t : ℝ, 0 ≤ t → γ t i1 = a := by
    intro T hT
    have hconst :=
      constant_of_has_deriv_right_zero (hcont i1 T)
        (fun t ht => by
          have h := hcoord i1 t ht.1
          rwa [hV1] at h)
        T ⟨hT, le_rfl⟩
    rw [hconst, hγ0]
    simp [x₀, i1]
  -- `γ₀ exp (-a² t)` is constant.
  let g : ℝ → ℝ := fun s => γ s i0 * Real.exp (-(a ^ 2) * s)
  have hexp :
      ∀ t : ℝ,
        HasDerivAt (fun s => Real.exp (-(a ^ 2) * s))
          (Real.exp (-(a ^ 2) * t) * (-(a ^ 2))) t := by
    intro t
    have h := ((hasDerivAt_id t).const_mul (-(a ^ 2))).exp
    simpa using h
  have hg : ∀ T : ℝ, 0 ≤ T → g T = a := by
    intro T hT
    have hconst :=
      constant_of_has_deriv_right_zero
        (f := g)
        ((hcont i0 T).mul
          (Real.continuous_exp.comp
            (continuous_const.mul continuous_id)).continuousOn)
        (fun t ht => by
          have h :=
            (hcoord i0 t ht.1).mul (hexp t).hasDerivWithinAt
          rw [hV0, hγ1 t ht.1] at h
          convert h using 1
          ring)
        T ⟨hT, le_rfl⟩
    rw [hconst]
    simp [g, hγ0, x₀, i0]
  -- Evaluate at `T = 1 / a³`.
  set T : ℝ := 1 / a ^ 3 with hT_def
  have hT : 0 ≤ T := by positivity
  have hgT := hg T hT
  have hγT : γ T i0 = a * Real.exp (a ^ 2 * T) := by
    have hprod :
        γ T i0 * Real.exp (-(a ^ 2) * T) *
            Real.exp (a ^ 2 * T) =
          a * Real.exp (a ^ 2 * T) := by
      rw [show γ T i0 * Real.exp (-(a ^ 2) * T) = a from hgT]
    rw [mul_assoc, ← Real.exp_add,
      show -(a ^ 2) * T + a ^ 2 * T = 0 by ring,
      Real.exp_zero, mul_one] at hprod
    exact hprod
  have hexp_ge : a ^ 2 * T + 1 ≤ Real.exp (a ^ 2 * T) :=
    Real.add_one_le_exp _
  have haT : a ^ 2 * T * a = 1 := by
    rw [hT_def]
    field_simp
  have hlarge : 1 < γ T i0 := by
    rw [hγT]
    nlinarith
  have hsmall := hbound γ hγ T hT
  rw [dist_zero_right] at hsmall
  have hcoordle : ‖γ T i0‖ ≤ ‖γ T‖ := norm_le_pi_norm (γ T) i0
  rw [Real.norm_eq_abs] at hcoordle
  have := le_abs_self (γ T i0)
  linarith

theorem not_globallyAsymptoticallyStable_unstableCubicCode
    (m : ℕ) (hm : 2 ≤ m) :
    ¬ HGAS.GloballyAsymptoticallyStable
        (HGAS.PolynomialFieldCode.realize (unstableCubicCode m)) 0 :=
  fun h =>
    not_lyapunovStableWithExistence_unstableCubicCode m hm
      h.lyapunovStableWithExistence

theorem unstableCubicCode_not_hgasQ
    (m : ℕ) (hm : 2 ≤ m) :
    ¬ HGAS.HGASQ m 3 (unstableCubicCode m) :=
  fun h => not_globallyAsymptoticallyStable_unstableCubicCode m hm h.2

theorem unstableCubicCode_not_hlsQ
    (m : ℕ) (hm : 2 ≤ m) :
    ¬ HGAS.HLSQ m 3 (unstableCubicCode m) :=
  fun h => not_lyapunovStableWithExistence_unstableCubicCode m hm h.2

/-! ## The total compiler for the Lyapunov-stability reduction -/

/-- For `n ≥ 2` and `k ≥ 1`, the cubic target dimension is at least two,
so the explicit unstable cubic field is available there. -/
theorem two_le_cubicLiftCodeDimension
    (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    2 ≤ cubicLiftCodeDimension n k := by
  unfold cubicLiftCodeDimension
  rw [Nat.succ_le_iff, Fintype.one_lt_card_iff]
  refine ⟨pureMultiIndex (k := k) (⟨0, by omega⟩ : Fin n),
    pureMultiIndex (k := k) (⟨1, by omega⟩ : Fin n), ?_⟩
  intro h
  have happ := congrArg
    (fun a : MultiIndex n k => a.1 (⟨0, by omega⟩ : Fin n)) h
  have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
    simp [Fin.ext_iff]
  simp only [pureMultiIndex_apply_same,
    pureMultiIndex_apply_of_ne hne] at happ
  omega

/-- Total fixed-parameter compiler for the Lyapunov-stability reduction.
Valid inputs are sent to the stabilized cubic lift with the shadowing
gain; malformed inputs to the explicit unstable cubic field. -/
def effectiveCubicLSReductionCode
    (n k : ℕ) (hk : 1 ≤ k)
    (F : HGAS.PolynomialFieldCode n) :
    HGAS.PolynomialFieldCode (cubicLiftCodeDimension n k) :=
  bif HGAS.PolynomialFieldCode.homogeneous (2 * k + 1) F then
    stabilizedCubicFieldCode n k F
      (effectiveCubicShadowGainCode n k hk F)
  else
    unstableCubicCode (cubicLiftCodeDimension n k)

theorem effectiveCubicLSReductionCode_primrec
    (n k : ℕ) (hk : 1 ≤ k) :
    Primrec (effectiveCubicLSReductionCode n k hk) := by
  apply Primrec.cond
  · exact
      (HGAS.PolynomialFieldCode.homogeneous_primrec n).comp
        (Primrec.pair (Primrec.const (2 * k + 1)) Primrec.id)
  · exact
      (stabilizedCubicFieldCode_primrec n k).comp
        Primrec.id (effectiveCubicShadowGainCode_primrec n k hk)
  · exact Primrec.const
      (unstableCubicCode (cubicLiftCodeDimension n k))

theorem effectiveCubicLSReductionCode_of_homogeneous
    (n k : ℕ) (hk : 1 ≤ k)
    (F : HGAS.PolynomialFieldCode n)
    (hvalid :
      HGAS.PolynomialFieldCode.homogeneous (2 * k + 1) F = true) :
    effectiveCubicLSReductionCode n k hk F =
      stabilizedCubicFieldCode n k F
        (effectiveCubicShadowGainCode n k hk F) := by
  simp [effectiveCubicLSReductionCode, hvalid]

theorem effectiveCubicLSReductionCode_of_not_homogeneous
    (n k : ℕ) (hk : 1 ≤ k)
    (F : HGAS.PolynomialFieldCode n)
    (hinvalid :
      HGAS.PolynomialFieldCode.homogeneous (2 * k + 1) F = false) :
    effectiveCubicLSReductionCode n k hk F =
      unstableCubicCode (cubicLiftCodeDimension n k) := by
  simp [effectiveCubicLSReductionCode, hinvalid]

/-- Every output of the compiler is a valid cubic code. -/
theorem effectiveCubicLSReductionCode_homogeneous
    (n k : ℕ) (hk : 1 ≤ k)
    (F : HGAS.PolynomialFieldCode n) :
    HGAS.PolynomialFieldCode.homogeneous 3
      (effectiveCubicLSReductionCode n k hk F) = true := by
  by_cases h :
      HGAS.PolynomialFieldCode.homogeneous (2 * k + 1) F = true
  · rw [effectiveCubicLSReductionCode_of_homogeneous n k hk F h]
    exact stabilizedCubicFieldCode_homogeneous n k F _
  · rw [effectiveCubicLSReductionCode_of_not_homogeneous n k hk F
      (Bool.eq_false_of_not_eq_true h)]
    exact unstableCubicCode_homogeneous _

/-- Malformed inputs are sent to codes outside both `HGASQ` and `HLSQ`. -/
theorem effectiveCubicLSReductionCode_not_hgasQ_not_hlsQ_of_invalid
    (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k)
    (Fcode : HGAS.PolynomialFieldCode n)
    (hinvalid :
      HGAS.PolynomialFieldCode.homogeneous (2 * k + 1) Fcode = false) :
    ¬ HGAS.HGASQ (cubicLiftCodeDimension n k) 3
        (effectiveCubicLSReductionCode n k hk Fcode) ∧
      ¬ HGAS.HLSQ (cubicLiftCodeDimension n k) 3
        (effectiveCubicLSReductionCode n k hk Fcode) := by
  rw [effectiveCubicLSReductionCode_of_not_homogeneous n k hk Fcode
    hinvalid]
  have hdim := two_le_cubicLiftCodeDimension n k hn hk
  exact ⟨unstableCubicCode_not_hgasQ _ hdim,
    unstableCubicCode_not_hlsQ _ hdim⟩

/-! ## Correctness for global asymptotic stability -/

/-- The Lyapunov-stability compiler is also an exact many-one reduction
for homogeneous GAS. -/
theorem effectiveCubicLSReductionCode_hgasQ_iff
    (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k)
    (Fcode : HGAS.PolynomialFieldCode n) :
    HGAS.HGASQ n (2 * k + 1) Fcode ↔
      HGAS.HGASQ (cubicLiftCodeDimension n k) 3
        (effectiveCubicLSReductionCode n k hk Fcode) := by
  by_cases hvalid :
      HGAS.PolynomialFieldCode.homogeneous
        (2 * k + 1) Fcode = true
  · have hF :
        HGAS.IsHomogeneousOfDegree (2 * k + 1)
          (HGAS.PolynomialFieldCode.decode Fcode) :=
      (HGAS.PolynomialFieldCode.homogeneous_eq_true_iff
        (2 * k + 1) Fcode).mp hvalid
    letI : Nonempty (sourceUnitSphere n) :=
      ⟨sourceUnitSpherePointOfPos n (by omega)⟩
    rw [HGAS.hgasQ_iff_of_homogeneous Fcode hvalid,
      HGAS.hgasQ_iff_of_homogeneous
        (effectiveCubicLSReductionCode n k hk Fcode)
        (effectiveCubicLSReductionCode_homogeneous n k hk Fcode),
      effectiveCubicLSReductionCode_of_homogeneous n k hk Fcode hvalid,
      globallyAsymptoticallyStable_realize_stabilizedCode_iff]
    obtain ⟨b, hbK⟩ :=
      exists_effectiveCubicLiftShadowingBounds Fcode hF hk
    rw [← hbK]
    exact sourceGAS_iff_stabilizedCubicGAS
      b.toCubicLiftStabilizationBounds hF hk
  · have hfalse :
        HGAS.PolynomialFieldCode.homogeneous
          (2 * k + 1) Fcode = false :=
      Bool.eq_false_of_not_eq_true hvalid
    have hsource :
        ¬ HGAS.HGASQ n (2 * k + 1) Fcode :=
      fun h => hvalid h.1
    have htarget :=
      (effectiveCubicLSReductionCode_not_hgasQ_not_hlsQ_of_invalid
        n k hn hk Fcode hfalse).1
    exact ⟨fun h => (hsource h).elim,
      fun h => (htarget h).elim⟩

theorem hgasQ_manyOneReducible_cubic_viaLS
    (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    HGAS.HGASQ n (2 * k + 1) ≤₀
      HGAS.HGASQ (cubicLiftCodeDimension n k) 3 :=
  ⟨effectiveCubicLSReductionCode n k hk,
    (effectiveCubicLSReductionCode_primrec n k hk).to_comp,
    effectiveCubicLSReductionCode_hgasQ_iff n k hn hk⟩

/-! ## Correctness for Lyapunov stability, modulo the semantic theorem -/

/-- Lyapunov stability of the realized stabilized cubic code is Lyapunov
stability of the semantic stabilized field: the two are linearly
conjugate by a coordinate reindexing. -/
theorem lyapunovStableWithExistence_realize_stabilizedCode_iff
    (n k : ℕ) (F : HGAS.PolynomialFieldCode n)
    (K : HGAS.RationalCode) :
    HGAS.LyapunovStableWithExistence
        (HGAS.PolynomialFieldCode.realize
          (stabilizedCubicFieldCode n k F K)) 0 ↔
      HGAS.LyapunovStableWithExistence
        (fun y : RealVeroneseSpace n k =>
          evalCoordinateField
            (stabilizedCubicField (k := k)
              (HGAS.PolynomialFieldCode.decode F)
              (HGAS.RationalCode.decode K)) y) 0 := by
  rw [realize_stabilizedCubicFieldCode]
  exact HGAS.lyapunovStableWithExistence_conjugateField_iff
    (cubicLiftReindexEquiv n k) _

/-- For valid source codes, `HLSQ` membership is Lyapunov stability of
the evaluated source field. -/
theorem hlsQ_iff_evaluatedSourceField_of_homogeneous
    (n d : ℕ) (Fcode : HGAS.PolynomialFieldCode n)
    (hvalid : HGAS.PolynomialFieldCode.homogeneous d Fcode = true) :
    HGAS.HLSQ n d Fcode ↔
      HGAS.LyapunovStableWithExistence
        (evaluatedSourceField (HGAS.PolynomialFieldCode.decode Fcode))
        0 := by
  rw [HGAS.hlsQ_iff_of_homogeneous Fcode hvalid]
  rfl

/-- For valid source codes, `HLSQ` membership of the compiled target is
Lyapunov stability of the semantic stabilized cubic field, for every
shadowing package carrying the computed gain. -/
theorem effectiveCubicLSReductionCode_hlsQ_iff_stabilized
    (n k : ℕ) (hk : 1 ≤ k)
    (Fcode : HGAS.PolynomialFieldCode n)
    (hvalid :
      HGAS.PolynomialFieldCode.homogeneous (2 * k + 1) Fcode = true)
    (b : CubicLiftShadowingBounds
      (HGAS.PolynomialFieldCode.decode Fcode) k)
    (hbK :
      b.K =
        HGAS.RationalCode.decode
          (effectiveCubicShadowGainCode n k hk Fcode)) :
    HGAS.HLSQ (cubicLiftCodeDimension n k) 3
        (effectiveCubicLSReductionCode n k hk Fcode) ↔
      HGAS.LyapunovStableWithExistence
        (evaluatedStabilizedCubicField
          b.toCubicLiftStabilizationBounds) 0 := by
  rw [HGAS.hlsQ_iff_of_homogeneous
      (effectiveCubicLSReductionCode n k hk Fcode)
      (effectiveCubicLSReductionCode_homogeneous n k hk Fcode),
    effectiveCubicLSReductionCode_of_homogeneous n k hk Fcode hvalid,
    lyapunovStableWithExistence_realize_stabilizedCode_iff, ← hbK]
  rfl

/-- **The Lyapunov-stability reduction, modulo the semantic theorem.**

If, for every homogeneous source field of degree `2k+1` and every
shadowing package, Lyapunov stability of the source is equivalent to
Lyapunov stability of the stabilized cubic lift, then the computable
compiler `effectiveCubicLSReductionCode n k hk` is an exact reduction from
`HLSQ n (2k+1)` to cubic `HLSQ`. -/
theorem effectiveCubicLSReductionCode_hlsQ_iff_of_semantic
    (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hsem : ∀ (F : HGAS.PolynomialField n) (b : CubicLiftShadowingBounds F k),
      HGAS.IsHomogeneousOfDegree (2 * k + 1) F →
      (HGAS.LyapunovStableWithExistence (evaluatedSourceField F) 0 ↔
        HGAS.LyapunovStableWithExistence
          (evaluatedStabilizedCubicField b.toCubicLiftStabilizationBounds) 0))
    (Fcode : HGAS.PolynomialFieldCode n) :
    HGAS.HLSQ n (2 * k + 1) Fcode ↔
      HGAS.HLSQ (cubicLiftCodeDimension n k) 3
        (effectiveCubicLSReductionCode n k hk Fcode) := by
  by_cases hvalid :
      HGAS.PolynomialFieldCode.homogeneous
        (2 * k + 1) Fcode = true
  · have hF :
        HGAS.IsHomogeneousOfDegree (2 * k + 1)
          (HGAS.PolynomialFieldCode.decode Fcode) :=
      (HGAS.PolynomialFieldCode.homogeneous_eq_true_iff
        (2 * k + 1) Fcode).mp hvalid
    obtain ⟨b, hbK⟩ :=
      exists_effectiveCubicLiftShadowingBounds Fcode hF hk
    rw [hlsQ_iff_evaluatedSourceField_of_homogeneous n (2 * k + 1)
        Fcode hvalid,
      effectiveCubicLSReductionCode_hlsQ_iff_stabilized n k hk Fcode
        hvalid b hbK]
    exact hsem _ b hF
  · have hfalse :
        HGAS.PolynomialFieldCode.homogeneous
          (2 * k + 1) Fcode = false :=
      Bool.eq_false_of_not_eq_true hvalid
    have hsource :
        ¬ HGAS.HLSQ n (2 * k + 1) Fcode :=
      fun h => hvalid h.1
    have htarget :=
      (effectiveCubicLSReductionCode_not_hgasQ_not_hlsQ_of_invalid
        n k hn hk Fcode hfalse).2
    exact ⟨fun h => (hsource h).elim,
      fun h => (htarget h).elim⟩

/-- Conditional many-one reduction for Lyapunov stability. -/
theorem hlsQ_manyOneReducible_cubic_of_semantic
    (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hsem : ∀ (F : HGAS.PolynomialField n) (b : CubicLiftShadowingBounds F k),
      HGAS.IsHomogeneousOfDegree (2 * k + 1) F →
      (HGAS.LyapunovStableWithExistence (evaluatedSourceField F) 0 ↔
        HGAS.LyapunovStableWithExistence
          (evaluatedStabilizedCubicField b.toCubicLiftStabilizationBounds) 0)) :
    HGAS.HLSQ n (2 * k + 1) ≤₀
      HGAS.HLSQ (cubicLiftCodeDimension n k) 3 :=
  ⟨effectiveCubicLSReductionCode n k hk,
    (effectiveCubicLSReductionCode_primrec n k hk).to_comp,
    effectiveCubicLSReductionCode_hlsQ_iff_of_semantic n k hn hk hsem⟩

end

end HGAS.Veronese
