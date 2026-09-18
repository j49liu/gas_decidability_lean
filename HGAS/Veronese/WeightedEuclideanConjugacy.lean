import HGAS.Dynamics.EuclideanAngularBlockGAS
import HGAS.Dynamics.LinearConjugacyGAS
import HGAS.Dynamics.StateTimeChange
import HGAS.Veronese.WeightedAngularFlow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Euclidean normalization of the weighted Veronese geometry

The Veronese reduction uses the positive-definite diagonal form

```
Q(y) = ∑ₐ wₐ yₐ²,
```

where every multinomial weight `wₐ` is positive.  This file makes the
standard normalization completely explicit.  The linear coordinate map

```
S(y)ₐ = √wₐ yₐ
```

is a continuous linear equivalence from the raw coordinate space to the
genuine `ℓ²` Euclidean space.  It satisfies

```
⟪S y, S z⟫ = weightedInner y z,
‖S y‖²      = Q(y).
```

Consequently, `S` maps the weighted unit sphere exactly onto the Euclidean
unit sphere.  It also conjugates the weighted angular vector field of `G`
to the ordinary Euclidean angular vector field of the linearly conjugated
ambient field.

The later part of the module promotes these pointwise identities to exact
flow and finite-cocycle conjugacies on the unit spheres.  This is the bridge
between the invariant-measure theorem for the stabilized cubic lift and
the reusable Euclidean angular-block characterization of GAS.
-/

namespace HGAS.Veronese

open Function Metric Set
open scoped BoundedContinuousFunction RealInnerProductSpace

noncomputable section

variable {n k : ℕ}

/-! ## The diagonal square-root equivalence -/

/-- Algebraic diagonal scaling by the positive square roots of the
multinomial weights. -/
noncomputable def weightedDiagonalLinearEquiv :
    RealVeroneseSpace n k ≃ₗ[ℝ] RealVeroneseSpace n k where
  toFun y a := Real.sqrt (multinomialWeight a : ℝ) * y a
  invFun z a := (Real.sqrt (multinomialWeight a : ℝ))⁻¹ * z a
  left_inv y := by
    funext a
    have hsqrt :
        Real.sqrt (multinomialWeight a : ℝ) ≠ 0 :=
      (Real.sqrt_pos.2 (multinomialWeight_real_pos a)).ne'
    simp [hsqrt]
  right_inv z := by
    funext a
    have hsqrt :
        Real.sqrt (multinomialWeight a : ℝ) ≠ 0 :=
      (Real.sqrt_pos.2 (multinomialWeight_real_pos a)).ne'
    simp [hsqrt]
  map_add' y z := by
    funext a
    simp only [Pi.add_apply]
    ring
  map_smul' c y := by
    funext a
    simp [mul_assoc, mul_comm]

@[simp]
theorem weightedDiagonalLinearEquiv_apply
    (y : RealVeroneseSpace n k) (a : MultiIndex n k) :
    weightedDiagonalLinearEquiv y a =
      Real.sqrt (multinomialWeight a : ℝ) * y a :=
  rfl

@[simp]
theorem weightedDiagonalLinearEquiv_symm_apply
    (z : RealVeroneseSpace n k) (a : MultiIndex n k) :
    weightedDiagonalLinearEquiv.symm z a =
      (Real.sqrt (multinomialWeight a : ℝ))⁻¹ * z a :=
  rfl

/-- The diagonal square-root map, with Euclidean `ℓ²` norm on the target. -/
noncomputable def weightedEuclideanEquiv :
    RealVeroneseSpace n k ≃L[ℝ]
      EuclideanSpace ℝ (MultiIndex n k) :=
  ((weightedDiagonalLinearEquiv (n := n) (k := k)).trans
    (WithLp.linearEquiv 2 ℝ
      (RealVeroneseSpace n k)).symm).toContinuousLinearEquiv

@[simp]
theorem weightedEuclideanEquiv_apply_coord
    (y : RealVeroneseSpace n k) (a : MultiIndex n k) :
    weightedEuclideanEquiv y a =
      Real.sqrt (multinomialWeight a : ℝ) * y a :=
  rfl

@[simp]
theorem weightedEuclideanEquiv_symm_apply_coord
    (z : EuclideanSpace ℝ (MultiIndex n k))
    (a : MultiIndex n k) :
    weightedEuclideanEquiv.symm z a =
      (Real.sqrt (multinomialWeight a : ℝ))⁻¹ * z a :=
  rfl

/-- The square-root normalization identifies the weighted bilinear form
with the ordinary Euclidean inner product. -/
theorem inner_weightedEuclideanEquiv
    (y z : RealVeroneseSpace n k) :
    ⟪weightedEuclideanEquiv y, weightedEuclideanEquiv z⟫ =
      weightedInner y z := by
  rw [PiLp.inner_apply]
  unfold weightedInner
  apply Finset.sum_congr rfl
  intro a _
  simp only [weightedEuclideanEquiv_apply_coord, RCLike.inner_apply,
    conj_trivial]
  have hsqrt :
      Real.sqrt (multinomialWeight a : ℝ) *
          Real.sqrt (multinomialWeight a : ℝ) =
        (multinomialWeight a : ℝ) := by
    nlinarith [Real.sq_sqrt
      (multinomialWeight_real_pos a).le]
  calc
    Real.sqrt (multinomialWeight a : ℝ) * z a *
          (Real.sqrt (multinomialWeight a : ℝ) * y a) =
        (Real.sqrt (multinomialWeight a : ℝ) *
          Real.sqrt (multinomialWeight a : ℝ)) * y a * z a := by
            ring
    _ = (multinomialWeight a : ℝ) * y a * z a := by
      rw [hsqrt]

/-- In normalized coordinates the Euclidean norm-square is exactly `Q`. -/
theorem norm_sq_weightedEuclideanEquiv
    (y : RealVeroneseSpace n k) :
    ‖weightedEuclideanEquiv y‖ ^ 2 = Q y := by
  rw [← real_inner_self_eq_norm_sq,
    inner_weightedEuclideanEquiv, weightedInner_self]

/-- The weighted ellipsoid `Q=1` maps to the Euclidean unit sphere. -/
theorem norm_weightedEuclideanEquiv_eq_one_iff
    (y : RealVeroneseSpace n k) :
    ‖weightedEuclideanEquiv y‖ = 1 ↔ Q y = 1 := by
  constructor
  · intro hnorm
    rw [← norm_sq_weightedEuclideanEquiv y, hnorm]
    norm_num
  · intro hQ
    have hsquare :
        ‖weightedEuclideanEquiv y‖ ^ 2 = 1 := by
      rw [norm_sq_weightedEuclideanEquiv, hQ]
    have hnonneg : 0 ≤ ‖weightedEuclideanEquiv y‖ :=
      norm_nonneg _
    nlinarith

/-- Conversely, every Euclidean unit vector pulls back to `Q=1`. -/
theorem Q_weightedEuclideanEquiv_symm_eq_one_iff
    (z : EuclideanSpace ℝ (MultiIndex n k)) :
    Q (weightedEuclideanEquiv.symm z) = 1 ↔ ‖z‖ = 1 := by
  simpa using
    (norm_weightedEuclideanEquiv_eq_one_iff
      (weightedEuclideanEquiv.symm z)).symm

/-! ## Pointwise conjugacy of radial and angular fields -/

/-- Linear normalization turns the weighted radial reward into the ordinary
Euclidean radial reward of the conjugated field. -/
theorem innerRadialReward_conjugateField_weightedEuclideanEquiv
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (y : RealVeroneseSpace n k) :
    HGAS.innerRadialReward
        (HGAS.conjugateField weightedEuclideanEquiv G)
        (weightedEuclideanEquiv y) =
      weightedRadialReward G y := by
  rw [HGAS.innerRadialReward,
    HGAS.conjugateField_apply_equiv,
    inner_weightedEuclideanEquiv]
  rfl

/-- The weighted angular field is linearly conjugate to the ordinary
Euclidean angular field. -/
theorem innerAngularField_conjugateField_weightedEuclideanEquiv
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (y : RealVeroneseSpace n k) :
    HGAS.innerAngularField
        (HGAS.conjugateField weightedEuclideanEquiv G)
        (weightedEuclideanEquiv y) =
      weightedEuclideanEquiv (weightedAngularField G y) := by
  rw [HGAS.innerAngularField, weightedAngularField,
    innerRadialReward_conjugateField_weightedEuclideanEquiv,
    HGAS.conjugateField_apply_equiv, map_sub, map_smul]

/-! ## Conjugacy of the angular flows on the unit spheres -/

/-- On `Q=1`, the bounded Euclidean cutoff reward is exactly the weighted
radial reward before normalization. -/
theorem boundedCutoffInnerRadialReward_weightedEuclideanEquiv
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (hG : ContDiff ℝ 1 G)
    (y : RealVeroneseSpace n k) (hy : Q y = 1) :
    HGAS.boundedCutoffInnerRadialReward
        (HGAS.conjugateField weightedEuclideanEquiv G)
        (HGAS.ContDiff.conjugateField weightedEuclideanEquiv hG)
        (weightedEuclideanEquiv y) =
      weightedRadialReward G y := by
  rw [HGAS.boundedCutoffInnerRadialReward_apply,
    HGAS.cutoffInnerRadialReward_eq_of_norm_eq_one
      (HGAS.conjugateField weightedEuclideanEquiv G)
      (weightedEuclideanEquiv y)
      ((norm_weightedEuclideanEquiv_eq_one_iff y).2 hy),
    innerRadialReward_conjugateField_weightedEuclideanEquiv]

set_option maxHeartbeats 800000 in
-- The finite-dimensional ODE uniqueness theorem constructs a Lipschitz
-- bound on a compact ball; elaborating its bundled norm estimates is costly.
/-- The weighted angular flow and the Euclidean angular flow of the
normalized field are exactly linearly conjugate for every initial point on
`Q=1`.

The two compactly supported ambient cutoffs need not be conjugate away from
the sphere.  We therefore compare their sphere orbits as solutions of the
same *uncut* Euclidean angular ODE and invoke uniqueness on the closed unit
ball. -/
theorem weightedAngularFlow_weightedEuclideanEquiv
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (hG : ContDiff ℝ 1 G)
    (y : RealVeroneseSpace n k) (hy : Q y = 1) :
    ∀ t : ℝ,
      weightedEuclideanEquiv (weightedAngularFlow G hG t y) =
        HGAS.euclideanAngularFlow
          (HGAS.conjugateField weightedEuclideanEquiv G)
          (HGAS.ContDiff.conjugateField weightedEuclideanEquiv hG)
          t (weightedEuclideanEquiv y) := by
  let G' :
      EuclideanSpace ℝ (MultiIndex n k) →
        EuclideanSpace ℝ (MultiIndex n k) :=
    HGAS.conjugateField weightedEuclideanEquiv G
  let hG' : ContDiff ℝ 1 G' :=
    HGAS.ContDiff.conjugateField weightedEuclideanEquiv hG
  let Y := HGAS.innerAngularField G'
  have hY : ContDiff ℝ 1 Y :=
    HGAS.contDiff_innerAngularField hG'
  obtain ⟨K, hK⟩ :=
    hY.contDiffOn.exists_lipschitzOnWith
      one_ne_zero
      (convex_closedBall
        (0 : EuclideanSpace ℝ (MultiIndex n k)) 1)
      (isCompact_closedBall
        (0 : EuclideanSpace ℝ (MultiIndex n k)) 1)
  let γ₁ : ℝ → EuclideanSpace ℝ (MultiIndex n k) :=
    fun t ↦ weightedEuclideanEquiv
      (weightedAngularFlow G hG t y)
  let γ₂ : ℝ → EuclideanSpace ℝ (MultiIndex n k) :=
    fun t ↦ HGAS.euclideanAngularFlow G' hG' t
      (weightedEuclideanEquiv y)
  have hγ₁ : IsIntegralCurve γ₁ (fun _ ↦ Y) := by
    intro t
    have hold :=
      weightedAngularFlow_isIntegralCurve G hG y hy t
    have hmap :=
      weightedEuclideanEquiv.hasFDerivAt.comp_hasDerivAt t hold
    simpa only [γ₁, Y, G',
      innerAngularField_conjugateField_weightedEuclideanEquiv] using
        hmap
  have hγ₂ : IsIntegralCurve γ₂ (fun _ ↦ Y) := by
    simpa only [γ₂, Y] using
      HGAS.euclideanAngularFlow_isIntegralCurve
        G' hG' (weightedEuclideanEquiv y)
        ((norm_weightedEuclideanEquiv_eq_one_iff y).2 hy)
  have hγ₁norm : ∀ t, ‖γ₁ t‖ = 1 := by
    intro t
    exact (norm_weightedEuclideanEquiv_eq_one_iff _).2
      (weightedAngularFlow_preserves_Q G hG y hy t)
  have hγ₂norm : ∀ t, ‖γ₂ t‖ = 1 :=
    HGAS.euclideanAngularFlow_preserves_norm
      G' hG' (weightedEuclideanEquiv y)
      ((norm_weightedEuclideanEquiv_eq_one_iff y).2 hy)
  have heq : γ₁ = γ₂ := by
    apply ODE_solution_unique_univ
      (v := fun _ : ℝ ↦ Y)
      (s := fun _ ↦ closedBall
        (0 : EuclideanSpace ℝ (MultiIndex n k)) 1)
      (K := K) (t₀ := 0)
    · intro _
      exact hK
    · intro t
      exact ⟨hγ₁ t, by
        simp [Metric.mem_closedBall, dist_zero_right, hγ₁norm t]⟩
    · intro t
      exact ⟨hγ₂ t, by
        simp [Metric.mem_closedBall, dist_zero_right, hγ₂norm t]⟩
    · simp [γ₁, γ₂, Flow.map_zero_apply]
  intro t
  exact congrFun heq t

/-! ## Equivalence of finite negative blocks -/

/-- A common negative radial-reward block on the weighted unit sphere.

The reward is written as an ordinary interval integral because it need not
be bounded on the whole ambient coordinate space.  Its restriction to the
compact weighted sphere is, of course, bounded. -/
def HasUniformNegativeWeightedAngularBlock
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (hG : ContDiff ℝ 1 G) : Prop :=
  ∃ T c : ℝ, 0 < T ∧ 0 < c ∧
    ∀ y : RealVeroneseSpace n k, Q y = 1 →
      (∫ t in (0 : ℝ)..T,
        weightedRadialReward G
          (weightedAngularFlow G hG t y)) ≤ -c

/-- Exact equality of a weighted radial cocycle and its Euclidean
normalization. -/
theorem orbitIntegral_weightedEuclideanEquiv
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (hG : ContDiff ℝ 1 G)
    (T : ℝ) (y : RealVeroneseSpace n k) (hy : Q y = 1) :
    HGAS.Dynamics.orbitIntegral
        (HGAS.euclideanAngularFlow
          (HGAS.conjugateField weightedEuclideanEquiv G)
          (HGAS.ContDiff.conjugateField weightedEuclideanEquiv hG))
        (HGAS.boundedCutoffInnerRadialReward
          (HGAS.conjugateField weightedEuclideanEquiv G)
          (HGAS.ContDiff.conjugateField weightedEuclideanEquiv hG))
        T (weightedEuclideanEquiv y) =
      ∫ t in (0 : ℝ)..T,
        weightedRadialReward G
          (weightedAngularFlow G hG t y) := by
  rw [HGAS.Dynamics.orbitIntegral]
  apply intervalIntegral.integral_congr
  intro t _
  change
    HGAS.boundedCutoffInnerRadialReward
        (HGAS.conjugateField weightedEuclideanEquiv G)
        (HGAS.ContDiff.conjugateField weightedEuclideanEquiv hG)
        (HGAS.euclideanAngularFlow
          (HGAS.conjugateField weightedEuclideanEquiv G)
          (HGAS.ContDiff.conjugateField weightedEuclideanEquiv hG)
          t (weightedEuclideanEquiv y)) =
      weightedRadialReward G (weightedAngularFlow G hG t y)
  rw [← weightedAngularFlow_weightedEuclideanEquiv G hG y hy t]
  exact boundedCutoffInnerRadialReward_weightedEuclideanEquiv
    G hG _ (weightedAngularFlow_preserves_Q G hG y hy t)

/-- Diagonal square-root normalization preserves, in both directions, the
existence of one common strictly negative angular block. -/
theorem uniformNegativeWeightedAngularBlock_iff_euclidean
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (hG : ContDiff ℝ 1 G) :
    HasUniformNegativeWeightedAngularBlock G hG ↔
      HGAS.HasUniformNegativeEuclideanAngularBlock
        (HGAS.conjugateField weightedEuclideanEquiv G)
        (HGAS.ContDiff.conjugateField weightedEuclideanEquiv hG) := by
  constructor
  · rintro ⟨T, c, hT, hc, hweighted⟩
    refine ⟨T, c, hT, hc, ?_⟩
    intro z hz
    let y : RealVeroneseSpace n k :=
      weightedEuclideanEquiv.symm z
    have hy : Q y = 1 := by
      exact (Q_weightedEuclideanEquiv_symm_eq_one_iff z).2 hz
    have hblock := hweighted y hy
    calc
      HGAS.Dynamics.orbitIntegral
          (HGAS.euclideanAngularFlow
            (HGAS.conjugateField weightedEuclideanEquiv G)
            (HGAS.ContDiff.conjugateField weightedEuclideanEquiv hG))
          (HGAS.boundedCutoffInnerRadialReward
            (HGAS.conjugateField weightedEuclideanEquiv G)
            (HGAS.ContDiff.conjugateField weightedEuclideanEquiv hG))
          T z =
        HGAS.Dynamics.orbitIntegral
          (HGAS.euclideanAngularFlow
            (HGAS.conjugateField weightedEuclideanEquiv G)
            (HGAS.ContDiff.conjugateField weightedEuclideanEquiv hG))
          (HGAS.boundedCutoffInnerRadialReward
            (HGAS.conjugateField weightedEuclideanEquiv G)
            (HGAS.ContDiff.conjugateField weightedEuclideanEquiv hG))
          T (weightedEuclideanEquiv y) := by
            simp [y]
      _ = ∫ t in (0 : ℝ)..T,
          weightedRadialReward G
            (weightedAngularFlow G hG t y) :=
        orbitIntegral_weightedEuclideanEquiv G hG T y hy
      _ ≤ -c := hblock
  · rintro ⟨T, c, hT, hc, heuclidean⟩
    refine ⟨T, c, hT, hc, ?_⟩
    intro y hy
    have hnorm :
        ‖weightedEuclideanEquiv y‖ = 1 :=
      (norm_weightedEuclideanEquiv_eq_one_iff y).2 hy
    have hblock := heuclidean (weightedEuclideanEquiv y) hnorm
    rw [orbitIntegral_weightedEuclideanEquiv G hG T y hy] at hblock
    exact hblock

/-! ## The weighted angular-block characterization of GAS -/

/-- For a `C²` homogeneous field, GAS in the original weighted coordinates
is equivalent to a common negative block on `Q=1`.

The proof has no weighted dynamical argument left to supply: diagonal
normalization converts the block to the Euclidean criterion, while the
general continuous-linear conjugacy theorem transports GAS itself. -/
theorem
    globallyAsymptoticallyStable_iff_uniformNegativeWeightedAngularBlock
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k)
    (j : ℕ)
    (hGhom : HGAS.ScalesAsDegree ℝ (j + 1) G)
    (hG : ContDiff ℝ 2 G)
    (hzero : G 0 = 0) :
    HGAS.GloballyAsymptoticallyStable G 0 ↔
      HasUniformNegativeWeightedAngularBlock G
        (hG.of_le (by norm_num)) := by
  let G' :
      EuclideanSpace ℝ (MultiIndex n k) →
        EuclideanSpace ℝ (MultiIndex n k) :=
    HGAS.conjugateField weightedEuclideanEquiv G
  let hG1 : ContDiff ℝ 1 G :=
    hG.of_le (by norm_num)
  let hG' : ContDiff ℝ 2 G' :=
    HGAS.ContDiff.conjugateField weightedEuclideanEquiv hG
  have hGhom' : HGAS.ScalesAsDegree ℝ (j + 1) G' := by
    exact HGAS.scalesAsDegree_conjugateField
      weightedEuclideanEquiv hGhom
  have hzero' : G' 0 = 0 := by
    exact HGAS.conjugateField_zero weightedEuclideanEquiv hzero
  have heuclidean :
      HGAS.GloballyAsymptoticallyStable G' 0 ↔
        HGAS.HasUniformNegativeEuclideanAngularBlock G'
          (hG'.of_le (by norm_num)) :=
    HGAS.globallyAsymptoticallyStable_iff_uniformNegativeEuclideanAngularBlock
      G' j hGhom' hG' hzero'
  have hblocks :
      HasUniformNegativeWeightedAngularBlock G hG1 ↔
        HGAS.HasUniformNegativeEuclideanAngularBlock G'
          (hG'.of_le (by norm_num)) := by
    simpa only [G', hG', hG1] using
      uniformNegativeWeightedAngularBlock_iff_euclidean G hG1
  constructor
  · intro hgas
    have hgas' :
        HGAS.GloballyAsymptoticallyStable G' 0 :=
      hgas.conjugateField weightedEuclideanEquiv
    exact hblocks.mpr (heuclidean.mp hgas')
  · intro hblock
    have hgas' :
        HGAS.GloballyAsymptoticallyStable G' 0 :=
      heuclidean.mpr (hblocks.mp hblock)
    exact
      (HGAS.globallyAsymptoticallyStable_conjugateField_iff
        weightedEuclideanEquiv G).mp hgas'

end

end HGAS.Veronese
