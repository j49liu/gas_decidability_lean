import HGAS.Dynamics.EuclideanAngularBlockGAS
import HGAS.Dynamics.LinearConjugacyGAS
import HGAS.Dynamics.StateTimeChange
import HGAS.Veronese.SourceAngularFlow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Euclidean normalization of the source angular system

The source development represents vectors as ordinary functions
`Fin n → ℝ`, whose default norm in Mathlib is the sup norm, while its
algebraic radius is the Euclidean sum of squares

```
sourceRadiusSq(x) = ∑ᵢ xᵢ².
```

This file removes that harmless representation mismatch.  The canonical
linear equivalence

```
Fin n → ℝ  ≃L[ℝ]  EuclideanSpace ℝ (Fin n)
```

keeps every coordinate unchanged and equips the target with its genuine
`ℓ²` norm.  We prove that it:

* identifies `sourceRadiusSq=1` with the Euclidean unit sphere;
* conjugates the source radial and angular fields to their inner-product
  versions;
* conjugates the angular flows on those spheres; and
* identifies their finite radial cocycles.

Combining these identities with the Euclidean angular-block criterion gives
a reusable GAS characterization in the original source coordinates.
-/

namespace HGAS.Veronese

open Function Metric Set
open scoped BoundedContinuousFunction RealInnerProductSpace

noncomputable section

variable {n : ℕ}

/-- The coordinate-preserving equivalence from raw source coordinates to
the genuine finite Euclidean space. -/
noncomputable def sourceEuclideanEquiv :
    (Fin n → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm

@[simp]
theorem sourceEuclideanEquiv_apply_coord
    (x : Fin n → ℝ) (i : Fin n) :
    sourceEuclideanEquiv x i = x i :=
  rfl

@[simp]
theorem sourceEuclideanEquiv_symm_apply_coord
    (u : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    sourceEuclideanEquiv.symm u i = u i :=
  rfl

/-- The Euclidean norm-square in normalized coordinates is the source
algebraic radius-square. -/
theorem norm_sq_sourceEuclideanEquiv
    (x : Fin n → ℝ) :
    ‖sourceEuclideanEquiv x‖ ^ 2 = sourceRadiusSq x := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold sourceRadiusSq
  apply Finset.sum_congr rfl
  intro i _
  simp only [sourceEuclideanEquiv_apply_coord, Real.norm_eq_abs,
    sq_abs]

/-- The source algebraic unit sphere maps exactly to the Euclidean one. -/
theorem norm_sourceEuclideanEquiv_eq_one_iff
    (x : Fin n → ℝ) :
    ‖sourceEuclideanEquiv x‖ = 1 ↔ sourceRadiusSq x = 1 := by
  constructor
  · intro hnorm
    rw [← norm_sq_sourceEuclideanEquiv x, hnorm]
    norm_num
  · intro hR
    have hsquare : ‖sourceEuclideanEquiv x‖ ^ 2 = 1 := by
      rw [norm_sq_sourceEuclideanEquiv, hR]
    have hnonneg : 0 ≤ ‖sourceEuclideanEquiv x‖ :=
      norm_nonneg _
    nlinarith

theorem sourceRadiusSq_sourceEuclideanEquiv_symm_eq_one_iff
    (u : EuclideanSpace ℝ (Fin n)) :
    sourceRadiusSq (sourceEuclideanEquiv.symm u) = 1 ↔ ‖u‖ = 1 := by
  simpa using
    (norm_sourceEuclideanEquiv_eq_one_iff
      (sourceEuclideanEquiv.symm u)).symm

/-- The source dot product becomes the ordinary Euclidean inner product. -/
theorem inner_sourceEuclideanEquiv
    (x y : Fin n → ℝ) :
    ⟪sourceEuclideanEquiv x, sourceEuclideanEquiv y⟫ =
      HGAS.dot x y := by
  rw [PiLp.inner_apply]
  unfold HGAS.dot
  apply Finset.sum_congr rfl
  intro i _
  simp [RCLike.inner_apply, mul_comm]

/-- The source radial reward is the Euclidean radial reward of the
linearly conjugated field. -/
theorem innerRadialReward_conjugateField_sourceEuclideanEquiv
    (F : (Fin n → ℝ) → (Fin n → ℝ))
    (x : Fin n → ℝ) :
    HGAS.innerRadialReward
        (HGAS.conjugateField sourceEuclideanEquiv F)
        (sourceEuclideanEquiv x) =
      HGAS.radialReward F x := by
  rw [HGAS.innerRadialReward,
    HGAS.conjugateField_apply_equiv,
    inner_sourceEuclideanEquiv]
  rfl

/-- The source angular field is linearly conjugate to the Euclidean angular
field of the normalized ambient field. -/
theorem innerAngularField_conjugateField_sourceEuclideanEquiv
    (F : (Fin n → ℝ) → (Fin n → ℝ))
    (x : Fin n → ℝ) :
    HGAS.innerAngularField
        (HGAS.conjugateField sourceEuclideanEquiv F)
        (sourceEuclideanEquiv x) =
      sourceEuclideanEquiv (HGAS.angularField F x) := by
  ext i
  simp [HGAS.innerAngularField, HGAS.angularField,
    innerRadialReward_conjugateField_sourceEuclideanEquiv]

set_option maxHeartbeats 800000 in
-- ODE uniqueness on a finite-dimensional closed ball elaborates a bundled
-- Lipschitz estimate; the larger budget is confined to this one theorem.
/-- Exact conjugacy of the source angular flow and normalized Euclidean
angular flow on the unit sphere. -/
theorem sourceAngularAmbientFlow_sourceEuclideanEquiv
    (F : (Fin n → ℝ) → (Fin n → ℝ))
    (hF : ContDiff ℝ 1 F)
    (x : Fin n → ℝ) (hx : sourceRadiusSq x = 1) :
    ∀ t : ℝ,
      sourceEuclideanEquiv (sourceAngularAmbientFlow F hF t x) =
        HGAS.euclideanAngularFlow
          (HGAS.conjugateField sourceEuclideanEquiv F)
          (HGAS.ContDiff.conjugateField sourceEuclideanEquiv hF)
          t (sourceEuclideanEquiv x) := by
  let F' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    HGAS.conjugateField sourceEuclideanEquiv F
  let hF' : ContDiff ℝ 1 F' :=
    HGAS.ContDiff.conjugateField sourceEuclideanEquiv hF
  let Y := HGAS.innerAngularField F'
  have hY : ContDiff ℝ 1 Y :=
    HGAS.contDiff_innerAngularField hF'
  obtain ⟨K, hK⟩ :=
    hY.contDiffOn.exists_lipschitzOnWith
      one_ne_zero
      (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
  let γ₁ : ℝ → EuclideanSpace ℝ (Fin n) :=
    fun t ↦ sourceEuclideanEquiv
      (sourceAngularAmbientFlow F hF t x)
  let γ₂ : ℝ → EuclideanSpace ℝ (Fin n) :=
    fun t ↦ HGAS.euclideanAngularFlow F' hF' t
      (sourceEuclideanEquiv x)
  have hγ₁ : IsIntegralCurve γ₁ (fun _ ↦ Y) := by
    intro t
    have hold :=
      sourceAngularAmbientFlow_isIntegralCurve F hF x hx t
    have hmap :=
      sourceEuclideanEquiv.hasFDerivAt.comp_hasDerivAt t hold
    simpa only [γ₁, Y, F',
      innerAngularField_conjugateField_sourceEuclideanEquiv] using hmap
  have hγ₂ : IsIntegralCurve γ₂ (fun _ ↦ Y) := by
    simpa only [γ₂, Y] using
      HGAS.euclideanAngularFlow_isIntegralCurve
        F' hF' (sourceEuclideanEquiv x)
        ((norm_sourceEuclideanEquiv_eq_one_iff x).2 hx)
  have hγ₁norm : ∀ t, ‖γ₁ t‖ = 1 := by
    intro t
    exact (norm_sourceEuclideanEquiv_eq_one_iff _).2
      (sourceAngularAmbientFlow_preserves_radiusSq F hF x hx t)
  have hγ₂norm : ∀ t, ‖γ₂ t‖ = 1 :=
    HGAS.euclideanAngularFlow_preserves_norm
      F' hF' (sourceEuclideanEquiv x)
      ((norm_sourceEuclideanEquiv_eq_one_iff x).2 hx)
  have heq : γ₁ = γ₂ := by
    apply ODE_solution_unique_univ
      (v := fun _ : ℝ ↦ Y)
      (s := fun _ ↦
        closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
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

/-- One common negative radial-reward block on the algebraic source unit
sphere. -/
def HasUniformNegativeSourceAngularBlock
    (F : (Fin n → ℝ) → (Fin n → ℝ))
    (hF : ContDiff ℝ 1 F) : Prop :=
  ∃ T c : ℝ, 0 < T ∧ 0 < c ∧
    ∀ x : Fin n → ℝ, sourceRadiusSq x = 1 →
      (∫ t in (0 : ℝ)..T,
        HGAS.radialReward F
          (sourceAngularAmbientFlow F hF t x)) ≤ -c

/-- Exact equality of a source radial cocycle and its normalized Euclidean
cocycle. -/
theorem orbitIntegral_sourceEuclideanEquiv
    (F : (Fin n → ℝ) → (Fin n → ℝ))
    (hF : ContDiff ℝ 1 F)
    (T : ℝ) (x : Fin n → ℝ) (hx : sourceRadiusSq x = 1) :
    HGAS.Dynamics.orbitIntegral
        (HGAS.euclideanAngularFlow
          (HGAS.conjugateField sourceEuclideanEquiv F)
          (HGAS.ContDiff.conjugateField sourceEuclideanEquiv hF))
        (HGAS.boundedCutoffInnerRadialReward
          (HGAS.conjugateField sourceEuclideanEquiv F)
          (HGAS.ContDiff.conjugateField sourceEuclideanEquiv hF))
        T (sourceEuclideanEquiv x) =
      ∫ t in (0 : ℝ)..T,
        HGAS.radialReward F
          (sourceAngularAmbientFlow F hF t x) := by
  rw [HGAS.Dynamics.orbitIntegral]
  apply intervalIntegral.integral_congr
  intro t _
  change
    HGAS.boundedCutoffInnerRadialReward
        (HGAS.conjugateField sourceEuclideanEquiv F)
        (HGAS.ContDiff.conjugateField sourceEuclideanEquiv hF)
        (HGAS.euclideanAngularFlow
          (HGAS.conjugateField sourceEuclideanEquiv F)
          (HGAS.ContDiff.conjugateField sourceEuclideanEquiv hF)
          t (sourceEuclideanEquiv x)) =
      HGAS.radialReward F (sourceAngularAmbientFlow F hF t x)
  rw [← sourceAngularAmbientFlow_sourceEuclideanEquiv F hF x hx t]
  rw [HGAS.boundedCutoffInnerRadialReward_apply,
    HGAS.cutoffInnerRadialReward_eq_of_norm_eq_one
      (HGAS.conjugateField sourceEuclideanEquiv F)
      (sourceEuclideanEquiv (sourceAngularAmbientFlow F hF t x))
      ((norm_sourceEuclideanEquiv_eq_one_iff _).2
        (sourceAngularAmbientFlow_preserves_radiusSq F hF x hx t)),
    innerRadialReward_conjugateField_sourceEuclideanEquiv]

/-- Source and normalized Euclidean negative blocks are equivalent. -/
theorem uniformNegativeSourceAngularBlock_iff_euclidean
    (F : (Fin n → ℝ) → (Fin n → ℝ))
    (hF : ContDiff ℝ 1 F) :
    HasUniformNegativeSourceAngularBlock F hF ↔
      HGAS.HasUniformNegativeEuclideanAngularBlock
        (HGAS.conjugateField sourceEuclideanEquiv F)
        (HGAS.ContDiff.conjugateField sourceEuclideanEquiv hF) := by
  constructor
  · rintro ⟨T, c, hT, hc, hsource⟩
    refine ⟨T, c, hT, hc, ?_⟩
    intro u hu
    let x : Fin n → ℝ := sourceEuclideanEquiv.symm u
    have hx : sourceRadiusSq x = 1 :=
      (sourceRadiusSq_sourceEuclideanEquiv_symm_eq_one_iff u).2 hu
    calc
      HGAS.Dynamics.orbitIntegral
          (HGAS.euclideanAngularFlow
            (HGAS.conjugateField sourceEuclideanEquiv F)
            (HGAS.ContDiff.conjugateField sourceEuclideanEquiv hF))
          (HGAS.boundedCutoffInnerRadialReward
            (HGAS.conjugateField sourceEuclideanEquiv F)
            (HGAS.ContDiff.conjugateField sourceEuclideanEquiv hF))
          T u =
        HGAS.Dynamics.orbitIntegral
          (HGAS.euclideanAngularFlow
            (HGAS.conjugateField sourceEuclideanEquiv F)
            (HGAS.ContDiff.conjugateField sourceEuclideanEquiv hF))
          (HGAS.boundedCutoffInnerRadialReward
            (HGAS.conjugateField sourceEuclideanEquiv F)
            (HGAS.ContDiff.conjugateField sourceEuclideanEquiv hF))
          T (sourceEuclideanEquiv x) := by
            simp [x]
      _ = ∫ t in (0 : ℝ)..T,
          HGAS.radialReward F
            (sourceAngularAmbientFlow F hF t x) :=
        orbitIntegral_sourceEuclideanEquiv F hF T x hx
      _ ≤ -c := hsource x hx
  · rintro ⟨T, c, hT, hc, heuclidean⟩
    refine ⟨T, c, hT, hc, ?_⟩
    intro x hx
    have hnorm : ‖sourceEuclideanEquiv x‖ = 1 :=
      (norm_sourceEuclideanEquiv_eq_one_iff x).2 hx
    have hblock := heuclidean (sourceEuclideanEquiv x) hnorm
    rw [orbitIntegral_sourceEuclideanEquiv F hF T x hx] at hblock
    exact hblock

/-- GAS of a `C²` homogeneous source-coordinate field is equivalent to one
common negative source angular block. -/
theorem
    globallyAsymptoticallyStable_iff_uniformNegativeSourceAngularBlock
    (F : (Fin n → ℝ) → (Fin n → ℝ))
    (j : ℕ)
    (hFhom : HGAS.ScalesAsDegree ℝ (j + 1) F)
    (hF : ContDiff ℝ 2 F)
    (hzero : F 0 = 0) :
    HGAS.GloballyAsymptoticallyStable F 0 ↔
      HasUniformNegativeSourceAngularBlock F
        (hF.of_le (by norm_num)) := by
  let F' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    HGAS.conjugateField sourceEuclideanEquiv F
  let hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  let hF' : ContDiff ℝ 2 F' :=
    HGAS.ContDiff.conjugateField sourceEuclideanEquiv hF
  have hFhom' : HGAS.ScalesAsDegree ℝ (j + 1) F' :=
    HGAS.scalesAsDegree_conjugateField sourceEuclideanEquiv hFhom
  have hzero' : F' 0 = 0 :=
    HGAS.conjugateField_zero sourceEuclideanEquiv hzero
  have heuclidean :
      HGAS.GloballyAsymptoticallyStable F' 0 ↔
        HGAS.HasUniformNegativeEuclideanAngularBlock F'
          (hF'.of_le (by norm_num)) :=
    HGAS.globallyAsymptoticallyStable_iff_uniformNegativeEuclideanAngularBlock
      F' j hFhom' hF' hzero'
  have hblocks :
      HasUniformNegativeSourceAngularBlock F hF1 ↔
        HGAS.HasUniformNegativeEuclideanAngularBlock F'
          (hF'.of_le (by norm_num)) := by
    simpa only [F', hF', hF1] using
      uniformNegativeSourceAngularBlock_iff_euclidean F hF1
  constructor
  · intro hgas
    exact hblocks.mpr
      (heuclidean.mp (hgas.conjugateField sourceEuclideanEquiv))
  · intro hblock
    have hgas' := heuclidean.mpr (hblocks.mp hblock)
    exact
      (HGAS.globallyAsymptoticallyStable_conjugateField_iff
        sourceEuclideanEquiv F).mp hgas'

end

end HGAS.Veronese
