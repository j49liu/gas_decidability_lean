import HGAS.Stability.AngularLyapunov
import HGAS.Stability.LinearConjugacyLyapunov
import HGAS.Veronese.SourceEuclideanConjugacy
import HGAS.Veronese.WeightedEuclideanConjugacy
import Mathlib.Tactic

/-!
# The angular Lyapunov criterion in source and weighted Veronese coordinates

Korda's Lemma 2.2 is proved in `HGAS.Stability.AngularLyapunov` for
Euclidean spaces.  The source space `Fin n → ℝ` carries the sup norm, and the
Veronese space is used with the weighted form `Q`.  The two diagonal
normalizations `sourceEuclideanEquiv` and `weightedEuclideanEquiv` identify
their angular cocycles with Euclidean ones; combined with the invariance of
Lyapunov stability under linear coordinate changes this gives the criterion
in the coordinates used by the cubic lift.
-/

namespace HGAS.Veronese

open Function Set

noncomputable section

variable {n k : ℕ}

/-! ## Source coordinates -/

/-- The source radial cocycle is bounded above on forward angular time,
uniformly on the source unit sphere. -/
def HasBoundedSourceAngularCocycle
    (F : (Fin n → ℝ) → (Fin n → ℝ)) (hF : ContDiff ℝ 1 F) : Prop :=
  ∃ M : ℝ, ∀ x : Fin n → ℝ, sourceRadiusSq x = 1 → ∀ τ : ℝ, 0 ≤ τ →
    (∫ t in (0 : ℝ)..τ, HGAS.radialReward F (sourceAngularAmbientFlow F hF t x)) ≤ M

theorem boundedSourceAngularCocycle_iff_euclidean
    (F : (Fin n → ℝ) → (Fin n → ℝ)) (hF : ContDiff ℝ 1 F) :
    HasBoundedSourceAngularCocycle F hF ↔
      HGAS.HasBoundedEuclideanAngularCocycle
        (HGAS.conjugateField sourceEuclideanEquiv F)
        (HGAS.ContDiff.conjugateField sourceEuclideanEquiv hF) := by
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M, fun u hu τ hτ ↦ ?_⟩
    let x : Fin n → ℝ := sourceEuclideanEquiv.symm u
    have hx : sourceRadiusSq x = 1 :=
      (sourceRadiusSq_sourceEuclideanEquiv_symm_eq_one_iff u).2 hu
    have hux : u = sourceEuclideanEquiv x := by simp [x]
    unfold HGAS.euclideanAngularLogRadius
    rw [hux, orbitIntegral_sourceEuclideanEquiv F hF τ x hx]
    exact hM x hx τ hτ
  · rintro ⟨M, hM⟩
    refine ⟨M, fun x hx τ hτ ↦ ?_⟩
    have hnorm : ‖sourceEuclideanEquiv x‖ = 1 :=
      (norm_sourceEuclideanEquiv_eq_one_iff x).2 hx
    have h := hM (sourceEuclideanEquiv x) hnorm τ hτ
    unfold HGAS.euclideanAngularLogRadius at h
    rwa [orbitIntegral_sourceEuclideanEquiv F hF τ x hx] at h

/-- **Angular Lyapunov criterion in source coordinates.** -/
theorem lyapunovStableWithExistence_iff_boundedSourceAngularCocycle
    (F : (Fin n → ℝ) → (Fin n → ℝ)) (j : ℕ)
    (hFhom : HGAS.ScalesAsDegree ℝ (j + 1) F)
    (hF : ContDiff ℝ 1 F) (hzero : F 0 = 0) :
    HGAS.LyapunovStableWithExistence F 0 ↔
      HasBoundedSourceAngularCocycle F hF := by
  rw [boundedSourceAngularCocycle_iff_euclidean,
    ← HGAS.lyapunovStableWithExistence_iff_boundedEuclideanAngularCocycle
      (HGAS.conjugateField sourceEuclideanEquiv F)
      (HGAS.ContDiff.conjugateField sourceEuclideanEquiv hF) j
      (HGAS.scalesAsDegree_conjugateField sourceEuclideanEquiv hFhom)
      (HGAS.conjugateField_zero sourceEuclideanEquiv hzero),
    HGAS.lyapunovStableWithExistence_conjugateField_iff]

/-! ## Weighted Veronese coordinates -/

/-- The weighted radial cocycle is bounded above on forward angular time,
uniformly on the weighted unit sphere `Q = 1`. -/
def HasBoundedWeightedAngularCocycle
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k) (hG : ContDiff ℝ 1 G) :
    Prop :=
  ∃ M : ℝ, ∀ y : RealVeroneseSpace n k, Q y = 1 → ∀ τ : ℝ, 0 ≤ τ →
    (∫ t in (0 : ℝ)..τ, weightedRadialReward G (weightedAngularFlow G hG t y)) ≤ M

theorem boundedWeightedAngularCocycle_iff_euclidean
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k) (hG : ContDiff ℝ 1 G) :
    HasBoundedWeightedAngularCocycle G hG ↔
      HGAS.HasBoundedEuclideanAngularCocycle
        (HGAS.conjugateField weightedEuclideanEquiv G)
        (HGAS.ContDiff.conjugateField weightedEuclideanEquiv hG) := by
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M, fun u hu τ hτ ↦ ?_⟩
    let y : RealVeroneseSpace n k := weightedEuclideanEquiv.symm u
    have hy : Q y = 1 := (Q_weightedEuclideanEquiv_symm_eq_one_iff u).2 hu
    have huy : u = weightedEuclideanEquiv y := by simp [y]
    unfold HGAS.euclideanAngularLogRadius
    rw [huy, orbitIntegral_weightedEuclideanEquiv G hG τ y hy]
    exact hM y hy τ hτ
  · rintro ⟨M, hM⟩
    refine ⟨M, fun y hy τ hτ ↦ ?_⟩
    have hnorm : ‖weightedEuclideanEquiv y‖ = 1 :=
      (norm_weightedEuclideanEquiv_eq_one_iff y).2 hy
    have h := hM (weightedEuclideanEquiv y) hnorm τ hτ
    unfold HGAS.euclideanAngularLogRadius at h
    rwa [orbitIntegral_weightedEuclideanEquiv G hG τ y hy] at h

/-- **Angular Lyapunov criterion in weighted Veronese coordinates.** -/
theorem lyapunovStableWithExistence_iff_boundedWeightedAngularCocycle
    (G : RealVeroneseSpace n k → RealVeroneseSpace n k) (j : ℕ)
    (hGhom : HGAS.ScalesAsDegree ℝ (j + 1) G)
    (hG : ContDiff ℝ 1 G) (hzero : G 0 = 0) :
    HGAS.LyapunovStableWithExistence G 0 ↔
      HasBoundedWeightedAngularCocycle G hG := by
  rw [boundedWeightedAngularCocycle_iff_euclidean,
    ← HGAS.lyapunovStableWithExistence_iff_boundedEuclideanAngularCocycle
      (HGAS.conjugateField weightedEuclideanEquiv G)
      (HGAS.ContDiff.conjugateField weightedEuclideanEquiv hG) j
      (HGAS.scalesAsDegree_conjugateField weightedEuclideanEquiv hGhom)
      (HGAS.conjugateField_zero weightedEuclideanEquiv hzero),
    HGAS.lyapunovStableWithExistence_conjugateField_iff]

end

end HGAS.Veronese
