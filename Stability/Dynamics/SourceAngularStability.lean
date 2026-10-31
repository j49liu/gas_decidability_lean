import HGAS.Stability.AngularLyapunov
import HGAS.Stability.LinearConjugacyLyapunov
import HGAS.Veronese.SourceEuclideanConjugacy

/-!
# The angular stability criterion in polynomial coordinate space

Polynomial codes use the finite product space with its sup norm. The
coordinate-preserving Euclidean equivalence transports the established
angular criterion back to these coordinates. The radius constraint is
the algebraic sum of squares, so no sup-norm sphere is substituted for
the Euclidean sphere.
-/

namespace Stability

noncomputable section

open HGAS HGAS.Veronese Set MeasureTheory

variable {n : ℕ}

def HasBoundedSourceAngularCocycle (F : (Fin n → ℝ) → Fin n → ℝ)
    (hF : ContDiff ℝ 1 F) : Prop :=
  ∃ M : ℝ, ∀ x : Fin n → ℝ, sourceRadiusSq x = 1 → ∀ T : ℝ, 0 ≤ T →
    (∫ t in 0..T, radialReward F (sourceAngularAmbientFlow F hF t x)) ≤ M

theorem boundedSourceAngularCocycle_iff_euclidean
    (F : (Fin n → ℝ) → Fin n → ℝ) (hF : ContDiff ℝ 1 F) :
    HasBoundedSourceAngularCocycle F hF ↔
      HasBoundedEuclideanAngularCocycle (conjugateField sourceEuclideanEquiv F)
        (HGAS.ContDiff.conjugateField sourceEuclideanEquiv hF) := by
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro u hu T hT
    have hx : sourceRadiusSq (sourceEuclideanEquiv.symm u) = 1 :=
      (sourceRadiusSq_sourceEuclideanEquiv_symm_eq_one_iff u).mpr hu
    have heq := orbitIntegral_sourceEuclideanEquiv F hF T (sourceEuclideanEquiv.symm u) hx
    simp only [ContinuousLinearEquiv.apply_symm_apply] at heq
    change euclideanAngularLogRadius _ _ T u = _ at heq
    rw [heq]
    exact hM _ hx T hT
  · rintro ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro x hx T hT
    have heq := orbitIntegral_sourceEuclideanEquiv F hF T x hx
    change euclideanAngularLogRadius _ _ T (sourceEuclideanEquiv x) = _ at heq
    rw [← heq]
    exact hM _ ((norm_sourceEuclideanEquiv_eq_one_iff x).mpr hx) T hT

theorem lyapunovStable_iff_boundedSourceAngularCocycle
    (F : (Fin n → ℝ) → Fin n → ℝ) (hF : ContDiff ℝ 1 F) (k : ℕ)
    (hhom : ScalesAsDegree ℝ (k + 1) F) (hzero : F 0 = 0) :
    LyapunovStableWithExistence F 0 ↔ HasBoundedSourceAngularCocycle F hF := by
  rw [← lyapunovStableWithExistence_conjugateField_iff sourceEuclideanEquiv F,
    lyapunovStableWithExistence_iff_boundedEuclideanAngularCocycle
      (conjugateField sourceEuclideanEquiv F) (HGAS.ContDiff.conjugateField sourceEuclideanEquiv hF)
      k (scalesAsDegree_conjugateField sourceEuclideanEquiv hhom)
      (conjugateField_zero sourceEuclideanEquiv hzero)]
  exact (boundedSourceAngularCocycle_iff_euclidean F hF).symm

end

end Stability
