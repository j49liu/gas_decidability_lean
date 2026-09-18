import HGAS.Dynamics.Stability
import HGAS.Propagation.DegreePadding
import Mathlib.Analysis.ODE.Transform
import Mathlib.Tactic

/-!
# Scaling trajectories of homogeneous vector fields

If `F` is homogeneous of degree `k+1` and `γ` solves `x' = F(x)`, then

```
γ_λ(t) = λ γ(λ^k t)
```

is the trajectory starting at `λ γ(0)`.  This is equation (2.1) in the
paper.  The theorem below is stated for `λ ≥ 0`, exactly what is needed for
radial scaling on a forward time ray.  It works even at `λ=0`: positive
homogeneity forces the vector field to vanish there.
-/

namespace HGAS

open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The rescaled curve associated with degree `k+1` and scale `c`. -/
def scaledForwardCurve (k : ℕ) (c : ℝ) (γ : ℝ → E) : ℝ → E :=
  fun t ↦ c • γ (t * c ^ k)

/-- Homogeneous trajectory-scaling identity. -/
theorem IsForwardTrajectory.scale_of_homogeneous
    (F : E → E) (k : ℕ)
    (hF : ∀ (c : ℝ) (x : E), F (c • x) = c ^ (k + 1) • F x)
    {γ : ℝ → E} {x₀ : E}
    (hγ : IsForwardTrajectory F γ x₀)
    (c : ℝ) (hc : 0 ≤ c) :
    IsForwardTrajectory F (scaledForwardCurve k c γ) (c • x₀) := by
  constructor
  · simp [scaledForwardCurve, hγ.1]
  · let a : ℝ := c ^ k
    have ha : 0 ≤ a := pow_nonneg hc k
    have htime :
        IsIntegralCurveOn (γ ∘ (· * a))
          (a • (fun _ : ℝ ↦ F) ∘ (· * a))
          {t | t * a ∈ Ici (0 : ℝ)} :=
      hγ.2.comp_mul a
    have htimeIci :
        IsIntegralCurveOn (γ ∘ (· * a))
          (a • (fun _ : ℝ ↦ F) ∘ (· * a)) (Ici 0) :=
      htime.mono (fun t ht ↦ mul_nonneg ht ha)
    intro t ht
    have hderiv :=
      HasDerivWithinAt.const_smul c (htimeIci t ht)
    change HasDerivWithinAt
      (fun s ↦ c • γ (s * c ^ k))
      (c • (c ^ k • F (γ (t * c ^ k)))) (Ici 0) t at hderiv
    convert hderiv using 1
    change F (c • γ (t * c ^ k)) =
      c • c ^ k • F (γ (t * c ^ k))
    rw [hF]
    simp only [smul_smul]
    congr 1
    rw [pow_succ]
    ring

/-- Forward completeness is closed under taking any nonnegative radial
rescaling of a supplied trajectory. -/
theorem ForwardComplete.exists_scaled_trajectory
    (F : E → E) (k : ℕ)
    (hF : ∀ (c : ℝ) (x : E), F (c • x) = c ^ (k + 1) • F x)
    (hcomplete : ForwardComplete F)
    (x₀ : E) (c : ℝ) (hc : 0 ≤ c) :
    ∃ γ : ℝ → E, IsForwardTrajectory F γ (c • x₀) := by
  obtain ⟨γ, hγ⟩ := hcomplete x₀
  exact ⟨scaledForwardCurve k c γ,
    hγ.scale_of_homogeneous F k hF c hc⟩

end

end HGAS
