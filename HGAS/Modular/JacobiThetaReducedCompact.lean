import HGAS.Modular.JacobiThetaVectorNonvanishing
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Tactic

/-!
# A compact reduced domain for the Jacobi theta vector

For a fixed lattice height `γ > 0`, level-two reduction places the
elliptic coordinate in

```
               |Re z| ≤ 1,        |Im z| ≤ γ,
```

and modular translation reduction places the real part of `τ` in
`[-1,1]`, while `Im τ = γ`.  This file constructs that domain explicitly
as the continuous image of a rectangular box in `ℝ³`, proves it compact
and nonempty, and packages the resulting uniform lower-bound theorem.

The only analytic hypothesis of the final theorem is pointwise
nonvanishing of the four-coordinate theta vector.  It is intentionally
kept separate so that a global no-common-zero theorem can discharge it
without changing the compactness argument.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I

noncomputable section

/-- The real rectangular parameter box for a reduced elliptic/modular
pair.  Its coordinates are `Re z`, `Im z`, and `Re τ`. -/
def reducedThetaParameterBox (γ : ℝ) :
    Set (ℝ × (ℝ × ℝ)) :=
  Set.Icc (-1) 1 ×ˢ
    (Set.Icc (-γ) γ ×ˢ Set.Icc (-1) 1)

/-- Convert a point of the parameter box into `(z,τ) ∈ ℂ × ℍ`. -/
def reducedThetaParam
    (γ : ℝ) (hγ : 0 < γ)
    (p : ℝ × (ℝ × ℝ)) : ℂ × ℍ :=
  ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I,
    ⟨(p.2.2 : ℂ) + (γ : ℂ) * Complex.I, by
      simpa using hγ⟩)

/-- The compact reduced theta domain at fixed height `γ`. -/
def reducedThetaDomain
    (γ : ℝ) (hγ : 0 < γ) :
    Set (ℂ × ℍ) :=
  reducedThetaParam γ hγ ''
    reducedThetaParameterBox γ

theorem continuous_reducedThetaParam
    (γ : ℝ) (hγ : 0 < γ) :
    Continuous (reducedThetaParam γ hγ) := by
  unfold reducedThetaParam
  fun_prop

theorem isCompact_reducedThetaParameterBox
    (γ : ℝ) :
    IsCompact (reducedThetaParameterBox γ) := by
  exact
    isCompact_Icc.prod
      (isCompact_Icc.prod isCompact_Icc)

theorem isCompact_reducedThetaDomain
    (γ : ℝ) (hγ : 0 < γ) :
    IsCompact (reducedThetaDomain γ hγ) := by
  exact
    (isCompact_reducedThetaParameterBox γ).image
      (continuous_reducedThetaParam γ hγ)

theorem reducedThetaDomain_nonempty
    (γ : ℝ) (hγ : 0 < γ) :
    (reducedThetaDomain γ hγ).Nonempty := by
  refine ⟨reducedThetaParam γ hγ (0, (0, 0)), ?_⟩
  refine ⟨(0, (0, 0)), ?_, rfl⟩
  exact
    ⟨by norm_num,
      ⟨⟨by linarith, by linarith⟩, by norm_num⟩⟩

/-- Coordinate characterization used to put a concretely reduced pair in
the compact domain. -/
theorem mem_reducedThetaDomain
    {γ : ℝ} (hγ : 0 < γ)
    (z : ℂ) (τ : ℍ)
    (hzre : |z.re| ≤ 1)
    (hzim : |z.im| ≤ γ)
    (hτre : |τ.re| ≤ 1)
    (hτim : τ.im = γ) :
    (z, τ) ∈ reducedThetaDomain γ hγ := by
  refine
    ⟨(z.re, (z.im, τ.re)), ?_, ?_⟩
  · exact
      ⟨abs_le.mp hzre,
        ⟨abs_le.mp hzim, abs_le.mp hτre⟩⟩
  · apply Prod.ext
    · apply Complex.ext <;>
        simp [reducedThetaParam]
    · apply UpperHalfPlane.ext
      apply Complex.ext
      · simp [reducedThetaParam]
      · simpa [reducedThetaParam] using hτim.symm

/-- Compactness turns pointwise no-common-zero into one positive lower
bound valid on the whole reduced domain. -/
theorem exists_uniform_pos_le_norm_jacobiThetaVector_reduced
    (γ : ℝ) (hγ : 0 < γ)
    (hzero :
      ∀ p ∈ reducedThetaDomain γ hγ,
        jacobiThetaVector p.1 (p.2 : ℂ) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧
      ∀ z : ℂ, ∀ τ : ℍ,
        |z.re| ≤ 1 →
        |z.im| ≤ γ →
        |τ.re| ≤ 1 →
        τ.im = γ →
        c ≤ ‖jacobiThetaVector z (τ : ℂ)‖ := by
  obtain ⟨c, hc, hcLower⟩ :=
    exists_uniform_pos_le_norm_jacobiThetaVector
      (isCompact_reducedThetaDomain γ hγ)
      (reducedThetaDomain_nonempty γ hγ)
      hzero
  refine ⟨c, hc, ?_⟩
  intro z τ hzre hzim hτre hτim
  exact hcLower (z, τ)
    (mem_reducedThetaDomain
      hγ z τ hzre hzim hτre hτim)

/-- Unconditional uniform lower bound on the reduced domain, obtained from
the global no-common-zero theorem. -/
theorem exists_uniform_pos_le_norm_jacobiThetaVector_reduced_global
    (γ : ℝ) (hγ : 0 < γ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ z : ℂ, ∀ τ : ℍ,
        |z.re| ≤ 1 →
        |z.im| ≤ γ →
        |τ.re| ≤ 1 →
        τ.im = γ →
        c ≤ ‖jacobiThetaVector z (τ : ℂ)‖ :=
  exists_uniform_pos_le_norm_jacobiThetaVector_reduced
    γ hγ
    (fun p _ ↦ jacobiThetaVector_ne_zero p.1 p.2)

end

end HGAS.Modular
