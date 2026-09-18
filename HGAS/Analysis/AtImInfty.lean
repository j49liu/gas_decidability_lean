import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

/-!
# Elementary adapters for the `Im τ → +∞` filter

Mathlib defines the upper-half-plane cusp filter as the pullback of
`atTop` along the imaginary-part map.  These lemmas expose that definition
in the two forms most useful for direct estimates.
-/

namespace HGAS.Analysis

open UpperHalfPlane Filter Topology

/-- Eventual truth at the cusp means truth above some imaginary-height
threshold. -/
theorem eventually_atImInfty {p : ℍ → Prop} :
    (∀ᶠ z in atImInfty, p z) ↔
      ∃ A : ℝ, ∀ z : ℍ, A ≤ z.im → p z :=
  atImInfty_mem {z | p z}

/-- The imaginary part tends to `+∞` along `atImInfty`. -/
theorem tendsto_im_atImInfty :
    Tendsto (fun z : ℍ ↦ z.im)
      atImInfty atTop :=
  tendsto_iff_comap.mpr fun ⦃_⦄ h ↦ h

/-- A function with a finite cusp limit is bounded at the cusp. -/
theorem isBoundedAtImInfty_of_tendsto
    {E : Type*} [SeminormedAddCommGroup E]
    {f : ℍ → E} {c : E}
    (hf : Tendsto f atImInfty (𝓝 c)) :
    IsBoundedAtImInfty f := by
  have hzero :
      ZeroAtFilter atImInfty
        (fun z ↦ f z - c) := by
    simpa [ZeroAtFilter] using
      hf.sub
        (tendsto_const_nhds :
          Tendsto (fun _ : ℍ ↦ c)
            atImInfty (𝓝 c))
  have hbounded :=
    hzero.boundedAtFilter.add
      (const_boundedAtFilter atImInfty c)
  convert hbounded using 1
  ext z
  simp

end HGAS.Analysis
