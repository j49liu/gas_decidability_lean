import HGAS.Analysis.LinearODEZero
import HGAS.Dynamics.Recurrence
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Recurrence obstruction for a complex Riccati equation

The degenerate divisors of the unary modular system leave a scalar
coordinate satisfying

```
                              q' = a q².
```

For the physical modular clock, `a` is a nonzero purely imaginary
constant.  The argument below does not use that special phase: for every
nonzero complex `a`, a globally defined forward-recurrent solution must
vanish at the recurrent time.

The proof is elementary and exposes the geometry.  If `q(t₀) ≠ 0`, scalar
ODE uniqueness says that `q` never vanishes.  Hence `w=1/q` is defined
globally and satisfies `w'=-a`, so

```
                         w(t)=w(t₀)-a(t-t₀).
```

A late return of `q` to `q(t₀)` would therefore force the corresponding
times to converge back to `t₀`, contradicting their escape to `+∞`.
-/

namespace HGAS.Modular

open Filter Topology
open HGAS

noncomputable section

/-- A globally differentiable complex Riccati trajectory with nonzero
coefficient cannot be forward recurrent at a nonzero state. -/
theorem complexRiccati_eq_zero_of_forwardRecurrent
    (a : ℂ) (ha : a ≠ 0)
    (q : ℝ → ℂ)
    (hq : ∀ t : ℝ, HasDerivAt q (a * q t ^ 2) t)
    {t₀ : ℝ}
    (hrec : ForwardRecurrentAt q t₀) :
    q t₀ = 0 := by
  by_contra hq₀
  have hq_cont : Continuous q :=
    continuous_iff_continuousAt.mpr fun t ↦ (hq t).continuousAt
  have hq_ne : ∀ t : ℝ, q t ≠ 0 := by
    intro t ht
    have hlinear :
        ∀ s : ℝ,
          HasDerivAt q ((a * q s) * q s) s := by
      intro s
      convert hq s using 1
      ring
    have hident :=
      complex_eq_zero_of_hasDerivAt_eq_mul
        (fun s ↦ a * q s) q
        (continuous_const.mul hq_cont)
        hlinear ht
    exact hq₀ (congrFun hident t₀)
  let w : ℝ → ℂ := fun t ↦ (q t)⁻¹
  have hw :
      ∀ t : ℝ, HasDerivAt w (-a) t := by
    intro t
    have hinv :=
      (hasDerivAt_inv (hq_ne t)).scomp t (hq t)
    convert hinv using 1
    change
      -a = (a * q t ^ 2) * (-(q t ^ 2)⁻¹)
    field_simp [hq_ne t]
  let affine : ℝ → ℂ :=
    fun t ↦ w t₀ - a * ((t - t₀ : ℝ) : ℂ)
  have haffine :
      ∀ t : ℝ, HasDerivAt affine (-a) t := by
    intro t
    have hcast :
        HasDerivAt (fun s : ℝ ↦ ((s - t₀ : ℝ) : ℂ)) 1 t :=
      ((hasDerivAt_id t).sub_const t₀).ofReal_comp
    have hproduct := hcast.const_mul a
    have hsub :=
      (hasDerivAt_const t (w t₀)).sub hproduct
    convert hsub using 1
    all_goals simp
  have hw_diff : Differentiable ℝ w :=
    fun t ↦ (hw t).differentiableAt
  have haffine_diff : Differentiable ℝ affine :=
    fun t ↦ (haffine t).differentiableAt
  have hw_eq_affine : w = affine := by
    exact eq_of_fderiv_eq hw_diff haffine_diff
      (fun t ↦ by
        rw [(hw t).hasFDerivAt.fderiv,
          (haffine t).hasFDerivAt.fderiv])
      t₀ (by simp [affine])
  obtain ⟨τ, hτtop, hreturn⟩ := hrec
  have hreturn_inv :
      Tendsto (fun n ↦ w (τ n)) atTop (𝓝 (w t₀)) := by
    simpa only [w] using hreturn.inv₀ hq₀
  have hdiff :
      Tendsto (fun n ↦ w t₀ - w (τ n))
        atTop (𝓝 0) := by
    have h :=
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ w t₀) atTop (𝓝 (w t₀))).sub
          hreturn_inv
    simpa using h
  have hmul :
      Tendsto
        (fun n ↦ a * (((τ n - t₀ : ℝ) : ℂ)))
        atTop (𝓝 0) := by
    apply hdiff.congr'
    filter_upwards with n
    rw [congrFun hw_eq_affine (τ n)]
    simp only [affine]
    ring
  have hcast :
      Tendsto
        (fun n ↦ (((τ n - t₀ : ℝ) : ℂ)))
        atTop (𝓝 0) := by
    have hscaled := hmul.const_mul a⁻¹
    simpa [ha] using hscaled
  have hsub :
      Tendsto (fun n ↦ τ n - t₀)
        atTop (𝓝 0) := by
    have hre :=
      Complex.continuous_re.continuousAt.tendsto.comp hcast
    simpa using hre
  have hτfinite :
      Tendsto τ atTop (𝓝 t₀) := by
    have hadd := hsub.add_const t₀
    simpa using hadd
  exact (not_tendsto_atTop_of_tendsto_nhds hτfinite) hτtop

end

end HGAS.Modular
