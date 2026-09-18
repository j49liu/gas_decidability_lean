import HGAS.Modular.UnaryDegenerateRecurrence
import Mathlib.Tactic

/-!
# Constant time rescaling for unary modular trajectories

The detector supplies a signed real phase frequency `ω`, hence the unary
clock `iω`.  The modular reconstruction is normalized with the clock
`iπ`.  This file records the elementary bridge explicitly: replacing
`z(t)` by `z(a t)` multiplies its complex clock by the real factor `a`.

Positive rescaling also preserves forward recurrence.  Keeping positivity
visible is important: a negative rescaling uses recurrence of the reversed
complete orbit, not recurrence of the original forward orbit.
-/

namespace HGAS

open Filter Topology

noncomputable section

/-- Forward recurrence at time zero is preserved by a positive linear
rescaling of time. -/
theorem ForwardRecurrentAt.rescale_zero
    {X : Type*} [TopologicalSpace X]
    {γ : ℝ → X}
    (hγ : ForwardRecurrentAt γ 0)
    {a : ℝ} (ha : 0 < a) :
    ForwardRecurrentAt (fun t ↦ γ (a * t)) 0 := by
  obtain ⟨τ, hτ, hreturn⟩ := hγ
  refine ⟨fun n ↦ τ n / a, ?_, ?_⟩
  · exact hτ.atTop_div_const ha
  · have hcancel : ∀ n, a * (τ n / a) = τ n := by
      intro n
      field_simp
    simpa only [hcancel, mul_zero] using hreturn

namespace Modular

/-- Constant real rescaling multiplies the complex unary clock by the
same real factor. -/
theorem IsScaledUnaryModularTrajectory.rescale
    {κ : ℂ}
    {z : ℝ → UnaryModularState ℂ}
    (hz : IsScaledUnaryModularTrajectory κ z)
    (a : ℝ) :
    IsScaledUnaryModularTrajectory
      ((a : ℂ) * κ)
      (fun t ↦ z (a * t)) := by
  have hinner (t : ℝ) :
      HasDerivAt (fun s : ℝ ↦ a * s) a t := by
    convert (hasDerivAt_id t).const_mul a using 1
    all_goals simp
  constructor
  · intro t
    have h := (hz.A (a * t)).scomp t (hinner t)
    simpa only [Function.comp_def, Complex.real_smul, mul_assoc] using h
  · intro t
    have h := (hz.C (a * t)).scomp t (hinner t)
    simpa only [Function.comp_def, Complex.real_smul, mul_assoc] using h
  · intro t
    have h := (hz.E (a * t)).scomp t (hinner t)
    simpa only [Function.comp_def, Complex.real_smul, mul_assoc] using h
  · intro t
    have h := (hz.Y (a * t)).scomp t (hinner t)
    simpa only [Function.comp_def, Complex.real_smul, mul_assoc] using h

/-- Coordinatewise unary recurrence at time zero is preserved by a
positive linear rescaling. -/
noncomputable def ForwardRecurrentUnaryModularAt.rescale_zero
    {z : ℝ → UnaryModularState ℂ}
    (hrec : ForwardRecurrentUnaryModularAt z 0)
    {a : ℝ} (ha : 0 < a) :
    ForwardRecurrentUnaryModularAt
      (fun t ↦ z (a * t)) 0 := by
  let τ : ℕ → ℝ := fun n ↦ hrec.times n / a
  have hτ : Tendsto τ atTop atTop := by
    exact hrec.times_tendsto.atTop_div_const ha
  have hcancel : ∀ n, a * τ n = hrec.times n := by
    intro n
    dsimp only [τ]
    field_simp
  refine
    { times := τ
      times_tendsto := hτ
      A_tendsto := ?_
      C_tendsto := ?_
      E_tendsto := ?_
      Y_tendsto := ?_ }
  · simpa only [hcancel, mul_zero] using hrec.A_tendsto
  · simpa only [hcancel, mul_zero] using hrec.C_tendsto
  · simpa only [hcancel, mul_zero] using hrec.E_tendsto
  · simpa only [hcancel, mul_zero] using hrec.Y_tendsto

end Modular

end

end HGAS
