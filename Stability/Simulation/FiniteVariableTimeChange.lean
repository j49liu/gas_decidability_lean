import Stability.Simulation.FiniteTimeChange
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Removing a positive time-dependent rate on a finite interval

Adjoining the literal time coordinate converts the prescribed rate to a
state-dependent speed. The proved finite reparametrization theorem then
removes that rate and preserves the corresponding weighted integral.
-/

namespace Stability.TimeChange

open Set MeasureTheory

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_segment_of_positive_time_rate {F : E → E} {g : E → ℝ} {q : ℝ → ℝ}
    {T : ℝ} (hT : 0 ≤ T) {x : ℝ → E}
    (hx : ContinuousOn x (Icc 0 T))
    (hq : ContinuousOn q (Icc 0 T))
    (hg : ContinuousOn (fun t ↦ g (x t)) (Icc 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt x (q t • F (x t)) t)
    (hpositive : ∀ t ∈ Icc 0 T, 0 < q t) :
    ∃ S ≥ 0, ∃ z : ℝ → E,
      ContinuousOn z (Icc 0 S) ∧ z 0 = x 0 ∧ z S = x T ∧
      MapsTo z (Icc 0 S) (x '' Icc 0 T) ∧
      (∀ t ∈ Ioo 0 S, HasDerivAt z (F (z t)) t) ∧
      (∫ t in 0..S, g (z t)) = ∫ t in 0..T, q t * g (x t) := by
  let lifted : ℝ → ℝ × E := fun t ↦ (t, x t)
  let G : (ℝ × E) → ℝ × E := fun p ↦ ((q p.1)⁻¹, F p.2)
  have hpair : ∀ t ∈ Ioo 0 T, HasDerivAt lifted (q t • G (lifted t)) t := by
    intro t ht
    convert (hasDerivAt_id t).prodMk (hderiv t ht) using 1
    ext <;> simp [G, lifted, mul_inv_cancel₀ (ne_of_gt (hpositive t (Ioo_subset_Icc_self ht)))]
  obtain ⟨S, hS, y, hy, hy0, hyS, himage, hdy, hint⟩ :=
    exists_decelerated_segment (F := G) (Q := fun p ↦ q p.1) (g := fun p ↦ g p.2)
      hT (continuousOn_id.prodMk hx) hq hg hpair hpositive
  refine ⟨S, hS, fun t ↦ (y t).2, hy.snd,
    congrArg Prod.snd hy0, congrArg Prod.snd hyS, ?_, ?_, hint⟩
  · intro t ht
    obtain ⟨r, hr, heq⟩ := himage ht
    exact ⟨r, hr, congrArg Prod.snd heq⟩
  · intro t ht
    exact (hdy t ht).snd

end

end Stability.TimeChange
