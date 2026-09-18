import HGAS.Dynamics.Recurrence

/-!
# Forward recurrence under eventual equality

Forward recurrence only samples times tending to `+∞`.  Consequently it
is insensitive to changing a trajectory on an initial segment, provided
the value at the distinguished recurrence time is unchanged.  This
small transport lemma is useful for physical curves whose negative-time
extension is arbitrary.
-/

namespace HGAS

open Filter Topology

/-- Transport forward recurrence across eventual equality at `+∞`, with
an explicit equality at the distinguished base time. -/
theorem ForwardRecurrentAt.congr_of_eventuallyEq_atTop
    {X : Type*} [TopologicalSpace X]
    {γ η : ℝ → X} {t₀ : ℝ}
    (hγ : ForwardRecurrentAt γ t₀)
    (hbase : γ t₀ = η t₀)
    (heq : γ =ᶠ[atTop] η) :
    ForwardRecurrentAt η t₀ := by
  obtain ⟨τ, hτ, hreturn⟩ := hγ
  refine ⟨τ, hτ, ?_⟩
  have heqAlong :
      (fun n => γ (τ n)) =ᶠ[atTop]
        (fun n => η (τ n)) := by
    simpa only [Function.comp_apply] using heq.comp_tendsto hτ
  have hreturnEta :
      Tendsto (fun n => η (τ n)) atTop (𝓝 (γ t₀)) :=
    hreturn.congr' heqAlong
  simpa only [hbase] using hreturnEta

/-- In particular, equality on the nonnegative time ray transports
recurrence based at a nonnegative time. -/
theorem ForwardRecurrentAt.congr_of_eqOn_Ici
    {X : Type*} [TopologicalSpace X]
    {γ η : ℝ → X} {t₀ : ℝ}
    (hγ : ForwardRecurrentAt γ t₀)
    (ht₀ : 0 ≤ t₀)
    (heq : ∀ t, 0 ≤ t → γ t = η t) :
    ForwardRecurrentAt η t₀ := by
  apply hγ.congr_of_eventuallyEq_atTop (heq t₀ ht₀)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact heq t ht

end HGAS
