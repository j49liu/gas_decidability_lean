import HGAS.Dynamics.StateTimeChange

/-!
# Uniqueness for finite solutions with interior derivatives

A finite solution is continuous on its closed time interval, but its
differential equation need only be stated in the interior. Continuity
of the field supplies the missing one-sided endpoint derivatives. The
usual compact-interval uniqueness theorem then applies without asking
the supplied curve to solve the equation outside its interval.
-/

namespace Stability

open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivWithinAt_leftEndpoint {γ v : ℝ → E} {a b : ℝ}
    (hab : a < b) (hγ : ContinuousOn γ (Icc a b))
    (hv : ContinuousOn v (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt γ (v t) t) :
    HasDerivWithinAt γ (v a) (Ici a) a := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (s := Ioo a b) (fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt)
    ((hγ a ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self) (Ioo_mem_nhdsGT hab)
  have hvlim := (hv a ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self
  rw [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsGT hab] at hvlim
  apply hvlim.congr'
  filter_upwards [Ioo_mem_nhdsGT hab] with t ht
  exact (hd t ht).deriv.symm

theorem hasDerivWithinAt_rightEndpoint {γ v : ℝ → E} {a b : ℝ}
    (hab : a < b) (hγ : ContinuousOn γ (Icc a b))
    (hv : ContinuousOn v (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt γ (v t) t) :
    HasDerivWithinAt γ (v b) (Iic b) b := by
  apply hasDerivWithinAt_Iic_of_tendsto_deriv
    (s := Ioo a b) (fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt)
    ((hγ b ⟨hab.le, le_rfl⟩).mono Ioo_subset_Icc_self) (Ioo_mem_nhdsLT hab)
  have hvlim := (hv b ⟨hab.le, le_rfl⟩).mono Ioo_subset_Icc_self
  rw [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT hab] at hvlim
  apply hvlim.congr'
  filter_upwards [Ioo_mem_nhdsLT hab] with t ht
  exact (hd t ht).deriv.symm

theorem finiteSolution_unique [ProperSpace E] {F : E → E}
    (hF : ContDiff ℝ 1 F) {γ η : ℝ → E} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b))
    (hγd : ∀ t ∈ Ioo a b, HasDerivAt γ (F (γ t)) t)
    (hη : ContinuousOn η (Icc a b))
    (hηd : ∀ t ∈ Ioo a b, HasDerivAt η (F (η t)) t)
    (heq : γ a = η a) : EqOn γ η (Icc a b) := by
  apply HGAS.ode_solution_unique_Icc_right_of_contDiff hF hγ ?_ hη ?_ heq
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | hat
    · exact hasDerivWithinAt_leftEndpoint ht.2 hγ
        (hF.continuous.comp_continuousOn hγ) hγd
    · exact (hγd t ⟨hat, ht.2⟩).hasDerivWithinAt
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | hat
    · exact hasDerivWithinAt_leftEndpoint ht.2 hη
        (hF.continuous.comp_continuousOn hη) hηd
    · exact (hηd t ⟨hat, ht.2⟩).hasDerivWithinAt

end Stability
