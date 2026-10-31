import Stability.Dynamics.FiniteOutputBound
import Stability.Simulation.PenalizedMonitorIntegral
import Stability.Simulation.NonhaltingLiftedOutput

/-!
# Halting is equivalent to bounded output for the actual rational monitor

The halting direction bounds every finite trajectory, even off graph.
The nonhalting direction constructs a global graph trajectory with
unbounded finite output integrals. Thus neither direction relies on an
abstract simulation assumption. Polynomial time change, homogeneous
lifting, and code-level effectivity are subsequent steps.
-/

namespace Stability.Simulation.ClockedMonitor

noncomputable section

open Set

variable {k s : ℕ}

theorem halts_iff_bounded_penalizedOutput (program : RegisterMachine.Program k s)
    (entry : Fin s) (initial : Fin k → ℕ) {ε : ℚ}
    (hε : 0 < ε) (hεSmall : ε ≤ 1 / 1024) :
    RegisterMachine.Halts program ⟨some entry, initial⟩ ↔
      Stability.HasBoundedFiniteOutput (liftedField program entry initial ε)
        (fun y ↦ PolynomialFraction.value y (penalizedOutput program entry initial ε)) := by
  constructor
  · rintro ⟨T, hT⟩
    refine ⟨penalizedIntegralBound T ε, ?_⟩
    intro b hb y hy hderiv
    exact integral_penalizedOutput_le_of_halts program entry initial hε
      (show ε ≤ 1 by linarith) hb hy hderiv T hT
  · intro hbounded
    by_contra hnonhalt
    obtain ⟨M, hM⟩ := hbounded
    obtain ⟨y, hy, hlarge⟩ := exists_lifted_nonhalting_output_witness
      program entry initial hnonhalt hε hεSmall
    obtain ⟨b, hb, hvalue⟩ := hlarge M
    have hcontinuous : ContinuousOn y (Icc 0 b) := by
      intro t ht
      exact (hy.2 t ht.1).continuousWithinAt.mono (fun _ hr ↦ hr.1)
    have hderiv : ∀ t ∈ Ioo 0 b, HasDerivAt y
        (liftedField program entry initial ε (y t)) t := by
      intro t ht
      exact (hy.2 t ht.1.le).hasDerivAt (Ici_mem_nhds ht.1)
    exact (not_lt_of_ge (hM b hb y hcontinuous hderiv)) hvalue

end

end Stability.Simulation.ClockedMonitor
