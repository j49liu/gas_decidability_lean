import Stability.Simulation.ClockedMonitorClearing

/-!
# Fixed coordinates for a register monitor

The root count is evaluated at a fixed reference input. A single finite
enumeration therefore serves every loaded register tuple and precision.
This enumeration is a fixed parameter, not a search performed by the
input-to-polynomial compiler.
-/

namespace Stability.ClockedMonitorCode

noncomputable section

open Simulation

variable {k s : ℕ}

def dimension (program : RegisterMachine.Program k s) (entry : Fin s) : ℕ :=
  Fintype.card (MonitorCoordinate k) + ClockedMonitor.fixedRootCount program entry

def fixedEquiv (program : RegisterMachine.Program k s) (entry : Fin s) :
    (MonitorCoordinate k ⊕ Fin (ClockedMonitor.fixedRootCount program entry)) ≃
      Fin (dimension program entry) :=
  (Fintype.equivFin _).trans (finCongr (by simp [dimension]))

theorem dimension_pos (program : RegisterMachine.Program k s) (entry : Fin s) :
    0 < dimension program entry := by
  have hc : 0 < Fintype.card (MonitorCoordinate k) :=
    Fintype.card_pos_iff.mpr ⟨MonitorCoordinate.clock⟩
  unfold dimension
  omega

theorem two_le_homogeneousDimension (program : RegisterMachine.Program k s) (entry : Fin s) :
    2 ≤ dimension program entry + 1 := by
  have := dimension_pos program entry
  omega

end

end Stability.ClockedMonitorCode
