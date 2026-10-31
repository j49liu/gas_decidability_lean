import Stability.Simulation.CompiledGraphTrajectory
import Mathlib.Data.List.OfFn

/-!
# Listing a finite formula family without changing its coordinates

An explicit equivalence fixes the order of a finite family. The resulting
list and position map feed the shared radical compiler, and selecting an
output recovers the original formula. The equivalence is fixed data: it
does not depend on coefficients, states, or trajectories.
-/

namespace Stability.Simulation.AbsFormula

variable {σ ι : Type*} {count : ℕ}

def familyList (index : ι ≃ Fin count) (formulas : ι → AbsFormula σ) :
    List (AbsFormula σ) := List.ofFn (fun j ↦ formulas (index.symm j))

def familyPosition (index : ι ≃ Fin count) (formulas : ι → AbsFormula σ) (i : ι) :
    Fin (familyList index formulas).length :=
  (index i).cast (List.length_ofFn).symm

theorem familyList_get (index : ι ≃ Fin count) (formulas : ι → AbsFormula σ) (i : ι) :
    (familyList index formulas).get (familyPosition index formulas i) = formulas i := by
  simp [familyList, familyPosition]

end Stability.Simulation.AbsFormula
