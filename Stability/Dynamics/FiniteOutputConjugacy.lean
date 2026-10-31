import Stability.Dynamics.FiniteOutputBound
import HGAS.Dynamics.LinearConjugacyGAS

/-!
# Finite output bounds under linear coordinate changes

Transporting a finite trajectory through a continuous linear equivalence
does not change its time interval or its scalar output integral. Hence a
uniform bound is preserved with the same constant. This includes the
finite coordinate reindexings used when compiling polynomial codes.
-/

namespace Stability

open Set

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem HasBoundedFiniteOutput.conjugateField (e : E ≃L[ℝ] H)
    {F : E → E} {g : E → ℝ} (h : HasBoundedFiniteOutput F g) :
    HasBoundedFiniteOutput (HGAS.conjugateField e F) (fun y ↦ g (e.symm y)) := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M, fun T hT y hy hd ↦ ?_⟩
  apply hM T hT (fun t ↦ e.symm (y t)) (e.symm.continuous.comp_continuousOn hy)
  intro t ht
  have hcomp := e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hd t ht)
  simpa only [HGAS.conjugateField, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using hcomp

theorem hasBoundedFiniteOutput_iff_conjugateField (e : E ≃L[ℝ] H)
    {F : E → E} {g : E → ℝ} :
    HasBoundedFiniteOutput F g ↔
      HasBoundedFiniteOutput (HGAS.conjugateField e F) (fun y ↦ g (e.symm y)) := by
  constructor
  · exact HasBoundedFiniteOutput.conjugateField e
  · intro h
    simpa only [HGAS.conjugateField_symm_conjugateField,
      ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.symm_apply_apply] using
      h.conjugateField e.symm

end Stability
