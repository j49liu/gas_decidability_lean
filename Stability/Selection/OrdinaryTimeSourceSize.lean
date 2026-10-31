import Stability.Selection.OrdinaryTimeSourceGraph
import HGAS.Analysis.FiniteCoordinateNormSq

/-!
# RHS-independent size of the intended source graph

Only the unit-modulus RHS oscillator changes when the arithmetic right
hand side changes. The Euclidean squared norm is therefore unchanged.
Compactness yields a common natural-number size bound; no effective
algorithm for that bound is claimed here.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Analysis HGAS.Modular HGAS.Clocks
open HGAS.Analysis.FiniteCoordinateNormSq

variable {eqs vars : ℕ}

/-- Changing only the arithmetic RHS leaves the entire base graph fixed. -/
theorem intendedSourceStateGraph_base_replace_rhs (I : DQLSystem eqs vars)
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (rhs : Fin eqs → ℤ) (x : UnitAddTorus (Fin (vars + eqs))) :
    (intendedSourceStateGraph { I with rhs := rhs } controller x).base =
      (intendedSourceStateGraph I controller x).base := by
  rfl

private theorem intendedSourceGraph_normSq (I : DQLSystem eqs vars)
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (x : UnitAddTorus (Fin (vars + eqs))) :
    normSq (intendedSourceGraph I controller x) =
      normSq (DetectorPoissonReciprocalCode.point
        (intendedSourceStateGraph I controller x).base) + 1 := by
  rw [intendedSourceGraph, FixedDetectorPolynomialCode.point,
    RHSOscillatorPolynomialCode.combinedPoint, normSq_blockPoint]
  congr 1
  let z := UnitAddTorus.mFourier
    (DetectorCharacterCode.flattenCharacter (DetectorCharacterCode.rhsCharacter I)) x
  change normSq ![z.re, z.im] = 1
  have hz : ‖z‖ = 1 := norm_mFourier_apply _ _
  have hs := Complex.sq_norm z
  rw [hz, one_pow, Complex.normSq_apply] at hs
  simpa [normSq, dot, pow_two] using hs.symm

/-- The full Euclidean squared norm is independent of the arithmetic
RHS, not merely bounded by an RHS-dependent estimate. -/
theorem intendedSourceGraph_normSq_replace_rhs (I : DQLSystem eqs vars)
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (rhs : Fin eqs → ℤ) (x : UnitAddTorus (Fin (vars + eqs))) :
    normSq (intendedSourceGraph { I with rhs := rhs } controller x) =
      normSq (intendedSourceGraph I controller x) := by
  rw [intendedSourceGraph_normSq, intendedSourceGraph_normSq,
    intendedSourceStateGraph_base_replace_rhs]

/-- A common integral size bound exists for every RHS with these fixed
matrices and controller states. This is a non-effective compactness bound. -/
theorem exists_uniform_sourceGraph_size (I : DQLSystem eqs vars)
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ (rhs : Fin eqs → ℤ) (x : UnitAddTorus (Fin (vars + eqs))),
      normSq (intendedSourceGraph { I with rhs := rhs } controller x) ≤ (M : ℝ) := by
  have hc : Continuous (fun x ↦ normSq (intendedSourceGraph I controller x)) := by
    have hg := continuous_intendedSourceGraph I controller
    unfold normSq dot
    fun_prop
  obtain ⟨C, hC⟩ := (isCompact_univ.image hc).bddAbove
  obtain ⟨M, hM⟩ := exists_nat_ge (max (1 : ℝ) C)
  refine ⟨M, ?_, fun rhs x ↦ ?_⟩
  · have hreal : (1 : ℝ) ≤ M := (le_max_left _ _).trans hM
    exact_mod_cast hreal
  · rw [intendedSourceGraph_normSq_replace_rhs]
    exact (hC ⟨x, Set.mem_univ _, rfl⟩).trans ((le_max_right _ _).trans hM)

end Stability.Selection
