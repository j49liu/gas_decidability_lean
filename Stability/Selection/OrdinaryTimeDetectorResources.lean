import Stability.Selection.OrdinaryTimeSourcePrimitive
import HGAS.Arithmetic.NormalizedCorrectedFixedDetectorDriftDegrees

/-!
# Resources for the actual detector drift family

The decoded scalar tests, their semantic degree, and their primitive
budget are independent of the RHS. No zero-mode assertion is built into
these resource bounds.
-/

noncomputable section

open scoped BigOperators

namespace Stability.Selection

open HGAS HGAS.Analysis HGAS.Clocks

/-- Raw termwise degree bounds imply the semantic polynomial degree
bound, allowing duplicate terms and coefficient cancellation. -/
theorem decoded_totalDegree_le_of_termsDegreeLE {n D : ℕ}
    (p : PolynomialCode n) (hp : PolynomialCode.TermsDegreeLE D p) :
    (PolynomialCode.decode p).totalDegree ≤ D := by
  induction p with
  | nil => simp [PolynomialCode.decode_nil]
  | cons t p ih =>
    rw [PolynomialCode.termsDegreeLE_cons_iff] at hp
    rw [PolynomialCode.decode_cons]
    apply (MvPolynomial.totalDegree_add _ _).trans
    refine max_le ?_ (ih hp.2)
    exact (MvPolynomial.totalDegree_monomial_le _ _).trans
      (by simpa only [← ExponentCode.degree_decode] using hp.1)

/-- The literal decoded normalized scalar drift polynomials. -/
def detectorDriftPolynomials {eqs vars : ℕ} (I : DQLSystem eqs vars) :
    Fin (NormalizedCorrectedFixedDetectorDriftCode.driftCount vars) →
      MvPolynomial (Fin (FixedDetectorPolynomialCode.dimension eqs vars)) ℚ :=
  fun i ↦ PolynomialCode.decode (NormalizedCorrectedFixedDetectorDriftCode.driftCode I i)

/-- Semantic degree of the complete polynomial map, after cancellation. -/
def detectorDriftDegree {eqs vars : ℕ} (I : DQLSystem eqs vars) : ℕ :=
  Finset.univ.sup fun i ↦ (detectorDriftPolynomials I i).totalDegree

theorem detectorDriftPolynomials_degree_le {eqs vars : ℕ} (I : DQLSystem eqs vars)
    (i : Fin (NormalizedCorrectedFixedDetectorDriftCode.driftCount vars)) :
    (detectorDriftPolynomials I i).totalDegree ≤ detectorDriftDegree I :=
  Finset.le_sup (f := fun j ↦ (detectorDriftPolynomials I j).totalDegree) (Finset.mem_univ i)

theorem detectorDriftDegree_le_ledger {eqs vars : ℕ} (I : DQLSystem eqs vars) :
    detectorDriftDegree I ≤ NormalizedCorrectedFixedDetectorDriftCode.driftDegree I := by
  apply Finset.sup_le
  intro i _
  exact decoded_totalDegree_le_of_termsDegreeLE _
    (NormalizedCorrectedFixedDetectorDriftCode.driftCode_termsDegreeLE I i)

/-- The RHS enters the oscillator vector field, not these scalar tests. -/
theorem detectorDriftPolynomials_replace_rhs {eqs vars : ℕ} (I : DQLSystem eqs vars)
    (rhs : Fin eqs → ℤ) :
    detectorDriftPolynomials { I with rhs := rhs } = detectorDriftPolynomials I := rfl

theorem detectorDriftDegree_replace_rhs {eqs vars : ℕ} (I : DQLSystem eqs vars)
    (rhs : Fin eqs → ℤ) : detectorDriftDegree { I with rhs := rhs } = detectorDriftDegree I := rfl

/-- The explicit rational constant for the actual detector's drift map. -/
def detectorPrimitiveBudget {eqs vars : ℕ} (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) (m : ℕ) : ℚ :=
  sourcePrimitiveBudget p m (detectorDriftDegree I) (detectorDriftPolynomials I)

theorem detectorPrimitiveBudget_pos {eqs vars : ℕ} (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) (m : ℕ) : 0 < detectorPrimitiveBudget I p m :=
  sourcePrimitiveBudget_pos _ _ _ _

theorem detectorPrimitiveBudget_replace_rhs {eqs vars : ℕ} (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) (m : ℕ) (rhs : Fin eqs → ℤ) :
    detectorPrimitiveBudget { I with rhs := rhs } p m = detectorPrimitiveBudget I p m := rfl

/-- Evaluation is the literal normalized drift value on the structured
source state, rather than a surrogate polynomial family. -/
theorem sourcePolynomialFunction_detectorDrift {eqs vars : ℕ} (I : DQLSystem eqs vars)
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (x : UnitAddTorus (Fin (vars + eqs)))
    (i : Fin (NormalizedCorrectedFixedDetectorDriftCode.driftCount vars)) :
    sourcePolynomialFunction I controller (detectorDriftPolynomials I i) x =
      NormalizedCorrectedFixedDetectorDriftCode.driftValue I
        (intendedSourceStateGraph I controller x) i :=
  NormalizedCorrectedFixedDetectorDriftCode.eval_driftCode I i _

/-- The primitive of the actual drift on the actual positive-controller
source graph. -/
def detectorSourcePrimitive {eqs vars : ℕ} (I : DQLSystem eqs vars)
    (p : Fin (vars + eqs) → ℕ) :=
  sourcePolynomialPrimitive I
    (fun i ↦ ExplicitPositiveControllerEquilibrium.state (p i : ℝ)) p (fun _ ↦ 1)
    (detectorDriftPolynomials I)

/-- Concrete analytic resources for the literal detector. The equation
still subtracts the actual mean; arithmetic zero-mode vanishing is a
separate statement. -/
theorem detectorSourcePrimitive_resources {eqs vars : ℕ}
    (I : DQLSystem eqs vars) (p : Fin (vars + eqs) → ℕ)
    (hp : ∀ i, (p i).Prime) (hinjective : Function.Injective p) (m : ℕ) (hm : 0 < m)
    (hθ : (1 / 256 : ℝ) * (1 + 1 / (m : ℝ)) ^
      (4 + 4 * ∑ row, ∑ j, |(I.linear row j : ℝ)|) ≤ 1 / 8)
    (hP : (1 / 2 : ℝ) * (1 + 1 / (m : ℝ)) ^
      (4 + 4 * ∑ row, ∑ j, |(I.quadratic row j : ℝ)|) ≤ 3 / 4) :
    Continuous (detectorSourcePrimitive I p) ∧
    (∀ x, normSq (detectorSourcePrimitive I p x) ≤
      ((detectorPrimitiveBudget I p m : ℝ) * (1 + 1 / (m : ℝ)) ^
        (4 * (detectorDriftDegree I : ℝ) * ∑ row, |(I.rhs row : ℝ)|)) ^ 2) ∧
    ∀ x t i,
      let ω := ScaledRadicalClock.scaledSignedPrimeSqrtFrequency
        (1 / (2 * Real.pi)) p (fun _ ↦ 1)
      let controller := fun j ↦ ExplicitPositiveControllerEquilibrium.state (p j : ℝ)
      HasDerivAt (fun s ↦ detectorSourcePrimitive I p (RadicalClock.torusTranslationFlow ω s x) i)
        (NormalizedCorrectedFixedDetectorDriftCode.driftValue I
          (intendedSourceStateGraph I controller (RadicalClock.torusTranslationFlow ω t x)) i -
          (UnitAddTorus.mFourierCoeff (fun y ↦
            (NormalizedCorrectedFixedDetectorDriftCode.driftValue I
              (intendedSourceStateGraph I controller y) i : ℂ)) 0).re) t := by
  have h := sourcePolynomialPrimitive_resources I
    (fun i ↦ ExplicitPositiveControllerEquilibrium.state (p i : ℝ))
    (fun i ↦ explicitController_coordinates_le_one (p i : ℝ))
    p hp hinjective (fun _ ↦ 1) (fun _ ↦ Or.inl rfl) m hm hθ hP
    (detectorDriftPolynomials I) (detectorDriftDegree I) (detectorDriftPolynomials_degree_le I)
  simpa only [detectorSourcePrimitive, detectorPrimitiveBudget,
    sourcePolynomialFunction_detectorDrift] using h

end Stability.Selection
