import HGAS.Compiler.AllAffineCompactBaseChartTrajectory
import HGAS.Dynamics.FiniteFlowTwoSidedGenericZeroOrbit
import HGAS.Dynamics.ErgodicFullMeasureRestriction
import HGAS.Dynamics.InvariantComponentAverage

/-!
# The finite chart of the compact base flow

The central coordinate satisfies a scalar homogeneous equation, so its
nonzero locus is invariant in both time directions. On that locus the
even central power is exactly the positive affine clock speed.

This is the chart geometry in Section 9, Lemma `lem:selectedorbit`.
-/

noncomputable section

namespace Stability.Selection

open HGAS HGAS.Dynamics HGAS.CompactAccumulatorPipelineCode
open HGAS.CompactAccumulatorPipelineCode.AllAffineCompactSourceChart (layout affineSpeed)
open HGAS.CompactAccumulatorPipelineCode.AllAffineCompactBaseChartTrajectory
open Filter Topology MeasureTheory Set
open scoped BoundedContinuousFunction

variable {n : ℕ}

/-- The finite central chart is invariant for the actual compact base
field, independently of any invariant probability. -/
theorem ordinaryBase_finiteInterior_invariant
    (E K : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE E (P j)) :
    IsInvariant (baseFlow (layout n) E (2 * K) P) (finiteInterior (n := n)) := by
  let ϕ := baseFlow (layout n) E (2 * K) P
  let a : BaseSpace (layout n) → ℝ := fun b ↦ -weight b *
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) b.1
      (PolynomialCode.decode (MixedCentralPolynomialCode.affineBlockDotCode
        (layout n) (2 * K) P 0))
  have ha : Continuous a := by
    apply continuous_weight.neg.mul
    have hp := (MvPolynomial.continuous_eval
      (MvPolynomial.map (algebraMap ℚ ℝ)
        (PolynomialCode.decode (MixedCentralPolynomialCode.affineBlockDotCode
          (layout n) (2 * K) P 0)))).comp
            (continuous_subtype_val : Continuous (fun b : BaseSpace (layout n) ↦ b.1))
    simpa only [MvPolynomial.eval_map] using hp
  have hcoord (b : BaseSpace (layout n)) (t : ℝ) :
      HasDerivAt (fun s ↦ weight (ϕ s b)) (a (ϕ t b) * weight (ϕ t b)) t := by
    have h := (hasDerivAt_pi.mp
      (baseFlow_integralCurve (layout n) E (2 * K) P hP
        (by intro _; dsimp; intro c; exact Fin.elim0 c) b t))
      (MixedCentralPolynomialCode.wIndex (n := n) 0)
    apply h.congr_deriv
    simp only [PolynomialFieldCode.realize_apply, baseFieldCode,
      MixedCentralPolynomialCode.fieldCode, MixedCentralPolynomialCode.finSumFinEquiv_symm_wIndex,
      MixedCentralPolynomialCode.wFieldCode, PolynomialCode.decode_neg_code,
      PolynomialCode.decode_mul_code, PolynomialCode.decode_pow_code,
      PolynomialCode.decode_varCode, map_neg, map_mul, map_pow, MvPolynomial.eval₂Hom_X']
    dsimp [a, weight, ϕ]
    ring
  have hequator : IsInvariant ϕ {b | weight b = 0} := by
    intro t b hb
    have hzero := real_eq_zero_of_hasDerivAt_eq_mul
      (fun s ↦ a (ϕ s b)) (fun s ↦ weight (ϕ s b))
      (ha.comp (ϕ.continuous continuous_id continuous_const)) (hcoord b)
      (t₀ := 0) (by simpa using hb)
    exact congrFun hzero t
  exact isInvariant_compl_of_flow ϕ hequator

/-- The compact-base clock observable, including its zero equatorial
values. The denominator-clearing exponent is `2K`. -/
def ordinaryBaseSpeed (K : ℕ) : BaseSpace (layout n) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun b ↦ weight b ^ (2 * K), continuous_weight.pow _⟩

theorem ordinaryBaseSpeed_nonneg (K : ℕ) (b : BaseSpace (layout n)) :
    0 ≤ ordinaryBaseSpeed K b := by
  change 0 ≤ weight b ^ (2 * K)
  rw [pow_mul]
  positivity

theorem ordinaryBaseSpeed_eq (K : ℕ) (b : FiniteBaseSpace n) :
    ordinaryBaseSpeed K b.1 = affineSpeed K (affinePoint b) :=
  weight_evenPow_eq_affineSpeed K b

theorem ordinaryBaseSpeed_pos (K : ℕ) (b : FiniteBaseSpace n) :
    0 < ordinaryBaseSpeed K b.1 := by
  rw [ordinaryBaseSpeed_eq]
  exact AllAffineCompactSourceChart.affineSpeed_pos K _

/-- The finite chart is a measurable open subset of the compact base. -/
theorem ordinaryBase_finiteInterior_measurable :
    MeasurableSet (finiteInterior (n := n)) :=
  (isClosed_eq continuous_weight continuous_const).measurableSet.compl

end Stability.Selection
