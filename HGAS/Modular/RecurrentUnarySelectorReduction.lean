import HGAS.Modular.RecurrentLiftGeometry
import HGAS.Modular.JacobiCoefficientLinkDynamics
import HGAS.Modular.LinkedJacobiPolynomialCode
import HGAS.Modular.UnaryDegenerateRecurrence

/-!
# A total recurrent reduction for the unary modular block

The recurrent modular analysis is naturally split into a generic locus

```
                    A C (A + C) ≠ 0
```

and its three invariant divisors.  The generic and degenerate arguments
were previously available as separate theorems:

* on the generic locus, global lambda uniformization and Riccati
  reconstruction produce an upper-half-plane lift which is either a
  horizontal line or a boundary-tangent horocycle;
* on `A = 0` or `C = 0`, recurrence forces the unary vector field to
  vanish;
* on `A + C = 0`, the same conclusion holds on the unary Jacobi residual
  locus.

This file is the all-cases bridge between those results.  It is deliberately
stated at one recurrent time, because that is the form consumed by the
ergodic/invariant-measure selector.  No modular quotient, finite-cover map,
or measure-classification theorem is assumed here.
-/

namespace HGAS.Modular

open HGAS
open UpperHalfPlane hiding I

noncomputable section

/-- Forward recurrence of the actual fourteen-coordinate linked polynomial
state projects to coordinatewise recurrence of its unary modular block.

Keeping the same return-time sequence matters: four unrelated recurrent
subsequences would not suffice for the nonlinear unary argument. -/
noncomputable def forwardRecurrentUnaryModularAt_of_linkedPolynomialPoint
    {z : ℝ → LinkedJacobiState ℂ}
    {t₀ : ℝ}
    (hrec :
      ForwardRecurrentAt
        (fun t ↦ LinkedJacobiPolynomialCode.point (z t)) t₀) :
    ForwardRecurrentUnaryModularAt
      (fun t ↦ (z t).unary) t₀ := by
  let times : ℕ → ℝ := Classical.choose hrec
  have htimes :
      Filter.Tendsto times Filter.atTop Filter.atTop :=
    (Classical.choose_spec hrec).1
  have hreturn :
      Filter.Tendsto
        (fun n ↦
          LinkedJacobiPolynomialCode.point (z (times n)))
        Filter.atTop
        (nhds (LinkedJacobiPolynomialCode.point (z t₀))) :=
    (Classical.choose_spec hrec).2
  refine
    { times := times
      times_tendsto := htimes
      A_tendsto := ?_
      C_tendsto := ?_
      E_tendsto := ?_
      Y_tendsto := ?_ }
  · simpa [LinkedJacobiPolynomialCode.point,
      UnaryPolynomialCode.modularPoint] using
      (tendsto_pi_nhds.mp hreturn
        (LinkedJacobiPolynomialCode.unaryEmbedding
          UnaryPolynomialCode.AIndex))
  · simpa [LinkedJacobiPolynomialCode.point,
      UnaryPolynomialCode.modularPoint] using
      (tendsto_pi_nhds.mp hreturn
        (LinkedJacobiPolynomialCode.unaryEmbedding
          UnaryPolynomialCode.CIndex))
  · simpa [LinkedJacobiPolynomialCode.point,
      UnaryPolynomialCode.modularPoint] using
      (tendsto_pi_nhds.mp hreturn
        (LinkedJacobiPolynomialCode.unaryEmbedding
          UnaryPolynomialCode.EIndex))
  · simpa [LinkedJacobiPolynomialCode.point,
      UnaryPolynomialCode.modularPoint] using
      (tendsto_pi_nhds.mp hreturn
        (LinkedJacobiPolynomialCode.unaryEmbedding
          UnaryPolynomialCode.YIndex))

/-- The exact exhaustive alternatives for a recurrent unary modular state
on the unary Jacobi residual locus.

The left branch records both the divisor on which the state lies and the
fact that it is an equilibrium of the formal unary vector field.  The
right branch records genericity and supplies the canonical-lambda lift
with its global horizontal-or-horocycle classification. -/
theorem recurrentUnarySelectorReduction
    {z : ℝ → UnaryModularState ℂ}
    (hz :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock z)
    {t₀ : ℝ}
    (hrec : ForwardRecurrentUnaryModularAt z t₀)
    (hJacobi :
      UnaryModularState.jacobiResidual (z t₀) = 0) :
    (((z t₀).A = 0 ∨
        (z t₀).C = 0 ∨
        UnaryModularState.B (z t₀) = 0) ∧
      UnaryModularState.vectorField (z t₀) = 0) ∨
    ((z t₀).A ≠ 0 ∧
      (z t₀).C ≠ 0 ∧
      UnaryModularState.B (z t₀) ≠ 0 ∧
      ∃ T : ℝ → ℍ,
        Continuous T ∧
        (∀ t,
          UnaryModularState.lambdaCoordinate (z t) =
            canonicalLambda (T t)) ∧
        IsHorizontalOrHorocycleLift z T t₀) := by
  by_cases hA : (z t₀).A = 0
  · left
    refine ⟨Or.inl hA, ?_⟩
    exact
      hz.vectorField_eq_zero_of_A_eq_zero_of_recurrent
        modularIndependentVariableClock_ne_zero hrec hA
  by_cases hC : (z t₀).C = 0
  · left
    refine ⟨Or.inr (Or.inl hC), ?_⟩
    exact
      hz.vectorField_eq_zero_of_C_eq_zero_of_recurrent
        modularIndependentVariableClock_ne_zero hrec hC
  by_cases hB : UnaryModularState.B (z t₀) = 0
  · left
    refine ⟨Or.inr (Or.inr hB), ?_⟩
    exact
      hz.vectorField_eq_zero_of_B_eq_zero_of_recurrent
        modularIndependentVariableClock_ne_zero hrec hB hJacobi
  · right
    refine ⟨hA, hC, hB, ?_⟩
    exact
      recurrentGenericUnaryTrajectory_exists_horizontal_or_horocycle
        hz hA hC hB hrec

/-- Polynomial-source form of `recurrentUnarySelectorReduction`.

This theorem starts from recurrence in the literal fourteen-complex-
coordinate state used by the linked Jacobi polynomial compiler.  The
projection theorem above supplies one common unary return sequence, and
the linked trajectory structure supplies the unary ODE. -/
theorem recurrentLinkedJacobiUnarySelectorReduction
    {κZ : ℂ}
    {z : ℝ → LinkedJacobiState ℂ}
    (hz :
      IsScaledLinkedJacobiTrajectory
        κZ modularIndependentVariableClock z)
    {t₀ : ℝ}
    (hrec :
      ForwardRecurrentAt
        (fun t ↦ LinkedJacobiPolynomialCode.point (z t)) t₀)
    (hJacobi :
      UnaryModularState.jacobiResidual (z t₀).unary = 0) :
    (((z t₀).unary.A = 0 ∨
        (z t₀).unary.C = 0 ∨
        UnaryModularState.B (z t₀).unary = 0) ∧
      UnaryModularState.vectorField (z t₀).unary = 0) ∨
    ((z t₀).unary.A ≠ 0 ∧
      (z t₀).unary.C ≠ 0 ∧
      UnaryModularState.B (z t₀).unary ≠ 0 ∧
      ∃ T : ℝ → ℍ,
        Continuous T ∧
        (∀ t,
          UnaryModularState.lambdaCoordinate (z t).unary =
            canonicalLambda (T t)) ∧
        IsHorizontalOrHorocycleLift
          (fun t ↦ (z t).unary) T t₀) := by
  exact recurrentUnarySelectorReduction
    hz.unary
    (forwardRecurrentUnaryModularAt_of_linkedPolynomialPoint hrec)
    hJacobi

/-- A compact corollary used when the particular degenerate divisor is
irrelevant: a recurrent residual state is either an equilibrium or has a
globally classified canonical-lambda lift. -/
theorem recurrentUnary_equilibrium_or_horizontalOrHorocycleLift
    {z : ℝ → UnaryModularState ℂ}
    (hz :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock z)
    {t₀ : ℝ}
    (hrec : ForwardRecurrentUnaryModularAt z t₀)
    (hJacobi :
      UnaryModularState.jacobiResidual (z t₀) = 0) :
    UnaryModularState.vectorField (z t₀) = 0 ∨
      ∃ T : ℝ → ℍ,
        Continuous T ∧
        (∀ t,
          UnaryModularState.lambdaCoordinate (z t) =
            canonicalLambda (T t)) ∧
        IsHorizontalOrHorocycleLift z T t₀ := by
  rcases recurrentUnarySelectorReduction hz hrec hJacobi with
    hdegenerate | hgeneric
  · exact Or.inl hdegenerate.2
  · exact Or.inr hgeneric.2.2.2

end

end HGAS.Modular
