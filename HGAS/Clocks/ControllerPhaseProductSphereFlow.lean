import HGAS.Clocks.ControllerPhaseProductFlowPolynomial
import Mathlib.Tactic

/-!
# The canonical polynomial flow on a finite product of clock circles

`ControllerPhaseProductFlowPolynomial` identifies the analytic clock flow
with an interleaved family of algebraic circle states and proves the
flattened polynomial ODE.  This file packages the actual compact
real-algebraic state space inside `ℝ^(4q)`.

An ambient point belongs to `ClockProductSphere q` exactly when the
controller pair and phase pair in every four-coordinate block each have
squared radius one.  The space is homeomorphic to the interleaved
algebraic state, so the analytic flow transports to a genuine global flow
on this literal polynomial state space.  Its ambient coordinate curve
solves the primitive-recursive finite-product polynomial field.
-/

noncomputable section

open Function

namespace HGAS.Clocks.ControllerPhaseProductSphereFlow

open HGAS

variable {q : ℕ}

namespace ProductCode

abbrev dimension (q : ℕ) :=
  ControllerPhaseProductPolynomialCode.dimension q

end ProductCode

/-- The two unit-circle equations in every four-coordinate clock block. -/
def OnClockCircles
    (x : Fin (ProductCode.dimension q) → ℝ) : Prop :=
  ∀ a : Fin q,
    Controller.controllerRadiusSq
          (ControllerPhaseProductPolynomialCode.state x a).controller =
        1 ∧
      Controller.phaseRadiusSq
          (ControllerPhaseProductPolynomialCode.state x a).phase =
        1

/-- Literal compact real-algebraic state space of `q` clocks. -/
abbrev ClockProductSphere (q : ℕ) :=
  {x : Fin (ProductCode.dimension q) → ℝ // OnClockCircles x}

/-- Every interleaved algebraic circle state flattens to a point of the
literal clock product sphere. -/
def algebraicToSphere
    (z :
      ControllerPhaseProductFlowPolynomial.AlgebraicState q) :
    ClockProductSphere q :=
  ⟨ControllerPhaseProductFlowPolynomial.rawPoint z, by
    intro a
    simpa [OnClockCircles,
      ControllerPhaseProductFlowPolynomial.rawPoint,
      ControllerPhaseProductFlowPolynomial.structuredState,
      Controller.controllerRadiusSq,
      Controller.phaseRadiusSq] using
      And.intro (z a).1.2 (z a).2.2⟩

/-- Reassemble the two algebraic circles in every ambient clock block. -/
def sphereToAlgebraic
    (x : ClockProductSphere q) :
    ControllerPhaseProductFlowPolynomial.AlgebraicState q :=
  fun a ↦
    let s :=
      ControllerPhaseProductPolynomialCode.state x.1 a
    (⟨![s.controller.r, s.controller.s], by
        simpa [Controller.controllerRadiusSq] using
          (x.2 a).1⟩,
      ⟨![s.phase.c, s.phase.d], by
        simpa [Controller.phaseRadiusSq] using
          (x.2 a).2⟩)

@[simp]
theorem structuredState_sphereToAlgebraic
    (x : ClockProductSphere q) (a : Fin q) :
    ControllerPhaseProductFlowPolynomial.structuredState
        (sphereToAlgebraic x) a =
      ControllerPhaseProductPolynomialCode.state x.1 a := by
  ext <;>
    simp [sphereToAlgebraic,
      ControllerPhaseProductFlowPolynomial.structuredState]

@[simp]
theorem rawPoint_sphereToAlgebraic
    (x : ClockProductSphere q) :
    ControllerPhaseProductFlowPolynomial.rawPoint
        (sphereToAlgebraic x) = x.1 := by
  rw [ControllerPhaseProductFlowPolynomial.rawPoint]
  apply
    ControllerPhaseProductPolynomialCode.point_state

@[simp]
theorem sphereToAlgebraic_algebraicToSphere
    (z :
      ControllerPhaseProductFlowPolynomial.AlgebraicState q) :
    sphereToAlgebraic (algebraicToSphere z) = z := by
  funext a
  apply Prod.ext
  · apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [sphereToAlgebraic, algebraicToSphere,
        ControllerPhaseProductFlowPolynomial.rawPoint,
        ControllerPhaseProductFlowPolynomial.structuredState]
  · apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [sphereToAlgebraic, algebraicToSphere,
        ControllerPhaseProductFlowPolynomial.rawPoint,
        ControllerPhaseProductFlowPolynomial.structuredState]

@[simp]
theorem algebraicToSphere_sphereToAlgebraic
    (x : ClockProductSphere q) :
    algebraicToSphere (sphereToAlgebraic x) = x := by
  apply Subtype.ext
  exact rawPoint_sphereToAlgebraic x

theorem continuous_algebraicToSphere :
    Continuous (algebraicToSphere :
      ControllerPhaseProductFlowPolynomial.AlgebraicState q →
        ClockProductSphere q) :=
  ControllerPhaseProductFlowPolynomial.continuous_rawPoint.subtype_mk _

theorem continuous_sphereToAlgebraic :
    Continuous (sphereToAlgebraic :
      ClockProductSphere q →
        ControllerPhaseProductFlowPolynomial.AlgebraicState q) := by
  apply continuous_pi
  intro a
  have hcoord
      (i : Fin ControllerPolynomialCode.dimension) :
      Continuous
        (fun x : ClockProductSphere q ↦
          x.1
            (ControllerPhaseProductPolynomialCode.blockEmbedding
              a i)) :=
    (continuous_apply
      (ControllerPhaseProductPolynomialCode.blockEmbedding a i)).comp
        continuous_subtype_val
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · simpa [ControllerPhaseProductPolynomialCode.state,
        ControllerPolynomialCode.state,
        PolynomialFiniteProductCode.unflattenPoint] using
        hcoord ControllerPolynomialCode.rIndex
    · simpa [ControllerPhaseProductPolynomialCode.state,
        ControllerPolynomialCode.state,
        PolynomialFiniteProductCode.unflattenPoint] using
        hcoord ControllerPolynomialCode.sIndex
  · apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · simpa [ControllerPhaseProductPolynomialCode.state,
        ControllerPolynomialCode.state,
        PolynomialFiniteProductCode.unflattenPoint] using
        hcoord ControllerPolynomialCode.cIndex
    · simpa [ControllerPhaseProductPolynomialCode.state,
        ControllerPolynomialCode.state,
        PolynomialFiniteProductCode.unflattenPoint] using
        hcoord ControllerPolynomialCode.dIndex

/-- Exact homeomorphism from the literal `4q`-coordinate compact variety
to the interleaved algebraic circle representation. -/
def clockSphereHomeomorph :
    ClockProductSphere q ≃ₜ
      ControllerPhaseProductFlowPolynomial.AlgebraicState q where
  toFun := sphereToAlgebraic
  invFun := algebraicToSphere
  left_inv := algebraicToSphere_sphereToAlgebraic
  right_inv := sphereToAlgebraic_algebraicToSphere
  continuous_toFun := continuous_sphereToAlgebraic
  continuous_invFun := continuous_algebraicToSphere

/-- Compactness of the literal algebraic clock variety, transported from
the finite product of real algebraic circles. -/
noncomputable instance instCompactSpaceClockProductSphere :
    CompactSpace (ClockProductSphere q) :=
  clockSphereHomeomorph.symm.compactSpace

/-- Canonical global flow of the literal polynomial clock product. -/
def clockSphereFlow
    (p : Fin q → ℝ) (hp : ∀ a, 1 < p a) :
    Flow ℝ (ClockProductSphere q) :=
  Flow.pullbackHomeomorph clockSphereHomeomorph
    (ControllerPhaseProductFlowPolynomial.algebraicFlow p hp)

@[simp]
theorem clockSphereHomeomorph_flow
    (p : Fin q → ℝ) (hp : ∀ a, 1 < p a)
    (t : ℝ) (x : ClockProductSphere q) :
    clockSphereHomeomorph (clockSphereFlow p hp t x) =
      ControllerPhaseProductFlowPolynomial.algebraicFlow
        p hp t (clockSphereHomeomorph x) := by
  simp [clockSphereFlow]

/-- The literal circle-space flow is an exact continuous factor of the
analytic coupled controller--phase flow. -/
theorem toAnalytic_semiconj
    (p : Fin q → ℝ) (hp : ∀ a, 1 < p a)
    (t : ℝ) :
    Function.Semiconj
      (ControllerPhaseProductFlowPolynomial.analyticHomeomorph.symm ∘
        clockSphereHomeomorph)
      (clockSphereFlow p hp t)
      (ControllerPhaseFlow.controllerPhaseFlow p hp t) :=
  (ControllerPhaseProductFlowPolynomial.analyticHomeomorph_symm_semiconj
    p hp t).comp_left
      (Flow.semiconj_pullbackHomeomorph
        clockSphereHomeomorph
        (ControllerPhaseProductFlowPolynomial.algebraicFlow p hp) t)

theorem continuous_toAnalytic :
    Continuous
      (ControllerPhaseProductFlowPolynomial.analyticHomeomorph.symm ∘
        (clockSphereHomeomorph :
          ClockProductSphere q →
            ControllerPhaseProductFlowPolynomial.AlgebraicState q)) :=
  ControllerPhaseProductFlowPolynomial.analyticHomeomorph.symm.continuous.comp
    clockSphereHomeomorph.continuous

/-- **Canonical compact polynomial-flow theorem.**

Every orbit of the transported global clock flow, read in its literal
`4q` ambient real coordinates, is an integral curve of the exact sparse
polynomial field emitted by the finite-product compiler. -/
theorem clockSphereFlow_isIntegralCurve
    (pCode : Fin q → RationalCode)
    (hp : ∀ a, (1 : ℝ) <
      (RationalCode.decode (pCode a) : ℝ))
    (x : ClockProductSphere q) :
    IsIntegralCurve
      (fun t ↦
        (clockSphereFlow
          (fun a ↦ (RationalCode.decode (pCode a) : ℝ))
          hp t x).1)
      (fun _ y ↦
        PolynomialFieldCode.realize
          (ControllerPhaseProductPolynomialCode.fieldCode pCode) y) := by
  simpa [clockSphereFlow, clockSphereHomeomorph] using
    ControllerPhaseProductFlowPolynomial.rawPoint_algebraicFlow_isIntegralCurve
      pCode hp (clockSphereHomeomorph x)

end HGAS.Clocks.ControllerPhaseProductSphereFlow
