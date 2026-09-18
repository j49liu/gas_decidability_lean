import HGAS.Dynamics.ZeroIntegralSupport
import HGAS.Modular.JacobiCoefficientLinks

/-!
# The finite validity-residual energy of the linked Jacobi block

The linked unary/Jacobi state carries ten polynomial validity residuals:

* the four Jacobi-chart residuals `R₀,R₁,R₂,Rᵁ`;
* the unary Jacobi relation `Y⁴-A-C`;
* the four coefficient links `L₂,L₃,L₄,L_H`; and
* the signed square-root link `p₃-Y²`.

This file gives that finite list a named index type.  Its real validity
energy is the sum of the ten squared complex moduli.  The generic support
principle from `Dynamics.ZeroIntegralSupport` then proves the sentence used
after equation (7.25) of the written proof: zero integral of the validity
energy forces **each** polynomial residual to vanish at **every** point of
the measure support.

The ambient compiler eventually adds other finite residual blocks (gauge,
Poisson, and arithmetic links).  They can be combined with this one by a
sum type; the support theorem itself is deliberately independent of this
particular list.
-/

namespace HGAS.Modular

open MeasureTheory

noncomputable section

/-- Names of the ten polynomial residuals in the linked unary/Jacobi
validity block. -/
inductive LinkedJacobiResidualIndex
  | coefficientCurve
  | thetaQuadricOne
  | thetaQuadricTwo
  | reciprocalChart
  | unaryJacobi
  | coefficientLinkTwo
  | coefficientLinkThree
  | coefficientLinkFour
  | eisensteinLink
  | signedRootLinkThree
  deriving DecidableEq, Fintype

/-- The residual selected by a validity-block index. -/
def linkedJacobiResidual :
    LinkedJacobiResidualIndex →
      LinkedJacobiState ℂ → ℂ
  | .coefficientCurve, z =>
      JacobiState.residualR0 z.jacobi
  | .thetaQuadricOne, z =>
      JacobiState.residualR1 z.jacobi
  | .thetaQuadricTwo, z =>
      JacobiState.residualR2 z.jacobi
  | .reciprocalChart, z =>
      JacobiState.residualRU z.jacobi
  | .unaryJacobi, z =>
      LinkedJacobiState.jacobiResidual z
  | .coefficientLinkTwo, z =>
      LinkedJacobiState.link2 z
  | .coefficientLinkThree, z =>
      LinkedJacobiState.link3 z
  | .coefficientLinkFour, z =>
      LinkedJacobiState.link4 z
  | .eisensteinLink, z =>
      LinkedJacobiState.linkH z
  | .signedRootLinkThree, z =>
      LinkedJacobiState.signedLink3 z

variable {X : Type*}

/-- Validity energy along an arbitrary family of linked Jacobi states. -/
def linkedJacobiResidualEnergy
    (z : X → LinkedJacobiState ℂ) (x : X) : ℝ :=
  HGAS.Dynamics.complexResidualEnergy
    (fun i x ↦ linkedJacobiResidual i (z x)) x

/-- The linked-block energy is zero exactly when all ten named residuals
vanish. -/
theorem linkedJacobiResidualEnergy_eq_zero_iff
    (z : X → LinkedJacobiState ℂ) (x : X) :
    linkedJacobiResidualEnergy z x = 0 ↔
      ∀ i, linkedJacobiResidual i (z x) = 0 := by
  exact HGAS.Dynamics.complexResidualEnergy_eq_zero_iff
    (fun i x ↦ linkedJacobiResidual i (z x)) x

variable [TopologicalSpace X] [MeasurableSpace X]
  {μ : Measure X}

/-- **Linked Jacobi validity on support.**

Continuity is stated for the ten composed residuals, rather than by
installing an arbitrary topology on the algebraic state record.  In every
compiler application the state coordinates are ordinary real or complex
coordinate projections, so these hypotheses follow by polynomial
continuity. -/
theorem linkedJacobiResiduals_eq_zero_on_support
    (z : X → LinkedJacobiState ℂ)
    (hcontinuous :
      ∀ i, Continuous
        (fun x ↦ linkedJacobiResidual i (z x)))
    (hintegrable :
      Integrable (linkedJacobiResidualEnergy z) μ)
    (hintegral :
      ∫ x, linkedJacobiResidualEnergy z x ∂μ = 0) :
    ∀ x ∈ μ.support, ∀ i,
      linkedJacobiResidual i (z x) = 0 := by
  exact
    HGAS.Dynamics.complexResiduals_eq_zero_on_support_of_integral_energy_eq_zero
      hcontinuous hintegrable hintegral

/-- Expanded conclusion for the four intrinsic Jacobi-chart residuals. -/
theorem jacobiChartResiduals_eq_zero_on_support
    (z : X → LinkedJacobiState ℂ)
    (hcontinuous :
      ∀ i, Continuous
        (fun x ↦ linkedJacobiResidual i (z x)))
    (hintegrable :
      Integrable (linkedJacobiResidualEnergy z) μ)
    (hintegral :
      ∫ x, linkedJacobiResidualEnergy z x ∂μ = 0)
    {x : X} (hx : x ∈ μ.support) :
    JacobiState.residualR0 (z x).jacobi = 0 ∧
      JacobiState.residualR1 (z x).jacobi = 0 ∧
      JacobiState.residualR2 (z x).jacobi = 0 ∧
      JacobiState.residualRU (z x).jacobi = 0 := by
  have hall :=
    linkedJacobiResiduals_eq_zero_on_support
      z hcontinuous hintegrable hintegral x hx
  exact
    ⟨hall .coefficientCurve,
      hall .thetaQuadricOne,
      hall .thetaQuadricTwo,
      hall .reciprocalChart⟩

end

end HGAS.Modular
