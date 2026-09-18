import HGAS.Clocks.CircleRealCoordinates
import HGAS.Clocks.ControllerPhaseFlow
import HGAS.Clocks.ControllerPhaseProductPolynomialCode
import HGAS.Dynamics.HomeomorphicFlow
import Mathlib.Tactic

/-!
# The analytic controller--phase flow in polynomial real coordinates

The analytic clock flow is naturally written on a product of copies of
`Circle`, while the polynomial compiler emits four real coordinates
`(r,s,c,d)` for every clock.  This file proves that these are not merely
analogous descriptions:

* the analytic state space is homeomorphic to a product of real algebraic
  circles;
* the transported analytic flow is a genuine global flow on that algebraic
  state space; and
* after flattening the real coordinates, every orbit is an integral curve
  of the literal finite-product sparse polynomial field.

This is the bridge needed when a larger compact source exposes its compact
clock blocks as an equivariant factor.  No uniqueness or informal
identification of circle coordinates is hidden in the statement.
-/

noncomputable section

open Complex Function

namespace HGAS.Clocks.ControllerPhaseProductFlowPolynomial

open HGAS

variable {q : ℕ}

abbrev AnalyticState (q : ℕ) :=
  ControllerPhaseFlow.State (Fin q)

/-- The algebraic state keeps, for each clock, one real controller circle
and one real phase circle. -/
abbrev AlgebraicState (q : ℕ) :=
  Fin q →
    CircleRealCoordinates.State ×
      CircleRealCoordinates.State

/-- Regroup all controller circles and phase circles into interleaved
algebraic clock blocks. -/
def analyticHomeomorph :
    AnalyticState q ≃ₜ AlgebraicState q where
  toFun z a :=
    (CircleRealCoordinates.homeomorph (z.1 a),
      CircleRealCoordinates.homeomorph (z.2 a))
  invFun z :=
    (fun a ↦ CircleRealCoordinates.homeomorph.symm (z a).1,
      fun a ↦ CircleRealCoordinates.homeomorph.symm (z a).2)
  left_inv z := by
    apply Prod.ext <;>
      funext a <;>
      simp
  right_inv z := by
    funext a
    apply Prod.ext
    · apply Subtype.ext
      exact CircleRealCoordinates.point_circle (z a).1
    · apply Subtype.ext
      exact CircleRealCoordinates.point_circle (z a).2
  continuous_toFun := by
    apply continuous_pi
    intro a
    apply Continuous.prodMk
    · exact
        CircleRealCoordinates.homeomorph.continuous.comp
          ((continuous_apply a).comp continuous_fst)
    · exact
        CircleRealCoordinates.homeomorph.continuous.comp
          ((continuous_apply a).comp continuous_snd)
  continuous_invFun := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro a
      exact
        CircleRealCoordinates.homeomorph.symm.continuous.comp
          (continuous_fst.comp (continuous_apply a))
    · apply continuous_pi
      intro a
      exact
        CircleRealCoordinates.homeomorph.symm.continuous.comp
          (continuous_snd.comp (continuous_apply a))

/-- Read one algebraic pair of circles as the local structured state
expected by the four-coordinate polynomial compiler. -/
def structuredState
    (z : AlgebraicState q) (a : Fin q) :
    ControllerPhaseState ℝ where
  controller :=
    ⟨(z a).1.1 0, (z a).1.1 1⟩
  phase :=
    ⟨(z a).2.1 0, (z a).2.1 1⟩

/-- Flatten all algebraic clock blocks into the compiler's `4q` real
coordinates. -/
def rawPoint
    (z : AlgebraicState q) :
    Fin
      (ControllerPhaseProductPolynomialCode.dimension q) → ℝ :=
  ControllerPhaseProductPolynomialCode.point
    (fun a ↦ structuredState z a)

@[simp]
theorem structuredState_analyticHomeomorph
    (z : AnalyticState q) (a : Fin q) :
    structuredState (analyticHomeomorph z) a =
      { controller :=
          ControllerFlow.circleControllerState (z.1 a)
        phase :=
          PhaseClockFlow.circlePhaseState (z.2 a) } := by
  ext <;>
    simp [structuredState, analyticHomeomorph,
      CircleRealCoordinates.homeomorph,
      CircleRealCoordinates.point,
      ControllerFlow.circleControllerState,
      PhaseClockFlow.circlePhaseState]

theorem continuous_rawPoint :
    Continuous (rawPoint :
      AlgebraicState q →
        (Fin
          (ControllerPhaseProductPolynomialCode.dimension q) → ℝ)) := by
  unfold rawPoint
  apply continuous_pi
  intro k
  obtain ⟨⟨a, i⟩, rfl⟩ := finProdFinEquiv.surjective k
  have hcontroller (j : Fin 2) :
      Continuous (fun z : AlgebraicState q ↦ (z a).1.1 j) :=
    (continuous_apply j).comp
      (continuous_subtype_val.comp
        (continuous_fst.comp (continuous_apply a)))
  have hphase (j : Fin 2) :
      Continuous (fun z : AlgebraicState q ↦ (z a).2.1 j) :=
    (continuous_apply j).comp
      (continuous_subtype_val.comp
        (continuous_snd.comp (continuous_apply a)))
  fin_cases i
  · simpa [ControllerPhaseProductPolynomialCode.point,
      PolynomialFiniteProductCode.flattenPoint,
      structuredState, ControllerPolynomialCode.point] using
      hcontroller 0
  · simpa [ControllerPhaseProductPolynomialCode.point,
      PolynomialFiniteProductCode.flattenPoint,
      structuredState, ControllerPolynomialCode.point] using
      hcontroller 1
  · simpa [ControllerPhaseProductPolynomialCode.point,
      PolynomialFiniteProductCode.flattenPoint,
      structuredState, ControllerPolynomialCode.point] using
      hphase 0
  · simpa [ControllerPhaseProductPolynomialCode.point,
      PolynomialFiniteProductCode.flattenPoint,
      structuredState, ControllerPolynomialCode.point] using
      hphase 1

/-- Transport the explicit analytic coupled flow to the algebraic circle
coordinates. -/
def algebraicFlow
    (p : Fin q → ℝ) (hp : ∀ a, 1 < p a) :
    Flow ℝ (AlgebraicState q) :=
  Flow.pullbackHomeomorph analyticHomeomorph.symm
    (ControllerPhaseFlow.controllerPhaseFlow p hp)

@[simp]
theorem analyticHomeomorph_symm_algebraicFlow
    (p : Fin q → ℝ) (hp : ∀ a, 1 < p a)
    (t : ℝ) (z : AlgebraicState q) :
    analyticHomeomorph.symm
        (algebraicFlow p hp t z) =
      ControllerPhaseFlow.controllerPhaseFlow p hp t
        (analyticHomeomorph.symm z) := by
  simp [algebraicFlow]

theorem analyticHomeomorph_symm_semiconj
    (p : Fin q → ℝ) (hp : ∀ a, 1 < p a)
    (t : ℝ) :
    Function.Semiconj analyticHomeomorph.symm
      (algebraicFlow p hp t)
      (ControllerPhaseFlow.controllerPhaseFlow p hp t) :=
  Flow.semiconj_pullbackHomeomorph
    analyticHomeomorph.symm
    (ControllerPhaseFlow.controllerPhaseFlow p hp) t

@[simp]
theorem structuredState_algebraicFlow
    (p : Fin q → ℝ) (hp : ∀ a, 1 < p a)
    (t : ℝ) (z : AlgebraicState q) (a : Fin q) :
    structuredState (algebraicFlow p hp t z) a =
      { controller :=
          ControllerFlow.circleControllerState
            ((ControllerPhaseFlow.controllerPhaseFlow
              p hp t (analyticHomeomorph.symm z)).1 a)
        phase :=
          PhaseClockFlow.circlePhaseState
            ((ControllerPhaseFlow.controllerPhaseFlow
              p hp t (analyticHomeomorph.symm z)).2 a) } := by
  change
    structuredState
        (analyticHomeomorph
          (ControllerPhaseFlow.controllerPhaseFlow
            p hp t (analyticHomeomorph.symm z))) a = _
  exact structuredState_analyticHomeomorph _ _

@[simp]
theorem rawPoint_blockEmbedding
    (z : AlgebraicState q) (a : Fin q)
    (i : Fin ControllerPolynomialCode.dimension) :
    rawPoint z
        (ControllerPhaseProductPolynomialCode.blockEmbedding a i) =
      ControllerPolynomialCode.point (structuredState z a) i := by
  simp [rawPoint,
    ControllerPhaseProductPolynomialCode.point,
    ControllerPhaseProductPolynomialCode.blockEmbedding]

/-! ## Real coordinate derivative lemmas -/

/-- Real part of the complex phase ODE. -/
theorem controllerPhaseFlow_solves_phase_c
    (p : Fin q → ℝ) (hp : ∀ a, 1 < p a)
    (z : AnalyticState q) (a : Fin q) (t : ℝ) :
    HasDerivAt
      (fun u ↦
        (PhaseClockFlow.circlePhaseState
          ((ControllerPhaseFlow.controllerPhaseFlow
            p hp u z).2 a)).c)
      (Controller.lockedPhaseField
        (p a)
        (ControllerFlow.circleControllerState
          ((ControllerPhaseFlow.controllerPhaseFlow
            p hp t z).1 a))
        (PhaseClockFlow.circlePhaseState
          ((ControllerPhaseFlow.controllerPhaseFlow
            p hp t z).2 a))).c t := by
  have hcomplex :=
    ControllerPhaseFlow.controllerPhaseFlow_solves_lockedPhaseField
      p hp z a t
  have hre :=
    Complex.reCLM.hasFDerivAt.comp t
      hcomplex.hasFDerivAt
  rw [hasFDerivAt_iff_hasDerivAt] at hre
  simpa only [Function.comp_apply, Complex.reCLM_apply,
    ContinuousLinearMap.coe_comp',
    ContinuousLinearMap.toSpanSingleton_apply_one,
    PhaseClockFlow.circlePhaseState,
    PhaseClockFlow.phaseStateComplex,
    Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, mul_one, sub_zero, add_zero] using hre

/-- Imaginary part of the complex phase ODE. -/
theorem controllerPhaseFlow_solves_phase_d
    (p : Fin q → ℝ) (hp : ∀ a, 1 < p a)
    (z : AnalyticState q) (a : Fin q) (t : ℝ) :
    HasDerivAt
      (fun u ↦
        (PhaseClockFlow.circlePhaseState
          ((ControllerPhaseFlow.controllerPhaseFlow
            p hp u z).2 a)).d)
      (Controller.lockedPhaseField
        (p a)
        (ControllerFlow.circleControllerState
          ((ControllerPhaseFlow.controllerPhaseFlow
            p hp t z).1 a))
        (PhaseClockFlow.circlePhaseState
          ((ControllerPhaseFlow.controllerPhaseFlow
            p hp t z).2 a))).d t := by
  have hcomplex :=
    ControllerPhaseFlow.controllerPhaseFlow_solves_lockedPhaseField
      p hp z a t
  have him :=
    Complex.imCLM.hasFDerivAt.comp t
      hcomplex.hasFDerivAt
  rw [hasFDerivAt_iff_hasDerivAt] at him
  simpa only [Function.comp_apply, Complex.imCLM_apply,
    ContinuousLinearMap.coe_comp',
    ContinuousLinearMap.toSpanSingleton_apply_one,
    PhaseClockFlow.circlePhaseState,
    PhaseClockFlow.phaseStateComplex,
    Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im,
    zero_mul, mul_one, zero_add, add_zero] using him

/-! ## The emitted polynomial ODE -/

/-- One flattened real coordinate of the transported analytic flow solves
the corresponding local four-coordinate polynomial equation. -/
theorem rawPoint_algebraicFlow_hasDerivAt_block
    (pCode : Fin q → RationalCode)
    (hp : ∀ a, (1 : ℝ) <
      (RationalCode.decode (pCode a) : ℝ))
    (z : AlgebraicState q)
    (a : Fin q)
    (i : Fin ControllerPolynomialCode.dimension)
    (t : ℝ) :
    HasDerivAt
      (fun u ↦
        rawPoint
          (algebraicFlow
            (fun b ↦ (RationalCode.decode (pCode b) : ℝ))
            hp u z)
          (ControllerPhaseProductPolynomialCode.blockEmbedding a i))
      (PolynomialFieldCode.realize
        (ControllerPolynomialCode.fieldCode (pCode a))
        (ControllerPolynomialCode.point
          (structuredState
              (algebraicFlow
              (fun b ↦ (RationalCode.decode (pCode b) : ℝ))
              hp t z) a)) i) t := by
  let p : Fin q → ℝ :=
    fun b ↦ (RationalCode.decode (pCode b) : ℝ)
  let z₀ : AnalyticState q :=
    analyticHomeomorph.symm z
  have hcontroller :=
    ControllerPhaseFlow.controllerPhaseFlow_solves_controllerField
      p hp z₀ a t
  have hc :=
    controllerPhaseFlow_solves_phase_c p hp z₀ a t
  have hd :=
    controllerPhaseFlow_solves_phase_d p hp z₀ a t
  fin_cases i
  · change
      HasDerivAt
        (fun u ↦
          rawPoint (algebraicFlow p hp u z)
            (ControllerPhaseProductPolynomialCode.blockEmbedding
              a ControllerPolynomialCode.rIndex))
        (PolynomialFieldCode.realize
          (ControllerPolynomialCode.fieldCode (pCode a))
          (ControllerPolynomialCode.point
            (structuredState (algebraicFlow p hp t z) a))
          ControllerPolynomialCode.rIndex) t
    have hcurve :
        (fun u ↦
          rawPoint (algebraicFlow p hp u z)
            (ControllerPhaseProductPolynomialCode.blockEmbedding
              a ControllerPolynomialCode.rIndex)) =
        (fun u ↦
          (ControllerFlow.circleControllerState
            ((ControllerPhaseFlow.controllerPhaseFlow
              p hp u z₀).1 a)).r) := by
      funext u
      rw [rawPoint_blockEmbedding,
        structuredState_algebraicFlow]
      rfl
    have hvelocity :=
      congrFun
        (ControllerPolynomialCode.realize_fieldCode
          (pCode a)
          (structuredState (algebraicFlow p hp t z) a))
        ControllerPolynomialCode.rIndex
    have hvelocity' :
        PolynomialFieldCode.realize
            (ControllerPolynomialCode.fieldCode (pCode a))
            (ControllerPolynomialCode.point
              (structuredState (algebraicFlow p hp t z) a))
            ControllerPolynomialCode.rIndex =
          (Controller.controllerField (p a)
            (ControllerFlow.circleControllerState
              ((ControllerPhaseFlow.controllerPhaseFlow
                p hp t z₀).1 a))).r := by
      simpa [ControllerPolynomialCode.point,
        ControllerPolynomialCode.vectorField,
        ControllerPolynomialCode.rIndex] using hvelocity
    rw [hcurve, hvelocity']
    exact hcontroller.1
  · change
      HasDerivAt
        (fun u ↦
          rawPoint (algebraicFlow p hp u z)
            (ControllerPhaseProductPolynomialCode.blockEmbedding
              a ControllerPolynomialCode.sIndex))
        (PolynomialFieldCode.realize
          (ControllerPolynomialCode.fieldCode (pCode a))
          (ControllerPolynomialCode.point
            (structuredState (algebraicFlow p hp t z) a))
          ControllerPolynomialCode.sIndex) t
    have hcurve :
        (fun u ↦
          rawPoint (algebraicFlow p hp u z)
            (ControllerPhaseProductPolynomialCode.blockEmbedding
              a ControllerPolynomialCode.sIndex)) =
        (fun u ↦
          (ControllerFlow.circleControllerState
            ((ControllerPhaseFlow.controllerPhaseFlow
              p hp u z₀).1 a)).s) := by
      funext u
      rw [rawPoint_blockEmbedding,
        structuredState_algebraicFlow]
      rfl
    have hvelocity :=
      congrFun
        (ControllerPolynomialCode.realize_fieldCode
          (pCode a)
          (structuredState (algebraicFlow p hp t z) a))
        ControllerPolynomialCode.sIndex
    have hvelocity' :
        PolynomialFieldCode.realize
            (ControllerPolynomialCode.fieldCode (pCode a))
            (ControllerPolynomialCode.point
              (structuredState (algebraicFlow p hp t z) a))
            ControllerPolynomialCode.sIndex =
          (Controller.controllerField (p a)
            (ControllerFlow.circleControllerState
              ((ControllerPhaseFlow.controllerPhaseFlow
                p hp t z₀).1 a))).s := by
      simpa [ControllerPolynomialCode.point,
        ControllerPolynomialCode.vectorField,
        ControllerPolynomialCode.sIndex] using hvelocity
    rw [hcurve, hvelocity']
    exact hcontroller.2
  · change
      HasDerivAt
        (fun u ↦
          rawPoint (algebraicFlow p hp u z)
            (ControllerPhaseProductPolynomialCode.blockEmbedding
              a ControllerPolynomialCode.cIndex))
        (PolynomialFieldCode.realize
          (ControllerPolynomialCode.fieldCode (pCode a))
          (ControllerPolynomialCode.point
            (structuredState (algebraicFlow p hp t z) a))
          ControllerPolynomialCode.cIndex) t
    have hcurve :
        (fun u ↦
          rawPoint (algebraicFlow p hp u z)
            (ControllerPhaseProductPolynomialCode.blockEmbedding
              a ControllerPolynomialCode.cIndex)) =
        (fun u ↦
          (PhaseClockFlow.circlePhaseState
            ((ControllerPhaseFlow.controllerPhaseFlow
              p hp u z₀).2 a)).c) := by
      funext u
      rw [rawPoint_blockEmbedding,
        structuredState_algebraicFlow]
      rfl
    have hvelocity :=
      congrFun
        (ControllerPolynomialCode.realize_fieldCode
          (pCode a)
          (structuredState (algebraicFlow p hp t z) a))
        ControllerPolynomialCode.cIndex
    have hvelocity' :
        PolynomialFieldCode.realize
            (ControllerPolynomialCode.fieldCode (pCode a))
            (ControllerPolynomialCode.point
              (structuredState (algebraicFlow p hp t z) a))
            ControllerPolynomialCode.cIndex =
          (Controller.lockedPhaseField (p a)
            (ControllerFlow.circleControllerState
              ((ControllerPhaseFlow.controllerPhaseFlow
                p hp t z₀).1 a))
            (PhaseClockFlow.circlePhaseState
              ((ControllerPhaseFlow.controllerPhaseFlow
                p hp t z₀).2 a))).c := by
      simpa [ControllerPolynomialCode.point,
        ControllerPolynomialCode.vectorField,
        ControllerPolynomialCode.cIndex] using hvelocity
    rw [hcurve, hvelocity']
    exact hc
  · change
      HasDerivAt
        (fun u ↦
          rawPoint (algebraicFlow p hp u z)
            (ControllerPhaseProductPolynomialCode.blockEmbedding
              a ControllerPolynomialCode.dIndex))
        (PolynomialFieldCode.realize
          (ControllerPolynomialCode.fieldCode (pCode a))
          (ControllerPolynomialCode.point
            (structuredState (algebraicFlow p hp t z) a))
          ControllerPolynomialCode.dIndex) t
    have hcurve :
        (fun u ↦
          rawPoint (algebraicFlow p hp u z)
            (ControllerPhaseProductPolynomialCode.blockEmbedding
              a ControllerPolynomialCode.dIndex)) =
        (fun u ↦
          (PhaseClockFlow.circlePhaseState
            ((ControllerPhaseFlow.controllerPhaseFlow
              p hp u z₀).2 a)).d) := by
      funext u
      rw [rawPoint_blockEmbedding,
        structuredState_algebraicFlow]
      rfl
    have hvelocity :=
      congrFun
        (ControllerPolynomialCode.realize_fieldCode
          (pCode a)
          (structuredState (algebraicFlow p hp t z) a))
        ControllerPolynomialCode.dIndex
    have hvelocity' :
        PolynomialFieldCode.realize
            (ControllerPolynomialCode.fieldCode (pCode a))
            (ControllerPolynomialCode.point
              (structuredState (algebraicFlow p hp t z) a))
            ControllerPolynomialCode.dIndex =
          (Controller.lockedPhaseField (p a)
            (ControllerFlow.circleControllerState
              ((ControllerPhaseFlow.controllerPhaseFlow
                p hp t z₀).1 a))
            (PhaseClockFlow.circlePhaseState
              ((ControllerPhaseFlow.controllerPhaseFlow
                p hp t z₀).2 a))).d := by
      simpa [ControllerPolynomialCode.point,
        ControllerPolynomialCode.vectorField,
        ControllerPolynomialCode.dIndex] using hvelocity
    rw [hcurve, hvelocity']
    exact hd

/-- **Exact analytic-to-polynomial bridge.**

For every initial algebraic clock state, the raw `4q`-coordinate orbit of
the transported global analytic flow is an integral curve of the literal
primitive-recursive product field emitted by `fieldCode`. -/
theorem rawPoint_algebraicFlow_isIntegralCurve
    (pCode : Fin q → RationalCode)
    (hp : ∀ a, (1 : ℝ) <
      (RationalCode.decode (pCode a) : ℝ))
    (z : AlgebraicState q) :
    IsIntegralCurve
      (fun t ↦
        rawPoint
          (algebraicFlow
            (fun a ↦ (RationalCode.decode (pCode a) : ℝ))
            hp t z))
      (fun _ x ↦
        PolynomialFieldCode.realize
          (ControllerPhaseProductPolynomialCode.fieldCode pCode) x) := by
  intro t
  rw [hasDerivAt_pi]
  intro k
  obtain ⟨⟨a, i⟩, rfl⟩ := finProdFinEquiv.surjective k
  have h :=
    rawPoint_algebraicFlow_hasDerivAt_block
      pCode hp z a i t
  have hvelocity :=
    ControllerPhaseProductPolynomialCode.realize_fieldCode_blockEmbedding
      pCode
      (rawPoint
        (algebraicFlow
          (fun b ↦ (RationalCode.decode (pCode b) : ℝ))
          hp t z))
      a i
  have hvelocity' :
      PolynomialFieldCode.realize
          (ControllerPhaseProductPolynomialCode.fieldCode pCode)
          (rawPoint
            (algebraicFlow
              (fun b ↦ (RationalCode.decode (pCode b) : ℝ))
              hp t z))
          (ControllerPhaseProductPolynomialCode.blockEmbedding a i) =
        PolynomialFieldCode.realize
          (ControllerPolynomialCode.fieldCode (pCode a))
          (ControllerPolynomialCode.point
            (structuredState
              (algebraicFlow
                (fun b ↦ (RationalCode.decode (pCode b) : ℝ))
                hp t z) a)) i := by
    simpa [rawPoint,
      ControllerPhaseProductPolynomialCode.point] using hvelocity
  change
    HasDerivAt
      (fun u ↦
        rawPoint
          (algebraicFlow
            (fun b ↦ (RationalCode.decode (pCode b) : ℝ))
            hp u z)
          (ControllerPhaseProductPolynomialCode.blockEmbedding a i))
      (PolynomialFieldCode.realize
        (ControllerPhaseProductPolynomialCode.fieldCode pCode)
        (rawPoint
          (algebraicFlow
            (fun b ↦ (RationalCode.decode (pCode b) : ℝ))
            hp t z))
        (ControllerPhaseProductPolynomialCode.blockEmbedding a i)) t
  rw [hvelocity']
  exact h

end HGAS.Clocks.ControllerPhaseProductFlowPolynomial
