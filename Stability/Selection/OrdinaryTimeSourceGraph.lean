import Stability.Selection.OrdinaryTimeJacobiDerivativeGraph
import Stability.Selection.OrdinaryTimeThetaReciprocal
import Stability.Selection.OrdinaryTimePoissonGraph
import Stability.Selection.OrdinaryTimeEisensteinGraph
import HGAS.Clocks.ExplicitPositiveControllerEquilibrium

/-!
# The literal intended source graph

The component Fourier series assemble into the actual source-state type.
They agree on every real phase lift with the theta formulas in Section 8,
equation `graph`.
-/

noncomputable section

open scoped BigOperators

namespace Stability.Selection

open HGAS HGAS.Analysis HGAS.Modular HGAS.Clocks

variable {eqs vars : ℕ}

/-- The linked unary--Jacobi block of the literal intended graph. -/
def sourceLinkedThetaGraph (I : DQLSystem eqs vars) (j : Fin vars)
    (x : UnitAddTorus (Fin (vars + eqs))) : LinkedJacobiState ℂ where
  unary :=
    { A := unaryThetaGraph (finSumFinEquiv (Sum.inl j)) 1 0 x ^ 4
      C := unaryThetaGraph (finSumFinEquiv (Sum.inl j)) 0 1 x ^ 4
      E := eisensteinGraph (finSumFinEquiv (Sum.inl j)) x
      Y := unaryThetaGraph (finSumFinEquiv (Sum.inl j)) 0 0 x }
  jacobi :=
    { p2 := unaryThetaGraph (finSumFinEquiv (Sum.inl j)) 1 0 x ^ 2
      p3 := unaryThetaGraph (finSumFinEquiv (Sum.inl j)) 0 0 x ^ 2
      p4 := unaryThetaGraph (finSumFinEquiv (Sum.inl j)) 0 1 x ^ 2
      H := eisensteinGraph (finSumFinEquiv (Sum.inl j)) x / 12
      T1 := halfPeriodThetaGraph I j x
      T2 := halfPeriodJacobiVectorGraph I j x 1
      T3 := halfPeriodJacobiVectorGraph I j x 2
      T4 := halfPeriodJacobiVectorGraph I j x 3
      Delta := halfPeriodJacobiDerivativeGraph I j x
      U := thetaReciprocalGraph I j x }

/-- Every linked coordinate is the actual canonical theta coordinate
at the printed modular and elliptic arguments, on every real phase lift. -/
theorem sourceLinkedThetaGraph_eq_canonical
    (I : DQLSystem eqs vars) (j : Fin vars) (x : Fin (vars + eqs) → ℝ) :
    let τ := fundamentalThetaParameter (finSumFinEquiv (Sum.inl j)) x
    let w : ℂ := 4 * ((∑ row, (I.linear row j : ℝ) *
      x (finSumFinEquiv (Sum.inr row)) : ℝ) : ℂ) + (1 + (τ : ℂ)) / 2
    sourceLinkedThetaGraph I j (fun i ↦ (x i : UnitAddCircle)) =
      { unary := canonicalUnaryTheta τ, jacobi := canonicalJacobiThetaState w τ } := by
  obtain ⟨h2, h3, h4⟩ := unaryThetaGraph_eq_thetaConstants
    (finSumFinEquiv (Sum.inl j)) x
  have hE := eisensteinGraph_eq_E2 (finSumFinEquiv (Sum.inl j)) x
  have hT1 := halfPeriodThetaGraph_eq_jacobiTheta1 I j x
  have hT := halfPeriodJacobiVectorGraph_eq_jacobiThetaVector I j x
  have hT2 := congrFun hT 1
  have hT3 := congrFun hT 2
  have hT4 := congrFun hT 3
  have hD := halfPeriodJacobiDerivativeGraph_eq_jacobiTheta1Prime I j x
  have hU := thetaReciprocalGraph_eq_inv I j (fun i ↦ (x i : UnitAddCircle))
  dsimp only at hT1 hT2 hT3 hT4 hD ⊢
  rw [hT1] at hU
  simp only [sourceLinkedThetaGraph, h2, h3, h4, hE, hT1, hT2, hT3, hT4, hD, hU]
  rfl

theorem continuous_sourceLinkedThetaGraph_point (I : DQLSystem eqs vars) (j : Fin vars) :
    Continuous (fun x ↦ LinkedJacobiPolynomialCode.point (sourceLinkedThetaGraph I j x)) := by
  have hu (q r : ℤ) := continuous_unaryThetaGraph
    (d := Fin (vars + eqs)) (finSumFinEquiv (Sum.inl j)) q r
  have hE := continuous_eisensteinGraph
    (d := Fin (vars + eqs)) (finSumFinEquiv (Sum.inl j))
  have hT1 := continuous_halfPeriodThetaGraph I j
  have hT (k : Fin 4) := (continuous_apply k).comp (continuous_halfPeriodJacobiVectorGraph I j)
  have hD := continuous_halfPeriodJacobiDerivativeGraph I j
  have hU := continuous_thetaReciprocalGraph I j
  apply continuous_pi
  intro i
  obtain ⟨u | q, rfl⟩ := finSumFinEquiv.surjective i
  · fin_cases u <;>
      dsimp [LinkedJacobiPolynomialCode.point, ComplexPolynomialBlockCode.point,
        UnaryPolynomialCode.modularPoint, sourceLinkedThetaGraph] <;> fun_prop
  · fin_cases q <;>
      dsimp [LinkedJacobiPolynomialCode.point, ComplexPolynomialBlockCode.point,
        JacobiPolynomialCode.point, sourceLinkedThetaGraph] <;> fun_prop

/-- The phase and gauge characters use fundamental clock angles. -/
def sourcePhaseGraph (x : UnitAddTorus (Fin (vars + eqs)))
    (i : Fin (vars + eqs)) : Controller.PhaseState ℝ :=
  { c := (UnitAddTorus.mFourier (Pi.single i 1) x).re
    d := (UnitAddTorus.mFourier (Pi.single i 1) x).im }

/-- The literal complete source graph, with the constant controller
states left explicit so that either signed equilibrium may be used. -/
def intendedSourceStateGraph (I : DQLSystem eqs vars)
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (x : UnitAddTorus (Fin (vars + eqs))) : FixedDetectorPolynomialCode.State eqs vars where
  base :=
    { base :=
      { source :=
        { controllers := fun i ↦ { controller := controller i, phase := sourcePhaseGraph x i }
          linked := fun j ↦ sourceLinkedThetaGraph I j x }
        gauge := fun j ↦ (1 / 4 : ℂ) * UnitAddTorus.mFourier
          (CanonicalFixedDetectorTrajectory.gaugeRootExponent I j) x }
      reciprocal := fun k ↦
        let js := finProdFinEquiv.symm k
        poissonReciprocalGraph I js.1 (if js.2 = 0 then 1 else -1) x }
  rhs :=
    { c := (UnitAddTorus.mFourier
        (DetectorCharacterCode.flattenCharacter (DetectorCharacterCode.rhsCharacter I)) x).re
      d := (UnitAddTorus.mFourier
        (DetectorCharacterCode.flattenCharacter (DetectorCharacterCode.rhsCharacter I)) x).im }

/-- The map `Γ` in the actual real source coordinates. -/
def intendedSourceGraph (I : DQLSystem eqs vars)
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ)
    (x : UnitAddTorus (Fin (vars + eqs))) :
    Fin (FixedDetectorPolynomialCode.dimension eqs vars) → ℝ :=
  FixedDetectorPolynomialCode.point (intendedSourceStateGraph I controller x)

private theorem continuous_blockPoint {X R : Type*} [TopologicalSpace X] [TopologicalSpace R]
    {m n : ℕ} {f : X → Fin m → R} {g : X → Fin n → R}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x ↦ PolynomialBlockCode.point (f x) (g x)) := by
  apply continuous_pi
  intro i
  obtain ⟨a | b, rfl⟩ := finSumFinEquiv.surjective i
  · simpa only [PolynomialBlockCode.point, Equiv.symm_apply_apply, Sum.elim_inl,
      Function.comp_apply] using (continuous_apply a).comp hf
  · simpa only [PolynomialBlockCode.point, Equiv.symm_apply_apply, Sum.elim_inr,
      Function.comp_apply] using (continuous_apply b).comp hg

private theorem continuous_realifyPoint {X : Type*} [TopologicalSpace X]
    {n : ℕ} {f : X → Fin n → ℂ} (hf : Continuous f) :
    Continuous (fun x ↦ ComplexCoordinates.realifyPoint (f x)) := by
  apply continuous_pi
  intro i
  obtain ⟨a | b, rfl⟩ := finSumFinEquiv.surjective i
  · simpa only [ComplexCoordinates.realifyPoint, Equiv.symm_apply_apply,
      Function.comp_apply] using Complex.continuous_re.comp ((continuous_apply a).comp hf)
  · simpa only [ComplexCoordinates.realifyPoint, Equiv.symm_apply_apply,
      Function.comp_apply] using Complex.continuous_im.comp ((continuous_apply b).comp hf)

private theorem continuous_reciprocalPoint {X : Type*} [TopologicalSpace X]
    {n : ℕ} {f : X → Fin n → ℂ} (hf : Continuous f) :
    Continuous (fun x ↦ ComplexReciprocalFamilyPolynomialCode.reciprocalPoint (f x)) := by
  apply continuous_pi
  intro i
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective i
  fin_cases b
  · simpa [ComplexReciprocalFamilyPolynomialCode.reciprocalPoint,
      PolynomialFiniteProductCode.flattenPoint] using
      Complex.continuous_re.comp ((continuous_apply a).comp hf)
  · simpa [ComplexReciprocalFamilyPolynomialCode.reciprocalPoint,
      PolynomialFiniteProductCode.flattenPoint] using
      Complex.continuous_im.comp ((continuous_apply a).comp hf)

/-- The literal graph is continuous in the actual flattened real source
coordinates. Compactness therefore applies to this map itself. -/
theorem continuous_intendedSourceGraph (I : DQLSystem eqs vars)
    (controller : Fin (vars + eqs) → Controller.ControllerState ℝ) :
    Continuous (intendedSourceGraph I controller) := by
  have hc (i : Fin (vars + eqs)) : Continuous (fun x : UnitAddTorus (Fin (vars + eqs)) ↦
      ControllerPolynomialCode.point
      { controller := controller i, phase := sourcePhaseGraph x i }) := by
    apply continuous_pi
    intro k
    fin_cases k
    · change Continuous (fun _ : UnitAddTorus (Fin (vars + eqs)) ↦ (controller i).r)
      exact continuous_const
    · change Continuous (fun _ : UnitAddTorus (Fin (vars + eqs)) ↦ (controller i).s)
      exact continuous_const
    · exact Complex.continuous_re.comp (UnitAddTorus.mFourier (Pi.single i 1)).continuous
    · exact Complex.continuous_im.comp (UnitAddTorus.mFourier (Pi.single i 1)).continuous
  have hcontrollers : Continuous (fun x ↦
      ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint
        (intendedSourceStateGraph I controller x).base.base.source) := by
    apply continuous_pi
    intro i
    exact (continuous_apply (finProdFinEquiv.symm i).2).comp
      (hc (finProdFinEquiv.symm i).1)
  have hlinked : Continuous (fun x ↦
      ControllerProductLinkedJacobiFamilyPolynomialCode.linkedFamilyPoint
        (intendedSourceStateGraph I controller x).base.base.source) := by
    apply continuous_pi
    intro i
    exact (continuous_apply (finProdFinEquiv.symm i).2).comp
      (continuous_realifyPoint (continuous_sourceLinkedThetaGraph_point I
        (finProdFinEquiv.symm i).1))
  have hsource : Continuous (fun x ↦ ControllerProductLinkedJacobiFamilyPolynomialCode.point
      (intendedSourceStateGraph I controller x).base.base.source) :=
    continuous_blockPoint hcontrollers hlinked
  have hgauge : Continuous (fun x ↦
      (intendedSourceStateGraph I controller x).base.base.gauge) := by
    apply continuous_pi
    intro j
    exact continuous_const.mul (UnitAddTorus.mFourier _).continuous
  have hbase : Continuous (fun x ↦ ControllerProductLinkedJacobiGaugeFamilyPolynomialCode.point
      (intendedSourceStateGraph I controller x).base.base) :=
    continuous_blockPoint hsource (continuous_reciprocalPoint hgauge)
  have hreciprocal : Continuous (fun x ↦
      (intendedSourceStateGraph I controller x).base.reciprocal) := by
    apply continuous_pi
    intro k
    exact continuous_poissonReciprocalGraph I _ _
  have hpoisson : Continuous (fun x ↦ DetectorPoissonReciprocalCode.point
      (intendedSourceStateGraph I controller x).base) :=
    continuous_blockPoint hbase (continuous_reciprocalPoint hreciprocal)
  have hrhs : Continuous (fun x ↦ ![(intendedSourceStateGraph I controller x).rhs.c,
      (intendedSourceStateGraph I controller x).rhs.d]) := by
    apply continuous_pi
    intro k
    fin_cases k
    · exact Complex.continuous_re.comp (UnitAddTorus.mFourier _).continuous
    · exact Complex.continuous_im.comp (UnitAddTorus.mFourier _).continuous
  exact continuous_blockPoint hpoisson hrhs

end Stability.Selection
