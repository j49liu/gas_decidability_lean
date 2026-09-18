import HGAS.Modular.CanonicalLinkedJacobiThetaMovingTrajectory
import HGAS.Modular.ControllerProductLinkedJacobiFamilyPolynomialCode
import HGAS.Clocks.ControllerPhaseProductFlowPolynomial
import HGAS.Analysis.ComplexRealTimeDerivative

/-!
# From structured linked trajectories to the polynomial compiler

The dynamical modules describe unary and Jacobi coordinates as complex
scalar ODEs, whereas the executable compiler stores their real and
imaginary parts in a finite real vector.  This file proves the exact
crosswalk.

There are three levels:

1. every one of the fourteen complex coordinates has the derivative
   encoded by `LinkedJacobiState.combinedVectorField`;
2. realification gives the corresponding twenty-eight real coordinate
   derivatives; and
3. one controller product together with a finite family of linked blocks
   is an integral curve of the literal dynamically coupled family field.

The last theorem specializes this interface to the canonical moving theta
family and makes the normalization equations for every block explicit.
-/

namespace HGAS.Modular

open HGAS Complex

noncomputable section

/-! ## One linked block -/

/-- Every complex coordinate of a structured linked trajectory has the
velocity recorded by the structured combined vector field. -/
theorem IsScaledLinkedJacobiTrajectory.point_hasDerivAt
    {κZ κPhi : ℂ}
    {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    (j : Fin LinkedJacobiPolynomialCode.dimension)
    (t : ℝ) :
    HasDerivAt
      (fun u =>
        LinkedJacobiPolynomialCode.point (z u) j)
      (LinkedJacobiPolynomialCode.point
        (LinkedJacobiState.combinedVectorField
          κZ κPhi (z t)) j) t := by
  obtain ⟨i | k, rfl⟩ :=
    finSumFinEquiv.surjective j
  · fin_cases i
    · simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.unaryEmbedding,
        UnaryPolynomialCode.modularPoint,
        LinkedJacobiState.combinedVectorField] using
        hz.unary.A t
    · simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.unaryEmbedding,
        UnaryPolynomialCode.modularPoint,
        LinkedJacobiState.combinedVectorField] using
        hz.unary.C t
    · simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.unaryEmbedding,
        UnaryPolynomialCode.modularPoint,
        LinkedJacobiState.combinedVectorField] using
        hz.unary.E t
    · simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.unaryEmbedding,
        UnaryPolynomialCode.modularPoint,
        LinkedJacobiState.combinedVectorField] using
        hz.unary.Y t
  · fin_cases k
    · simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.jacobiEmbedding,
        JacobiPolynomialCode.point,
        LinkedJacobiState.combinedVectorField] using
        hz.jacobi.p2 t
    · simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.jacobiEmbedding,
        JacobiPolynomialCode.point,
        LinkedJacobiState.combinedVectorField] using
        hz.jacobi.p3 t
    · simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.jacobiEmbedding,
        JacobiPolynomialCode.point,
        LinkedJacobiState.combinedVectorField] using
        hz.jacobi.p4 t
    · simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.jacobiEmbedding,
        JacobiPolynomialCode.point,
        LinkedJacobiState.combinedVectorField] using
        hz.jacobi.H t
    · simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.jacobiEmbedding,
        JacobiPolynomialCode.point,
        LinkedJacobiState.combinedVectorField] using
        hz.jacobi.T1 t
    · simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.jacobiEmbedding,
        JacobiPolynomialCode.point,
        LinkedJacobiState.combinedVectorField] using
        hz.jacobi.T2 t
    · simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.jacobiEmbedding,
        JacobiPolynomialCode.point,
        LinkedJacobiState.combinedVectorField] using
        hz.jacobi.T3 t
    · simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.jacobiEmbedding,
        JacobiPolynomialCode.point,
        LinkedJacobiState.combinedVectorField] using
        hz.jacobi.T4 t
    · simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.jacobiEmbedding,
        JacobiPolynomialCode.point,
        LinkedJacobiState.combinedVectorField] using
        hz.jacobi.Delta t
    · simpa [LinkedJacobiPolynomialCode.point,
        LinkedJacobiPolynomialCode.jacobiEmbedding,
        JacobiPolynomialCode.point,
        LinkedJacobiState.combinedVectorField] using
        hz.jacobi.U t

/-- Realifying a structured linked trajectory gives every derivative
expected by the real polynomial compiler. -/
theorem IsScaledLinkedJacobiTrajectory.realifyPoint_hasDerivAt
    {κZ κPhi : ℂ}
    {z : ℝ → LinkedJacobiState ℂ}
    (hz : IsScaledLinkedJacobiTrajectory κZ κPhi z)
    (j : Fin
      (LinkedJacobiPolynomialCode.dimension +
        LinkedJacobiPolynomialCode.dimension))
    (t : ℝ) :
    HasDerivAt
      (fun u =>
        ComplexCoordinates.realifyPoint
          (LinkedJacobiPolynomialCode.point (z u)) j)
      (ComplexCoordinates.realifyPoint
        (LinkedJacobiPolynomialCode.point
          (LinkedJacobiState.combinedVectorField
            κZ κPhi (z t))) j) t := by
  obtain ⟨i | i, rfl⟩ :=
    finSumFinEquiv.surjective j
  · rw [show
      finSumFinEquiv (Sum.inl i) =
        ComplexCoordinates.realIndex i by rfl]
    simpa only [
      ComplexCoordinates.realifyPoint_realIndex] using
      HasDerivAt.complex_re
        (hz.point_hasDerivAt i t)
  · rw [show
      finSumFinEquiv (Sum.inr i) =
        ComplexCoordinates.imagIndex i by rfl]
    simpa only [
      ComplexCoordinates.realifyPoint_imagIndex] using
      HasDerivAt.complex_im
        (hz.point_hasDerivAt i t)

/-! ## One controller product and a finite linked family -/

/-- A structured family trajectory whose controller block follows its
compiled field and whose linked clocks agree with the controller
readouts realifies to an integral curve of the literal family compiler. -/
theorem
    controllerProductLinkedJacobiFamily_point_isIntegralCurve
    {q b : ℕ}
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (z :
      ℝ →
        ControllerProductLinkedJacobiFamilyState q b)
    (κZ κPhi : Fin b → ℂ)
    (hcontrollers :
      IsIntegralCurve
        (fun t =>
          ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint
            (z t))
        (fun _ x =>
          PolynomialFieldCode.realize
            (HGAS.Clocks.ControllerPhaseProductPolynomialCode.fieldCode
              parameters) x))
    (hlinked :
      ∀ a,
        IsScaledLinkedJacobiTrajectory
          (κZ a) (κPhi a)
          (fun t => (z t).linked a))
    (hkappaZ :
      ∀ t a,
        ControllerProductLinkedJacobiFamilyPolynomialCode.kappaZ
            (fun d i =>
              (RationalCode.decode
                (omegaWeights d i) : ℝ))
            (fun d i =>
              (RationalCode.decode
                (numberWeights d i) : ℝ))
            (fun i =>
              (RationalCode.decode
                (parameters i) : ℝ))
            (z t) a =
          κZ a)
    (hkappaPhi :
      ∀ t a,
        ControllerProductLinkedJacobiFamilyPolynomialCode.kappaPhi
            (fun d i =>
              (RationalCode.decode
                (omegaWeights d i) : ℝ))
            (fun i =>
              (RationalCode.decode
                (parameters i) : ℝ))
            (z t) a =
          κPhi a) :
    IsIntegralCurve
      (fun t =>
        ControllerProductLinkedJacobiFamilyPolynomialCode.point
          (z t))
      (fun _ x =>
        PolynomialFieldCode.realize
          (ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode
            parameters omegaWeights numberWeights) x) := by
  intro t
  rw [hasDerivAt_pi]
  intro k
  change
    HasDerivAt
      (fun u =>
        ControllerProductLinkedJacobiFamilyPolynomialCode.point
          (z u) k)
      (PolynomialFieldCode.realize
        (ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode
          parameters omegaWeights numberWeights)
        (ControllerProductLinkedJacobiFamilyPolynomialCode.point
          (z t)) k)
      t
  rw [
    ControllerProductLinkedJacobiFamilyPolynomialCode.realize_fieldCode
      parameters omegaWeights numberWeights (z t)]
  obtain ⟨i | r, rfl⟩ :=
    finSumFinEquiv.surjective k
  · rw [show
      finSumFinEquiv (Sum.inl i) =
        ControllerProductLinkedJacobiFamilyPolynomialCode.controllersEmbedding
          i by rfl]
    have hc := hcontrollers t
    rw [hasDerivAt_pi] at hc
    simpa only [
      ControllerProductLinkedJacobiFamilyPolynomialCode.point,
      ControllerProductLinkedJacobiFamilyPolynomialCode.controllersEmbedding,
      PolynomialBlockCode.point_leftEmbedding,
      ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint,
      ControllerProductLinkedJacobiFamilyPolynomialCode.vectorField,
      HGAS.Clocks.ControllerPhaseProductPolynomialCode.realize_fieldCode]
      using hc i
  · obtain ⟨⟨a, j⟩, rfl⟩ :=
      finProdFinEquiv.surjective r
    rw [show
      finSumFinEquiv
          (Sum.inr (finProdFinEquiv (a, j)) :
            Fin
                (ControllerProductLinkedJacobiFamilyPolynomialCode.controllerDimension
                  q) ⊕
              Fin
                (ControllerProductLinkedJacobiFamilyPolynomialCode.linkedFamilyDimension
                  b)) =
        ControllerProductLinkedJacobiFamilyPolynomialCode.linkedFamilyEmbedding
          (ControllerProductLinkedJacobiFamilyPolynomialCode.linkedBlockEmbedding
            a j) by rfl]
    have hj :=
      (hlinked a).realifyPoint_hasDerivAt j t
    rw [← hkappaZ t a, ← hkappaPhi t a] at hj
    simpa only [
      ControllerProductLinkedJacobiFamilyPolynomialCode.point,
      ControllerProductLinkedJacobiFamilyPolynomialCode.linkedFamilyEmbedding,
      PolynomialBlockCode.point_rightEmbedding,
      ControllerProductLinkedJacobiFamilyPolynomialCode.linkedFamilyPoint,
      ControllerProductLinkedJacobiFamilyPolynomialCode.linkedBlockEmbedding,
      PolynomialFiniteProductCode.flattenPoint_blockEmbedding,
      ControllerProductLinkedJacobiFamilyPolynomialCode.vectorField]
      using hj

/-! ## Canonical theta specialization -/

/-- Combine an arbitrary controller trajectory with the canonical
moving theta family.  Keeping this constructor separate from the
compiler makes the analytic and algebraic sides of the reduction
independently reusable. -/
def canonicalControllerLinkedJacobiFamilyPath
    {q b : ℕ}
    (controllers :
      ℝ →
        HGAS.Clocks.ControllerPhaseProductPolynomialCode.StateFamily
          q ℝ)
    (ξ : Fin b → ℝ → ℂ)
    (T : Fin b → ℝ → UpperHalfPlane)
    (t : ℝ) :
    ControllerProductLinkedJacobiFamilyState q b where
  controllers := controllers t
  linked :=
    canonicalLinkedJacobiThetaFamilyMovingPath ξ T t

@[simp]
theorem canonicalControllerLinkedJacobiFamilyPath_controllers
    {q b : ℕ}
    (controllers :
      ℝ →
        HGAS.Clocks.ControllerPhaseProductPolynomialCode.StateFamily
          q ℝ)
    (ξ : Fin b → ℝ → ℂ)
    (T : Fin b → ℝ → UpperHalfPlane)
    (t : ℝ) :
    (canonicalControllerLinkedJacobiFamilyPath
      controllers ξ T t).controllers =
        controllers t :=
  rfl

@[simp]
theorem canonicalControllerLinkedJacobiFamilyPath_linked
    {q b : ℕ}
    (controllers :
      ℝ →
        HGAS.Clocks.ControllerPhaseProductPolynomialCode.StateFamily
          q ℝ)
    (ξ : Fin b → ℝ → ℂ)
    (T : Fin b → ℝ → UpperHalfPlane)
    (t : ℝ) (j : Fin b) :
    (canonicalControllerLinkedJacobiFamilyPath
      controllers ξ T t).linked j =
        canonicalLinkedJacobiThetaMovingPath
          (ξ j) (T j) t :=
  rfl

/-- The canonical moving theta family is an integral curve of the
literal common-controller compiler as soon as:

* the controller coordinates solve their compiled field;
* each elliptic and modular parameter has a constant velocity; and
* the controller readouts equal the analytically forced normalizations
  `π ξ'` and `π i T'`.

The nonvanishing hypothesis is exactly what is needed for the reciprocal
coordinate `U = 1 / θ₁`; no additional residual or invariant-manifold
hypothesis is hidden in this theorem. -/
theorem
    canonicalControllerLinkedJacobiFamilyPath_point_isIntegralCurve
    {q b : ℕ}
    (parameters : Fin q → RationalCode)
    (omegaWeights numberWeights :
      Fin b → Fin q → RationalCode)
    (controllers :
      ℝ →
        HGAS.Clocks.ControllerPhaseProductPolynomialCode.StateFamily
          q ℝ)
    (ξ : Fin b → ℝ → ℂ)
    (T : Fin b → ℝ → UpperHalfPlane)
    (a c : Fin b → ℂ)
    (hcontrollers :
      IsIntegralCurve
        (fun t =>
          HGAS.Clocks.ControllerPhaseProductPolynomialCode.point
            (controllers t))
        (fun _ x =>
          PolynomialFieldCode.realize
            (HGAS.Clocks.ControllerPhaseProductPolynomialCode.fieldCode
              parameters) x))
    (hξ :
      ∀ j t,
        HasDerivAt (ξ j) (a j) t)
    (hT :
      ∀ j t,
        HasDerivAt
          (fun u : ℝ => (T j u : ℂ))
          (c j) t)
    (h1 :
      ∀ j t,
        jacobiTheta1
          (ξ j t) (T j t : ℂ) ≠ 0)
    (hkappaZ :
      ∀ t j,
        ControllerProductLinkedJacobiFamilyPolynomialCode.kappaZ
            (fun d i =>
              (RationalCode.decode
                (omegaWeights d i) : ℝ))
            (fun d i =>
              (RationalCode.decode
                (numberWeights d i) : ℝ))
            (fun i =>
              (RationalCode.decode
                (parameters i) : ℝ))
            (canonicalControllerLinkedJacobiFamilyPath
              controllers ξ T t) j =
          (Real.pi : ℂ) * a j)
    (hkappaPhi :
      ∀ t j,
        ControllerProductLinkedJacobiFamilyPolynomialCode.kappaPhi
            (fun d i =>
              (RationalCode.decode
                (omegaWeights d i) : ℝ))
            (fun i =>
              (RationalCode.decode
                (parameters i) : ℝ))
            (canonicalControllerLinkedJacobiFamilyPath
              controllers ξ T t) j =
          (Real.pi : ℂ) * I * c j) :
    IsIntegralCurve
      (fun t =>
        ControllerProductLinkedJacobiFamilyPolynomialCode.point
          (canonicalControllerLinkedJacobiFamilyPath
            controllers ξ T t))
      (fun _ x =>
        PolynomialFieldCode.realize
          (ControllerProductLinkedJacobiFamilyPolynomialCode.fieldCode
            parameters omegaWeights numberWeights) x) := by
  apply
    controllerProductLinkedJacobiFamily_point_isIntegralCurve
      parameters omegaWeights numberWeights
      (canonicalControllerLinkedJacobiFamilyPath
        controllers ξ T)
      (fun j => (Real.pi : ℂ) * a j)
      (fun j => (Real.pi : ℂ) * I * c j)
  · simpa only [
      ControllerProductLinkedJacobiFamilyPolynomialCode.controllersPoint,
      canonicalControllerLinkedJacobiFamilyPath_controllers] using
      hcontrollers
  · have hfamily :=
      canonicalLinkedJacobiThetaFamilyMovingPath_isScaledTrajectory
        hξ hT h1
    intro j
    simpa only [
      canonicalControllerLinkedJacobiFamilyPath_linked] using
      hfamily.block j
  · exact hkappaZ
  · exact hkappaPhi

end

end HGAS.Modular
