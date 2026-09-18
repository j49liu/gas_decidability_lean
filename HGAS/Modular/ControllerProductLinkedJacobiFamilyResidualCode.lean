import HGAS.Algebra.PolynomialBlockDegrees
import HGAS.Modular.ControllerProductLinkedJacobiFamilyPolynomialCode
import HGAS.Modular.LinkedJacobiPolynomialComputability
import HGAS.Modular.LinkedJacobiPolynomialDegrees
import Mathlib.Tactic

/-!
# Validity residuals for a finite family of linked Jacobi blocks

The common-controller compiler stores `b` independent linked Jacobi blocks
in one flattened right-hand coordinate family.  Each linked block has ten
complex algebraic residuals, represented by twenty real polynomial
coordinates.  This module lifts those fixed local residuals into the common
ambient space.

The construction is deliberately independent of the controller parameters
and of the frequency weights.  It proves four facts needed by the eventual
compact accumulator:

* exact evaluation of every lifted residual at every structured state;
* exact simultaneous-vanishing semantics for all blocks;
* controller/linked bidegree `(0,4)` and total degree at most four; and
* primitive-recursive, hence computable, indexed access to the finite family.

All statements include `q = 0` and `b = 0`.  In the empty-family case the
simultaneous-vanishing theorem is the expected vacuous equivalence.
-/

namespace HGAS.Modular

open HGAS

namespace ControllerProductLinkedJacobiFamilyResidualCode

open ControllerProductLinkedJacobiFamilyPolynomialCode

variable {q b : ℕ}

/-- Twenty real residual coordinates for one linked block. -/
abbrev localResidualDimension : ℕ := 10 + 10

/-- Twenty real residual coordinates for each of the `b` linked blocks. -/
abbrev residualDimension (b : ℕ) : ℕ :=
  b * localResidualDimension

/-- Inject the local residual coordinates of block `a` into the flattened
family of all residual coordinates. -/
def residualBlockEmbedding (a : Fin b) :
    Fin localResidualDimension ↪ Fin (residualDimension b) :=
  PolynomialFiniteProductCode.blockEmbedding a

/-- Lift all twenty real residuals of all `b` linked blocks into the full
`4q + 28b` source-coordinate space. -/
def residualCode
    (q b : ℕ) :
    Fin (residualDimension b) →
      PolynomialCode
        (ControllerProductLinkedJacobiFamilyPolynomialCode.dimension q b) :=
  fun k ↦
    let ai := finProdFinEquiv.symm k
    PolynomialBlockCode.right
      (m := controllerDimension q)
      (PolynomialFiniteProductCode.lift ai.1
        (LinkedJacobiPolynomialCode.realResidualCode ai.2))

@[simp]
theorem residualCode_residualBlockEmbedding
    (q : ℕ) (a : Fin b) (i : Fin localResidualDimension) :
    residualCode q b (residualBlockEmbedding a i) =
      PolynomialBlockCode.right
        (m := controllerDimension q)
        (PolynomialFiniteProductCode.lift a
          (LinkedJacobiPolynomialCode.realResidualCode i)) := by
  unfold residualCode residualBlockEmbedding
  rw [
    PolynomialFiniteProductCode.finProdFinEquiv_symm_blockEmbedding]

/-! ## Exact semantics -/

/-- A lifted residual sees exactly one linked block and ignores both the
common controllers and every other linked block. -/
@[simp]
theorem eval_residualCode_residualBlockEmbedding
    (z : ControllerProductLinkedJacobiFamilyState q b)
    (a : Fin b) (i : Fin localResidualDimension) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (point z)
        (PolynomialCode.decode
          (residualCode q b (residualBlockEmbedding a i))) =
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (ComplexCoordinates.realifyPoint
          (LinkedJacobiPolynomialCode.point (z.linked a)))
        (PolynomialCode.decode
          (LinkedJacobiPolynomialCode.realResidualCode i)) := by
  rw [residualCode_residualBlockEmbedding, point,
    PolynomialBlockCode.eval₂Hom_right,
    PolynomialFiniteProductCode.eval₂Hom_lift]
  simp [linkedFamilyPoint]

/-- Reassembling the twenty real coordinates belonging to block `a`
recovers its ten named complex linked-Jacobi residuals. -/
@[simp]
theorem complexifyPoint_eval_residualBlock
    (z : ControllerProductLinkedJacobiFamilyState q b)
    (a : Fin b) :
    ComplexCoordinates.complexifyPoint
        (fun i ↦
          MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
            (point z)
            (PolynomialCode.decode
              (residualCode q b
                (residualBlockEmbedding a i)))) =
      fun i ↦
        linkedJacobiResidual
          (LinkedJacobiPolynomialCode.residualIndex i)
          (z.linked a) := by
  simpa only [eval_residualCode_residualBlockEmbedding] using
    LinkedJacobiPolynomialCode.complexifyPoint_eval_realResidualCode
      (z.linked a)

/-- All scalar residual coordinates vanish exactly when every named
complex residual vanishes in every linked block. -/
theorem forall_eval_residualCode_eq_zero_iff
    (z : ControllerProductLinkedJacobiFamilyState q b) :
    (∀ k,
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (point z)
        (PolynomialCode.decode (residualCode q b k)) = 0) ↔
      ∀ a (r : LinkedJacobiResidualIndex),
        linkedJacobiResidual r (z.linked a) = 0 := by
  constructor
  · intro h a
    apply
      (LinkedJacobiPolynomialCode.forall_eval_realResidualCode_eq_zero_iff
        (z.linked a)).1
    intro i
    simpa only [eval_residualCode_residualBlockEmbedding] using
      h (residualBlockEmbedding a i)
  · intro h k
    obtain ⟨⟨a, i⟩, rfl⟩ := finProdFinEquiv.surjective k
    have ha :=
      (LinkedJacobiPolynomialCode.forall_eval_realResidualCode_eq_zero_iff
        (z.linked a)).2 (h a)
    change
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
          (point z)
          (PolynomialCode.decode
            (residualCode q b
              (residualBlockEmbedding a i))) = 0
    rw [eval_residualCode_residualBlockEmbedding]
    exact ha i

/-- Ambient version of simultaneous-vanishing semantics.  No controller
circle equation or residual hypothesis is assumed. -/
theorem forall_eval_residualCode_eq_zero_iff_arbitrary
    (x :
      Fin
          (ControllerProductLinkedJacobiFamilyPolynomialCode.dimension q b) →
        ℝ) :
    (∀ k,
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (residualCode q b k)) = 0) ↔
      ∀ a (r : LinkedJacobiResidualIndex),
        linkedJacobiResidual r
          ((ControllerProductLinkedJacobiFamilyPolynomialCode.state x).linked
            a) = 0 := by
  have h :=
    forall_eval_residualCode_eq_zero_iff
      (ControllerProductLinkedJacobiFamilyPolynomialCode.state x)
  simpa using h

/-! ## Degree ledgers -/

/-- Every residual is independent of controller coordinates and has degree
at most four in the complete linked-family block. -/
theorem residualCode_termsBidegreeLE :
    ∀ k,
      PolynomialBlockCode.TermsBidegreeLE 0 4
        (residualCode q b k) := by
  intro k
  obtain ⟨⟨a, i⟩, rfl⟩ := finProdFinEquiv.surjective k
  rw [show
    finProdFinEquiv (a, i) = residualBlockEmbedding a i by rfl,
    residualCode_residualBlockEmbedding]
  exact
    PolynomialBlockCode.termsBidegreeLE_right
      (PolynomialFiniteProductCode.termsDegreeLE_lift
        (LinkedJacobiPolynomialCode.realResidualCode_termsDegreeLE i))

/-- The ordinary raw degree of every family residual is at most four,
independently of `q` and `b`. -/
theorem residualCode_termsDegreeLE :
    ∀ k, PolynomialCode.TermsDegreeLE 4 (residualCode q b k) := by
  intro k
  obtain ⟨⟨a, i⟩, rfl⟩ := finProdFinEquiv.surjective k
  rw [show
    finProdFinEquiv (a, i) = residualBlockEmbedding a i by rfl,
    residualCode_residualBlockEmbedding]
  exact
    PolynomialCode.termsDegreeLE_injectVariables _
      (PolynomialFiniteProductCode.termsDegreeLE_lift
        (LinkedJacobiPolynomialCode.realResidualCode_termsDegreeLE i))

/-! ## Effectivity -/

/-- Indexed access to the fixed finite residual family is primitive
recursive for every fixed `q` and `b`. -/
theorem residualCode_primrec :
    Primrec (residualCode q b) :=
  Primrec.dom_finite _

/-- Indexed access to the residual family is computable. -/
theorem residualCode_computable :
    Computable (residualCode q b) :=
  residualCode_primrec.to_comp

end ControllerProductLinkedJacobiFamilyResidualCode

end HGAS.Modular
