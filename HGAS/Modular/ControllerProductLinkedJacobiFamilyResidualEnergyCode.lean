import HGAS.Modular.ControllerProductLinkedJacobiFamilyResidualCode
import Mathlib.Tactic

/-!
# Nonnegative validity energies for a finite linked-Jacobi family

The scalar real and imaginary residual coordinates are useful for exact
algebraic semantics, but their invariant-measure averages can cancel.  The
selector argument needs nonnegative observables.  For every one of the ten
complex residuals in every linked block, this module therefore compiles

```
                         (Re R)² + (Im R)² = ‖R‖².
```

There are `10b` such observables.  Their pointwise nonnegativity means that
zero integral forces zero almost everywhere; their simultaneous pointwise
vanishing is exactly the complete linked-Jacobi residual condition.  The
price is the expected degree doubling: the energy codes have linked degree
at most eight.  This still fits the sharp affine clearing exponent used by
the mixed compactification.
-/

namespace HGAS.Modular

open HGAS

namespace ControllerProductLinkedJacobiFamilyResidualEnergyCode

open ControllerProductLinkedJacobiFamilyPolynomialCode
open ControllerProductLinkedJacobiFamilyResidualCode

variable {q b : ℕ}

/-- One nonnegative energy for each of the ten complex residuals. -/
abbrev localEnergyDimension : ℕ := 10

/-- Ten residual energies for each of the `b` linked blocks. -/
abbrev energyDimension (b : ℕ) : ℕ :=
  b * localEnergyDimension

/-- Inject the ten energy coordinates of linked block `a` into the
flattened energy family. -/
def energyBlockEmbedding (a : Fin b) :
    Fin localEnergyDimension ↪ Fin (energyDimension b) :=
  PolynomialFiniteProductCode.blockEmbedding a

/-- The local polynomial `(Re Rᵢ)² + (Im Rᵢ)²`. -/
def localResidualEnergyCode
    (i : Fin localEnergyDimension) :
    PolynomialCode localLinkedRealDimension :=
  let re :=
    LinkedJacobiPolynomialCode.realResidualCode
      (ComplexCoordinates.realIndex i)
  let im :=
    LinkedJacobiPolynomialCode.realResidualCode
      (ComplexCoordinates.imagIndex i)
  PolynomialCode.add
    (PolynomialCode.mul re re)
    (PolynomialCode.mul im im)

/-- Lift every local residual energy into the full common-controller
finite-family source. -/
def residualEnergyCode
    (q b : ℕ) :
    Fin (energyDimension b) →
      PolynomialCode
        (ControllerProductLinkedJacobiFamilyPolynomialCode.dimension q b) :=
  fun k ↦
    let ai := finProdFinEquiv.symm k
    PolynomialBlockCode.right
      (m := controllerDimension q)
      (PolynomialFiniteProductCode.lift ai.1
        (localResidualEnergyCode ai.2))

@[simp]
theorem residualEnergyCode_energyBlockEmbedding
    (q : ℕ) (a : Fin b) (i : Fin localEnergyDimension) :
    residualEnergyCode q b (energyBlockEmbedding a i) =
      PolynomialBlockCode.right
        (m := controllerDimension q)
        (PolynomialFiniteProductCode.lift a
          (localResidualEnergyCode i)) := by
  unfold residualEnergyCode energyBlockEmbedding
  rw [
    PolynomialFiniteProductCode.finProdFinEquiv_symm_blockEmbedding]

/-! ## Exact semantics and positivity -/

/-- Exact local evaluation: the code is the squared complex norm of the
named residual. -/
@[simp]
theorem eval_localResidualEnergyCode
    (z : LinkedJacobiState ℂ)
    (i : Fin localEnergyDimension) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (ComplexCoordinates.realifyPoint
          (LinkedJacobiPolynomialCode.point z))
        (PolynomialCode.decode (localResidualEnergyCode i)) =
      Complex.normSq
        (linkedJacobiResidual
          (LinkedJacobiPolynomialCode.residualIndex i) z) := by
  have hres :=
    LinkedJacobiPolynomialCode.eval_residualCode z i
  have hre := congrArg Complex.re hres
  have him := congrArg Complex.im hres
  simp only [ComplexPolynomialCode.eval,
    ComplexPolynomialCode.evalReal] at hre him
  simp only [localResidualEnergyCode,
    LinkedJacobiPolynomialCode.realResidualCode,
    ComplexPolynomialFamilyCode.realify_realIndex,
    ComplexPolynomialFamilyCode.realify_imagIndex,
    PolynomialCode.decode_add_code,
    PolynomialCode.decode_mul_code, map_add, map_mul,
    Complex.normSq_apply]
  rw [hre, him]

/-- Exact family evaluation at one block and one named residual. -/
@[simp]
theorem eval_residualEnergyCode_energyBlockEmbedding
    (z : ControllerProductLinkedJacobiFamilyState q b)
    (a : Fin b) (i : Fin localEnergyDimension) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (point z)
        (PolynomialCode.decode
          (residualEnergyCode q b (energyBlockEmbedding a i))) =
      Complex.normSq
        (linkedJacobiResidual
          (LinkedJacobiPolynomialCode.residualIndex i)
          (z.linked a)) := by
  rw [residualEnergyCode_energyBlockEmbedding, point,
    PolynomialBlockCode.eval₂Hom_right,
    PolynomialFiniteProductCode.eval₂Hom_lift]
  simp [linkedFamilyPoint]

/-- Exact evaluation at an arbitrary flattened energy index. -/
@[simp]
theorem eval_residualEnergyCode
    (z : ControllerProductLinkedJacobiFamilyState q b)
    (k : Fin (energyDimension b)) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (point z)
        (PolynomialCode.decode (residualEnergyCode q b k)) =
      let ai := finProdFinEquiv.symm k
      Complex.normSq
        (linkedJacobiResidual
          (LinkedJacobiPolynomialCode.residualIndex ai.2)
          (z.linked ai.1)) := by
  obtain ⟨⟨a, i⟩, rfl⟩ := finProdFinEquiv.surjective k
  simpa [energyBlockEmbedding] using
    eval_residualEnergyCode_energyBlockEmbedding z a i

/-- Every compiled residual energy is pointwise nonnegative. -/
theorem eval_residualEnergyCode_nonneg
    (z : ControllerProductLinkedJacobiFamilyState q b)
    (k : Fin (energyDimension b)) :
    0 ≤
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (point z)
        (PolynomialCode.decode (residualEnergyCode q b k)) := by
  obtain ⟨⟨a, i⟩, rfl⟩ := finProdFinEquiv.surjective k
  change
    0 ≤
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (point z)
        (PolynomialCode.decode
          (residualEnergyCode q b (energyBlockEmbedding a i)))
  rw [eval_residualEnergyCode_energyBlockEmbedding]
  exact Complex.normSq_nonneg _

/-- Simultaneous vanishing of the `10b` nonnegative energy codes is
equivalent to vanishing of every named complex residual in every block. -/
theorem forall_eval_residualEnergyCode_eq_zero_iff
    (z : ControllerProductLinkedJacobiFamilyState q b) :
    (∀ k,
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (point z)
        (PolynomialCode.decode (residualEnergyCode q b k)) = 0) ↔
      ∀ a (r : LinkedJacobiResidualIndex),
        linkedJacobiResidual r (z.linked a) = 0 := by
  constructor
  · intro h a r
    obtain ⟨i, rfl⟩ :=
      LinkedJacobiPolynomialCode.residualIndex_bijective.2 r
    have hi := h (energyBlockEmbedding a i)
    rw [eval_residualEnergyCode_energyBlockEmbedding,
      Complex.normSq_eq_zero] at hi
    exact hi
  · intro h k
    obtain ⟨⟨a, i⟩, rfl⟩ := finProdFinEquiv.surjective k
    change
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
          (point z)
          (PolynomialCode.decode
            (residualEnergyCode q b
              (energyBlockEmbedding a i))) = 0
    rw [eval_residualEnergyCode_energyBlockEmbedding,
      Complex.normSq_eq_zero]
    exact h a (LinkedJacobiPolynomialCode.residualIndex i)

/-- Ambient simultaneous-vanishing semantics, with no controller-circle
or residual hypothesis. -/
theorem forall_eval_residualEnergyCode_eq_zero_iff_arbitrary
    (x :
      Fin
          (ControllerProductLinkedJacobiFamilyPolynomialCode.dimension q b) →
        ℝ) :
    (∀ k,
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (residualEnergyCode q b k)) = 0) ↔
      ∀ a (r : LinkedJacobiResidualIndex),
        linkedJacobiResidual r
          ((ControllerProductLinkedJacobiFamilyPolynomialCode.state x).linked
            a) = 0 := by
  have h :=
    forall_eval_residualEnergyCode_eq_zero_iff
      (ControllerProductLinkedJacobiFamilyPolynomialCode.state x)
  simpa using h

/-! ## Degree and effectivity -/

/-- A local squared residual has raw degree at most eight. -/
theorem localResidualEnergyCode_termsDegreeLE :
    ∀ i,
      PolynomialCode.TermsDegreeLE 8
        (localResidualEnergyCode i) := by
  intro i
  have hre :=
    LinkedJacobiPolynomialCode.realResidualCode_termsDegreeLE
      (ComplexCoordinates.realIndex i)
  have him :=
    LinkedJacobiPolynomialCode.realResidualCode_termsDegreeLE
      (ComplexCoordinates.imagIndex i)
  simpa [localResidualEnergyCode] using
    PolynomialCode.termsDegreeLE_add
      (PolynomialCode.termsDegreeLE_mul hre hre)
      (PolynomialCode.termsDegreeLE_mul him him)

/-- Family residual energies have controller/linked bidegree `(0,8)`. -/
theorem residualEnergyCode_termsBidegreeLE :
    ∀ k,
      PolynomialBlockCode.TermsBidegreeLE 0 8
        (residualEnergyCode q b k) := by
  intro k
  obtain ⟨⟨a, i⟩, rfl⟩ := finProdFinEquiv.surjective k
  rw [show
    finProdFinEquiv (a, i) = energyBlockEmbedding a i by rfl,
    residualEnergyCode_energyBlockEmbedding]
  exact
    PolynomialBlockCode.termsBidegreeLE_right
      (PolynomialFiniteProductCode.termsDegreeLE_lift
        (localResidualEnergyCode_termsDegreeLE i))

/-- Ordinary total degree is at most eight, uniformly in `q` and `b`. -/
theorem residualEnergyCode_termsDegreeLE :
    ∀ k,
      PolynomialCode.TermsDegreeLE 8
        (residualEnergyCode q b k) := by
  intro k
  obtain ⟨⟨a, i⟩, rfl⟩ := finProdFinEquiv.surjective k
  rw [show
    finProdFinEquiv (a, i) = energyBlockEmbedding a i by rfl,
    residualEnergyCode_energyBlockEmbedding]
  exact
    PolynomialCode.termsDegreeLE_injectVariables _
      (PolynomialFiniteProductCode.termsDegreeLE_lift
        (localResidualEnergyCode_termsDegreeLE i))

/-- Indexed access to all residual-energy codes is primitive recursive for
fixed `q` and `b`. -/
theorem residualEnergyCode_primrec :
    Primrec (residualEnergyCode q b) :=
  Primrec.dom_finite _

/-- Indexed access to all residual-energy codes is computable. -/
theorem residualEnergyCode_computable :
    Computable (residualEnergyCode q b) :=
  residualEnergyCode_primrec.to_comp

/-! ## One aggregate nonnegative validity coordinate -/

/-- Sum of all `10b` squared residual norms.  One such coordinate is enough
to force every linked validity residual, because every summand is
nonnegative. -/
def totalResidualEnergyCode
    (q b : ℕ) :
    PolynomialCode
      (ControllerProductLinkedJacobiFamilyPolynomialCode.dimension q b) :=
  PolynomialCode.sumCodes
    (List.ofFn (residualEnergyCode q b))

/-- Exact evaluation of the aggregate energy. -/
@[simp]
theorem eval_totalResidualEnergyCode
    (z : ControllerProductLinkedJacobiFamilyState q b) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (point z)
        (PolynomialCode.decode (totalResidualEnergyCode q b)) =
      ∑ k : Fin (energyDimension b),
        Complex.normSq
          (linkedJacobiResidual
            (LinkedJacobiPolynomialCode.residualIndex
              (finProdFinEquiv.symm k).2)
            (z.linked (finProdFinEquiv.symm k).1)) := by
  rw [totalResidualEnergyCode, PolynomialCode.decode_sumCodes,
    List.map_ofFn, List.sum_ofFn, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact eval_residualEnergyCode z k

/-- The aggregate residual energy is pointwise nonnegative. -/
theorem eval_totalResidualEnergyCode_nonneg
    (z : ControllerProductLinkedJacobiFamilyState q b) :
    0 ≤
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (point z)
        (PolynomialCode.decode (totalResidualEnergyCode q b)) := by
  rw [eval_totalResidualEnergyCode]
  exact Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _

/-- The single aggregate energy vanishes exactly when every named
residual vanishes in every linked block. -/
theorem eval_totalResidualEnergyCode_eq_zero_iff
    (z : ControllerProductLinkedJacobiFamilyState q b) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (point z)
        (PolynomialCode.decode (totalResidualEnergyCode q b)) = 0 ↔
      ∀ a (r : LinkedJacobiResidualIndex),
        linkedJacobiResidual r (z.linked a) = 0 := by
  constructor
  · intro h
    apply (forall_eval_residualEnergyCode_eq_zero_iff z).1
    intro k
    have hsum :
        ∑ j : Fin (energyDimension b),
          Complex.normSq
            (linkedJacobiResidual
              (LinkedJacobiPolynomialCode.residualIndex
                (finProdFinEquiv.symm j).2)
              (z.linked (finProdFinEquiv.symm j).1)) = 0 := by
      rw [← eval_totalResidualEnergyCode]
      exact h
    have hk :
        Complex.normSq
            (linkedJacobiResidual
              (LinkedJacobiPolynomialCode.residualIndex
                (finProdFinEquiv.symm k).2)
              (z.linked (finProdFinEquiv.symm k).1)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ ↦ Complex.normSq_nonneg _)).1
          hsum k (Finset.mem_univ k)
    rw [eval_residualEnergyCode]
    exact hk
  · intro h
    rw [eval_totalResidualEnergyCode]
    apply Finset.sum_eq_zero
    intro k _
    exact Complex.normSq_eq_zero.2
      (h (finProdFinEquiv.symm k).1
        (LinkedJacobiPolynomialCode.residualIndex
          (finProdFinEquiv.symm k).2))

/-- The aggregate code retains the uniform degree-eight bound. -/
theorem totalResidualEnergyCode_termsDegreeLE :
    PolynomialCode.TermsDegreeLE 8
      (totalResidualEnergyCode q b) := by
  apply PolynomialCode.termsDegreeLE_sumCodes
  intro p hp
  rw [List.mem_ofFn] at hp
  obtain ⟨k, rfl⟩ := hp
  exact residualEnergyCode_termsDegreeLE k

/-- The aggregate validity coordinate is fixed finite syntax and hence is
primitive recursive as a constant compiler output. -/
theorem totalResidualEnergyCode_primrec :
    Primrec
      (fun (_ : Unit) ↦ totalResidualEnergyCode q b) :=
  Primrec.const _

theorem totalResidualEnergyCode_computable :
    Computable
      (fun (_ : Unit) ↦ totalResidualEnergyCode q b) :=
  totalResidualEnergyCode_primrec.to_comp

end ControllerProductLinkedJacobiFamilyResidualEnergyCode

end HGAS.Modular
