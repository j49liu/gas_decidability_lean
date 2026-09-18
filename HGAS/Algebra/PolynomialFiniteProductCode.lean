import HGAS.Algebra.PolynomialVariableEmbedding
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Finite block products of polynomial vector-field codes

This file packages a fixed finite family

```
F : Fin q → PolynomialFieldCode n
```

of `n`-dimensional rational polynomial vector fields into a single
block-diagonal field on `q * n` coordinates.  The coordinate convention is
the canonical equivalence

```
finProdFinEquiv : Fin q × Fin n ≃ Fin (q * n).
```

Thus `finProdFinEquiv (a, i)` is coordinate `i` of block `a`.  Every input
polynomial is transported by an injective renaming of its variables, so no
algebraic expansion or normalization is involved.

The module records all interfaces needed by later compilers:

* canonical flattening and unflattening of points, with both round trips;
* exact evaluation at an arbitrary ambient point;
* exact block-diagonal semantics for the realized real vector field;
* lifting of scalar polynomial families;
* exact preservation of uniform raw monomial-degree bounds; and
* primitive-recursive, hence computable, compilation for fixed `q` and `n`.

The construction also works in the degenerate cases `q = 0` or `n = 0`.
-/

namespace HGAS

namespace PolynomialFiniteProductCode

variable {q n : ℕ}

/-! ## Coordinate maps -/

/-- Inject the local coordinates of block `a` into the flattened product. -/
def blockEmbedding (a : Fin q) : Fin n ↪ Fin (q * n) where
  toFun i := finProdFinEquiv (a, i)
  inj' := by
    intro i j hij
    exact congrArg Prod.snd (finProdFinEquiv.injective hij)

@[simp]
theorem finProdFinEquiv_symm_blockEmbedding
    (a : Fin q) (i : Fin n) :
    finProdFinEquiv.symm (blockEmbedding a i) = (a, i) :=
  finProdFinEquiv.symm_apply_apply (a, i)

/-- Flatten a family of `q` local `n`-vectors into one `q * n`-vector. -/
def flattenPoint
    {R : Type*} (x : Fin q → Fin n → R) :
    Fin (q * n) → R :=
  fun k =>
    x (finProdFinEquiv.symm k).1
      (finProdFinEquiv.symm k).2

/-- Recover the local vectors of a flattened `q * n`-vector. -/
def unflattenPoint
    {R : Type*} (x : Fin (q * n) → R) :
    Fin q → Fin n → R :=
  fun a i => x (blockEmbedding a i)

@[simp]
theorem flattenPoint_blockEmbedding
    {R : Type*} (x : Fin q → Fin n → R)
    (a : Fin q) (i : Fin n) :
    flattenPoint x (blockEmbedding a i) = x a i := by
  change
    x (finProdFinEquiv.symm (blockEmbedding a i)).1
        (finProdFinEquiv.symm (blockEmbedding a i)).2 =
      x a i
  rw [finProdFinEquiv_symm_blockEmbedding]

@[simp]
theorem unflattenPoint_apply
    {R : Type*} (x : Fin (q * n) → R)
    (a : Fin q) (i : Fin n) :
    unflattenPoint x a i = x (blockEmbedding a i) :=
  rfl

@[simp]
theorem unflattenPoint_flattenPoint
    {R : Type*} (x : Fin q → Fin n → R) :
    unflattenPoint (flattenPoint x) = x := by
  funext a i
  simp

@[simp]
theorem flattenPoint_unflattenPoint
    {R : Type*} (x : Fin (q * n) → R) :
    flattenPoint (unflattenPoint x) = x := by
  funext k
  obtain ⟨⟨a, i⟩, rfl⟩ := finProdFinEquiv.surjective k
  rw [flattenPoint, finProdFinEquiv.symm_apply_apply]
  rfl

@[simp]
theorem flattenPoint_comp_blockEmbedding
    {R : Type*} (x : Fin q → Fin n → R)
    (a : Fin q) :
    flattenPoint x ∘ blockEmbedding a = x a := by
  funext i
  simp

/-! ## Polynomial and scalar-family lifting -/

/-- Regard a polynomial in the local variables of block `a` as a polynomial
in all `q * n` ambient variables. -/
def lift
    (a : Fin q) (p : PolynomialCode n) :
    PolynomialCode (q * n) :=
  PolynomialCode.injectVariables (blockEmbedding a) p

@[simp]
theorem decode_lift
    (a : Fin q) (p : PolynomialCode n) :
    PolynomialCode.decode (lift a p) =
      MvPolynomial.rename (blockEmbedding a)
        (PolynomialCode.decode p) := by
  simp [lift]

/-- Evaluation of a lifted polynomial at an arbitrary ambient point only
sees the coordinates of its own block. -/
@[simp]
theorem eval₂Hom_lift
    {R : Type*} [CommSemiring R] [Algebra ℚ R]
    (a : Fin q) (p : PolynomialCode n)
    (x : Fin (q * n) → R) :
    MvPolynomial.eval₂Hom (algebraMap ℚ R) x
        (PolynomialCode.decode (lift a p)) =
      MvPolynomial.eval₂Hom (algebraMap ℚ R)
        (unflattenPoint x a)
        (PolynomialCode.decode p) := by
  rw [lift, PolynomialCode.eval₂Hom_decode_injectVariables]
  rfl

/-- Evaluation at a point assembled from local blocks recovers the original
local evaluation. -/
@[simp]
theorem eval₂Hom_lift_flattenPoint
    {R : Type*} [CommSemiring R] [Algebra ℚ R]
    (a : Fin q) (p : PolynomialCode n)
    (x : Fin q → Fin n → R) :
    MvPolynomial.eval₂Hom (algebraMap ℚ R) (flattenPoint x)
        (PolynomialCode.decode (lift a p)) =
      MvPolynomial.eval₂Hom (algebraMap ℚ R) (x a)
        (PolynomialCode.decode p) := by
  rw [eval₂Hom_lift]
  simp

/-- Lift one scalar polynomial for each block into the common ambient
coordinate space. -/
def liftScalarFamily
    (P : Fin q → PolynomialCode n) :
    Fin q → PolynomialCode (q * n) :=
  fun a => lift a (P a)

@[simp]
theorem liftScalarFamily_apply
    (P : Fin q → PolynomialCode n) (a : Fin q) :
    liftScalarFamily P a = lift a (P a) :=
  rfl

@[simp]
theorem eval₂Hom_liftScalarFamily
    {R : Type*} [CommSemiring R] [Algebra ℚ R]
    (P : Fin q → PolynomialCode n)
    (x : Fin (q * n) → R) (a : Fin q) :
    MvPolynomial.eval₂Hom (algebraMap ℚ R) x
        (PolynomialCode.decode (liftScalarFamily P a)) =
      MvPolynomial.eval₂Hom (algebraMap ℚ R)
        (unflattenPoint x a)
        (PolynomialCode.decode (P a)) :=
  eval₂Hom_lift a (P a) x

/-! ## The block-diagonal field -/

/-- Pack a finite family of equal-dimensional polynomial vector fields into
one block-diagonal field. -/
def field
    (F : Fin q → PolynomialFieldCode n) :
    PolynomialFieldCode (q * n) :=
  fun k =>
    let ai := finProdFinEquiv.symm k
    lift ai.1 (F ai.1 ai.2)

@[simp]
theorem field_blockEmbedding
    (F : Fin q → PolynomialFieldCode n)
    (a : Fin q) (i : Fin n) :
    field F (blockEmbedding a i) = lift a (F a i) := by
  change
    lift (finProdFinEquiv.symm (blockEmbedding a i)).1
        (F (finProdFinEquiv.symm (blockEmbedding a i)).1
          (finProdFinEquiv.symm (blockEmbedding a i)).2) =
      lift a (F a i)
  rw [finProdFinEquiv_symm_blockEmbedding]

@[simp]
theorem decode_field_blockEmbedding
    (F : Fin q → PolynomialFieldCode n)
    (a : Fin q) (i : Fin n) :
    PolynomialCode.decode
        (field F (blockEmbedding a i)) =
      MvPolynomial.rename (blockEmbedding a)
        (PolynomialCode.decode (F a i)) := by
  simp

/-- Componentwise semantics at an arbitrary ambient point. -/
@[simp]
theorem eval₂Hom_field_blockEmbedding
    {R : Type*} [CommSemiring R] [Algebra ℚ R]
    (F : Fin q → PolynomialFieldCode n)
    (x : Fin (q * n) → R)
    (a : Fin q) (i : Fin n) :
    MvPolynomial.eval₂Hom (algebraMap ℚ R) x
        (PolynomialCode.decode
          (field F (blockEmbedding a i))) =
      MvPolynomial.eval₂Hom (algebraMap ℚ R)
        (unflattenPoint x a)
        (PolynomialCode.decode (F a i)) := by
  rw [field_blockEmbedding, eval₂Hom_lift]

/-- Exact arbitrary-point semantics of the packed real vector field.  Each
output block evaluates only the corresponding input block. -/
@[simp]
theorem realize_field
    (F : Fin q → PolynomialFieldCode n)
    (x : Fin (q * n) → ℝ) :
    PolynomialFieldCode.realize (field F) x =
      flattenPoint
        (fun a =>
          PolynomialFieldCode.realize (F a)
            (unflattenPoint x a)) := by
  funext k
  obtain ⟨⟨a, i⟩, rfl⟩ := finProdFinEquiv.surjective k
  change
    PolynomialFieldCode.realize (field F) x
        (blockEmbedding a i) =
      flattenPoint
        (fun a =>
          PolynomialFieldCode.realize (F a)
            (unflattenPoint x a))
        (blockEmbedding a i)
  rw [PolynomialFieldCode.realize_apply,
    eval₂Hom_field_blockEmbedding,
    flattenPoint_blockEmbedding,
    PolynomialFieldCode.realize_apply]

/-- On canonically flattened input, the packed field is literally the
flattening of the independently realized blocks. -/
@[simp]
theorem realize_field_flattenPoint
    (F : Fin q → PolynomialFieldCode n)
    (x : Fin q → Fin n → ℝ) :
    PolynomialFieldCode.realize (field F) (flattenPoint x) =
      flattenPoint
        (fun a => PolynomialFieldCode.realize (F a) (x a)) := by
  rw [realize_field]
  simp

/-! ## Exact raw-degree preservation -/

/-- Variable injection preserves, rather than merely increases, every raw
monomial-degree bound. -/
theorem termsDegreeLE_lift_iff
    {D : ℕ} (a : Fin q) (p : PolynomialCode n) :
    PolynomialCode.TermsDegreeLE D (lift a p) ↔
      PolynomialCode.TermsDegreeLE D p := by
  constructor
  · intro hp t ht
    have hmem :
        PolynomialCode.injectVariablesTerm
            (blockEmbedding a) t ∈
          lift a p := by
      rw [lift, PolynomialCode.injectVariables, List.mem_map]
      exact ⟨t, ht, rfl⟩
    simpa only [PolynomialCode.injectVariablesTerm,
      ExponentCode.totalDegree_injectVariables] using
        hp
          (PolynomialCode.injectVariablesTerm
            (blockEmbedding a) t)
          hmem
  · exact PolynomialCode.termsDegreeLE_injectVariables
      (blockEmbedding a)

theorem termsDegreeLE_lift
    {D : ℕ} {a : Fin q} {p : PolynomialCode n}
    (hp : PolynomialCode.TermsDegreeLE D p) :
    PolynomialCode.TermsDegreeLE D (lift a p) :=
  (termsDegreeLE_lift_iff a p).2 hp

theorem termsDegreeLE_liftScalarFamily_iff
    {D : ℕ} (P : Fin q → PolynomialCode n) :
    (∀ a, PolynomialCode.TermsDegreeLE D
        (liftScalarFamily P a)) ↔
      ∀ a, PolynomialCode.TermsDegreeLE D (P a) := by
  simp only [liftScalarFamily_apply, termsDegreeLE_lift_iff]

/-- A uniform raw degree bound holds for the packed field exactly when it
holds for every coordinate of every input block. -/
theorem field_termsDegreeLE_iff
    {D : ℕ} (F : Fin q → PolynomialFieldCode n) :
    (∀ k, PolynomialCode.TermsDegreeLE D (field F k)) ↔
      ∀ a i, PolynomialCode.TermsDegreeLE D (F a i) := by
  constructor
  · intro h a i
    exact
      (termsDegreeLE_lift_iff a (F a i)).1
        (by simpa using h (blockEmbedding a i))
  · intro h k
    obtain ⟨⟨a, i⟩, rfl⟩ := finProdFinEquiv.surjective k
    change PolynomialCode.TermsDegreeLE D
      (field F (blockEmbedding a i))
    rw [field_blockEmbedding]
    exact termsDegreeLE_lift (h a i)

theorem field_termsDegreeLE
    {D : ℕ} {F : Fin q → PolynomialFieldCode n}
    (hF : ∀ a i,
      PolynomialCode.TermsDegreeLE D (F a i)) :
    ∀ k, PolynomialCode.TermsDegreeLE D (field F k) :=
  (field_termsDegreeLE_iff F).2 hF

/-! ## Effective compilation -/

theorem lift_primrec (a : Fin q) :
    Primrec (lift a :
      PolynomialCode n → PolynomialCode (q * n)) :=
  PolynomialCode.injectVariables_primrec (blockEmbedding a)

/-- Lifting a finite scalar family block by block is primitive recursive for
fixed dimensions. -/
theorem liftScalarFamily_primrec :
    Primrec (liftScalarFamily :
      (Fin q → PolynomialCode n) →
        (Fin q → PolynomialCode (q * n))) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro a
  exact
    (lift_primrec a).comp
      (Primrec.fin_app.comp Primrec.id (Primrec.const a))

theorem liftScalarFamily_computable :
    Computable (liftScalarFamily :
      (Fin q → PolynomialCode n) →
        (Fin q → PolynomialCode (q * n))) :=
  liftScalarFamily_primrec.to_comp

/-- The complete finite-product field compiler is primitive recursive for
fixed `q` and `n`. -/
theorem field_primrec :
    Primrec (field :
      (Fin q → PolynomialFieldCode n) →
        PolynomialFieldCode (q * n)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro k
  obtain ⟨⟨a, i⟩, rfl⟩ := finProdFinEquiv.surjective k
  exact
    ((lift_primrec a).comp
      (Primrec.fin_app.comp
        (Primrec.fin_app.comp Primrec.id
          (Primrec.const a))
        (Primrec.const i))).of_eq fun F => by
          exact (field_blockEmbedding F a i).symm

theorem field_computable :
    Computable (field :
      (Fin q → PolynomialFieldCode n) →
        PolynomialFieldCode (q * n)) :=
  field_primrec.to_comp

end PolynomialFiniteProductCode

end HGAS
