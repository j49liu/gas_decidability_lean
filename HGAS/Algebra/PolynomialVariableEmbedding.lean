import HGAS.Algebra.ComplexPolynomialComputability
import HGAS.Algebra.ComplexPolynomialDegrees
import Mathlib.Tactic

/-!
# Injective changes of variables for finite polynomial codes

Polynomial source blocks are most useful when they can be assembled without
re-expanding every coordinate formula in the larger ambient space.  This file
provides the required reusable operation.

If `f : Fin m ↪ Fin n` is an injection, `PolynomialCode.injectVariables f p`
regards a polynomial in `m` variables as a polynomial in `n` variables by
placing its variables at the coordinates selected by `f`.  The construction is
performed directly on the finite sparse syntax:

* exponents are transported along `f`;
* coefficients and the raw term order are unchanged;
* decoding is exactly `MvPolynomial.rename f`;
* evaluation is substitution by `x ∘ f`;
* raw monomial degree is preserved; and
* for fixed finite dimensions and a fixed injection, the operation is
  primitive recursive.

The second half lifts the construction to complex polynomial codes.  Here the
real and imaginary coordinates must both be transported, and the proof checks
that this agrees exactly with complex-coordinate evaluation.  Finally,
`ComplexPolynomialBlockCode` specializes the generic operation to the left and
right summands of `Fin (m + p)` and combines two independent complex polynomial
vector fields into one block-diagonal field.
-/

namespace HGAS

open MvPolynomial

namespace ExponentCode

variable {m n : ℕ}

/-- Transport an exponent vector along an injective map of variable names.

The finite sum is deliberately used instead of a choice of inverse.  It is
executable, and injectivity guarantees that at most one summand is nonzero. -/
def injectVariables
    (f : Fin m ↪ Fin n) (e : ExponentCode m) :
    ExponentCode n :=
  fun q ↦ ∑ i : Fin m, if f i = q then e i else 0

@[simp]
theorem injectVariables_apply
    (f : Fin m ↪ Fin n) (e : ExponentCode m) (i : Fin m) :
    injectVariables f e (f i) = e i := by
  simp [injectVariables, f.injective.eq_iff]

theorem injectVariables_eq_zero_of_not_mem_range
    (f : Fin m ↪ Fin n) (e : ExponentCode m) (q : Fin n)
    (hq : q ∉ Set.range f) :
    injectVariables f e q = 0 := by
  simp only [injectVariables]
  apply Finset.sum_eq_zero
  intro i hi
  simp only [ite_eq_right_iff]
  intro hfi
  exact (hq ⟨i, hfi⟩).elim

/-- Decoding transported exponents is `Finsupp.mapDomain`. -/
theorem decode_injectVariables
    (f : Fin m ↪ Fin n) (e : ExponentCode m) :
    decode (injectVariables f e) =
      (decode e).mapDomain f := by
  ext q
  by_cases hq : q ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hq
    rw [Finsupp.mapDomain_apply f.injective]
    simp [ExponentCode.decode]
  · rw [Finsupp.mapDomain_notin_range]
    · simp [ExponentCode.decode,
        injectVariables_eq_zero_of_not_mem_range f e q hq]
    · simpa using hq

/-- Transporting variables preserves total monomial degree exactly. -/
theorem totalDegree_injectVariables
    (f : Fin m ↪ Fin n) (e : ExponentCode m) :
    totalDegree (injectVariables f e) = totalDegree e := by
  simp only [totalDegree, List.sum_ofFn, injectVariables]
  rw [Finset.sum_comm]
  simp

/-- For fixed finite dimensions and a fixed injection, exponent transport is
primitive recursive. -/
theorem injectVariables_primrec
    (f : Fin m ↪ Fin n) :
    Primrec (injectVariables f :
      ExponentCode m → ExponentCode n) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro q
  by_cases hq : q ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hq
    exact
      (Primrec.fin_app.comp Primrec.id (Primrec.const i)).of_eq
        fun e ↦ (injectVariables_apply f e i).symm
  · exact
      (Primrec.const 0).of_eq fun e ↦
        (injectVariables_eq_zero_of_not_mem_range f e q hq).symm

end ExponentCode

namespace PolynomialCode

variable {m n : ℕ}

/-- Transport one sparse monomial along an injection of variable names. -/
def injectVariablesTerm
    (f : Fin m ↪ Fin n)
    (t : ExponentCode m × RationalCode) :
    ExponentCode n × RationalCode :=
  (ExponentCode.injectVariables f t.1, t.2)

/-- Transport every term of a sparse polynomial along an injection of
variable names. -/
def injectVariables
    (f : Fin m ↪ Fin n) (p : PolynomialCode m) :
    PolynomialCode n :=
  p.map (injectVariablesTerm f)

@[simp]
theorem decodeTerm_injectVariablesTerm
    (f : Fin m ↪ Fin n)
    (t : ExponentCode m × RationalCode) :
    decodeTerm (injectVariablesTerm f t) =
      MvPolynomial.rename f (decodeTerm t) := by
  simp only [injectVariablesTerm, decodeTerm,
    ExponentCode.decode_injectVariables]
  exact
    (MvPolynomial.rename_monomial f
      (ExponentCode.decode t.1)
      (RationalCode.decode t.2)).symm

/-- Sparse variable transport decodes exactly to polynomial renaming. -/
@[simp]
theorem decode_injectVariables
    (f : Fin m ↪ Fin n) (p : PolynomialCode m) :
    decode (injectVariables f p) =
      MvPolynomial.rename f (decode p) := by
  induction p with
  | nil => simp [injectVariables]
  | cons t p ih =>
      change
        decodeTerm (injectVariablesTerm f t) +
            decode (injectVariables f p) =
          MvPolynomial.rename f (decodeTerm t + decode p)
      rw [decodeTerm_injectVariablesTerm, ih, map_add]

/-- Evaluation after variable transport is ordinary coordinate
substitution. -/
theorem eval₂Hom_decode_injectVariables
    {R : Type*} [CommSemiring R] [Algebra ℚ R]
    (f : Fin m ↪ Fin n) (p : PolynomialCode m)
    (x : Fin n → R) :
    MvPolynomial.eval₂Hom (algebraMap ℚ R) x
        (decode (injectVariables f p)) =
      MvPolynomial.eval₂Hom (algebraMap ℚ R) (x ∘ f)
        (decode p) := by
  rw [decode_injectVariables, MvPolynomial.eval₂Hom_rename]

/-- Variable transport preserves every raw monomial-degree bound. -/
theorem termsDegreeLE_injectVariables
    {D : ℕ} (f : Fin m ↪ Fin n) {p : PolynomialCode m}
    (hp : TermsDegreeLE D p) :
    TermsDegreeLE D (injectVariables f p) := by
  intro t ht
  rw [injectVariables, List.mem_map] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  simpa only [injectVariablesTerm,
    ExponentCode.totalDegree_injectVariables] using hp u hu

theorem injectVariablesTerm_primrec
    (f : Fin m ↪ Fin n) :
    Primrec (injectVariablesTerm f :
      (ExponentCode m × RationalCode) →
        (ExponentCode n × RationalCode)) := by
  exact Primrec.pair
    ((ExponentCode.injectVariables_primrec f).comp Primrec.fst)
    Primrec.snd

/-- For a fixed injection, sparse-polynomial variable transport is primitive
recursive. -/
theorem injectVariables_primrec
    (f : Fin m ↪ Fin n) :
    Primrec (injectVariables f :
      PolynomialCode m → PolynomialCode n) := by
  have hterm :
      Primrec₂
        (fun (_ : PolynomialCode m)
          (t : ExponentCode m × RationalCode) ↦
            injectVariablesTerm f t) :=
    (injectVariablesTerm_primrec f).comp₂ Primrec₂.right
  exact (Primrec.list_map Primrec.id hterm).of_eq fun _ ↦ rfl

end PolynomialCode

/-! ## Block sums of ordinary real polynomial fields -/

namespace PolynomialBlockCode

variable {m p : ℕ}

def leftEmbedding : Fin m ↪ Fin (m + p) where
  toFun i := finSumFinEquiv (Sum.inl i)
  inj' := finSumFinEquiv.injective.comp Sum.inl_injective

def rightEmbedding : Fin p ↪ Fin (m + p) where
  toFun i := finSumFinEquiv (Sum.inr i)
  inj' := finSumFinEquiv.injective.comp Sum.inr_injective

@[simp]
theorem finSumFinEquiv_symm_leftEmbedding (i : Fin m) :
    finSumFinEquiv.symm (leftEmbedding (p := p) i) =
      Sum.inl i :=
  finSumFinEquiv.symm_apply_apply _

@[simp]
theorem finSumFinEquiv_symm_rightEmbedding (i : Fin p) :
    finSumFinEquiv.symm (rightEmbedding (m := m) i) =
      Sum.inr i :=
  finSumFinEquiv.symm_apply_apply _

/-- Canonically flatten two finite coordinate vectors. -/
def point
    {R : Type*} (x : Fin m → R) (y : Fin p → R) :
    Fin (m + p) → R :=
  fun q ↦
    match finSumFinEquiv.symm q with
    | Sum.inl i => x i
    | Sum.inr j => y j

@[simp]
theorem point_leftEmbedding
    {R : Type*} (x : Fin m → R) (y : Fin p → R)
    (i : Fin m) :
    point x y (leftEmbedding (p := p) i) = x i := by
  simp [point]

@[simp]
theorem point_rightEmbedding
    {R : Type*} (x : Fin m → R) (y : Fin p → R)
    (j : Fin p) :
    point x y (rightEmbedding (m := m) j) = y j := by
  simp [point]

@[simp]
theorem point_comp_leftEmbedding
    {R : Type*} (x : Fin m → R) (y : Fin p → R) :
    point x y ∘ leftEmbedding (p := p) = x := by
  funext i
  simp

@[simp]
theorem point_comp_rightEmbedding
    {R : Type*} (x : Fin m → R) (y : Fin p → R) :
    point x y ∘ rightEmbedding (m := m) = y := by
  funext i
  simp

def left
    (q : PolynomialCode m) : PolynomialCode (m + p) :=
  PolynomialCode.injectVariables leftEmbedding q

def right
    (q : PolynomialCode p) : PolynomialCode (m + p) :=
  PolynomialCode.injectVariables rightEmbedding q

@[simp]
theorem eval₂Hom_left
    {R : Type*} [CommSemiring R] [Algebra ℚ R]
    (q : PolynomialCode m)
    (x : Fin m → R) (y : Fin p → R) :
    MvPolynomial.eval₂Hom (algebraMap ℚ R) (point x y)
        (PolynomialCode.decode (left (p := p) q)) =
      MvPolynomial.eval₂Hom (algebraMap ℚ R) x
        (PolynomialCode.decode q) := by
  rw [left, PolynomialCode.eval₂Hom_decode_injectVariables]
  simp

@[simp]
theorem eval₂Hom_right
    {R : Type*} [CommSemiring R] [Algebra ℚ R]
    (q : PolynomialCode p)
    (x : Fin m → R) (y : Fin p → R) :
    MvPolynomial.eval₂Hom (algebraMap ℚ R) (point x y)
        (PolynomialCode.decode (right (m := m) q)) =
      MvPolynomial.eval₂Hom (algebraMap ℚ R) y
        (PolynomialCode.decode q) := by
  rw [right, PolynomialCode.eval₂Hom_decode_injectVariables]
  simp

theorem left_primrec :
    Primrec (left (m := m) (p := p) :
      PolynomialCode m → PolynomialCode (m + p)) :=
  PolynomialCode.injectVariables_primrec leftEmbedding

theorem right_primrec :
    Primrec (right (m := m) (p := p) :
      PolynomialCode p → PolynomialCode (m + p)) :=
  PolynomialCode.injectVariables_primrec rightEmbedding

/-- Block-diagonal sum of two real rational polynomial fields. -/
def field
    (F : PolynomialFieldCode m)
    (G : PolynomialFieldCode p) :
    PolynomialFieldCode (m + p) :=
  fun q ↦
    match finSumFinEquiv.symm q with
    | Sum.inl i => left (p := p) (F i)
    | Sum.inr j => right (m := m) (G j)

@[simp]
theorem field_leftEmbedding
    (F : PolynomialFieldCode m)
    (G : PolynomialFieldCode p) (i : Fin m) :
    field F G (leftEmbedding (p := p) i) =
      left (p := p) (F i) := by
  simp [field]

@[simp]
theorem field_rightEmbedding
    (F : PolynomialFieldCode m)
    (G : PolynomialFieldCode p) (j : Fin p) :
    field F G (rightEmbedding (m := m) j) =
      right (m := m) (G j) := by
  simp [field]

@[simp]
theorem realize_field
    (F : PolynomialFieldCode m)
    (G : PolynomialFieldCode p)
    (x : Fin m → ℝ) (y : Fin p → ℝ) :
    PolynomialFieldCode.realize (field F G) (point x y) =
      point
        (PolynomialFieldCode.realize F x)
        (PolynomialFieldCode.realize G y) := by
  funext q
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective q
  · rw [show finSumFinEquiv (Sum.inl i) =
      leftEmbedding (p := p) i by rfl]
    simp [PolynomialFieldCode.realize_apply]
  · rw [show finSumFinEquiv (Sum.inr j) =
      rightEmbedding (m := m) j by rfl]
    simp [PolynomialFieldCode.realize_apply]

theorem field_primrec :
    Primrec₂ (field :
      PolynomialFieldCode m →
        PolynomialFieldCode p →
          PolynomialFieldCode (m + p)) := by
  change Primrec
    (fun FG : PolynomialFieldCode m × PolynomialFieldCode p ↦
      field FG.1 FG.2)
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro q
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective q
  · exact
      (left_primrec.comp
        (Primrec.fin_app.comp Primrec.fst
          (Primrec.const i))).of_eq fun FG ↦
            (field_leftEmbedding FG.1 FG.2 i).symm
  · exact
      (right_primrec.comp
        (Primrec.fin_app.comp Primrec.snd
          (Primrec.const j))).of_eq fun FG ↦
            (field_rightEmbedding FG.1 FG.2 j).symm

theorem field_termsDegreeLE
    {D : ℕ} {F : PolynomialFieldCode m}
    {G : PolynomialFieldCode p}
    (hF : ∀ i, PolynomialCode.TermsDegreeLE D (F i))
    (hG : ∀ j, PolynomialCode.TermsDegreeLE D (G j)) :
    ∀ q, PolynomialCode.TermsDegreeLE D (field F G q) := by
  intro q
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective q
  · change PolynomialCode.TermsDegreeLE D
      (field F G (leftEmbedding (p := p) i))
    rw [field_leftEmbedding]
    exact PolynomialCode.termsDegreeLE_injectVariables _ (hF i)
  · change PolynomialCode.TermsDegreeLE D
      (field F G (rightEmbedding (m := m) j))
    rw [field_rightEmbedding]
    exact PolynomialCode.termsDegreeLE_injectVariables _ (hG j)

end PolynomialBlockCode

namespace ComplexCoordinates

variable {m n : ℕ}

/-- An injection of complex coordinates induces the corresponding injection
of their realifications. -/
def realificationEmbedding
    (f : Fin m ↪ Fin n) :
    Fin (m + m) ↪ Fin (n + n) where
  toFun q :=
    match finSumFinEquiv.symm q with
    | Sum.inl i => realIndex (f i)
    | Sum.inr i => imagIndex (f i)
  inj' := by
    intro q r h
    obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective q
    · obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective r
      · simp only [Equiv.symm_apply_apply] at h
        have hh := congrArg finSumFinEquiv.symm h
        simp only [finSumFinEquiv_symm_realIndex] at hh
        exact congrArg (fun a ↦ finSumFinEquiv (Sum.inl a))
          (f.injective (Sum.inl.inj hh))
      · simp only [Equiv.symm_apply_apply] at h
        exact (realIndex_ne_imagIndex (f i) (f j) h).elim
    · obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective r
      · simp only [Equiv.symm_apply_apply] at h
        exact (realIndex_ne_imagIndex (f j) (f i) h.symm).elim
      · simp only [Equiv.symm_apply_apply] at h
        have hh := congrArg finSumFinEquiv.symm h
        simp only [finSumFinEquiv_symm_imagIndex] at hh
        exact congrArg (fun a ↦ finSumFinEquiv (Sum.inr a))
          (f.injective (Sum.inr.inj hh))

@[simp]
theorem realificationEmbedding_realIndex
    (f : Fin m ↪ Fin n) (i : Fin m) :
    realificationEmbedding f (realIndex i) =
      realIndex (f i) := by
  simp [realificationEmbedding]

@[simp]
theorem realificationEmbedding_imagIndex
    (f : Fin m ↪ Fin n) (i : Fin m) :
    realificationEmbedding f (imagIndex i) =
      imagIndex (f i) := by
  simp [realificationEmbedding]

/-- Realification commutes with restricting a complex point along an
injection. -/
theorem realifyPoint_comp_realificationEmbedding
    (f : Fin m ↪ Fin n) (z : Fin n → ℂ) :
    realifyPoint z ∘ realificationEmbedding f =
      realifyPoint (z ∘ f) := by
  funext q
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective q
  · rw [show finSumFinEquiv (Sum.inl i) = realIndex i by rfl]
    simp [Function.comp_apply]
  · rw [show finSumFinEquiv (Sum.inr i) = imagIndex i by rfl]
    simp [Function.comp_apply]

end ComplexCoordinates

namespace ComplexPolynomialCode

variable {m n : ℕ}

/-- Regard a complex polynomial in `m` variables as one in `n` variables
along an injection of complex coordinate names. -/
def injectVariables
    (f : Fin m ↪ Fin n) (p : ComplexPolynomialCode m) :
    ComplexPolynomialCode n :=
  (PolynomialCode.injectVariables
      (ComplexCoordinates.realificationEmbedding f) p.1,
    PolynomialCode.injectVariables
      (ComplexCoordinates.realificationEmbedding f) p.2)

/-- Exact evaluation semantics of complex variable transport. -/
@[simp]
theorem eval_injectVariables
    (f : Fin m ↪ Fin n) (p : ComplexPolynomialCode m)
    (z : Fin n → ℂ) :
    eval (injectVariables f p) z = eval p (z ∘ f) := by
  apply Complex.ext <;>
    simp only [eval, evalReal,
      injectVariables, PolynomialCode.eval₂Hom_decode_injectVariables,
      ComplexCoordinates.realifyPoint_comp_realificationEmbedding]

/-- Complex variable transport preserves raw degree bounds. -/
theorem termsDegreeLE_injectVariables
    {D : ℕ} (f : Fin m ↪ Fin n)
    {p : ComplexPolynomialCode m}
    (hp : TermsDegreeLE D p) :
    TermsDegreeLE D (injectVariables f p) :=
  ⟨PolynomialCode.termsDegreeLE_injectVariables _ hp.1,
    PolynomialCode.termsDegreeLE_injectVariables _ hp.2⟩

/-- Complex variable transport is primitive recursive for a fixed
injection. -/
theorem injectVariables_primrec
    (f : Fin m ↪ Fin n) :
    Primrec (injectVariables f :
      ComplexPolynomialCode m → ComplexPolynomialCode n) := by
  exact Primrec.pair
    ((PolynomialCode.injectVariables_primrec
      (ComplexCoordinates.realificationEmbedding f)).comp Primrec.fst)
    ((PolynomialCode.injectVariables_primrec
      (ComplexCoordinates.realificationEmbedding f)).comp Primrec.snd)

end ComplexPolynomialCode

/-! ## The two canonical blocks of a finite sum -/

namespace ComplexPolynomialBlockCode

variable {m p : ℕ}

/-- The left coordinate injection `Fin m ↪ Fin (m+p)`. -/
def leftEmbedding : Fin m ↪ Fin (m + p) where
  toFun i := finSumFinEquiv (Sum.inl i)
  inj' := finSumFinEquiv.injective.comp Sum.inl_injective

/-- The right coordinate injection `Fin p ↪ Fin (m+p)`. -/
def rightEmbedding : Fin p ↪ Fin (m + p) where
  toFun i := finSumFinEquiv (Sum.inr i)
  inj' := finSumFinEquiv.injective.comp Sum.inr_injective

@[simp]
theorem finSumFinEquiv_symm_leftEmbedding (i : Fin m) :
    finSumFinEquiv.symm (leftEmbedding (p := p) i) =
      Sum.inl i :=
  finSumFinEquiv.symm_apply_apply _

@[simp]
theorem finSumFinEquiv_symm_rightEmbedding (i : Fin p) :
    finSumFinEquiv.symm (rightEmbedding (m := m) i) =
      Sum.inr i :=
  finSumFinEquiv.symm_apply_apply _

/-- Combine two complex points in the canonical flattened sum order. -/
def point
    (x : Fin m → ℂ) (y : Fin p → ℂ) :
    Fin (m + p) → ℂ :=
  fun q ↦
    match finSumFinEquiv.symm q with
    | Sum.inl i => x i
    | Sum.inr j => y j

@[simp]
theorem point_leftEmbedding
    (x : Fin m → ℂ) (y : Fin p → ℂ) (i : Fin m) :
    point x y (leftEmbedding (p := p) i) = x i := by
  simp [point]

@[simp]
theorem point_rightEmbedding
    (x : Fin m → ℂ) (y : Fin p → ℂ) (j : Fin p) :
    point x y (rightEmbedding (m := m) j) = y j := by
  simp [point]

@[simp]
theorem point_comp_leftEmbedding
    (x : Fin m → ℂ) (y : Fin p → ℂ) :
    point x y ∘ leftEmbedding (p := p) = x := by
  funext i
  simp

@[simp]
theorem point_comp_rightEmbedding
    (x : Fin m → ℂ) (y : Fin p → ℂ) :
    point x y ∘ rightEmbedding (m := m) = y := by
  funext i
  simp

/-- Put a polynomial into the left block of a complex product. -/
def left
    (q : ComplexPolynomialCode m) :
    ComplexPolynomialCode (m + p) :=
  ComplexPolynomialCode.injectVariables leftEmbedding q

/-- Put a polynomial into the right block of a complex product. -/
def right
    (q : ComplexPolynomialCode p) :
    ComplexPolynomialCode (m + p) :=
  ComplexPolynomialCode.injectVariables rightEmbedding q

@[simp]
theorem eval_left
    (q : ComplexPolynomialCode m)
    (x : Fin m → ℂ) (y : Fin p → ℂ) :
    ComplexPolynomialCode.eval (left (p := p) q) (point x y) =
      ComplexPolynomialCode.eval q x := by
  simp [left]

@[simp]
theorem eval_right
    (q : ComplexPolynomialCode p)
    (x : Fin m → ℂ) (y : Fin p → ℂ) :
    ComplexPolynomialCode.eval (right (m := m) q) (point x y) =
      ComplexPolynomialCode.eval q y := by
  simp [right]

theorem left_primrec :
    Primrec (left (m := m) (p := p) :
      ComplexPolynomialCode m →
        ComplexPolynomialCode (m + p)) :=
  ComplexPolynomialCode.injectVariables_primrec leftEmbedding

theorem right_primrec :
    Primrec (right (m := m) (p := p) :
      ComplexPolynomialCode p →
        ComplexPolynomialCode (m + p)) :=
  ComplexPolynomialCode.injectVariables_primrec rightEmbedding

/-- Block-diagonal sum of two independent complex polynomial fields. -/
def field
    (F : ComplexPolynomialFieldCode m)
    (G : ComplexPolynomialFieldCode p) :
    ComplexPolynomialFieldCode (m + p) :=
  fun q ↦
    match finSumFinEquiv.symm q with
    | Sum.inl i => left (p := p) (F i)
    | Sum.inr j => right (m := m) (G j)

@[simp]
theorem field_leftEmbedding
    (F : ComplexPolynomialFieldCode m)
    (G : ComplexPolynomialFieldCode p) (i : Fin m) :
    field F G (leftEmbedding (p := p) i) =
      left (p := p) (F i) := by
  simp [field]

@[simp]
theorem field_rightEmbedding
    (F : ComplexPolynomialFieldCode m)
    (G : ComplexPolynomialFieldCode p) (j : Fin p) :
    field F G (rightEmbedding (m := m) j) =
      right (m := m) (G j) := by
  simp [field]

/-- Exact pointwise semantics of the block-diagonal field compiler. -/
@[simp]
theorem eval_field
    (F : ComplexPolynomialFieldCode m)
    (G : ComplexPolynomialFieldCode p)
    (x : Fin m → ℂ) (y : Fin p → ℂ) :
    (fun q ↦ ComplexPolynomialCode.eval
      (field F G q) (point x y)) =
      point
        (fun i ↦ ComplexPolynomialCode.eval (F i) x)
        (fun j ↦ ComplexPolynomialCode.eval (G j) y) := by
  funext q
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective q
  · change
      ComplexPolynomialCode.eval
          (field F G (leftEmbedding (p := p) i)) (point x y) =
        point
          (fun i ↦ ComplexPolynomialCode.eval (F i) x)
          (fun j ↦ ComplexPolynomialCode.eval (G j) y)
          (leftEmbedding (p := p) i)
    simp
  · change
      ComplexPolynomialCode.eval
          (field F G (rightEmbedding (m := m) j)) (point x y) =
        point
          (fun i ↦ ComplexPolynomialCode.eval (F i) x)
          (fun j ↦ ComplexPolynomialCode.eval (G j) y)
          (rightEmbedding (m := m) j)
    simp

/-- Assembly of a block-diagonal complex field is primitive recursive in
the two finite input fields. -/
theorem field_primrec :
    Primrec₂ (field :
      ComplexPolynomialFieldCode m →
        ComplexPolynomialFieldCode p →
          ComplexPolynomialFieldCode (m + p)) := by
  change Primrec
    (fun FG :
        ComplexPolynomialFieldCode m ×
          ComplexPolynomialFieldCode p ↦
      field FG.1 FG.2)
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro q
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective q
  · exact
      (left_primrec.comp
        (Primrec.fin_app.comp Primrec.fst
          (Primrec.const i))).of_eq fun FG ↦
            (field_leftEmbedding FG.1 FG.2 i).symm
  · exact
      (right_primrec.comp
        (Primrec.fin_app.comp Primrec.snd
          (Primrec.const j))).of_eq fun FG ↦
            (field_rightEmbedding FG.1 FG.2 j).symm

theorem field_termsDegreeLE
    {D : ℕ}
    {F : ComplexPolynomialFieldCode m}
    {G : ComplexPolynomialFieldCode p}
    (hF : ComplexPolynomialFieldCode.TermsDegreeLE D F)
    (hG : ComplexPolynomialFieldCode.TermsDegreeLE D G) :
    ComplexPolynomialFieldCode.TermsDegreeLE D (field F G) := by
  intro q
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective q
  · change
      ComplexPolynomialCode.TermsDegreeLE D
        (field F G (leftEmbedding (p := p) i))
    rw [field_leftEmbedding]
    exact ComplexPolynomialCode.termsDegreeLE_injectVariables _ (hF i)
  · change
      ComplexPolynomialCode.TermsDegreeLE D
        (field F G (rightEmbedding (m := m) j))
    rw [field_rightEmbedding]
    exact ComplexPolynomialCode.termsDegreeLE_injectVariables _ (hG j)

end ComplexPolynomialBlockCode

end HGAS
