import HGAS.Algebra.PolynomialFiniteProductCode
import HGAS.Compiler.ComplexReciprocalPolynomialCode
import Mathlib.Tactic

/-!
# A finite family of complex reciprocal polynomial extensions

This module adjoins `b` independent complex reciprocal coordinates to one
common real polynomial source.  The source state is `x ∈ ℝⁿ`; block `a`
stores `gₐ ∈ ℂ` and is driven by its own rational parameter and complex
polynomial velocity:

```text
                 gₐ' = ηₐ wdotₐ(x) gₐ².
```

For each block the compiler also emits the two real coordinates of

```text
                 ((1 - ηₐ wₐ(x)) gₐ - 1).
```

The construction reuses the audited one-reciprocal compiler.  A canonical
injection places its `n` base variables in the shared base block and its
two reciprocal variables in block `a` of the flattened `b × 2` family.
This makes the locality of every compiled coordinate explicit and keeps
the finite-family API useful outside the present reduction.

All semantic theorems are valid at arbitrary ambient points.  The
degenerate cases `n = 0` and `b = 0` are included without hypotheses:
for `b = 0` the extension is exactly the base field and the residual
family is empty.
-/

namespace HGAS

namespace ComplexReciprocalFamilyPolynomialCode

open _root_.MvPolynomial

namespace Single

abbrev ComplexObservableCode :=
  ComplexReciprocalPolynomialCode.ComplexObservableCode

end Single

variable {n b : ℕ}

/-- Two real coordinates represent one complex reciprocal state. -/
abbrev localReciprocalDimension : ℕ := 2

/-- Flattened dimension of all `b` complex reciprocal states. -/
abbrev reciprocalDimension (b : ℕ) : ℕ :=
  b * localReciprocalDimension

/-- Total real dimension after adjoining `b` complex reciprocals. -/
abbrev dimension (n b : ℕ) : ℕ :=
  n + reciprocalDimension b

/-- Structured state: one common base point and `b` complex reciprocals. -/
abbrev State (n b : ℕ) :=
  (Fin n → ℝ) × (Fin b → ℂ)

/-- A family of complex observables on the common base. -/
abbrev ObservableFamily (n b : ℕ) :=
  Fin b → Single.ComplexObservableCode n

/-- Embed the common base coordinates into the enlarged state. -/
def baseEmbedding : Fin n ↪ Fin (dimension n b) :=
  PolynomialBlockCode.leftEmbedding

/-- Embed the complete flattened reciprocal family as the right block. -/
def reciprocalFamilyEmbedding :
    Fin (reciprocalDimension b) ↪ Fin (dimension n b) :=
  PolynomialBlockCode.rightEmbedding

/-- Embed the two local real coordinates of reciprocal block `a` into the
flattened reciprocal family. -/
def reciprocalBlockEmbedding (a : Fin b) :
    Fin localReciprocalDimension ↪ Fin (reciprocalDimension b) :=
  PolynomialFiniteProductCode.blockEmbedding a

/-- Embed one local reciprocal block directly into the complete state. -/
def reciprocalEmbedding (a : Fin b) :
    Fin localReciprocalDimension ↪ Fin (dimension n b) :=
  (reciprocalBlockEmbedding a).trans reciprocalFamilyEmbedding

/-- Real coordinate of `gₐ`. -/
def reciprocalReIndex (a : Fin b) : Fin (dimension n b) :=
  reciprocalEmbedding a (0 : Fin 2)

/-- Imaginary coordinate of `gₐ`. -/
def reciprocalImIndex (a : Fin b) : Fin (dimension n b) :=
  reciprocalEmbedding a (1 : Fin 2)

/-- Flatten a family of complex numbers into interleaved real/imaginary
two-coordinate blocks. -/
def reciprocalPoint (g : Fin b → ℂ) :
    Fin (reciprocalDimension b) → ℝ :=
  PolynomialFiniteProductCode.flattenPoint
    (fun a ↦ ![(g a).re, (g a).im])

/-- Flatten a structured base/reciprocal-family state. -/
def point (z : State n b) : Fin (dimension n b) → ℝ :=
  PolynomialBlockCode.point z.1 (reciprocalPoint z.2)

/-- Recover a structured state from arbitrary ambient real coordinates. -/
def state (x : Fin (dimension n b) → ℝ) : State n b :=
  (x ∘ baseEmbedding,
    fun a ↦
      ⟨x (reciprocalReIndex a),
        x (reciprocalImIndex a)⟩)

@[simp]
theorem point_baseEmbedding
    (z : State n b) (i : Fin n) :
    point z (baseEmbedding i) = z.1 i := by
  simp [point, baseEmbedding]

@[simp]
theorem point_reciprocalEmbedding
    (z : State n b) (a : Fin b) (j : Fin 2) :
    point z (reciprocalEmbedding a j) =
      ![(z.2 a).re, (z.2 a).im] j := by
  simp [point, reciprocalEmbedding, reciprocalFamilyEmbedding,
    reciprocalBlockEmbedding, reciprocalPoint]

@[simp]
theorem point_reciprocalReIndex
    (z : State n b) (a : Fin b) :
    point z (reciprocalReIndex a) = (z.2 a).re := by
  simp [reciprocalReIndex]

@[simp]
theorem point_reciprocalImIndex
    (z : State n b) (a : Fin b) :
    point z (reciprocalImIndex a) = (z.2 a).im := by
  simp [reciprocalImIndex]

@[simp]
theorem state_point (z : State n b) :
    state (point z) = z := by
  apply Prod.ext
  · funext i
    simp [state]
  · funext a
    apply Complex.ext <;> simp [state]

@[simp]
theorem point_state
    (x : Fin (dimension n b) → ℝ) :
    point (state x) = x := by
  funext k
  obtain ⟨i | r, rfl⟩ := finSumFinEquiv.surjective k
  · change
      point (state x) (baseEmbedding i) =
        x (baseEmbedding i)
    rw [point_baseEmbedding]
    rfl
  · obtain ⟨⟨a, j⟩, rfl⟩ :=
      finProdFinEquiv.surjective r
    fin_cases j
    · change
        point (state x) (reciprocalReIndex a) =
          x (reciprocalReIndex a)
      rw [point_reciprocalReIndex]
      rfl
    · change
        point (state x) (reciprocalImIndex a) =
          x (reciprocalImIndex a)
      rw [point_reciprocalImIndex]
      rfl

/-! ## Reusable injection of one reciprocal extension -/

/-- On sum coordinates, retain the common base and send the local
two-coordinate reciprocal into block `a` of the family. -/
def sumBlockEmbedding (a : Fin b) :
    Sum (Fin n) (Fin 2) ↪
      Sum (Fin n) (Fin (reciprocalDimension b)) where
  toFun
    | Sum.inl i => Sum.inl i
    | Sum.inr j => Sum.inr (reciprocalBlockEmbedding a j)
  inj' := by
    intro x y h
    rcases x with i | i <;> rcases y with j | j
    · have : i = j := Sum.inl.inj h
      subst j
      rfl
    · simp at h
    · simp at h
    · have hij :
          reciprocalBlockEmbedding a i =
            reciprocalBlockEmbedding a j :=
        Sum.inr.inj h
      have : i = j :=
        (reciprocalBlockEmbedding a).injective hij
      subst j
      rfl

/-- Inject the state space of the one-reciprocal compiler into the
finite-family state, sharing all base variables and selecting block `a`. -/
def singleEmbedding (a : Fin b) :
    Fin (ComplexReciprocalPolynomialCode.dimension n) ↪
      Fin (dimension n b) :=
  ((finSumFinEquiv :
      Sum (Fin n) (Fin 2) ≃
        Fin (ComplexReciprocalPolynomialCode.dimension n)).symm.toEmbedding).trans
    ((sumBlockEmbedding a).trans
      (finSumFinEquiv :
        Sum (Fin n) (Fin (reciprocalDimension b)) ≃
          Fin (dimension n b)).toEmbedding)

@[simp]
theorem singleEmbedding_baseEmbedding
    (a : Fin b) (i : Fin n) :
    singleEmbedding a
        (ComplexReciprocalPolynomialCode.baseEmbedding i) =
      baseEmbedding i := by
  simp [singleEmbedding, sumBlockEmbedding,
    ComplexReciprocalPolynomialCode.baseEmbedding,
    baseEmbedding, PolynomialBlockCode.leftEmbedding]

@[simp]
theorem singleEmbedding_reciprocalReIndex
    (a : Fin b) :
    singleEmbedding a
        (ComplexReciprocalPolynomialCode.reciprocalReIndex n) =
      reciprocalReIndex a := by
  simp [singleEmbedding, sumBlockEmbedding,
    ComplexReciprocalPolynomialCode.reciprocalReIndex,
    reciprocalReIndex, reciprocalEmbedding,
    reciprocalFamilyEmbedding, reciprocalBlockEmbedding,
    PolynomialBlockCode.rightEmbedding]

@[simp]
theorem singleEmbedding_reciprocalImIndex
    (a : Fin b) :
    singleEmbedding a
        (ComplexReciprocalPolynomialCode.reciprocalImIndex n) =
      reciprocalImIndex a := by
  simp [singleEmbedding, sumBlockEmbedding,
    ComplexReciprocalPolynomialCode.reciprocalImIndex,
    reciprocalImIndex, reciprocalEmbedding,
    reciprocalFamilyEmbedding, reciprocalBlockEmbedding,
    PolynomialBlockCode.rightEmbedding]

@[simp]
theorem point_comp_singleEmbedding
    (z : State n b) (a : Fin b) :
    point z ∘ singleEmbedding a =
      ComplexReciprocalPolynomialCode.point
        (z.1, z.2 a) := by
  funext k
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective k
  · change
      point z
          (singleEmbedding a
            (ComplexReciprocalPolynomialCode.baseEmbedding i)) =
        ComplexReciprocalPolynomialCode.point
          (z.1, z.2 a)
          (ComplexReciprocalPolynomialCode.baseEmbedding i)
    rw [singleEmbedding_baseEmbedding,
      point_baseEmbedding,
      ComplexReciprocalPolynomialCode.point_baseEmbedding]
  · fin_cases j
    · change
        point z
            (singleEmbedding a
              (ComplexReciprocalPolynomialCode.reciprocalReIndex n)) =
          ComplexReciprocalPolynomialCode.point
            (z.1, z.2 a)
            (ComplexReciprocalPolynomialCode.reciprocalReIndex n)
      rw [singleEmbedding_reciprocalReIndex,
        point_reciprocalReIndex,
        ComplexReciprocalPolynomialCode.point_reciprocalReIndex]
    · change
        point z
            (singleEmbedding a
              (ComplexReciprocalPolynomialCode.reciprocalImIndex n)) =
          ComplexReciprocalPolynomialCode.point
            (z.1, z.2 a)
            (ComplexReciprocalPolynomialCode.reciprocalImIndex n)
      rw [singleEmbedding_reciprocalImIndex,
        point_reciprocalImIndex,
        ComplexReciprocalPolynomialCode.point_reciprocalImIndex]

/-- Inject one sparse polynomial emitted by the one-reciprocal compiler
into reciprocal block `a` of the family. -/
def liftSingle
    (a : Fin b)
    (p :
      PolynomialCode
        (ComplexReciprocalPolynomialCode.dimension n)) :
    PolynomialCode (dimension n b) :=
  PolynomialCode.injectVariables (singleEmbedding a) p

@[simp]
theorem eval₂Hom_liftSingle
    {R : Type*} [CommSemiring R] [Algebra ℚ R]
    (a : Fin b)
    (p :
      PolynomialCode
        (ComplexReciprocalPolynomialCode.dimension n))
    (x : Fin (dimension n b) → R) :
    eval₂Hom (algebraMap ℚ R) x
        (PolynomialCode.decode (liftSingle a p)) =
      eval₂Hom (algebraMap ℚ R) (x ∘ singleEmbedding a)
        (PolynomialCode.decode p) := by
  exact
    PolynomialCode.eval₂Hom_decode_injectVariables
      (singleEmbedding a) p x

@[simp]
theorem eval₂Hom_liftSingle_point
    (a : Fin b)
    (p :
      PolynomialCode
        (ComplexReciprocalPolynomialCode.dimension n))
    (z : State n b) :
    eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode (liftSingle a p)) =
      eval₂Hom (algebraMap ℚ ℝ)
        (ComplexReciprocalPolynomialCode.point
          (z.1, z.2 a))
        (PolynomialCode.decode p) := by
  rw [eval₂Hom_liftSingle, point_comp_singleEmbedding]

/-! ## Literal family field and residual syntax -/

/-- Lift a base polynomial into the complete family state. -/
def liftBase (p : PolynomialCode n) :
    PolynomialCode (dimension n b) :=
  PolynomialBlockCode.left (p := reciprocalDimension b) p

/-- Real velocity code for reciprocal block `a`. -/
def reciprocalVelocityReCode
    (η : Fin b → RationalCode)
    (wdot : ObservableFamily n b) (a : Fin b) :
    PolynomialCode (dimension n b) :=
  liftSingle a
    (ComplexReciprocalPolynomialCode.reciprocalVelocityReCode
      (η a) (wdot a))

/-- Imaginary velocity code for reciprocal block `a`. -/
def reciprocalVelocityImCode
    (η : Fin b → RationalCode)
    (wdot : ObservableFamily n b) (a : Fin b) :
    PolynomialCode (dimension n b) :=
  liftSingle a
    (ComplexReciprocalPolynomialCode.reciprocalVelocityImCode
      (η a) (wdot a))

/-- Extend the common base field by all `b` reciprocal velocities. -/
def fieldCode
    (F : PolynomialFieldCode n)
    (η : Fin b → RationalCode)
    (wdot : ObservableFamily n b) :
    PolynomialFieldCode (dimension n b) :=
  fun k ↦
    match finSumFinEquiv.symm k with
    | Sum.inl i => liftBase (F i)
    | Sum.inr r =>
        let aj := finProdFinEquiv.symm r
        ![reciprocalVelocityReCode η wdot aj.1,
          reciprocalVelocityImCode η wdot aj.1] aj.2

@[simp]
theorem fieldCode_baseEmbedding
    (F : PolynomialFieldCode n)
    (η : Fin b → RationalCode)
    (wdot : ObservableFamily n b) (i : Fin n) :
    fieldCode F η wdot (baseEmbedding i) =
      liftBase (F i) := by
  simp [fieldCode, baseEmbedding]

@[simp]
theorem fieldCode_reciprocalReIndex
    (F : PolynomialFieldCode n)
    (η : Fin b → RationalCode)
    (wdot : ObservableFamily n b) (a : Fin b) :
    fieldCode F η wdot (reciprocalReIndex a) =
      reciprocalVelocityReCode η wdot a := by
  change
    fieldCode F η wdot
        (reciprocalFamilyEmbedding
          (reciprocalBlockEmbedding a (0 : Fin 2))) =
      reciprocalVelocityReCode η wdot a
  unfold fieldCode reciprocalFamilyEmbedding
  rw [PolynomialBlockCode.finSumFinEquiv_symm_rightEmbedding]
  simp only
  unfold reciprocalBlockEmbedding
  rw [
    PolynomialFiniteProductCode.finProdFinEquiv_symm_blockEmbedding]
  rfl

@[simp]
theorem fieldCode_reciprocalImIndex
    (F : PolynomialFieldCode n)
    (η : Fin b → RationalCode)
    (wdot : ObservableFamily n b) (a : Fin b) :
    fieldCode F η wdot (reciprocalImIndex a) =
      reciprocalVelocityImCode η wdot a := by
  change
    fieldCode F η wdot
        (reciprocalFamilyEmbedding
          (reciprocalBlockEmbedding a (1 : Fin 2))) =
      reciprocalVelocityImCode η wdot a
  unfold fieldCode reciprocalFamilyEmbedding
  rw [PolynomialBlockCode.finSumFinEquiv_symm_rightEmbedding]
  simp only
  unfold reciprocalBlockEmbedding
  rw [
    PolynomialFiniteProductCode.finProdFinEquiv_symm_blockEmbedding]
  rfl

/-- Real residual code for block `a`. -/
def residualReCode
    (η : Fin b → RationalCode)
    (w : ObservableFamily n b) (a : Fin b) :
    PolynomialCode (dimension n b) :=
  liftSingle a
    (ComplexReciprocalPolynomialCode.residualReCode
      (η a) (w a))

/-- Imaginary residual code for block `a`. -/
def residualImCode
    (η : Fin b → RationalCode)
    (w : ObservableFamily n b) (a : Fin b) :
    PolynomialCode (dimension n b) :=
  liftSingle a
    (ComplexReciprocalPolynomialCode.residualImCode
      (η a) (w a))

/-- All `2b` real residual coordinates, flattened by reciprocal block. -/
def residualCode
    (η : Fin b → RationalCode)
    (w : ObservableFamily n b) :
    Fin (reciprocalDimension b) →
      PolynomialCode (dimension n b) :=
  fun k ↦
    let aj := finProdFinEquiv.symm k
    ![residualReCode η w aj.1,
      residualImCode η w aj.1] aj.2

@[simp]
theorem residualCode_reciprocalBlockEmbedding
    (η : Fin b → RationalCode)
    (w : ObservableFamily n b)
    (a : Fin b) (j : Fin 2) :
    residualCode η w (reciprocalBlockEmbedding a j) =
      ![residualReCode η w a,
        residualImCode η w a] j := by
  unfold residualCode reciprocalBlockEmbedding
  rw [
    PolynomialFiniteProductCode.finProdFinEquiv_symm_blockEmbedding]

/-! ## Exact semantic realization -/

noncomputable def evalObservable
    (p : Single.ComplexObservableCode n)
    (x : Fin n → ℝ) : ℂ :=
  ComplexReciprocalPolynomialCode.evalObservable p x

noncomputable def vectorField
    (F : PolynomialFieldCode n)
    (η : Fin b → RationalCode)
    (wdot : ObservableFamily n b)
    (z : State n b) : State n b :=
  (PolynomialFieldCode.realize F z.1,
    fun a ↦
      reciprocalVelocity
        ((RationalCode.decode (η a) : ℝ) : ℂ)
        (evalObservable (wdot a) z.1) (z.2 a))

noncomputable def residual
    (η : Fin b → RationalCode)
    (w : ObservableFamily n b)
    (z : State n b) (a : Fin b) : ℂ :=
  reciprocalResidual
    ((RationalCode.decode (η a) : ℝ) : ℂ)
    (evalObservable (w a) z.1) (z.2 a)

@[simp]
theorem eval₂Hom_liftBase_point
    (p : PolynomialCode n) (z : State n b) :
    eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode (liftBase p)) =
      eval₂Hom (algebraMap ℚ ℝ) z.1
        (PolynomialCode.decode p) := by
  simp [liftBase, point]

@[simp]
theorem eval₂Hom_reciprocalVelocityReCode
    (η : Fin b → RationalCode)
    (wdot : ObservableFamily n b)
    (z : State n b) (a : Fin b) :
    eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode
          (reciprocalVelocityReCode η wdot a)) =
      (reciprocalVelocity
        ((RationalCode.decode (η a) : ℝ) : ℂ)
        (evalObservable (wdot a) z.1)
        (z.2 a)).re := by
  rw [reciprocalVelocityReCode, eval₂Hom_liftSingle_point]
  exact
    ComplexReciprocalPolynomialCode.eval₂Hom_reciprocalVelocityReCode
      (η a) (wdot a) (z.1, z.2 a)

@[simp]
theorem eval₂Hom_reciprocalVelocityImCode
    (η : Fin b → RationalCode)
    (wdot : ObservableFamily n b)
    (z : State n b) (a : Fin b) :
    eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode
          (reciprocalVelocityImCode η wdot a)) =
      (reciprocalVelocity
        ((RationalCode.decode (η a) : ℝ) : ℂ)
        (evalObservable (wdot a) z.1)
        (z.2 a)).im := by
  rw [reciprocalVelocityImCode, eval₂Hom_liftSingle_point]
  exact
    ComplexReciprocalPolynomialCode.eval₂Hom_reciprocalVelocityImCode
      (η a) (wdot a) (z.1, z.2 a)

@[simp]
theorem realize_fieldCode
    (F : PolynomialFieldCode n)
    (η : Fin b → RationalCode)
    (wdot : ObservableFamily n b)
    (z : State n b) :
    PolynomialFieldCode.realize
        (fieldCode F η wdot) (point z) =
      point (vectorField F η wdot z) := by
  funext k
  obtain ⟨i | r, rfl⟩ := finSumFinEquiv.surjective k
  · change
      PolynomialFieldCode.realize
          (fieldCode F η wdot) (point z)
          (baseEmbedding i) =
        point (vectorField F η wdot z)
          (baseEmbedding i)
    rw [PolynomialFieldCode.realize_apply,
      fieldCode_baseEmbedding, eval₂Hom_liftBase_point,
      point_baseEmbedding]
    rfl
  · obtain ⟨⟨a, j⟩, rfl⟩ :=
      finProdFinEquiv.surjective r
    fin_cases j
    · change
        PolynomialFieldCode.realize
            (fieldCode F η wdot) (point z)
            (reciprocalReIndex a) =
          point (vectorField F η wdot z)
            (reciprocalReIndex a)
      rw [PolynomialFieldCode.realize_apply,
        fieldCode_reciprocalReIndex,
        eval₂Hom_reciprocalVelocityReCode,
        point_reciprocalReIndex]
      rfl
    · change
        PolynomialFieldCode.realize
            (fieldCode F η wdot) (point z)
            (reciprocalImIndex a) =
          point (vectorField F η wdot z)
            (reciprocalImIndex a)
      rw [PolynomialFieldCode.realize_apply,
        fieldCode_reciprocalImIndex,
        eval₂Hom_reciprocalVelocityImCode,
        point_reciprocalImIndex]
      rfl

/-- Exact field semantics at every ambient real point. -/
@[simp]
theorem realize_fieldCode_arbitrary
    (F : PolynomialFieldCode n)
    (η : Fin b → RationalCode)
    (wdot : ObservableFamily n b)
    (x : Fin (dimension n b) → ℝ) :
    PolynomialFieldCode.realize (fieldCode F η wdot) x =
      point (vectorField F η wdot (state x)) := by
  simpa using realize_fieldCode F η wdot (state x)

@[simp]
theorem eval₂Hom_residualReCode
    (η : Fin b → RationalCode)
    (w : ObservableFamily n b)
    (z : State n b) (a : Fin b) :
    eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode (residualReCode η w a)) =
      (residual η w z a).re := by
  rw [residualReCode, eval₂Hom_liftSingle_point]
  exact
    ComplexReciprocalPolynomialCode.eval₂Hom_residualReCode
      (η a) (w a) (z.1, z.2 a)

@[simp]
theorem eval₂Hom_residualImCode
    (η : Fin b → RationalCode)
    (w : ObservableFamily n b)
    (z : State n b) (a : Fin b) :
    eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode (residualImCode η w a)) =
      (residual η w z a).im := by
  rw [residualImCode, eval₂Hom_liftSingle_point]
  exact
    ComplexReciprocalPolynomialCode.eval₂Hom_residualImCode
      (η a) (w a) (z.1, z.2 a)

@[simp]
theorem eval₂Hom_residualReCode_arbitrary
    (η : Fin b → RationalCode)
    (w : ObservableFamily n b)
    (x : Fin (dimension n b) → ℝ) (a : Fin b) :
    eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (residualReCode η w a)) =
      (residual η w (state x) a).re := by
  simpa using eval₂Hom_residualReCode η w (state x) a

@[simp]
theorem eval₂Hom_residualImCode_arbitrary
    (η : Fin b → RationalCode)
    (w : ObservableFamily n b)
    (x : Fin (dimension n b) → ℝ) (a : Fin b) :
    eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (residualImCode η w a)) =
      (residual η w (state x) a).im := by
  simpa using eval₂Hom_residualImCode η w (state x) a

/-- Reassembling the two evaluated scalar codes gives the exact complex
reciprocal residual of block `a`. -/
theorem complex_eval_residualCodes
    (η : Fin b → RationalCode)
    (w : ObservableFamily n b)
    (z : State n b) (a : Fin b) :
    (⟨
      eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode (residualReCode η w a)),
      eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode (residualImCode η w a))
    ⟩ : ℂ) =
      residual η w z a := by
  apply Complex.ext <;> simp

/-- Arbitrary-point complex reassembly semantics. -/
theorem complex_eval_residualCodes_arbitrary
    (η : Fin b → RationalCode)
    (w : ObservableFamily n b)
    (x : Fin (dimension n b) → ℝ) (a : Fin b) :
    (⟨
      eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (residualReCode η w a)),
      eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (residualImCode η w a))
    ⟩ : ℂ) =
      residual η w (state x) a := by
  apply Complex.ext <;> simp

/-- Exact structured evaluation of an arbitrary flattened scalar residual
coordinate. -/
@[simp]
theorem eval₂Hom_residualCode_reciprocalBlockEmbedding
    (η : Fin b → RationalCode)
    (w : ObservableFamily n b)
    (z : State n b) (a : Fin b) (j : Fin 2) :
    eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode
          (residualCode η w
            (reciprocalBlockEmbedding a j))) =
      ![(residual η w z a).re,
        (residual η w z a).im] j := by
  rw [residualCode_reciprocalBlockEmbedding]
  fin_cases j <;> simp

/-- Exact ambient evaluation of an arbitrary flattened scalar residual
coordinate. -/
@[simp]
theorem eval₂Hom_residualCode_reciprocalBlockEmbedding_arbitrary
    (η : Fin b → RationalCode)
    (w : ObservableFamily n b)
    (x : Fin (dimension n b) → ℝ)
    (a : Fin b) (j : Fin 2) :
    eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode
          (residualCode η w
            (reciprocalBlockEmbedding a j))) =
      ![(residual η w (state x) a).re,
        (residual η w (state x) a).im] j := by
  simpa using
    eval₂Hom_residualCode_reciprocalBlockEmbedding
      η w (state x) a j

/-- The two scalar residual codes of block `a` vanish exactly when its
complex reciprocal graph equation holds. -/
theorem residualCodes_eq_zero_iff
    (η : Fin b → RationalCode)
    (w : ObservableFamily n b)
    (z : State n b) (a : Fin b) :
    (eval₂Hom (algebraMap ℚ ℝ) (point z)
          (PolynomialCode.decode (residualReCode η w a)) = 0 ∧
        eval₂Hom (algebraMap ℚ ℝ) (point z)
          (PolynomialCode.decode (residualImCode η w a)) = 0) ↔
      residual η w z a = 0 := by
  rw [eval₂Hom_residualReCode, eval₂Hom_residualImCode]
  constructor
  · rintro ⟨hre, him⟩
    apply Complex.ext
    · simpa using hre
    · simpa using him
  · intro h
    rw [h]
    simp

/-- Arbitrary-point version of the two-coordinate zero-set semantics. -/
theorem residualCodes_eq_zero_iff_arbitrary
    (η : Fin b → RationalCode)
    (w : ObservableFamily n b)
    (x : Fin (dimension n b) → ℝ) (a : Fin b) :
    (eval₂Hom (algebraMap ℚ ℝ) x
          (PolynomialCode.decode (residualReCode η w a)) = 0 ∧
        eval₂Hom (algebraMap ℚ ℝ) x
          (PolynomialCode.decode (residualImCode η w a)) = 0) ↔
      residual η w (state x) a = 0 := by
  simpa using residualCodes_eq_zero_iff η w (state x) a

/-- Simultaneous vanishing of all `2b` scalar codes is equivalent to all
`b` complex reciprocal equations. -/
theorem forall_eval_residualCode_eq_zero_iff
    (η : Fin b → RationalCode)
    (w : ObservableFamily n b)
    (z : State n b) :
    (∀ k,
      eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode (residualCode η w k)) = 0) ↔
      ∀ a, residual η w z a = 0 := by
  constructor
  · intro h a
    apply (residualCodes_eq_zero_iff η w z a).1
    constructor
    · simpa using h (reciprocalBlockEmbedding a (0 : Fin 2))
    · simpa using h (reciprocalBlockEmbedding a (1 : Fin 2))
  · intro h k
    obtain ⟨⟨a, j⟩, rfl⟩ :=
      finProdFinEquiv.surjective k
    have ha :=
      (residualCodes_eq_zero_iff η w z a).2 (h a)
    fin_cases j
    · change
        eval₂Hom (algebraMap ℚ ℝ) (point z)
          (PolynomialCode.decode
            (residualCode η w
              (reciprocalBlockEmbedding a (0 : Fin 2)))) = 0
      rw [residualCode_reciprocalBlockEmbedding]
      exact ha.1
    · change
        eval₂Hom (algebraMap ℚ ℝ) (point z)
          (PolynomialCode.decode
            (residualCode η w
              (reciprocalBlockEmbedding a (1 : Fin 2)))) = 0
      rw [residualCode_reciprocalBlockEmbedding]
      exact ha.2

/-- Arbitrary-point simultaneous residual semantics. -/
theorem forall_eval_residualCode_eq_zero_iff_arbitrary
    (η : Fin b → RationalCode)
    (w : ObservableFamily n b)
    (x : Fin (dimension n b) → ℝ) :
    (∀ k,
      eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (residualCode η w k)) = 0) ↔
      ∀ a, residual η w (state x) a = 0 := by
  simpa using
    forall_eval_residualCode_eq_zero_iff η w (state x)

/-! ## Componentwise trajectory propagation -/

/-- One component of a genuine family trajectory supplies the reusable
single-reciprocal graph interface. -/
theorem isReciprocalGraphTrajectory_component
    (η : Fin b → RationalCode)
    (w wdot : ObservableFamily n b)
    (z : ℝ → State n b) (a : Fin b)
    (hw :
      ∀ t,
        HasDerivAt
          (fun s ↦ evalObservable (w a) (z s).1)
          (evalObservable (wdot a) (z t).1) t)
    (hg :
      ∀ t,
        HasDerivAt (fun s ↦ (z s).2 a)
          (reciprocalVelocity
            ((RationalCode.decode (η a) : ℝ) : ℂ)
            (evalObservable (wdot a) (z t).1)
            ((z t).2 a)) t)
    (hwdot :
      Continuous
        (fun t ↦ evalObservable (wdot a) (z t).1)) :
    IsReciprocalGraphTrajectory
      ((RationalCode.decode (η a) : ℝ) : ℂ)
      (fun t ↦ evalObservable (w a) (z t).1)
      (fun t ↦ (z t).2 a)
      (fun t ↦ evalObservable (wdot a) (z t).1) :=
  ComplexReciprocalPolynomialCode.isReciprocalGraphTrajectory
    (η a) (w a) (wdot a)
    (fun t ↦ ((z t).1, (z t).2 a))
    hw hg hwdot

/-- If every reciprocal equation holds at one time along a genuine
family trajectory, then every equation holds for all real time. -/
theorem forall_residual_eq_zero_along_trajectory
    (η : Fin b → RationalCode)
    (w wdot : ObservableFamily n b)
    (z : ℝ → State n b)
    (hw :
      ∀ a t,
        HasDerivAt
          (fun s ↦ evalObservable (w a) (z s).1)
          (evalObservable (wdot a) (z t).1) t)
    (hg :
      ∀ a t,
        HasDerivAt (fun s ↦ (z s).2 a)
          (reciprocalVelocity
            ((RationalCode.decode (η a) : ℝ) : ℂ)
            (evalObservable (wdot a) (z t).1)
            ((z t).2 a)) t)
    (hwdot :
      ∀ a,
        Continuous
          (fun t ↦ evalObservable (wdot a) (z t).1))
    {t₀ : ℝ}
    (hzero : ∀ a, residual η w (z t₀) a = 0) :
    ∀ t a, residual η w (z t) a = 0 := by
  intro t a
  exact
    (isReciprocalGraphTrajectory_component
      η w wdot z a (hw a) (hg a) (hwdot a)).residual_eq_zero
        (hzero a) t

end ComplexReciprocalFamilyPolynomialCode

end HGAS
