import HGAS.Algebra.PolynomialVariableEmbedding
import HGAS.Compiler.ReciprocalGraphDynamics
import Mathlib.Tactic

/-!
# A reusable rational polynomial compiler for one complex reciprocal state

Let a real polynomial source have state `x ∈ ℝⁿ`.  Suppose two pairs of
real polynomial codes represent a complex observable and its intended
velocity,

```
             w(x) = w_re(x) + i w_im(x),
          wdot(x) = v_re(x) + i v_im(x).
```

For rational `η`, this module adjoins one complex state `g = g_re+i g_im`
and emits the real polynomial equations

```
                         g' = η wdot(x) g².
```

It also compiles the two real coordinates of

```
                         ((1-ηw(x))g-1).
```

These are the Poisson-reciprocal equations used in the arithmetic detector.
The implementation is generic: it does not assume that `w` lies on a unit
circle, that `wdot` really is the derivative of `w`, or that the reciprocal
residual vanishes.  Those are semantic hypotheses proved by a source using
this compiler.

The exact evaluation theorems hold at every ambient point.  A final bridge
packages any genuine trajectory satisfying the observable derivative into
`IsReciprocalGraphTrajectory`; the already-proved scalar linear-ODE theorem
then propagates a zero reciprocal residual for all time.
-/

namespace HGAS

namespace ComplexReciprocalPolynomialCode

open _root_.MvPolynomial

variable {n : ℕ}

/-- Two real coordinates are adjoined for the complex reciprocal. -/
abbrev dimension (n : ℕ) : ℕ := n + 2

/-- A complex polynomial observable over a real source is represented by
its real and imaginary scalar codes. -/
abbrev ComplexObservableCode (n : ℕ) :=
  PolynomialCode n × PolynomialCode n

/-- Structured semantic state: the original real point and one complex
reciprocal coordinate. -/
abbrev State (n : ℕ) := (Fin n → ℝ) × ℂ

def baseEmbedding : Fin n ↪ Fin (dimension n) :=
  PolynomialBlockCode.leftEmbedding

def reciprocalReIndex (n : ℕ) : Fin (dimension n) :=
  PolynomialBlockCode.rightEmbedding (m := n) (0 : Fin 2)

def reciprocalImIndex (n : ℕ) : Fin (dimension n) :=
  PolynomialBlockCode.rightEmbedding (m := n) (1 : Fin 2)

/-- Flatten a real base point and a complex reciprocal coordinate. -/
def point (z : State n) : Fin (dimension n) → ℝ :=
  PolynomialBlockCode.point z.1 ![z.2.re, z.2.im]

/-- Recover the base and complex reciprocal from an arbitrary ambient
point. -/
def state (x : Fin (dimension n) → ℝ) : State n :=
  (x ∘ baseEmbedding,
    ⟨x (reciprocalReIndex n), x (reciprocalImIndex n)⟩)

@[simp]
theorem point_baseEmbedding
    (z : State n) (i : Fin n) :
    point z (baseEmbedding i) = z.1 i := by
  simp [point, baseEmbedding]

@[simp]
theorem point_reciprocalReIndex
    (z : State n) :
    point z (reciprocalReIndex n) = z.2.re := by
  simp [point, reciprocalReIndex]

@[simp]
theorem point_reciprocalImIndex
    (z : State n) :
    point z (reciprocalImIndex n) = z.2.im := by
  simp [point, reciprocalImIndex]

@[simp]
theorem state_point (z : State n) :
    state (point z) = z := by
  apply Prod.ext
  · funext i
    simp [state]
  · apply Complex.ext <;> simp [state]

@[simp]
theorem point_state (x : Fin (dimension n) → ℝ) :
    point (state x) = x := by
  funext k
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective k
  · change
      point (state x) (baseEmbedding i) = x (baseEmbedding i)
    rw [point_baseEmbedding]
    rfl
  · fin_cases j
    · change
        point (state x) (reciprocalReIndex n) =
          x (reciprocalReIndex n)
      rw [point_reciprocalReIndex]
      rfl
    · change
        point (state x) (reciprocalImIndex n) =
          x (reciprocalImIndex n)
      rw [point_reciprocalImIndex]
      rfl

/-! ## Literal polynomial syntax -/

def liftBase (p : PolynomialCode n) :
    PolynomialCode (dimension n) :=
  PolynomialBlockCode.left (p := 2) p

def reciprocalReCode : PolynomialCode (dimension n) :=
  PolynomialCode.varCode (reciprocalReIndex n)

def reciprocalImCode : PolynomialCode (dimension n) :=
  PolynomialCode.varCode (reciprocalImIndex n)

def etaCode (η : RationalCode) :
    PolynomialCode (dimension n) :=
  PolynomialCode.constant η

def oneCode : PolynomialCode (dimension n) :=
  PolynomialCode.one

def twoCode : PolynomialCode (dimension n) :=
  PolynomialCode.constant (RationalCode.encode 2)

/-- Real part of `g²`. -/
def reciprocalSquareReCode :
    PolynomialCode (dimension n) :=
  PolynomialCode.sub
    (PolynomialCode.mul reciprocalReCode reciprocalReCode)
    (PolynomialCode.mul reciprocalImCode reciprocalImCode)

/-- Imaginary part of `g²`. -/
def reciprocalSquareImCode :
    PolynomialCode (dimension n) :=
  PolynomialCode.mul twoCode
    (PolynomialCode.mul reciprocalReCode reciprocalImCode)

/-- Real part of `η wdot g²`. -/
def reciprocalVelocityReCode
    (η : RationalCode) (wdot : ComplexObservableCode n) :
    PolynomialCode (dimension n) :=
  PolynomialCode.mul (etaCode η)
    (PolynomialCode.sub
      (PolynomialCode.mul (liftBase wdot.1)
        reciprocalSquareReCode)
      (PolynomialCode.mul (liftBase wdot.2)
        reciprocalSquareImCode))

/-- Imaginary part of `η wdot g²`. -/
def reciprocalVelocityImCode
    (η : RationalCode) (wdot : ComplexObservableCode n) :
    PolynomialCode (dimension n) :=
  PolynomialCode.mul (etaCode η)
    (PolynomialCode.add
      (PolynomialCode.mul (liftBase wdot.1)
        reciprocalSquareImCode)
      (PolynomialCode.mul (liftBase wdot.2)
        reciprocalSquareReCode))

/-- Extend a base field by the two real reciprocal-velocity equations. -/
def fieldCode
    (F : PolynomialFieldCode n)
    (η : RationalCode) (wdot : ComplexObservableCode n) :
    PolynomialFieldCode (dimension n) :=
  fun k ↦
    match finSumFinEquiv.symm k with
    | Sum.inl i => liftBase (F i)
    | Sum.inr j =>
        ![reciprocalVelocityReCode η wdot,
          reciprocalVelocityImCode η wdot] j

/-- Real part of `1-ηw`. -/
def denominatorReCode
    (η : RationalCode) (w : ComplexObservableCode n) :
    PolynomialCode (dimension n) :=
  PolynomialCode.sub oneCode
    (PolynomialCode.mul (etaCode η) (liftBase w.1))

/-- Imaginary part of `1-ηw`, namely `-η Im(w)`. -/
def denominatorImCode
    (η : RationalCode) (w : ComplexObservableCode n) :
    PolynomialCode (dimension n) :=
  PolynomialCode.neg
    (PolynomialCode.mul (etaCode η) (liftBase w.2))

/-- Real part of the reciprocal residual `(1-ηw)g-1`. -/
def residualReCode
    (η : RationalCode) (w : ComplexObservableCode n) :
    PolynomialCode (dimension n) :=
  PolynomialCode.sub
    (PolynomialCode.sub
      (PolynomialCode.mul (denominatorReCode η w)
        reciprocalReCode)
      (PolynomialCode.mul (denominatorImCode η w)
        reciprocalImCode))
    oneCode

/-- Imaginary part of the reciprocal residual `(1-ηw)g-1`. -/
def residualImCode
    (η : RationalCode) (w : ComplexObservableCode n) :
    PolynomialCode (dimension n) :=
  PolynomialCode.add
    (PolynomialCode.mul (denominatorReCode η w)
      reciprocalImCode)
    (PolynomialCode.mul (denominatorImCode η w)
      reciprocalReCode)

/-! ## Exact evaluation semantics -/

noncomputable def evalObservable
    (p : ComplexObservableCode n) (x : Fin n → ℝ) : ℂ :=
  ⟨eval₂Hom (algebraMap ℚ ℝ) x (PolynomialCode.decode p.1),
    eval₂Hom (algebraMap ℚ ℝ) x (PolynomialCode.decode p.2)⟩

noncomputable def vectorField
    (F : PolynomialFieldCode n)
    (η : RationalCode) (wdot : ComplexObservableCode n)
    (z : State n) : State n :=
  (PolynomialFieldCode.realize F z.1,
    reciprocalVelocity
      ((RationalCode.decode η : ℝ) : ℂ)
      (evalObservable wdot z.1) z.2)

/-- Real-coordinate formula for the generic complex reciprocal velocity. -/
theorem reciprocalVelocity_re_formula
    (η : ℝ) (v g : ℂ) :
    (reciprocalVelocity (η : ℂ) v g).re =
      η * (v.re * (g.re ^ 2 - g.im ^ 2) -
        v.im * (2 * g.re * g.im)) := by
  simp [reciprocalVelocity, pow_two, Complex.mul_re,
    Complex.mul_im]
  ring

/-- Imaginary-coordinate formula for the generic complex reciprocal
velocity. -/
theorem reciprocalVelocity_im_formula
    (η : ℝ) (v g : ℂ) :
    (reciprocalVelocity (η : ℂ) v g).im =
      η * (v.re * (2 * g.re * g.im) +
        v.im * (g.re ^ 2 - g.im ^ 2)) := by
  simp [reciprocalVelocity, pow_two, Complex.mul_re,
    Complex.mul_im]
  ring

/-- Real-coordinate formula for the complex reciprocal residual. -/
theorem reciprocalResidual_re_formula
    (η : ℝ) (w g : ℂ) :
    (reciprocalResidual (η : ℂ) w g).re =
      (1 - η * w.re) * g.re + η * w.im * g.im - 1 := by
  simp [reciprocalResidual, Complex.mul_re, Complex.mul_im]

/-- Imaginary-coordinate formula for the complex reciprocal residual. -/
theorem reciprocalResidual_im_formula
    (η : ℝ) (w g : ℂ) :
    (reciprocalResidual (η : ℂ) w g).im =
      (1 - η * w.re) * g.im - η * w.im * g.re := by
  simp [reciprocalResidual, Complex.mul_re, Complex.mul_im]
  ring

@[simp]
theorem eval₂Hom_liftBase
    {R : Type*} [CommSemiring R] [Algebra ℚ R]
    (p : PolynomialCode n)
    (x : Fin n → R) (g : Fin 2 → R) :
    eval₂Hom (algebraMap ℚ R)
        (PolynomialBlockCode.point x g)
        (PolynomialCode.decode (liftBase p)) =
      eval₂Hom (algebraMap ℚ R) x
        (PolynomialCode.decode p) := by
  simp [liftBase]

@[simp]
theorem eval₂Hom_liftBase_point
    (p : PolynomialCode n) (z : State n) :
    eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode (liftBase p)) =
      eval₂Hom (algebraMap ℚ ℝ) z.1
        (PolynomialCode.decode p) := by
  exact eval₂Hom_liftBase p z.1 ![z.2.re, z.2.im]

@[simp]
theorem eval₂Hom_reciprocalReCode
    (z : State n) :
    eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode
          (reciprocalReCode :
            PolynomialCode (dimension n))) = z.2.re := by
  simp [reciprocalReCode]

@[simp]
theorem eval₂Hom_reciprocalImCode
    (z : State n) :
    eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode
          (reciprocalImCode :
            PolynomialCode (dimension n))) = z.2.im := by
  simp [reciprocalImCode]

@[simp]
theorem eval₂Hom_etaCode
    (η : RationalCode) (z : State n) :
    eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode (etaCode η)) =
      (RationalCode.decode η : ℝ) := by
  simp [etaCode]

@[simp]
theorem eval₂Hom_oneCode
    (z : State n) :
    eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode
          (oneCode : PolynomialCode (dimension n))) = 1 := by
  simp [oneCode]

@[simp]
theorem eval₂Hom_twoCode
    (z : State n) :
    eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode
          (twoCode : PolynomialCode (dimension n))) = 2 := by
  simp [twoCode]

@[simp]
theorem eval₂Hom_reciprocalSquareReCode
    (z : State n) :
    eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode
          (reciprocalSquareReCode :
            PolynomialCode (dimension n))) =
      z.2.re ^ 2 - z.2.im ^ 2 := by
  simp only [reciprocalSquareReCode,
    PolynomialCode.decode_sub_code,
    PolynomialCode.decode_mul_code, map_sub, map_mul]
  rw [eval₂Hom_reciprocalReCode,
    eval₂Hom_reciprocalImCode]
  ring

@[simp]
theorem eval₂Hom_reciprocalSquareImCode
    (z : State n) :
    eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode
          (reciprocalSquareImCode :
            PolynomialCode (dimension n))) =
      2 * z.2.re * z.2.im := by
  simp only [reciprocalSquareImCode,
    PolynomialCode.decode_mul_code, map_mul]
  rw [eval₂Hom_twoCode, eval₂Hom_reciprocalReCode,
    eval₂Hom_reciprocalImCode]
  ring

@[simp]
theorem eval₂Hom_reciprocalVelocityReCode
    (η : RationalCode) (wdot : ComplexObservableCode n)
    (z : State n) :
    eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode
          (reciprocalVelocityReCode η wdot)) =
      (reciprocalVelocity
        ((RationalCode.decode η : ℝ) : ℂ)
        (evalObservable wdot z.1) z.2).re := by
  simp only [reciprocalVelocityReCode,
    PolynomialCode.decode_mul_code,
    PolynomialCode.decode_sub_code, map_mul, map_sub,
    eval₂Hom_etaCode, eval₂Hom_liftBase_point,
    eval₂Hom_reciprocalSquareReCode,
    eval₂Hom_reciprocalSquareImCode]
  rw [reciprocalVelocity_re_formula]
  simp only [evalObservable]

@[simp]
theorem eval₂Hom_reciprocalVelocityImCode
    (η : RationalCode) (wdot : ComplexObservableCode n)
    (z : State n) :
    eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode
          (reciprocalVelocityImCode η wdot)) =
      (reciprocalVelocity
        ((RationalCode.decode η : ℝ) : ℂ)
        (evalObservable wdot z.1) z.2).im := by
  simp only [reciprocalVelocityImCode,
    PolynomialCode.decode_mul_code,
    PolynomialCode.decode_add_code, map_mul, map_add,
    eval₂Hom_etaCode, eval₂Hom_liftBase_point,
    eval₂Hom_reciprocalSquareReCode,
    eval₂Hom_reciprocalSquareImCode]
  rw [reciprocalVelocity_im_formula]
  simp only [evalObservable]

@[simp]
theorem fieldCode_baseEmbedding
    (F : PolynomialFieldCode n)
    (η : RationalCode) (wdot : ComplexObservableCode n)
    (i : Fin n) :
    fieldCode F η wdot (baseEmbedding i) =
      liftBase (F i) := by
  simp [fieldCode, baseEmbedding]

@[simp]
theorem fieldCode_reciprocalReIndex
    (F : PolynomialFieldCode n)
    (η : RationalCode) (wdot : ComplexObservableCode n) :
    fieldCode F η wdot (reciprocalReIndex n) =
      reciprocalVelocityReCode η wdot := by
  simp [fieldCode, reciprocalReIndex]

@[simp]
theorem fieldCode_reciprocalImIndex
    (F : PolynomialFieldCode n)
    (η : RationalCode) (wdot : ComplexObservableCode n) :
    fieldCode F η wdot (reciprocalImIndex n) =
      reciprocalVelocityImCode η wdot := by
  simp [fieldCode, reciprocalImIndex]

@[simp]
theorem realize_fieldCode
    (F : PolynomialFieldCode n)
    (η : RationalCode) (wdot : ComplexObservableCode n)
    (z : State n) :
    PolynomialFieldCode.realize (fieldCode F η wdot) (point z) =
      point (vectorField F η wdot z) := by
  funext k
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective k
  · change
      PolynomialFieldCode.realize (fieldCode F η wdot) (point z)
          (baseEmbedding i) =
        point (vectorField F η wdot z) (baseEmbedding i)
    rw [PolynomialFieldCode.realize_apply,
      fieldCode_baseEmbedding, eval₂Hom_liftBase_point,
      point_baseEmbedding]
    rfl
  · fin_cases j
    · change
        PolynomialFieldCode.realize (fieldCode F η wdot) (point z)
            (reciprocalReIndex n) =
          point (vectorField F η wdot z) (reciprocalReIndex n)
      rw [PolynomialFieldCode.realize_apply,
        fieldCode_reciprocalReIndex,
        eval₂Hom_reciprocalVelocityReCode,
        point_reciprocalReIndex]
      rfl
    · change
        PolynomialFieldCode.realize (fieldCode F η wdot) (point z)
            (reciprocalImIndex n) =
          point (vectorField F η wdot z) (reciprocalImIndex n)
      rw [PolynomialFieldCode.realize_apply,
        fieldCode_reciprocalImIndex,
        eval₂Hom_reciprocalVelocityImCode,
        point_reciprocalImIndex]
      rfl

/-- Exact field semantics at an arbitrary ambient point. -/
@[simp]
theorem realize_fieldCode_arbitrary
    (F : PolynomialFieldCode n)
    (η : RationalCode) (wdot : ComplexObservableCode n)
    (x : Fin (dimension n) → ℝ) :
    PolynomialFieldCode.realize (fieldCode F η wdot) x =
      point (vectorField F η wdot (state x)) := by
  simpa using realize_fieldCode F η wdot (state x)

@[simp]
theorem eval₂Hom_residualReCode
    (η : RationalCode) (w : ComplexObservableCode n)
    (z : State n) :
    eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode (residualReCode η w)) =
      (reciprocalResidual
        ((RationalCode.decode η : ℝ) : ℂ)
        (evalObservable w z.1) z.2).re := by
  simp only [residualReCode, denominatorReCode,
    denominatorImCode, PolynomialCode.decode_sub_code,
    PolynomialCode.decode_mul_code, PolynomialCode.decode_neg_code,
    map_sub, map_mul, map_neg, eval₂Hom_oneCode,
    eval₂Hom_etaCode, eval₂Hom_liftBase_point,
    eval₂Hom_reciprocalReCode, eval₂Hom_reciprocalImCode]
  rw [reciprocalResidual_re_formula]
  simp only [evalObservable]
  ring

@[simp]
theorem eval₂Hom_residualImCode
    (η : RationalCode) (w : ComplexObservableCode n)
    (z : State n) :
    eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode (residualImCode η w)) =
      (reciprocalResidual
        ((RationalCode.decode η : ℝ) : ℂ)
        (evalObservable w z.1) z.2).im := by
  simp only [residualImCode, denominatorReCode,
    denominatorImCode, PolynomialCode.decode_add_code,
    PolynomialCode.decode_sub_code, PolynomialCode.decode_mul_code,
    PolynomialCode.decode_neg_code, map_add, map_sub, map_mul,
    map_neg, eval₂Hom_oneCode, eval₂Hom_etaCode,
    eval₂Hom_liftBase_point, eval₂Hom_reciprocalReCode,
    eval₂Hom_reciprocalImCode]
  rw [reciprocalResidual_im_formula]
  simp only [evalObservable]
  ring

/-- The two scalar residual codes vanish exactly when the complex
reciprocal graph equation holds. -/
theorem residualCodes_eq_zero_iff
    (η : RationalCode) (w : ComplexObservableCode n)
    (z : State n) :
    (eval₂Hom (algebraMap ℚ ℝ) (point z)
          (PolynomialCode.decode (residualReCode η w)) = 0 ∧
        eval₂Hom (algebraMap ℚ ℝ) (point z)
          (PolynomialCode.decode (residualImCode η w)) = 0) ↔
      reciprocalResidual
          ((RationalCode.decode η : ℝ) : ℂ)
          (evalObservable w z.1) z.2 = 0 := by
  rw [eval₂Hom_residualReCode, eval₂Hom_residualImCode]
  constructor
  · rintro ⟨hre, him⟩
    apply Complex.ext
    · simpa using hre
    · simpa using him
  · intro h
    rw [h]
    simp

/-! ## Trajectory-level graph propagation -/

/-- A structured trajectory of the compiled extension, together with the
assertion that `wdot` is the actual derivative of `w`, supplies the generic
reciprocal-graph trajectory interface. -/
theorem isReciprocalGraphTrajectory
    (η : RationalCode) (w wdot : ComplexObservableCode n)
    (z : ℝ → State n)
    (hw :
      ∀ t,
        HasDerivAt
          (fun s ↦ evalObservable w (z s).1)
          (evalObservable wdot (z t).1) t)
    (hg :
      ∀ t,
        HasDerivAt (fun s ↦ (z s).2)
          (reciprocalVelocity
            ((RationalCode.decode η : ℝ) : ℂ)
            (evalObservable wdot (z t).1) (z t).2) t)
    (hwdot :
      Continuous
        (fun t ↦ evalObservable wdot (z t).1)) :
    IsReciprocalGraphTrajectory
      ((RationalCode.decode η : ℝ) : ℂ)
      (fun t ↦ evalObservable w (z t).1)
      (fun t ↦ (z t).2)
      (fun t ↦ evalObservable wdot (z t).1) where
  w_hasDerivAt := hw
  g_hasDerivAt := hg
  continuous_wdot := hwdot

/-- If the reciprocal equation holds once along such a trajectory, it
holds for all real time. -/
theorem residual_eq_zero_along_trajectory
    (η : RationalCode) (w wdot : ComplexObservableCode n)
    (z : ℝ → State n)
    (hw :
      ∀ t,
        HasDerivAt
          (fun s ↦ evalObservable w (z s).1)
          (evalObservable wdot (z t).1) t)
    (hg :
      ∀ t,
        HasDerivAt (fun s ↦ (z s).2)
          (reciprocalVelocity
            ((RationalCode.decode η : ℝ) : ℂ)
            (evalObservable wdot (z t).1) (z t).2) t)
    (hwdot :
      Continuous
        (fun t ↦ evalObservable wdot (z t).1))
    {t₀ : ℝ}
    (hzero :
      reciprocalResidual
          ((RationalCode.decode η : ℝ) : ℂ)
          (evalObservable w (z t₀).1) (z t₀).2 = 0) :
    ∀ t,
      reciprocalResidual
          ((RationalCode.decode η : ℝ) : ℂ)
          (evalObservable w (z t).1) (z t).2 = 0 :=
  (isReciprocalGraphTrajectory η w wdot z hw hg hwdot).residual_eq_zero
    hzero

end ComplexReciprocalPolynomialCode

end HGAS
