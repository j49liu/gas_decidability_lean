import HGAS.Clocks.ControllerPhaseProductCharacterCode
import HGAS.Compiler.ComplexReciprocalFamilyPolynomialCode
import Mathlib.Tactic

/-!
# Finite families of polynomial fourth-root gauges

This module adjoins a finite family of complex gauge coordinates to an
arbitrary real polynomial source.  The construction is deliberately
independent of the modular application.

For a real source point `x`, a real polynomial frequency `νₐ(x)`, and a
complex polynomial character `χₐ(x)`, gauge block `a` satisfies

```text
                    Gₐ' = (i/4) νₐ(x) Gₐ.
```

It carries the algebraic residual

```text
                    Gₐ⁴ - λₐ χₐ(x)
```

and can multiply any complex base observable `Tₐ(x)` to produce the
polynomial output `GₐTₐ(x)`.  In the Jacobi application,
`χₐ = exp(i(αₐ+2βₐ))`, `νₐ = αₐ' + 2βₐ'`, and this output is the
unshifted theta function.

The same interleaved two-real-coordinate layout as the reciprocal-family
compiler is reused.  All realization theorems hold at arbitrary ambient
points; no circle, residual, or nonvanishing hypothesis is used.
-/

namespace HGAS

namespace ComplexGaugeFamilyPolynomialCode

open _root_.MvPolynomial
open Clocks.ControllerPhaseProductCharacterCode

variable {n b : ℕ}

/-- A complex polynomial observable over `n` real source coordinates. -/
abbrev ComplexObservableCode (n : ℕ) :=
  ComplexPairCode n

/-- One complex gauge occupies two real coordinates. -/
abbrev localGaugeDimension : ℕ := 2

/-- Number of real coordinates occupied by `b` gauges. -/
abbrev gaugeDimension (b : ℕ) : ℕ :=
  b * localGaugeDimension

/-- Total dimension of the source together with all gauges. -/
abbrev dimension (n b : ℕ) : ℕ :=
  ComplexReciprocalFamilyPolynomialCode.dimension n b

/-- A source point together with one complex gauge in each block. -/
abbrev State (n b : ℕ) :=
  ComplexReciprocalFamilyPolynomialCode.State n b

/-- A finite family of complex source observables. -/
abbrev ObservableFamily (n b : ℕ) :=
  Fin b → ComplexObservableCode n

def baseEmbedding : Fin n ↪ Fin (dimension n b) :=
  ComplexReciprocalFamilyPolynomialCode.baseEmbedding

def gaugeFamilyEmbedding :
    Fin (gaugeDimension b) ↪ Fin (dimension n b) :=
  ComplexReciprocalFamilyPolynomialCode.reciprocalFamilyEmbedding

def gaugeBlockEmbedding (a : Fin b) :
    Fin localGaugeDimension ↪ Fin (gaugeDimension b) :=
  ComplexReciprocalFamilyPolynomialCode.reciprocalBlockEmbedding a

def gaugeEmbedding (a : Fin b) :
    Fin localGaugeDimension ↪ Fin (dimension n b) :=
  ComplexReciprocalFamilyPolynomialCode.reciprocalEmbedding a

def gaugeReIndex (a : Fin b) : Fin (dimension n b) :=
  ComplexReciprocalFamilyPolynomialCode.reciprocalReIndex a

def gaugeImIndex (a : Fin b) : Fin (dimension n b) :=
  ComplexReciprocalFamilyPolynomialCode.reciprocalImIndex a

def gaugePoint (G : Fin b → ℂ) :
    Fin (gaugeDimension b) → ℝ :=
  ComplexReciprocalFamilyPolynomialCode.reciprocalPoint G

def point (z : State n b) : Fin (dimension n b) → ℝ :=
  ComplexReciprocalFamilyPolynomialCode.point z

def state (x : Fin (dimension n b) → ℝ) : State n b :=
  ComplexReciprocalFamilyPolynomialCode.state x

@[simp]
theorem point_baseEmbedding
    (z : State n b) (i : Fin n) :
    point z (baseEmbedding i) = z.1 i := by
  exact
    ComplexReciprocalFamilyPolynomialCode.point_baseEmbedding z i

@[simp]
theorem point_gaugeEmbedding
    (z : State n b) (a : Fin b) (j : Fin 2) :
    point z (gaugeEmbedding a j) =
      ![(z.2 a).re, (z.2 a).im] j := by
  exact
    ComplexReciprocalFamilyPolynomialCode.point_reciprocalEmbedding
      z a j

@[simp]
theorem point_gaugeReIndex
    (z : State n b) (a : Fin b) :
    point z (gaugeReIndex a) = (z.2 a).re := by
  exact
    ComplexReciprocalFamilyPolynomialCode.point_reciprocalReIndex z a

@[simp]
theorem point_gaugeImIndex
    (z : State n b) (a : Fin b) :
    point z (gaugeImIndex a) = (z.2 a).im := by
  exact
    ComplexReciprocalFamilyPolynomialCode.point_reciprocalImIndex z a

@[simp]
theorem state_point (z : State n b) :
    state (point z) = z :=
  ComplexReciprocalFamilyPolynomialCode.state_point z

@[simp]
theorem point_state
    (x : Fin (dimension n b) → ℝ) :
    point (state x) = x :=
  ComplexReciprocalFamilyPolynomialCode.point_state x

/-! ## Complex-pair syntax in the enlarged real state -/

def liftBase (p : PolynomialCode n) :
    PolynomialCode (dimension n b) :=
  ComplexReciprocalFamilyPolynomialCode.liftBase p

def liftBasePair (p : ComplexObservableCode n) :
    ComplexObservableCode (dimension n b) :=
  (liftBase p.1, liftBase p.2)

def gaugeReCode (a : Fin b) :
    PolynomialCode (dimension n b) :=
  PolynomialCode.varCode (gaugeReIndex a)

def gaugeImCode (a : Fin b) :
    PolynomialCode (dimension n b) :=
  PolynomialCode.varCode (gaugeImIndex a)

/-- The complex coordinate `Gₐ`. -/
def gaugeCode (a : Fin b) :
    ComplexObservableCode (dimension n b) :=
  (gaugeReCode a, gaugeImCode a)

def sub
    (p q : ComplexObservableCode (dimension n b)) :
    ComplexObservableCode (dimension n b) :=
  (PolynomialCode.sub p.1 q.1,
    PolynomialCode.sub p.2 q.2)

def rationalConstant
    (c : RationalCode) :
    ComplexObservableCode (dimension n b) :=
  (PolynomialCode.constant c, PolynomialCode.zero)

@[simp]
theorem evalPair_sub
    (p q : ComplexObservableCode (dimension n b))
    (x : Fin (dimension n b) → ℝ) :
    evalPair (sub p q) x = evalPair p x - evalPair q x := by
  apply Complex.ext <;> simp [evalPair, sub]

@[simp]
theorem evalPair_rationalConstant
    (c : RationalCode)
    (x : Fin (dimension n b) → ℝ) :
    evalPair (rationalConstant c) x =
      ((RationalCode.decode c : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [evalPair, rationalConstant]

@[simp]
theorem evalPair_liftBasePair
    (p : ComplexObservableCode n)
    (z : State n b) :
    evalPair (liftBasePair p) (point z) =
      evalPair p z.1 := by
  apply Complex.ext <;>
    simp [evalPair, liftBasePair, liftBase, point]

@[simp]
theorem evalPair_gaugeCode
    (z : State n b) (a : Fin b) :
    evalPair (gaugeCode a) (point z) = z.2 a := by
  apply Complex.ext <;>
    simp [evalPair, gaugeCode, gaugeReCode, gaugeImCode]

/-! ## Gauge field and exact realization -/

def quarterCode : RationalCode :=
  RationalCode.encode (1 / 4 : ℚ)

/-- Code for the purely imaginary logarithmic coefficient
`(i/4)νₐ(x)`. -/
def logarithmicCoefficientCode
    (frequency : Fin b → PolynomialCode n)
    (a : Fin b) :
    ComplexObservableCode (dimension n b) :=
  (PolynomialCode.zero,
    PolynomialCode.mul
      (PolynomialCode.constant quarterCode)
      (liftBase (frequency a)))

/-- Real and imaginary velocity codes for `Gₐ'=(i/4)νₐGₐ`. -/
def gaugeVelocityCode
    (frequency : Fin b → PolynomialCode n)
    (a : Fin b) :
    ComplexObservableCode (dimension n b) :=
  mul (logarithmicCoefficientCode frequency a)
    (gaugeCode a)

noncomputable def evalRealObservable
    (p : PolynomialCode n) (x : Fin n → ℝ) : ℝ :=
  eval₂Hom (algebraMap ℚ ℝ) x
    (PolynomialCode.decode p)

noncomputable def gaugeVelocity
    (frequency : Fin b → PolynomialCode n)
    (z : State n b) (a : Fin b) : ℂ :=
  Complex.I *
    ((evalRealObservable (frequency a) z.1 / 4 : ℝ) : ℂ) *
      z.2 a

@[simp]
theorem evalPair_logarithmicCoefficientCode
    (frequency : Fin b → PolynomialCode n)
    (z : State n b) (a : Fin b) :
    evalPair (logarithmicCoefficientCode frequency a)
        (point z) =
      Complex.I *
        ((evalRealObservable (frequency a) z.1 / 4 : ℝ) : ℂ) := by
  have hfrequency :
      eval₂Hom (algebraMap ℚ ℝ) (point z)
          (PolynomialCode.decode (liftBase (frequency a))) =
        evalRealObservable (frequency a) z.1 := by
    exact
      ComplexReciprocalFamilyPolynomialCode.eval₂Hom_liftBase_point
        (frequency a) z
  apply Complex.ext
  · simp [logarithmicCoefficientCode, evalPair, quarterCode,
      Complex.mul_re]
  · change
      eval₂Hom (algebraMap ℚ ℝ) (point z)
          (PolynomialCode.decode
            (PolynomialCode.mul
              (PolynomialCode.constant quarterCode)
              (liftBase (frequency a)))) =
        (Complex.I *
          ((evalRealObservable (frequency a) z.1 / 4 : ℝ) : ℂ)).im
    rw [PolynomialCode.decode_mul_code, map_mul,
      PolynomialCode.decode_constant, eval₂Hom_C, hfrequency]
    simp [quarterCode, Complex.mul_im, div_eq_mul_inv]
    ring

@[simp]
theorem evalPair_gaugeVelocityCode
    (frequency : Fin b → PolynomialCode n)
    (z : State n b) (a : Fin b) :
    evalPair (gaugeVelocityCode frequency a) (point z) =
      gaugeVelocity frequency z a := by
  simp [gaugeVelocityCode, gaugeVelocity]

/-- Extend a base field by all gauge equations. -/
def fieldCode
    (F : PolynomialFieldCode n)
    (frequency : Fin b → PolynomialCode n) :
    PolynomialFieldCode (dimension n b) :=
  fun k ↦
    match finSumFinEquiv.symm k with
    | Sum.inl i => liftBase (F i)
    | Sum.inr r =>
        let aj := finProdFinEquiv.symm r
        ![(gaugeVelocityCode frequency aj.1).1,
          (gaugeVelocityCode frequency aj.1).2] aj.2

@[simp]
theorem fieldCode_baseEmbedding
    (F : PolynomialFieldCode n)
    (frequency : Fin b → PolynomialCode n)
    (i : Fin n) :
    fieldCode F frequency (baseEmbedding i) =
      liftBase (F i) := by
  change
    fieldCode F frequency
        (PolynomialBlockCode.leftEmbedding
          (p := gaugeDimension b) i) =
      liftBase (F i)
  unfold fieldCode
  rw [PolynomialBlockCode.finSumFinEquiv_symm_leftEmbedding]

@[simp]
theorem fieldCode_gaugeReIndex
    (F : PolynomialFieldCode n)
    (frequency : Fin b → PolynomialCode n)
    (a : Fin b) :
    fieldCode F frequency (gaugeReIndex a) =
      (gaugeVelocityCode frequency a).1 := by
  change
    fieldCode F frequency
        (PolynomialBlockCode.rightEmbedding
          (m := n)
          (gaugeBlockEmbedding a (0 : Fin 2))) =
      (gaugeVelocityCode frequency a).1
  unfold fieldCode
  rw [PolynomialBlockCode.finSumFinEquiv_symm_rightEmbedding]
  simp only
  unfold gaugeBlockEmbedding
    ComplexReciprocalFamilyPolynomialCode.reciprocalBlockEmbedding
  rw [
    PolynomialFiniteProductCode.finProdFinEquiv_symm_blockEmbedding]
  rfl

@[simp]
theorem fieldCode_gaugeImIndex
    (F : PolynomialFieldCode n)
    (frequency : Fin b → PolynomialCode n)
    (a : Fin b) :
    fieldCode F frequency (gaugeImIndex a) =
      (gaugeVelocityCode frequency a).2 := by
  change
    fieldCode F frequency
        (PolynomialBlockCode.rightEmbedding
          (m := n)
          (gaugeBlockEmbedding a (1 : Fin 2))) =
      (gaugeVelocityCode frequency a).2
  unfold fieldCode
  rw [PolynomialBlockCode.finSumFinEquiv_symm_rightEmbedding]
  simp only
  unfold gaugeBlockEmbedding
    ComplexReciprocalFamilyPolynomialCode.reciprocalBlockEmbedding
  rw [
    PolynomialFiniteProductCode.finProdFinEquiv_symm_blockEmbedding]
  rfl

noncomputable def vectorField
    (F : PolynomialFieldCode n)
    (frequency : Fin b → PolynomialCode n)
    (z : State n b) : State n b :=
  (PolynomialFieldCode.realize F z.1,
    fun a ↦ gaugeVelocity frequency z a)

@[simp]
theorem eval₂Hom_liftBase_point
    (p : PolynomialCode n) (z : State n b) :
    eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode (liftBase p)) =
      eval₂Hom (algebraMap ℚ ℝ) z.1
        (PolynomialCode.decode p) := by
  exact
    ComplexReciprocalFamilyPolynomialCode.eval₂Hom_liftBase_point p z

@[simp]
theorem eval₂Hom_gaugeVelocityReCode
    (frequency : Fin b → PolynomialCode n)
    (z : State n b) (a : Fin b) :
    eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode
          (gaugeVelocityCode frequency a).1) =
      (gaugeVelocity frequency z a).re := by
  have h :=
    congrArg Complex.re
      (evalPair_gaugeVelocityCode frequency z a)
  simpa [evalPair] using h

@[simp]
theorem eval₂Hom_gaugeVelocityImCode
    (frequency : Fin b → PolynomialCode n)
    (z : State n b) (a : Fin b) :
    eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode
          (gaugeVelocityCode frequency a).2) =
      (gaugeVelocity frequency z a).im := by
  have h :=
    congrArg Complex.im
      (evalPair_gaugeVelocityCode frequency z a)
  simpa [evalPair] using h

@[simp]
theorem realize_fieldCode
    (F : PolynomialFieldCode n)
    (frequency : Fin b → PolynomialCode n)
    (z : State n b) :
    PolynomialFieldCode.realize
        (fieldCode F frequency) (point z) =
      point (vectorField F frequency z) := by
  funext k
  obtain ⟨i | r, rfl⟩ := finSumFinEquiv.surjective k
  · change
      PolynomialFieldCode.realize
          (fieldCode F frequency) (point z)
          (baseEmbedding i) =
        point (vectorField F frequency z) (baseEmbedding i)
    rw [PolynomialFieldCode.realize_apply,
      fieldCode_baseEmbedding, eval₂Hom_liftBase_point,
      point_baseEmbedding]
    rfl
  · obtain ⟨⟨a, j⟩, rfl⟩ :=
      finProdFinEquiv.surjective r
    fin_cases j
    · change
        PolynomialFieldCode.realize
            (fieldCode F frequency) (point z)
            (gaugeReIndex a) =
          point (vectorField F frequency z) (gaugeReIndex a)
      rw [PolynomialFieldCode.realize_apply,
        fieldCode_gaugeReIndex,
        eval₂Hom_gaugeVelocityReCode,
        point_gaugeReIndex]
      rfl
    · change
        PolynomialFieldCode.realize
            (fieldCode F frequency) (point z)
            (gaugeImIndex a) =
          point (vectorField F frequency z) (gaugeImIndex a)
      rw [PolynomialFieldCode.realize_apply,
        fieldCode_gaugeImIndex,
        eval₂Hom_gaugeVelocityImCode,
        point_gaugeImIndex]
      rfl

@[simp]
theorem realize_fieldCode_arbitrary
    (F : PolynomialFieldCode n)
    (frequency : Fin b → PolynomialCode n)
    (x : Fin (dimension n b) → ℝ) :
    PolynomialFieldCode.realize (fieldCode F frequency) x =
      point (vectorField F frequency (state x)) := by
  simpa using realize_fieldCode F frequency (state x)

/-! ## Fourth-root residuals and polynomial outputs -/

def scaledCharacterCode
    (scale : Fin b → RationalCode)
    (character : ObservableFamily n b)
    (a : Fin b) :
    ComplexObservableCode (dimension n b) :=
  mul (rationalConstant (scale a))
    (liftBasePair (character a))

/-- Complex pair code for `Gₐ⁴-λₐχₐ`. -/
def residualPairCode
    (scale : Fin b → RationalCode)
    (character : ObservableFamily n b)
    (a : Fin b) :
    ComplexObservableCode (dimension n b) :=
  sub (pow (gaugeCode a) 4)
    (scaledCharacterCode scale character a)

def residualReCode
    (scale : Fin b → RationalCode)
    (character : ObservableFamily n b)
    (a : Fin b) :
    PolynomialCode (dimension n b) :=
  (residualPairCode scale character a).1

def residualImCode
    (scale : Fin b → RationalCode)
    (character : ObservableFamily n b)
    (a : Fin b) :
    PolynomialCode (dimension n b) :=
  (residualPairCode scale character a).2

def residualCode
    (scale : Fin b → RationalCode)
    (character : ObservableFamily n b) :
    Fin (gaugeDimension b) →
      PolynomialCode (dimension n b) :=
  fun k ↦
    let aj := finProdFinEquiv.symm k
    ![residualReCode scale character aj.1,
      residualImCode scale character aj.1] aj.2

noncomputable def residual
    (scale : Fin b → RationalCode)
    (character : ObservableFamily n b)
    (z : State n b) (a : Fin b) : ℂ :=
  z.2 a ^ 4 -
    ((RationalCode.decode (scale a) : ℝ) : ℂ) *
      evalPair (character a) z.1

@[simp]
theorem evalPair_residualPairCode
    (scale : Fin b → RationalCode)
    (character : ObservableFamily n b)
    (z : State n b) (a : Fin b) :
    evalPair (residualPairCode scale character a)
        (point z) =
      residual scale character z a := by
  simp [residualPairCode, scaledCharacterCode, residual]

@[simp]
theorem eval₂Hom_residualReCode
    (scale : Fin b → RationalCode)
    (character : ObservableFamily n b)
    (z : State n b) (a : Fin b) :
    eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode
          (residualReCode scale character a)) =
      (residual scale character z a).re := by
  have h :=
    congrArg Complex.re
      (evalPair_residualPairCode scale character z a)
  simpa [evalPair, residualReCode] using h

@[simp]
theorem eval₂Hom_residualImCode
    (scale : Fin b → RationalCode)
    (character : ObservableFamily n b)
    (z : State n b) (a : Fin b) :
    eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode
          (residualImCode scale character a)) =
      (residual scale character z a).im := by
  have h :=
    congrArg Complex.im
      (evalPair_residualPairCode scale character z a)
  simpa [evalPair, residualImCode] using h

theorem residualCodes_eq_zero_iff
    (scale : Fin b → RationalCode)
    (character : ObservableFamily n b)
    (z : State n b) (a : Fin b) :
    (eval₂Hom (algebraMap ℚ ℝ) (point z)
          (PolynomialCode.decode
            (residualReCode scale character a)) = 0 ∧
        eval₂Hom (algebraMap ℚ ℝ) (point z)
          (PolynomialCode.decode
            (residualImCode scale character a)) = 0) ↔
      residual scale character z a = 0 := by
  rw [eval₂Hom_residualReCode, eval₂Hom_residualImCode]
  constructor
  · rintro ⟨hre, him⟩
    apply Complex.ext <;> simpa
  · intro h
    rw [h]
    simp

@[simp]
theorem residualCode_gaugeBlockEmbedding
    (scale : Fin b → RationalCode)
    (character : ObservableFamily n b)
    (a : Fin b) (j : Fin 2) :
    residualCode scale character (gaugeBlockEmbedding a j) =
      ![residualReCode scale character a,
        residualImCode scale character a] j := by
  unfold residualCode gaugeBlockEmbedding
    ComplexReciprocalFamilyPolynomialCode.reciprocalBlockEmbedding
  rw [
    PolynomialFiniteProductCode.finProdFinEquiv_symm_blockEmbedding]

/-- All scalar residual coordinates vanish exactly when all complex
fourth-root equations hold. -/
theorem forall_eval_residualCode_eq_zero_iff
    (scale : Fin b → RationalCode)
    (character : ObservableFamily n b)
    (z : State n b) :
    (∀ k,
      eval₂Hom (algebraMap ℚ ℝ) (point z)
        (PolynomialCode.decode
          (residualCode scale character k)) = 0) ↔
      ∀ a, residual scale character z a = 0 := by
  constructor
  · intro h a
    apply (residualCodes_eq_zero_iff scale character z a).1
    constructor
    · simpa using h (gaugeBlockEmbedding a (0 : Fin 2))
    · simpa using h (gaugeBlockEmbedding a (1 : Fin 2))
  · intro h k
    obtain ⟨⟨a, j⟩, rfl⟩ :=
      finProdFinEquiv.surjective k
    have ha :=
      (residualCodes_eq_zero_iff scale character z a).2 (h a)
    fin_cases j
    · change
        eval₂Hom (algebraMap ℚ ℝ) (point z)
          (PolynomialCode.decode
            (residualCode scale character
              (gaugeBlockEmbedding a (0 : Fin 2)))) = 0
      rw [residualCode_gaugeBlockEmbedding]
      exact ha.1
    · change
        eval₂Hom (algebraMap ℚ ℝ) (point z)
          (PolynomialCode.decode
            (residualCode scale character
              (gaugeBlockEmbedding a (1 : Fin 2)))) = 0
      rw [residualCode_gaugeBlockEmbedding]
      exact ha.2

/-- Ambient-point form of simultaneous gauge residual semantics. -/
theorem forall_eval_residualCode_eq_zero_iff_arbitrary
    (scale : Fin b → RationalCode)
    (character : ObservableFamily n b)
    (x : Fin (dimension n b) → ℝ) :
    (∀ k,
      eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode
          (residualCode scale character k)) = 0) ↔
      ∀ a, residual scale character (state x) a = 0 := by
  simpa using
    forall_eval_residualCode_eq_zero_iff
      scale character (state x)

/-- Complex pair code for the gauge-corrected output `GₐTₐ`. -/
def outputCode
    (observable : ObservableFamily n b)
    (a : Fin b) :
    ComplexObservableCode (dimension n b) :=
  mul (gaugeCode a)
    (liftBasePair (observable a))

noncomputable def output
    (observable : ObservableFamily n b)
    (z : State n b) (a : Fin b) : ℂ :=
  z.2 a * evalPair (observable a) z.1

@[simp]
theorem evalPair_outputCode
    (observable : ObservableFamily n b)
    (z : State n b) (a : Fin b) :
    evalPair (outputCode observable a) (point z) =
      output observable z a := by
  simp [outputCode, output]

end ComplexGaugeFamilyPolynomialCode

end HGAS
