import HGAS.Accumulator.PolynomialCode
import HGAS.Algebra.PolynomialVariableEmbedding
import HGAS.Clocks.Controller
import Mathlib.Tactic

/-!
# A reusable polynomial compiler for the right-hand-side oscillator

Section 14 of the manuscript removes the input-dependent Laurent monomial
from the *syntax* of the final vector field.  If `νᵢ(x)` are real polynomial
clock frequencies and `aᵢ ∈ ℚ`, put

```
  W(x) = ∑ i, aᵢ νᵢ(x).
```

The extra unit complex coordinate `R = X + iY` is driven by

```
  R' = -4 i W(x) R,
```

or, in real coordinates,

```
  X' =  4 W(x) Y,       Y' = -4 W(x) X.
```

This module augments an arbitrary `n`-dimensional rational polynomial field
by that oscillator.  The frequency polynomials are arbitrary as well; in the
clock application they are the literals `pᵢ rᵢ`.  Thus the compiler can be
reused both for the fixed-resource reduction and for smaller test systems.

All semantic identities hold at every ambient point.  No circle equation,
controller equilibrium, or invariant-measure hypothesis is used here.
-/

namespace HGAS.Clocks.RHSOscillatorPolynomialCode

open HGAS
open _root_.MvPolynomial
open scoped BigOperators

variable {n q : ℕ}

abbrev dimension (n : ℕ) : ℕ := n + 2

/-- Ambient coordinate of the real part of the oscillator. -/
def xIndex (n : ℕ) : Fin (dimension n) :=
  PolynomialBlockCode.rightEmbedding (m := n) (0 : Fin 2)

/-- Ambient coordinate of the imaginary part of the oscillator. -/
def yIndex (n : ℕ) : Fin (dimension n) :=
  PolynomialBlockCode.rightEmbedding (m := n) (1 : Fin 2)

/-- Flatten a base point and a complex oscillator written as a phase state. -/
def combinedPoint
    {R : Type*} (x : Fin n → R)
    (z : HGAS.Clocks.Controller.PhaseState R) :
    Fin (dimension n) → R :=
  PolynomialBlockCode.point x ![z.c, z.d]

@[simp]
theorem combinedPoint_base
    {R : Type*} (x : Fin n → R)
    (z : HGAS.Clocks.Controller.PhaseState R) (i : Fin n) :
    combinedPoint x z
        (PolynomialBlockCode.leftEmbedding (p := 2) i) = x i := by
  simp [combinedPoint]

@[simp]
theorem combinedPoint_x
    {R : Type*} (x : Fin n → R)
    (z : HGAS.Clocks.Controller.PhaseState R) :
    combinedPoint x z (xIndex n) = z.c := by
  simp [combinedPoint, xIndex]

@[simp]
theorem combinedPoint_y
    {R : Type*} (x : Fin n → R)
    (z : HGAS.Clocks.Controller.PhaseState R) :
    combinedPoint x z (yIndex n) = z.d := by
  simp [combinedPoint, yIndex]

/-- Insert a base polynomial into the enlarged variable set. -/
def liftBase (p : PolynomialCode n) :
    PolynomialCode (dimension n) :=
  PolynomialBlockCode.left (p := 2) p

/-- Code of `∑ i, aᵢ νᵢ(x)` in the enlarged variable set. -/
def weightedFrequencyCode
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n) :
    PolynomialCode (dimension n) :=
  PolynomialCode.sumCodes
    (List.ofFn fun i : Fin q ↦
      PolynomialCode.mul
        (PolynomialCode.constant (a i))
        (liftBase (ν i)))

def xCode : PolynomialCode (dimension n) :=
  PolynomialCode.varCode (xIndex n)

def yCode : PolynomialCode (dimension n) :=
  PolynomialCode.varCode (yIndex n)

def fourCode : PolynomialCode (dimension n) :=
  PolynomialCode.constant (RationalCode.encode 4)

/-- Real equation `X' = 4 W Y`. -/
def xFieldCode
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n) :
    PolynomialCode (dimension n) :=
  PolynomialCode.mul
    (PolynomialCode.mul fourCode (weightedFrequencyCode a ν))
    yCode

/-- Imaginary equation `Y' = -4 W X`. -/
def yFieldCode
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n) :
    PolynomialCode (dimension n) :=
  PolynomialCode.neg
    (PolynomialCode.mul
      (PolynomialCode.mul fourCode (weightedFrequencyCode a ν))
      xCode)

/-- Augment a base field by the two oscillator equations. -/
def fieldCode
    (F : PolynomialFieldCode n)
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n) :
    PolynomialFieldCode (dimension n) :=
  fun k ↦
    match finSumFinEquiv.symm k with
    | Sum.inl i => liftBase (F i)
    | Sum.inr j => ![xFieldCode a ν, yFieldCode a ν] j

/-! ## Exact semantics -/

/-- The real scalar denoted by the weighted frequency code. -/
noncomputable def weightedFrequency
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n)
    (x : Fin n → ℝ) : ℝ :=
  ∑ i, (RationalCode.decode (a i) : ℝ) *
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
      (PolynomialCode.decode (ν i))

/-- Semantic oscillator velocity. -/
noncomputable def oscillatorField
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n)
    (x : Fin n → ℝ)
    (z : HGAS.Clocks.Controller.PhaseState ℝ) :
    HGAS.Clocks.Controller.PhaseState ℝ :=
  HGAS.Clocks.Controller.phaseField
    (-4 * weightedFrequency a ν x) z

private theorem eval_sumCodes_ofFn
    {R : Type*} [CommRing R] [Algebra ℚ R]
    {r N : ℕ} (p : Fin r → PolynomialCode N)
    (x : Fin N → R) :
    eval₂Hom (algebraMap ℚ R) x
        (PolynomialCode.decode
          (PolynomialCode.sumCodes (List.ofFn p))) =
      ∑ i, eval₂Hom (algebraMap ℚ R) x
        (PolynomialCode.decode (p i)) := by
  rw [PolynomialCode.decode_sumCodes, List.map_ofFn,
    List.sum_ofFn, map_sum]
  rfl

@[simp]
theorem eval₂Hom_liftBase
    {R : Type*} [CommSemiring R] [Algebra ℚ R]
    (p : PolynomialCode n)
    (x : Fin n → R)
    (z : HGAS.Clocks.Controller.PhaseState R) :
    eval₂Hom (algebraMap ℚ R) (combinedPoint x z)
        (PolynomialCode.decode (liftBase p)) =
      eval₂Hom (algebraMap ℚ R) x
        (PolynomialCode.decode p) := by
  simp [combinedPoint, liftBase]

@[simp]
theorem eval₂Hom_weightedFrequencyCode
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n)
    (x : Fin n → ℝ)
    (z : HGAS.Clocks.Controller.PhaseState ℝ) :
    eval₂Hom (algebraMap ℚ ℝ) (combinedPoint x z)
        (PolynomialCode.decode (weightedFrequencyCode a ν)) =
      weightedFrequency a ν x := by
  rw [weightedFrequencyCode, eval_sumCodes_ofFn]
  rw [weightedFrequency]
  apply Finset.sum_congr rfl
  intro i _
  simp only [PolynomialCode.decode_mul_code, map_mul,
    PolynomialCode.decode_constant, eval₂Hom_C]
  rw [eval₂Hom_liftBase]
  have ha :
      (algebraMap ℚ ℝ) (RationalCode.decode (a i)) =
        (RationalCode.decode (a i) : ℝ) := by
    rfl
  rw [ha]

@[simp]
theorem eval₂Hom_xCode
    (x : Fin n → ℝ)
    (z : HGAS.Clocks.Controller.PhaseState ℝ) :
    eval₂Hom (algebraMap ℚ ℝ) (combinedPoint x z)
        (PolynomialCode.decode (xCode (n := n))) = z.c := by
  simp [xCode]

@[simp]
theorem eval₂Hom_yCode
    (x : Fin n → ℝ)
    (z : HGAS.Clocks.Controller.PhaseState ℝ) :
    eval₂Hom (algebraMap ℚ ℝ) (combinedPoint x z)
        (PolynomialCode.decode (yCode (n := n))) = z.d := by
  simp [yCode]

@[simp]
theorem eval₂Hom_xFieldCode
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n)
    (x : Fin n → ℝ)
    (z : HGAS.Clocks.Controller.PhaseState ℝ) :
    eval₂Hom (algebraMap ℚ ℝ) (combinedPoint x z)
        (PolynomialCode.decode (xFieldCode a ν)) =
      (oscillatorField a ν x z).c := by
  simp only [xFieldCode, PolynomialCode.decode_mul_code, map_mul,
    fourCode, PolynomialCode.decode_constant, eval₂Hom_C,
    RationalCode.decode_encode]
  rw [eval₂Hom_weightedFrequencyCode, eval₂Hom_yCode]
  simp only [oscillatorField,
    HGAS.Clocks.Controller.phaseField]
  have hfour : (algebraMap ℚ ℝ) (4 : ℚ) = (4 : ℝ) := by
    rfl
  rw [hfour]
  ring

@[simp]
theorem eval₂Hom_yFieldCode
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n)
    (x : Fin n → ℝ)
    (z : HGAS.Clocks.Controller.PhaseState ℝ) :
    eval₂Hom (algebraMap ℚ ℝ) (combinedPoint x z)
        (PolynomialCode.decode (yFieldCode a ν)) =
      (oscillatorField a ν x z).d := by
  simp only [yFieldCode, PolynomialCode.decode_neg_code,
    PolynomialCode.decode_mul_code, map_neg, map_mul,
    fourCode, PolynomialCode.decode_constant, eval₂Hom_C,
    RationalCode.decode_encode]
  rw [eval₂Hom_weightedFrequencyCode, eval₂Hom_xCode]
  simp only [oscillatorField,
    HGAS.Clocks.Controller.phaseField]
  have hfour : (algebraMap ℚ ℝ) (4 : ℚ) = (4 : ℝ) := by
    rfl
  rw [hfour]
  ring

@[simp]
theorem fieldCode_base
    (F : PolynomialFieldCode n)
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n) (i : Fin n) :
    fieldCode F a ν
        (PolynomialBlockCode.leftEmbedding (p := 2) i) =
      liftBase (F i) := by
  simp [fieldCode]

@[simp]
theorem fieldCode_x
    (F : PolynomialFieldCode n)
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n) :
    fieldCode F a ν (xIndex n) = xFieldCode a ν := by
  simp [fieldCode, xIndex]

@[simp]
theorem fieldCode_y
    (F : PolynomialFieldCode n)
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n) :
    fieldCode F a ν (yIndex n) = yFieldCode a ν := by
  simp [fieldCode, yIndex]

/-- Exact arbitrary-point semantics of the complete augmented field. -/
@[simp]
theorem realize_fieldCode
    (F : PolynomialFieldCode n)
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n)
    (x : Fin n → ℝ)
    (z : HGAS.Clocks.Controller.PhaseState ℝ) :
    PolynomialFieldCode.realize
        (fieldCode F a ν) (combinedPoint x z) =
      combinedPoint
        (PolynomialFieldCode.realize F x)
        (oscillatorField a ν x z) := by
  funext k
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective k
  · change
      PolynomialFieldCode.realize
          (fieldCode F a ν) (combinedPoint x z)
          (PolynomialBlockCode.leftEmbedding (p := 2) i) =
        combinedPoint
          (PolynomialFieldCode.realize F x)
          (oscillatorField a ν x z)
          (PolynomialBlockCode.leftEmbedding (p := 2) i)
    simp [PolynomialFieldCode.realize_apply]
  · fin_cases j
    · change
        PolynomialFieldCode.realize
            (fieldCode F a ν) (combinedPoint x z)
            (xIndex n) =
          combinedPoint
            (PolynomialFieldCode.realize F x)
            (oscillatorField a ν x z) (xIndex n)
      simp [PolynomialFieldCode.realize_apply]
    · change
        PolynomialFieldCode.realize
            (fieldCode F a ν) (combinedPoint x z)
            (yIndex n) =
          combinedPoint
            (PolynomialFieldCode.realize F x)
            (oscillatorField a ν x z) (yIndex n)
      simp [PolynomialFieldCode.realize_apply]

/-- The emitted oscillator field is tangent to every centered circle. -/
theorem oscillator_tangent
    (F : PolynomialFieldCode n)
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n)
    (x : Fin n → ℝ)
    (z : HGAS.Clocks.Controller.PhaseState ℝ) :
    z.c *
          PolynomialFieldCode.realize
            (fieldCode F a ν)
            (combinedPoint x z) (xIndex n) +
        z.d *
          PolynomialFieldCode.realize
            (fieldCode F a ν)
            (combinedPoint x z) (yIndex n) = 0 := by
  simp only [PolynomialFieldCode.realize_apply, fieldCode_x, fieldCode_y,
    eval₂Hom_xFieldCode, eval₂Hom_yFieldCode]
  exact HGAS.Clocks.Controller.phaseField_tangent
    (-4 * weightedFrequency a ν x) z

end HGAS.Clocks.RHSOscillatorPolynomialCode
