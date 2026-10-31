import Stability.Simulation.ProjectiveHomogenization
import HGAS.Algebra.FiniteEuclidean

/-!
# The literal homogeneous projective field

The sparse code implements `|Y|² A - (Y · A) Y + |Y|² β Y`, where
`A = (z^ℓ P(y/z), 0)` and `β = z^(ℓ-1) b(y/z)` away from the equator.

Source: Section 6, https://arxiv.org/html/2609.22058v2#S6.
-/

namespace Stability.ProjectivePolynomialCode

open HGAS MvPolynomial
open scoped BigOperators

variable {n : ℕ}

/-- The homogeneous source field with a zero final coordinate. -/
def augmentedFieldCode (ell : ℕ) (P : PolynomialFieldCode n) : PolynomialFieldCode (n + 1) :=
  Fin.lastCases PolynomialCode.zero (fun i ↦ homogenize ell (P i))

@[simp] theorem augmentedFieldCode_last (ell : ℕ) (P : PolynomialFieldCode n) :
    augmentedFieldCode ell P (Fin.last n) = PolynomialCode.zero := by
  simp [augmentedFieldCode]

@[simp] theorem augmentedFieldCode_castSucc (ell : ℕ) (P : PolynomialFieldCode n) (i : Fin n) :
    augmentedFieldCode ell P i.castSucc = homogenize ell (P i) := by
  simp [augmentedFieldCode]

def radialRateCode (ell : ℕ) (b : PolynomialCode n) : PolynomialCode (n + 1) :=
  homogenize (ell - 1) b

def normSqCode (m : ℕ) : PolynomialCode m :=
  PolynomialCode.sumCodes (List.ofFn fun i ↦ PolynomialCode.pow (PolynomialCode.varCode i) 2)

def radialDotCode (ell : ℕ) (P : PolynomialFieldCode n) : PolynomialCode (n + 1) :=
  PolynomialCode.sumCodes (List.ofFn fun i ↦
    PolynomialCode.mul (PolynomialCode.varCode i) (augmentedFieldCode ell P i))

/-- The projective field is a literal finite sparse polynomial code. -/
def fieldCode (ell : ℕ) (P : PolynomialFieldCode n) (b : PolynomialCode n) :
    PolynomialFieldCode (n + 1) := fun i ↦
  PolynomialCode.add
    (PolynomialCode.sub
      (PolynomialCode.mul (normSqCode (n + 1)) (augmentedFieldCode ell P i))
      (PolynomialCode.mul (radialDotCode ell P) (PolynomialCode.varCode i)))
    (PolynomialCode.mul
      (PolynomialCode.mul (normSqCode (n + 1)) (radialRateCode ell b))
      (PolynomialCode.varCode i))

theorem decode_normSqCode (m : ℕ) :
    PolynomialCode.decode (normSqCode m) = ∑ i : Fin m, X i ^ 2 := by
  simp [normSqCode, PolynomialCode.decode_sumCodes, List.map_ofFn, List.sum_ofFn]

theorem decode_radialDotCode (ell : ℕ) (P : PolynomialFieldCode n) :
    PolynomialCode.decode (radialDotCode ell P) =
      ∑ i, X i * PolynomialCode.decode (augmentedFieldCode ell P i) := by
  rw [radialDotCode, PolynomialCode.decode_sumCodes, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply, PolynomialCode.decode_mul_code, PolynomialCode.decode_varCode]

theorem decode_fieldCode (ell : ℕ) (P : PolynomialFieldCode n) (b : PolynomialCode n)
    (i : Fin (n + 1)) :
    PolynomialCode.decode (fieldCode ell P b i) =
      PolynomialCode.decode (normSqCode (n + 1)) *
        PolynomialCode.decode (augmentedFieldCode ell P i) -
      PolynomialCode.decode (radialDotCode ell P) * X i +
      PolynomialCode.decode (normSqCode (n + 1)) *
        PolynomialCode.decode (radialRateCode ell b) * X i := by
  simp [fieldCode]

theorem eval_normSqCode (m : ℕ) (y : Fin m → ℝ) :
    eval₂Hom (algebraMap ℚ ℝ) y (PolynomialCode.decode (normSqCode m)) = HGAS.normSq y := by
  rw [decode_normSqCode]
  simp [HGAS.normSq, HGAS.dot, pow_two]

theorem eval_radialDotCode (ell : ℕ) (P : PolynomialFieldCode n) (y : Fin (n + 1) → ℝ) :
    eval₂Hom (algebraMap ℚ ℝ) y (PolynomialCode.decode (radialDotCode ell P)) =
      HGAS.dot y (PolynomialFieldCode.realize (augmentedFieldCode ell P) y) := by
  rw [decode_radialDotCode]
  simp [HGAS.dot, PolynomialFieldCode.realize_apply]

/-- Decoding gives the actual algebraic projective field on every state. -/
theorem realize_fieldCode (ell : ℕ) (P : PolynomialFieldCode n) (b : PolynomialCode n)
    (y : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    PolynomialFieldCode.realize (fieldCode ell P b) y i =
      HGAS.normSq y * PolynomialFieldCode.realize (augmentedFieldCode ell P) y i -
      HGAS.dot y (PolynomialFieldCode.realize (augmentedFieldCode ell P) y) * y i +
      HGAS.normSq y *
        eval₂Hom (algebraMap ℚ ℝ) y (PolynomialCode.decode (radialRateCode ell b)) * y i := by
  rw [PolynomialFieldCode.realize_apply, decode_fieldCode]
  simp only [map_add, map_sub, map_mul, eval₂Hom_X', eval_normSqCode, eval_radialDotCode,
    PolynomialFieldCode.realize_apply]

@[simp] theorem realize_augmentedFieldCode_last (ell : ℕ) (P : PolynomialFieldCode n)
    (y : Fin (n + 1) → ℝ) :
    PolynomialFieldCode.realize (augmentedFieldCode ell P) y (Fin.last n) = 0 := by
  simp [PolynomialFieldCode.realize_apply]

/-- The source part of the actual homogeneous field has the literal
denominator-cleared quotient-chart value. -/
theorem realize_augmentedFieldCode_quotient (ell : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ i, PolynomialCode.TermsDegreeLE ell (P i))
    (y : Fin (n + 1) → ℝ) (hy : y (Fin.last n) ≠ 0) (i : Fin n) :
    PolynomialFieldCode.realize (augmentedFieldCode ell P) y i.castSucc =
      y (Fin.last n) ^ ell * PolynomialFieldCode.realize P
        (fun j ↦ y j.castSucc / y (Fin.last n)) i := by
  rw [PolynomialFieldCode.realize_apply, augmentedFieldCode_castSucc,
    PolynomialFieldCode.realize_apply]
  exact eval_homogenize_quotient ell (P i) (hP i) y hy

theorem eval_radialRateCode_quotient (ell : ℕ) (b : PolynomialCode n)
    (hb : PolynomialCode.TermsDegreeLE (ell - 1) b)
    (y : Fin (n + 1) → ℝ) (hy : y (Fin.last n) ≠ 0) :
    eval₂Hom (algebraMap ℚ ℝ) y (PolynomialCode.decode (radialRateCode ell b)) =
      y (Fin.last n) ^ (ell - 1) * eval₂Hom (algebraMap ℚ ℝ)
        (fun j ↦ y j.castSucc / y (Fin.last n)) (PolynomialCode.decode b) :=
  eval_homogenize_quotient (ell - 1) b hb y hy

theorem realize_fieldCode_last (ell : ℕ) (P : PolynomialFieldCode n) (b : PolynomialCode n)
    (y : Fin (n + 1) → ℝ) :
    PolynomialFieldCode.realize (fieldCode ell P b) y (Fin.last n) =
      (HGAS.normSq y *
        eval₂Hom (algebraMap ℚ ℝ) y (PolynomialCode.decode (radialRateCode ell b)) -
        HGAS.dot y (PolynomialFieldCode.realize (augmentedFieldCode ell P) y)) *
        y (Fin.last n) := by
  rw [realize_fieldCode, realize_augmentedFieldCode_last]
  ring

theorem isHomogeneous_augmentedFieldCode (ell : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ i, PolynomialCode.TermsDegreeLE ell (P i)) (i : Fin (n + 1)) :
    (PolynomialCode.decode (augmentedFieldCode ell P i)).IsHomogeneous ell := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · rw [augmentedFieldCode_last, PolynomialCode.decode_zero_code]
    exact isHomogeneous_zero _ _ ell
  · rw [augmentedFieldCode_castSucc]
    exact isHomogeneous_homogenize ell (P j) (hP j)

theorem isHomogeneous_normSqCode (m : ℕ) :
    (PolynomialCode.decode (normSqCode m)).IsHomogeneous 2 := by
  rw [decode_normSqCode]
  exact IsHomogeneous.sum _ _ _ (fun i _ ↦ isHomogeneous_X_pow i 2)

theorem isHomogeneous_radialDotCode (ell : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ i, PolynomialCode.TermsDegreeLE ell (P i)) :
    (PolynomialCode.decode (radialDotCode ell P)).IsHomogeneous (1 + ell) := by
  rw [decode_radialDotCode]
  exact IsHomogeneous.sum _ _ _ (fun i _ ↦
    (isHomogeneous_X ℚ i).mul (isHomogeneous_augmentedFieldCode ell P hP i))

/-- Every coordinate is homogeneous of the asserted common degree. -/
theorem isHomogeneous_fieldCode (ell : ℕ) (hell : 1 ≤ ell)
    (P : PolynomialFieldCode n) (b : PolynomialCode n)
    (hP : ∀ i, PolynomialCode.TermsDegreeLE ell (P i))
    (hb : PolynomialCode.TermsDegreeLE (ell - 1) b) (i : Fin (n + 1)) :
    (PolynomialCode.decode (fieldCode ell P b i)).IsHomogeneous (ell + 2) := by
  rw [decode_fieldCode]
  have hnorm := isHomogeneous_normSqCode (n + 1)
  have hA := isHomogeneous_augmentedFieldCode ell P hP i
  have hdot := isHomogeneous_radialDotCode ell P hP
  have hbeta := isHomogeneous_homogenize (ell - 1) b hb
  have hX := isHomogeneous_X ℚ i
  apply IsHomogeneous.add
  · apply IsHomogeneous.sub
    · simpa only [Nat.add_comm 2 ell] using hnorm.mul hA
    · convert hdot.mul hX using 1
      omega
  · convert (hnorm.mul hbeta).mul hX using 1
    omega

theorem realize_augmentedFieldCode_equator (ell : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ i t, t ∈ P i → ExponentCode.totalDegree t.1 < ell)
    (y : Fin (n + 1) → ℝ) (hy : y (Fin.last n) = 0) :
    PolynomialFieldCode.realize (augmentedFieldCode ell P) y = 0 := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [PolynomialFieldCode.realize_apply]
  · rw [PolynomialFieldCode.realize_apply, augmentedFieldCode_castSucc]
    exact eval_homogenize_equator ell (P j) (hP j) y hy

/-- Strict source degree bounds make the entire projective field vanish
on the equator, including its radial output term. -/
theorem realize_fieldCode_equator (ell : ℕ) (P : PolynomialFieldCode n) (b : PolynomialCode n)
    (hP : ∀ i t, t ∈ P i → ExponentCode.totalDegree t.1 < ell)
    (hb : ∀ t ∈ b, ExponentCode.totalDegree t.1 < ell - 1)
    (y : Fin (n + 1) → ℝ) (hy : y (Fin.last n) = 0) :
    PolynomialFieldCode.realize (fieldCode ell P b) y = 0 := by
  have hA := realize_augmentedFieldCode_equator ell P hP y hy
  have hbeta := eval_homogenize_equator (ell - 1) b hb y hy
  funext i
  rw [realize_fieldCode, hA]
  simp only [Pi.zero_apply, mul_zero, dot_zero, zero_mul, sub_zero, zero_add]
  change HGAS.normSq y *
    eval₂Hom (algebraMap ℚ ℝ) y (PolynomialCode.decode (homogenize (ell - 1) b)) * y i = 0
  rw [hbeta, mul_zero, zero_mul]

end Stability.ProjectivePolynomialCode
