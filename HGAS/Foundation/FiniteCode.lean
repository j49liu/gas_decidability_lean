import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Real.Basic

/-!
# Finite rational codes for homogeneous polynomial vector fields

The decision problem takes a finite list of rational coefficients as input.
For a fixed dimension `n`, a vector field is represented by `n`
multivariate polynomials indexed by `Fin n`.

`PolynomialField` is the raw syntactic object. `IsHomogeneousOfDegree`
records the validity condition used by the paper. The zero polynomial is
accepted at every degree because `MvPolynomial.IsHomogeneous d 0` holds for
all `d`.
-/

namespace HGAS

open MvPolynomial

noncomputable section

/-- A rational polynomial vector field in `n` variables. -/
abbrev PolynomialField (n : ℕ) :=
  Fin n → MvPolynomial (Fin n) ℚ

/-- Every component of `F` is homogeneous of the same prescribed degree. -/
def IsHomogeneousOfDegree {n : ℕ} (d : ℕ) (F : PolynomialField n) : Prop :=
  ∀ i, (F i).IsHomogeneous d

/-- A valid fixed-dimension, fixed-degree coefficient code. The proof field
is computationally irrelevant; the raw coefficient data remain `field`. -/
structure HomogeneousFieldCode (n d : ℕ) where
  field : PolynomialField n
  homogeneous : IsHomogeneousOfDegree d field

namespace HomogeneousFieldCode

variable {n d : ℕ}

/-- Forget the homogeneity certificate. -/
def toPolynomialField (F : HomogeneousFieldCode n d) : PolynomialField n :=
  F.field

@[simp]
theorem toPolynomialField_apply (F : HomogeneousFieldCode n d) (i : Fin n) :
    F.toPolynomialField i = F.field i :=
  rfl

end HomogeneousFieldCode

/-- Evaluate a rational polynomial vector field over any rational algebra.
This is the coefficient-independent bridge used for both real dynamics and
exact rational test computations. -/
def evalPolynomialField
    {n : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R]
    (F : PolynomialField n) (x : Fin n → R) : Fin n → R :=
  fun i ↦ eval₂Hom (algebraMap ℚ R) x (F i)

@[simp]
theorem evalPolynomialField_apply
    {n : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R]
    (F : PolynomialField n) (x : Fin n → R) (i : Fin n) :
    evalPolynomialField F x i =
      eval₂Hom (algebraMap ℚ R) x (F i) :=
  rfl

/-- The real vector field denoted by a rational coefficient code. -/
def HomogeneousFieldCode.realize
    {n d : ℕ} (F : HomogeneousFieldCode n d) :
    (Fin n → ℝ) → (Fin n → ℝ) :=
  evalPolynomialField F.field

end

end HGAS
