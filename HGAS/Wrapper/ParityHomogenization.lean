import HGAS.Lyapunov.RationalCertificateAlgebra
import Mathlib.Tactic

/-!
# Parity-preserving homogenization

The product-sphere wrapper first produces polynomial expressions which are
sums of homogeneous pieces of one parity.  If the target degree is `e` and
a piece has degree `ℓ ≤ e` with `ℓ ≡ e (mod 2)`, multiply it by

```
(ρ/L)^((e-ℓ)/2).
```

Since `ρ` has degree two, the result has degree `e`; on the sphere `ρ=L`
the multiplier is exactly one.  This file packages equation (12.14) as a
reusable finite-syntax construction over `ℚ`.
-/

namespace HGAS

open MvPolynomial

noncomputable section

variable {n targetDegree : ℕ}

/-- One homogeneous summand eligible for parity homogenization. -/
structure ParityPiece (n targetDegree : ℕ) where
  degree : ℕ
  polynomial : MvPolynomial (Fin n) ℚ
  homogeneous : polynomial.IsHomogeneous degree
  degree_le : degree ≤ targetDegree
  same_parity : degree % 2 = targetDegree % 2

/-- The normalized quadratic radius `ρ/L`. -/
def normalizedRho (L : ℚ) : MvPolynomial (Fin n) ℚ :=
  C L⁻¹ * rhoPolynomial

/-- Homogenize one parity-compatible piece to the target degree. -/
def homogenizePiece (L : ℚ) (p : ParityPiece n targetDegree) :
    MvPolynomial (Fin n) ℚ :=
  normalizedRho L ^ ((targetDegree - p.degree) / 2) * p.polynomial

/-- Sum of the individually homogenized pieces. -/
def parityHomogenize
    (L : ℚ) (pieces : List (ParityPiece n targetDegree)) :
    MvPolynomial (Fin n) ℚ :=
  (pieces.map (homogenizePiece L)).sum

/-- The parity and ordering hypotheses give the exact degree arithmetic. -/
theorem two_mul_half_difference_add
    (p : ParityPiece n targetDegree) :
    2 * ((targetDegree - p.degree) / 2) + p.degree =
      targetDegree := by
  have hle : p.degree ≤ targetDegree := p.degree_le
  have hparity : p.degree % 2 = targetDegree % 2 :=
    p.same_parity
  have hmod : (targetDegree - p.degree) % 2 = 0 := by
    omega
  have hdivision :=
    Nat.mod_add_div (targetDegree - p.degree) 2
  omega

/-- The normalized radius remains homogeneous of degree two. -/
theorem normalizedRho_isHomogeneous (L : ℚ) :
    (normalizedRho (n := n) L).IsHomogeneous 2 := by
  exact (isHomogeneous_C _ _).mul rhoPolynomial_isHomogeneous

/-- Every homogenized piece has exactly the requested target degree. -/
theorem homogenizePiece_isHomogeneous
    (L : ℚ) (p : ParityPiece n targetDegree) :
    (homogenizePiece L p).IsHomogeneous targetDegree := by
  have h :=
    ((normalizedRho_isHomogeneous (n := n) L).pow
      ((targetDegree - p.degree) / 2)).mul p.homogeneous
  convert h using 1
  exact (two_mul_half_difference_add p).symm

/-- The whole finite sum is homogeneous of the target degree. -/
theorem parityHomogenize_isHomogeneous
    (L : ℚ) (pieces : List (ParityPiece n targetDegree)) :
    (parityHomogenize L pieces).IsHomogeneous targetDegree := by
  induction pieces with
  | nil =>
      simpa [parityHomogenize] using
        (isHomogeneous_zero (Fin n) ℚ targetDegree)
  | cons p pieces ih =>
      simp only [parityHomogenize, List.map_cons, List.sum_cons]
      exact (homogenizePiece_isHomogeneous L p).add ih

/-- On the real sphere `ρ=L`, the normalized radius evaluates to one. -/
theorem eval₂Hom_normalizedRho_of_normSq
    (L : ℚ) (hL : L ≠ 0) (x : Fin n → ℝ)
    (hsphere : normSq x = (L : ℝ)) :
    eval₂Hom (algebraMap ℚ ℝ) x (normalizedRho L) = 1 := by
  simp only [normalizedRho, map_mul, eval₂Hom_C,
    eval₂Hom_rhoPolynomial]
  rw [hsphere]
  rw [map_inv₀]
  apply inv_mul_cancel₀
  intro hmap
  apply hL
  apply FaithfulSMul.algebraMap_injective ℚ ℝ
  simpa using hmap

/-- A single homogenized piece agrees with its original polynomial on the
chosen sphere. -/
theorem eval₂Hom_homogenizePiece_of_normSq
    (L : ℚ) (hL : L ≠ 0) (p : ParityPiece n targetDegree)
    (x : Fin n → ℝ) (hsphere : normSq x = (L : ℝ)) :
    eval₂Hom (algebraMap ℚ ℝ) x (homogenizePiece L p) =
      eval₂Hom (algebraMap ℚ ℝ) x p.polynomial := by
  simp only [homogenizePiece, map_mul, map_pow,
    eval₂Hom_normalizedRho_of_normSq L hL x hsphere, one_pow,
    one_mul]

/-- Parity homogenization agrees with the original sum of pieces on
`ρ=L`. -/
theorem eval₂Hom_parityHomogenize_of_normSq
    (L : ℚ) (hL : L ≠ 0)
    (pieces : List (ParityPiece n targetDegree))
    (x : Fin n → ℝ) (hsphere : normSq x = (L : ℝ)) :
    eval₂Hom (algebraMap ℚ ℝ) x (parityHomogenize L pieces) =
      (pieces.map
        (fun p ↦ eval₂Hom (algebraMap ℚ ℝ) x p.polynomial)).sum := by
  induction pieces with
  | nil =>
      simp [parityHomogenize]
  | cons p pieces ih =>
      simp only [parityHomogenize, List.map_cons, List.sum_cons, map_add]
      rw [eval₂Hom_homogenizePiece_of_normSq L hL p x hsphere]
      congr 1

end

end HGAS
