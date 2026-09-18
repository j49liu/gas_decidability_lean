import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Tactic

/-!
# Fixed real coordinates for the moving elliptic lattice

For `τ` in the upper half-plane, the real vectors `1, τ` form a basis
of `ℂ`.  Thus every elliptic parameter has a unique expression

```
                         z = a + b τ,       a,b ∈ ℝ.
```

This file packages that elementary change of coordinates as a
homeomorphism

```
                    ℍ × ℂ  ≃ₜ  ℍ × (ℝ × ℝ).
```

Its main use is topological.  Under this homeomorphism the apparently
moving doubled-period action

```
                  z ↦ z + 2m + 2nτ
```

becomes the fixed coordinate translation

```
                  (a,b) ↦ (a+2m,b+2n).
```

Consequently the varying level-two elliptic quotient is topologically a
product of the upper half-plane with a fixed real two-torus.  This does
not by itself identify the quotient with the reciprocal theta residual
family, but it removes the moving-lattice issue from that remaining
identification.
-/

namespace HGAS.Topology

open Complex Real
open UpperHalfPlane hiding I

noncomputable section

/-- The real coefficient of `τ` in `z=a+bτ`. -/
def movingEllipticTauCoordinate
    (p : ℍ × ℂ) : ℝ :=
  p.2.im / p.1.im

/-- The real coefficient of `1` in `z=a+bτ`. -/
def movingEllipticOneCoordinate
    (p : ℍ × ℂ) : ℝ :=
  p.2.re -
    movingEllipticTauCoordinate p * p.1.re

/-- Convert `(τ,z)` to `(τ,a,b)` where `z=a+bτ`. -/
def movingEllipticRealCoordinates
    (p : ℍ × ℂ) : ℍ × (ℝ × ℝ) :=
  (p.1,
    (movingEllipticOneCoordinate p,
      movingEllipticTauCoordinate p))

/-- Reconstruct `z=a+bτ` from real coordinates. -/
def movingEllipticComplexReconstruction
    (p : ℍ × (ℝ × ℝ)) : ℍ × ℂ :=
  (p.1,
    (p.2.1 : ℂ) + (p.2.2 : ℂ) * (p.1 : ℂ))

theorem continuous_movingEllipticTauCoordinate :
    Continuous movingEllipticTauCoordinate := by
  have himTau :
      Continuous (fun p : ℍ × ℂ ↦ p.1.im) := by
    exact UpperHalfPlane.continuous_im.comp continuous_fst
  have himZ :
      Continuous (fun p : ℍ × ℂ ↦ p.2.im) :=
    continuous_im.comp continuous_snd
  exact himZ.div himTau (fun p ↦ p.1.im_ne_zero)

theorem continuous_movingEllipticOneCoordinate :
    Continuous movingEllipticOneCoordinate := by
  have hreTau :
      Continuous (fun p : ℍ × ℂ ↦ p.1.re) := by
    exact UpperHalfPlane.continuous_re.comp continuous_fst
  have hreZ :
      Continuous (fun p : ℍ × ℂ ↦ p.2.re) :=
    continuous_re.comp continuous_snd
  exact hreZ.sub
    (continuous_movingEllipticTauCoordinate.mul hreTau)

theorem continuous_movingEllipticRealCoordinates :
    Continuous movingEllipticRealCoordinates := by
  exact continuous_fst.prodMk
    (continuous_movingEllipticOneCoordinate.prodMk
      continuous_movingEllipticTauCoordinate)

theorem continuous_movingEllipticComplexReconstruction :
    Continuous movingEllipticComplexReconstruction := by
  unfold movingEllipticComplexReconstruction
  fun_prop

theorem movingEllipticComplexReconstruction_leftInverse :
    Function.LeftInverse
      movingEllipticComplexReconstruction
      movingEllipticRealCoordinates := by
  rintro ⟨τ, z⟩
  apply Prod.ext
  · rfl
  · apply Complex.ext
    · simp [movingEllipticComplexReconstruction,
        movingEllipticRealCoordinates,
        movingEllipticOneCoordinate,
        movingEllipticTauCoordinate]
    · simp [movingEllipticComplexReconstruction,
        movingEllipticRealCoordinates,
        movingEllipticOneCoordinate,
        movingEllipticTauCoordinate]
      field_simp [τ.im_ne_zero]

theorem movingEllipticComplexReconstruction_rightInverse :
    Function.RightInverse
      movingEllipticComplexReconstruction
      movingEllipticRealCoordinates := by
  rintro ⟨τ, a, b⟩
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · simp [movingEllipticComplexReconstruction,
        movingEllipticRealCoordinates,
        movingEllipticOneCoordinate,
        movingEllipticTauCoordinate]
      field_simp [τ.im_ne_zero]
      ring
    · simp [movingEllipticComplexReconstruction,
        movingEllipticRealCoordinates,
        movingEllipticTauCoordinate]
      field_simp [τ.im_ne_zero]

/-- The homeomorphism `(τ,z) ↔ (τ,a,b)` with `z=a+bτ`. -/
def movingEllipticLatticeHomeomorph :
    (ℍ × ℂ) ≃ₜ (ℍ × (ℝ × ℝ)) where
  toFun := movingEllipticRealCoordinates
  invFun := movingEllipticComplexReconstruction
  left_inv :=
    movingEllipticComplexReconstruction_leftInverse
  right_inv :=
    movingEllipticComplexReconstruction_rightInverse
  continuous_toFun :=
    continuous_movingEllipticRealCoordinates
  continuous_invFun :=
    continuous_movingEllipticComplexReconstruction

/-- Translation by a doubled elliptic period in complex coordinates. -/
def movingLevelTwoTranslate
    (m n : ℤ) (p : ℍ × ℂ) : ℍ × ℂ :=
  (p.1,
    p.2 + 2 * (m : ℂ) +
      2 * (n : ℂ) * (p.1 : ℂ))

/-- The corresponding fixed translation in real `(a,b)` coordinates. -/
def fixedLevelTwoTranslate
    (m n : ℤ) (p : ℍ × (ℝ × ℝ)) :
    ℍ × (ℝ × ℝ) :=
  (p.1,
    (p.2.1 + 2 * (m : ℝ),
      p.2.2 + 2 * (n : ℝ)))

/-- The moving level-two action is conjugate to the fixed integer
translation action. -/
theorem movingEllipticLatticeHomeomorph_translate
    (m n : ℤ) (p : ℍ × ℂ) :
    movingEllipticLatticeHomeomorph
        (movingLevelTwoTranslate m n p) =
      fixedLevelTwoTranslate m n
        (movingEllipticLatticeHomeomorph p) := by
  rcases p with ⟨τ, z⟩
  change
    movingEllipticRealCoordinates
        (movingLevelTwoTranslate m n (τ, z)) =
      fixedLevelTwoTranslate m n
        (movingEllipticRealCoordinates (τ, z))
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · simp [movingEllipticRealCoordinates,
        movingEllipticOneCoordinate,
        movingEllipticTauCoordinate,
        movingLevelTwoTranslate,
        fixedLevelTwoTranslate]
      field_simp [τ.im_ne_zero]
      ring
    · simp [movingEllipticRealCoordinates,
        movingEllipticTauCoordinate,
        movingLevelTwoTranslate,
        fixedLevelTwoTranslate]
      field_simp [τ.im_ne_zero]

end

end HGAS.Topology
