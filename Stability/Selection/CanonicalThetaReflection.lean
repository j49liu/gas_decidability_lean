import Stability.Selection.UnaryClockConjugation
import HGAS.Modular.CanonicalUnaryTheta
import HGAS.Modular.HorizontalTrajectory

/-!
# Reflection of the canonical theta--Eisenstein state

The reflection `τ ↦ -conj τ` preserves the upper half-plane and
conjugates every canonical unary coordinate. The identities below follow
from the actual theta series and the divisor-sum expansion of `E₂`.
They allow a canonical modular conclusion obtained after state
conjugation to be transported back to the original signed clock.
-/

namespace Stability.Selection

open HGAS.Modular
open UpperHalfPlane hiding I

noncomputable section

/-- The standard antiholomorphic reflection of the upper half-plane. -/
def reflectUpperHalfPlane (τ : ℍ) : ℍ := UpperHalfPlane.J • τ

@[simp]
theorem reflectUpperHalfPlane_coe (τ : ℍ) :
    (reflectUpperHalfPlane τ : ℂ) = -star (τ : ℂ) :=
  UpperHalfPlane.coe_J_smul τ

@[simp]
theorem reflectUpperHalfPlane_involutive (τ : ℍ) :
    reflectUpperHalfPlane (reflectUpperHalfPlane τ) = τ := by
  ext
  simp

@[simp]
theorem reflectUpperHalfPlane_im (τ : ℍ) :
    (reflectUpperHalfPlane τ).im = τ.im := by
  change (reflectUpperHalfPlane τ : ℂ).im = τ.im
  rw [reflectUpperHalfPlane_coe]
  simp

/-- Reflection conjugates each shifted-square theta summand. -/
theorem theta₂Term_reflect (n : ℤ) (τ : ℍ) :
    theta₂Term n (reflectUpperHalfPlane τ) = star (theta₂Term n τ) := by
  norm_num [theta₂Term, ← Complex.exp_conj, map_ofNat]

/-- Reflection conjugates each integer-square theta summand. -/
theorem theta₃Term_reflect (n : ℤ) (τ : ℍ) :
    theta₃Term n (reflectUpperHalfPlane τ) = star (theta₃Term n τ) := by
  simp [theta₃Term, ← Complex.exp_conj]

/-- The alternating coefficient in the fourth theta series is real. -/
theorem theta₄Term_reflect (n : ℤ) (τ : ℍ) :
    theta₄Term n (reflectUpperHalfPlane τ) = star (theta₄Term n τ) := by
  simp [theta₄Term, ← Complex.exp_conj]

theorem theta₂_reflect (τ : ℍ) :
    theta₂ (reflectUpperHalfPlane τ) = star (theta₂ τ) := by
  simp only [theta₂, Complex.star_def, Complex.conj_tsum]
  exact tsum_congr fun n ↦ theta₂Term_reflect n τ

theorem theta₃_reflect (τ : ℍ) :
    theta₃ (reflectUpperHalfPlane τ) = star (theta₃ τ) := by
  simp only [theta₃, Complex.star_def, Complex.conj_tsum]
  exact tsum_congr fun n ↦ theta₃Term_reflect n τ

theorem theta₄_reflect (τ : ℍ) :
    theta₄ (reflectUpperHalfPlane τ) = star (theta₄ τ) := by
  simp only [theta₄, Complex.star_def, Complex.conj_tsum]
  exact tsum_congr fun n ↦ theta₄Term_reflect n τ

/-- The nome in the divisor-sum expansion of `E₂` conjugates under
reflection. -/
theorem exp_two_pi_I_reflect (τ : ℍ) :
    Complex.exp (2 * Real.pi * Complex.I * (reflectUpperHalfPlane τ : ℂ)) =
      star (Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ))) := by
  norm_num [← Complex.exp_conj, map_ofNat]

/-- The coefficients of the `E₂` divisor-sum expansion are real, so
reflection conjugates the full Eisenstein coordinate. -/
theorem E2_reflect (τ : ℍ) :
    EisensteinSeries.E2 (reflectUpperHalfPlane τ) = star (EisensteinSeries.E2 τ) := by
  rw [EisensteinSeries.E2_eq_tsum_cexp, EisensteinSeries.E2_eq_tsum_cexp]
  simp only [exp_two_pi_I_reflect, Complex.star_def, map_sub, map_mul, map_ofNat, map_one,
    Complex.conj_tsum]
  congr 2
  apply tsum_congr
  intro n
  simp

/-- Exact reflection law for all four canonical unary coordinates. -/
theorem canonicalUnaryTheta_reflect (τ : ℍ) :
    canonicalUnaryTheta (reflectUpperHalfPlane τ) =
      conjugateUnary (canonicalUnaryTheta τ) := by
  ext
  · simp [canonicalUnaryTheta, unaryStateOfFunctions, conjugateUnary, H₂,
      theta₂_reflect]
  · simp [canonicalUnaryTheta, unaryStateOfFunctions, conjugateUnary, H₄,
      theta₄_reflect]
  · exact E2_reflect τ
  · exact theta₃_reflect τ

/-- A canonical conclusion about the conjugated state determines the
original state at the reflected upper-half-plane argument. -/
theorem eq_canonicalUnaryTheta_reflect_of_conjugate_eq
    {z : UnaryModularState ℂ} {τ : ℍ}
    (hz : conjugateUnary z = canonicalUnaryTheta τ) :
    z = canonicalUnaryTheta (reflectUpperHalfPlane τ) := by
  rw [canonicalUnaryTheta_reflect, ← hz, conjugateUnary_involutive]

/-- Reflection reverses the horizontal phase and speed, while preserving
height and physical time. -/
theorem reflectUpperHalfPlane_horizontalLine
    (x y s : ℝ) (hy : 0 < y) (t : ℝ) :
    reflectUpperHalfPlane (horizontalLine x y s hy t) =
      horizontalLine (-x) y (-s) hy t := by
  ext
  rw [reflectUpperHalfPlane_coe]
  apply Complex.ext
  · simp [horizontalLine, add_comm]
  · simp [horizontalLine]

end

end Stability.Selection
