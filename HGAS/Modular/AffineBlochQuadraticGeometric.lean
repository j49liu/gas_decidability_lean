import HGAS.Modular.JacobiBlochGaugeSeries
import HGAS.Modular.JacobiThreeMomentTargetRigidity
import Mathlib.Tactic

/-!
# Affine Bloch coefficients are quadratic--geometric

The coefficient of a gauged affine Jacobi--Bloch trace is an exponential
of a quadratic polynomial in its integer summation index.  This file
packages that elementary observation in the phase-free interface used by
`JacobiThreeMomentTargetRigidity`.

No reality, recurrence, or clock hypothesis is needed: it is a direct
identity in the defining affine parameters.
-/

noncomputable section

namespace HGAS.Modular

namespace AffineBlochParameters

/-- Index-independent scale in the quadratic--geometric coefficient
factorization. -/
def gaugedBlochQuadraticScale
    (p : AffineBlochParameters) (d : ℂ) : ℂ :=
  d * p.c0 *
    Complex.exp (Real.pi * Complex.I * p.a0) *
    Complex.exp
      (Real.pi * Complex.I *
        (p.a0 ^ 2 * p.tauComplex 0 +
          2 * p.a0 * p.centeredW 0 - p.b0))

/-- Base carrying the quadratic dependence on the integer index. -/
def gaugedBlochQuadraticBase
    (p : AffineBlochParameters) : ℂ :=
  Complex.exp
    (Real.pi * Complex.I * p.tauComplex 0)

/-- Base carrying the linear dependence on the integer index. -/
def gaugedBlochLinearBase
    (p : AffineBlochParameters) : ℂ :=
  Complex.exp
    (Real.pi * Complex.I *
      (2 * p.a0 * p.tauComplex 0 +
        2 * p.centeredW 0 + 2 * p.b0))

theorem gaugedBlochQuadraticBase_ne_zero
    (p : AffineBlochParameters) :
    p.gaugedBlochQuadraticBase ≠ 0 :=
  Complex.exp_ne_zero _

theorem gaugedBlochLinearBase_ne_zero
    (p : AffineBlochParameters) :
    p.gaugedBlochLinearBase ≠ 0 :=
  Complex.exp_ne_zero _

/-- Exact quadratic--geometric factorization of every gauged Bloch
coefficient. -/
theorem gaugedBlochCoefficient_eq_quadraticGeometric
    (p : AffineBlochParameters) (d : ℂ) (k : ℤ) :
    p.gaugedBlochCoefficient d k =
      p.gaugedBlochQuadraticScale d *
        quadraticGeometricSequence
          p.gaugedBlochQuadraticBase
          p.gaugedBlochLinearBase k := by
  have hexponent :
      p.gaugedBlochReducedExponent k =
        Real.pi * Complex.I *
            (p.a0 ^ 2 * p.tauComplex 0 +
              2 * p.a0 * p.centeredW 0 - p.b0) +
          (k ^ 2 : ℤ) *
            (Real.pi * Complex.I * p.tauComplex 0) +
          k *
            (Real.pi * Complex.I *
              (2 * p.a0 * p.tauComplex 0 +
                2 * p.centeredW 0 + 2 * p.b0)) := by
    unfold gaugedBlochReducedExponent
    push_cast
    ring
  rw [p.gaugedBlochCoefficient_eq_explicit, hexponent]
  unfold gaugedBlochQuadraticScale
    gaugedBlochQuadraticBase gaugedBlochLinearBase
    quadraticGeometricSequence
  rw [Complex.exp_add, Complex.exp_add,
    Complex.exp_int_mul, Complex.exp_int_mul]
  ring

/-- The raw coefficient family is scaled quadratic--geometric. -/
theorem gaugedBlochCoefficient_isScaledQuadraticGeometric
    (p : AffineBlochParameters) (d : ℂ) :
    IsScaledQuadraticGeometric
      (p.gaugedBlochCoefficient d) := by
  refine
    ⟨p.gaugedBlochQuadraticScale d,
      p.gaugedBlochQuadraticBase,
      p.gaugedBlochLinearBase,
      p.gaugedBlochQuadraticBase_ne_zero,
      p.gaugedBlochLinearBase_ne_zero, ?_⟩
  exact p.gaugedBlochCoefficient_eq_quadraticGeometric d

/-- Every integer translate of the raw coefficient family is again
scaled quadratic--geometric. -/
theorem gaugedBlochCoefficient_translate_isScaledQuadraticGeometric
    (p : AffineBlochParameters) (d : ℂ) (l : ℤ) :
    IsScaledQuadraticGeometric
      (fun k : ℤ ↦ p.gaugedBlochCoefficient d (k - l)) := by
  let C :=
    p.gaugedBlochQuadraticScale d *
      quadraticGeometricSequence
        p.gaugedBlochQuadraticBase
        p.gaugedBlochLinearBase (-l)
  let R := p.gaugedBlochQuadraticBase
  let S :=
    p.gaugedBlochQuadraticBase ^ (-2 * l) *
      p.gaugedBlochLinearBase
  refine
    ⟨C, R, S,
      p.gaugedBlochQuadraticBase_ne_zero,
      mul_ne_zero
        (zpow_ne_zero _ p.gaugedBlochQuadraticBase_ne_zero)
        p.gaugedBlochLinearBase_ne_zero,
      ?_⟩
  intro k
  change
    p.gaugedBlochCoefficient d (k - l) =
      C * quadraticGeometricSequence R S k
  rw [p.gaugedBlochCoefficient_eq_quadraticGeometric d (k - l)]
  unfold C R S quadraticGeometricSequence
  have hquad :
      (k - l) ^ 2 =
        (-l) ^ 2 + (k ^ 2 + (-2 * l) * k) := by
    ring
  have hlinear :
      k - l = -l + k := by
    ring
  rw [hquad, hlinear,
    zpow_add₀ p.gaugedBlochQuadraticBase_ne_zero,
    zpow_add₀ p.gaugedBlochQuadraticBase_ne_zero,
    zpow_add₀ p.gaugedBlochLinearBase_ne_zero,
    mul_zpow,
    ← zpow_mul]
  ring

/-- Reflection followed by an integer translate also preserves the
scaled quadratic--geometric form. -/
theorem gaugedBlochCoefficient_reflectTranslate_isScaledQuadraticGeometric
    (p : AffineBlochParameters) (d : ℂ) (l : ℤ) :
    IsScaledQuadraticGeometric
      (fun k : ℤ ↦ p.gaugedBlochCoefficient d (-k - l)) := by
  let C :=
    p.gaugedBlochQuadraticScale d *
      quadraticGeometricSequence
        p.gaugedBlochQuadraticBase
        p.gaugedBlochLinearBase (-l)
  let R := p.gaugedBlochQuadraticBase
  let S :=
    p.gaugedBlochQuadraticBase ^ (2 * l) *
      p.gaugedBlochLinearBase⁻¹
  refine
    ⟨C, R, S,
      p.gaugedBlochQuadraticBase_ne_zero,
      mul_ne_zero
        (zpow_ne_zero _ p.gaugedBlochQuadraticBase_ne_zero)
        (inv_ne_zero p.gaugedBlochLinearBase_ne_zero),
      ?_⟩
  intro k
  change
    p.gaugedBlochCoefficient d (-k - l) =
      C * quadraticGeometricSequence R S k
  rw [p.gaugedBlochCoefficient_eq_quadraticGeometric d (-k - l)]
  unfold C R S quadraticGeometricSequence
  have hquad :
      (-k - l) ^ 2 =
        (-l) ^ 2 + (k ^ 2 + (2 * l) * k) := by
    ring
  have hlinear :
      -k - l = -l + (-k) := by
    ring
  rw [hquad, hlinear,
    zpow_add₀ p.gaugedBlochQuadraticBase_ne_zero,
    zpow_add₀ p.gaugedBlochQuadraticBase_ne_zero,
    zpow_add₀ p.gaugedBlochLinearBase_ne_zero,
    mul_zpow, inv_zpow,
    ← zpow_mul, zpow_neg]
  rw [zpow_neg]
  ring

end AffineBlochParameters

end HGAS.Modular
