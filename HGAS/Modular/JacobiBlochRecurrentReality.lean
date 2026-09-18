import HGAS.Modular.JacobiBlochEscape
import HGAS.Modular.JacobiBlochSelectedContinuation

/-!
# Forward recurrence forces the affine Bloch parameter to be real

The affine Jacobi--Bloch classification produces a complex constant
`a₀`.  Its imaginary part is not merely an inessential choice of lift:
when the modular line has nonzero horizontal speed, a nonzero imaginary
part makes the elliptic argument travel vertically at linear speed.
The theta transformation law then forces the four scaled theta
coordinates to escape to infinity.

The polynomial selector, however, supplies recurrence of all ten Jacobi
coordinates.  This module closes the small but important interface gap:
projection to coordinates `T₁,...,T₄` is continuous, so recurrence of the
ten polynomial coordinates implies recurrence of the scaled theta
vector.  The escape theorem rules this out unless `Im a₀ = 0`.

The result is stated for an arbitrary actual Jacobi path which is known
globally to equal an affine Bloch path.  It therefore composes directly
with `JacobiBlochSelectedContinuation`, while keeping the elementary
recurrence argument reusable.
-/

namespace HGAS.Modular

open Complex

noncomputable section

/-- Continuous projection from the ten Jacobi polynomial coordinates to
the four theta coordinates, in the order `T₁,T₂,T₃,T₄`. -/
def jacobiThetaCoordinateObservation
    (x : Fin JacobiPolynomialCode.dimension → ℂ) :
    Fin 4 → ℂ :=
  ![x JacobiPolynomialCode.T1Index,
    x JacobiPolynomialCode.T2Index,
    x JacobiPolynomialCode.T3Index,
    x JacobiPolynomialCode.T4Index]

/-- The four-coordinate observation is continuous. -/
theorem continuous_jacobiThetaCoordinateObservation :
    Continuous jacobiThetaCoordinateObservation := by
  unfold jacobiThetaCoordinateObservation
  apply continuous_pi
  intro i
  fin_cases i <;> fun_prop

/-- On an affine Bloch path, the observed polynomial coordinates are
exactly the common scale times the canonical theta vector. -/
@[simp]
theorem jacobiThetaCoordinateObservation_point_jacobiBlochPath
    (p : AffineBlochParameters) (t : ℝ) :
    jacobiThetaCoordinateObservation
        (JacobiPolynomialCode.point (p.jacobiBlochPath t)) =
      p.commonScale t •
        jacobiThetaVector (p.xi t) (p.tau t : ℂ) := by
  funext i
  fin_cases i <;>
    simp [jacobiThetaCoordinateObservation,
      JacobiPolynomialCode.point,
      JacobiPolynomialCode.T1Index,
      JacobiPolynomialCode.T2Index,
      JacobiPolynomialCode.T3Index,
      JacobiPolynomialCode.T4Index,
      AffineBlochParameters.jacobiBlochPath,
      jacobiBlochGaugePath,
      JacobiState.blochGauge,
      AffineBlochParameters.canonicalJacobiPath,
      canonicalJacobiThetaMovingPath,
      canonicalJacobiThetaState,
      jacobiThetaVector]

/-- **Recurrent affine Bloch trajectories have real Bloch parameter.**

Suppose the actual ten-coordinate polynomial trajectory is forward
recurrent and agrees globally with an affine Jacobi--Bloch formula.
When the modular horizontal speed and common scale constant are nonzero,
the Bloch parameter has zero imaginary part. -/
theorem AffineBlochParameters.a0_im_eq_zero_of_forwardRecurrent_point
    (p : AffineBlochParameters)
    {z : ℝ → JacobiState ℂ}
    {t₀ : ℝ}
    (hrec :
      HGAS.ForwardRecurrentAt
        (fun t ↦ JacobiPolynomialCode.point (z t)) t₀)
    (heq : z = p.jacobiBlochPath)
    (hkappa : p.kappa ≠ 0)
    (hc0 : p.c0 ≠ 0) :
    p.a0.im = 0 := by
  subst z
  have hobserved :
      HGAS.ForwardRecurrentAt
        (fun t ↦
          jacobiThetaCoordinateObservation
            (JacobiPolynomialCode.point
              (p.jacobiBlochPath t))) t₀ :=
    hrec.map continuous_jacobiThetaCoordinateObservation
  have htheta :
      HGAS.ForwardRecurrentAt
        (fun t ↦
          p.commonScale t •
            jacobiThetaVector (p.xi t) (p.tau t : ℂ)) t₀ := by
    simpa only [
      jacobiThetaCoordinateObservation_point_jacobiBlochPath]
      using hobserved
  by_contra ha0
  exact
    (p.scaled_jacobiThetaVector_not_forwardRecurrentAt
      ha0 hkappa hc0 t₀) htheta

end

end HGAS.Modular
