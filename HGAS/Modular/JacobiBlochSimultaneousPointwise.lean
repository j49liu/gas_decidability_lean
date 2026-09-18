import HGAS.Modular.JacobiBlochGaugePointwise
import HGAS.Modular.JacobiBlochSimultaneousTrajectory

/-!
# Local form of the simultaneous Jacobi--Bloch solution

The affine Bloch formula satisfies the polynomial Jacobi ODE at every
time at which its first theta coordinate is nonzero.  Unlike the global
trajectory theorem, this pointwise statement makes no assumption about
other times.  It is the analytic input for extending regularity by a
closed-and-open continuation argument.
-/

namespace HGAS.Modular

open Complex Real
open UpperHalfPlane hiding I

noncomputable section

namespace AffineBlochParameters

/-- The affine Jacobi--Bloch formula solves the target ODE at one regular
time. -/
theorem jacobiBlochPath_isScaledAt
    (p : AffineBlochParameters)
    (hc0 : p.c0 ≠ 0)
    {t : ℝ}
    (hregular :
      jacobiTheta1 (p.xi t) (p.tau t : ℂ) ≠ 0) :
    IsScaledJacobiRealTrajectoryAt
      ((π : ℂ) * (p.nu : ℂ))
      ((π : ℂ) * I * (p.kappa : ℂ))
      p.jacobiBlochPath t := by
  have hbaseRaw :=
    canonicalJacobiThetaMovingPath_isScaledAt
      (p.hasDerivAt_xi t)
      (p.hasDerivAt_tauComplex t)
      hregular
  have hbase :
      IsScaledJacobiRealTrajectoryAt
        ((π : ℂ) * (p.nu : ℂ) -
          ((π : ℂ) * I * (p.kappa : ℂ)) *
            p.jacobiSlope / 2)
        ((π : ℂ) * I * (p.kappa : ℂ))
        p.canonicalJacobiPath t := by
    rw [← p.canonicalEllipticClock_eq_shifted]
    simpa only [canonicalJacobiPath] using hbaseRaw
  apply jacobiBlochGaugePath_isScaledAt hbase
  · rw [← p.scaleLinearExponent_eq_blochGaugeDrift]
    exact p.commonScale_hasDerivAt t
  · exact p.commonScale_ne_zero hc0 t
  · simp only [canonicalJacobiPath,
      canonicalJacobiThetaMovingPath,
      canonicalJacobiThetaState_U,
      canonicalJacobiThetaState_T1]
    exact inv_mul_cancel₀ hregular

end AffineBlochParameters

end

end HGAS.Modular
