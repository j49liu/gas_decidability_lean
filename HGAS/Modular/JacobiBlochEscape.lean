import HGAS.Modular.JacobiBlochAffine
import HGAS.Modular.JacobiThetaEscape

/-!
# Unconditional escape of a nonreal affine Jacobi--Bloch leaf

This module composes the previously separated pieces of equation
(8.14)--(8.16):

* exact affine Bloch parameter bookkeeping;
* canonical reduction by both level-two elliptic periods;
* horizontal modular reduction modulo `τ ↦ τ+2k`;
* global nonvanishing of the four-coordinate theta vector;
* compactness of the reduced coordinate box; and
* domination of every linear exponential loss by the quadratic lattice
  multiplier.

The resulting theorem starts with the literal affine Bloch parameters.
If the Bloch shift has nonzero imaginary part, the modular line has
nonzero horizontal speed, and the common scale constant is nonzero, then
the norm of the four theta coordinates tends to infinity.  No lower-bound,
reduction, or asymptotic hypothesis remains.
-/

namespace HGAS.Modular

open Filter

noncomputable section

namespace AffineBlochParameters

/-- **Nonreal affine Bloch escape.**  The complete scaled theta vector
leaves every bounded subset in forward time. -/
theorem scaled_jacobiThetaVector_tendsto_atTop
    (p : AffineBlochParameters)
    (ha0 : p.a0.im ≠ 0)
    (hkappa : p.kappa ≠ 0)
    (hc0 : p.c0 ≠ 0) :
    Tendsto
      (fun t : ℝ ↦
        ‖p.commonScale t •
          jacobiThetaVector (p.xi t) (p.tau t : ℂ)‖)
      atTop atTop := by
  obtain ⟨hslope, hxi, hscale⟩ :=
    p.nonreal_escape_parameter_bounds
      ha0 hkappa hc0
  apply
    scaled_jacobiThetaVector_tendsto_atTop_of_fixedHeight
      (τ := p.tau) (ξ := p.xi) (S := p.commonScale)
      (γ := p.gamma)
      (verticalSlope := p.verticalSlope)
      (err := |p.xiImaginaryIntercept|)
      (scale := p.commonScaleLoss)
      p.gamma_pos hslope
  · exact p.tau_im
  · exact hxi
  · exact hscale

/-- No point of a nonreal affine Bloch theta trajectory is forward
recurrent in the affine theta coordinates. -/
theorem scaled_jacobiThetaVector_not_forwardRecurrentAt
    (p : AffineBlochParameters)
    (ha0 : p.a0.im ≠ 0)
    (hkappa : p.kappa ≠ 0)
    (hc0 : p.c0 ≠ 0)
    (t₀ : ℝ) :
    ¬ HGAS.ForwardRecurrentAt
      (fun t : ℝ ↦
        p.commonScale t •
          jacobiThetaVector (p.xi t) (p.tau t : ℂ))
      t₀ := by
  exact
    HGAS.not_forwardRecurrentAt_of_norm_tendsto_atTop
      (p.scaled_jacobiThetaVector_tendsto_atTop
        ha0 hkappa hc0)

end AffineBlochParameters

end

end HGAS.Modular
