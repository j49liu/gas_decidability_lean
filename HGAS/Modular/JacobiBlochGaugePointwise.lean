import HGAS.Modular.JacobiBlochGaugeCovariance
import HGAS.Modular.JacobiThetaMovingTrajectory

/-!
# Pointwise Bloch-gauge covariance

The global trajectory theorem in `JacobiBlochGaugeCovariance` assumes that
the reciprocal theta chart is regular for every real time.  Continuation
arguments need a local version: at one regular time, the product rule and
the algebraic gauge identity already give the transformed ODE.

This file states precisely that pointwise fact.  It is intentionally
separate from the theta-function formula, so any locally regular solution
of the rational Jacobi chart can use it.
-/

namespace HGAS.Modular

noncomputable section

/-- A pointwise solution of the shifted Jacobi system transforms to a
pointwise solution of the target system under the Bloch gauge. -/
theorem jacobiBlochGaugePath_isScaledAt
    {κZ κPhi L : ℂ}
    {S : ℝ → ℂ} {z : ℝ → JacobiState ℂ}
    {t : ℝ}
    (hz :
      IsScaledJacobiRealTrajectoryAt
        (κZ - κPhi * L / 2) κPhi z t)
    (hS :
      HasDerivAt S
        (JacobiState.blochGaugeLogarithmicDrift
          κZ κPhi L * S t) t)
    (hSzero : S t ≠ 0)
    (hreciprocal : (z t).U * (z t).T1 = 1) :
    IsScaledJacobiRealTrajectoryAt
      κZ κPhi (jacobiBlochGaugePath S L z) t := by
  let g : ℂ :=
    JacobiState.blochGaugeLogarithmicDrift
      κZ κPhi L
  have hcov :
      JacobiState.blochGaugeCombinedTangent
          κZ κPhi (S t) L (z t) =
        JacobiState.combinedVectorField κZ κPhi
          (JacobiState.blochGauge (S t) L (z t)) :=
    JacobiState.blochGaugeCombinedTangent_eq
      κZ κPhi (S t) L (z t)
        hSzero hreciprocal
  refine
    {
      p2 := ?_
      p3 := ?_
      p4 := ?_
      H := ?_
      T1 := ?_
      T2 := ?_
      T3 := ?_
      T4 := ?_
      Delta := ?_
      U := ?_
    }
  · have htangent :
        HasDerivAt
          (fun s ↦
            (jacobiBlochGaugePath S L z s).p2)
          (JacobiState.blochGaugeCombinedTangent
            κZ κPhi (S t) L (z t)).p2 t := by
      simpa [jacobiBlochGaugePath,
        JacobiState.blochGaugeCombinedTangent] using hz.p2
    rw [hcov] at htangent
    exact htangent
  · have htangent :
        HasDerivAt
          (fun s ↦
            (jacobiBlochGaugePath S L z s).p3)
          (JacobiState.blochGaugeCombinedTangent
            κZ κPhi (S t) L (z t)).p3 t := by
      simpa [jacobiBlochGaugePath,
        JacobiState.blochGaugeCombinedTangent] using hz.p3
    rw [hcov] at htangent
    exact htangent
  · have htangent :
        HasDerivAt
          (fun s ↦
            (jacobiBlochGaugePath S L z s).p4)
          (JacobiState.blochGaugeCombinedTangent
            κZ κPhi (S t) L (z t)).p4 t := by
      simpa [jacobiBlochGaugePath,
        JacobiState.blochGaugeCombinedTangent] using hz.p4
    rw [hcov] at htangent
    exact htangent
  · have htangent :
        HasDerivAt
          (fun s ↦
            (jacobiBlochGaugePath S L z s).H)
          (JacobiState.blochGaugeCombinedTangent
            κZ κPhi (S t) L (z t)).H t := by
      simpa [jacobiBlochGaugePath,
        JacobiState.blochGaugeCombinedTangent] using hz.H
    rw [hcov] at htangent
    exact htangent
  · have hraw := hS.mul hz.T1
    have htangent :
        HasDerivAt
          (fun s ↦
            (jacobiBlochGaugePath S L z s).T1)
          (JacobiState.blochGaugeCombinedTangent
            κZ κPhi (S t) L (z t)).T1 t := by
      change
        HasDerivAt
          (fun s ↦ S s * (z s).T1)
          _ t
      convert hraw using 1
      simp only [
        JacobiState.blochGaugeCombinedTangent]
      ring
    rw [hcov] at htangent
    exact htangent
  · have hraw := hS.mul hz.T2
    have htangent :
        HasDerivAt
          (fun s ↦
            (jacobiBlochGaugePath S L z s).T2)
          (JacobiState.blochGaugeCombinedTangent
            κZ κPhi (S t) L (z t)).T2 t := by
      change
        HasDerivAt
          (fun s ↦ S s * (z s).T2)
          _ t
      convert hraw using 1
      simp only [
        JacobiState.blochGaugeCombinedTangent]
      ring
    rw [hcov] at htangent
    exact htangent
  · have hraw := hS.mul hz.T3
    have htangent :
        HasDerivAt
          (fun s ↦
            (jacobiBlochGaugePath S L z s).T3)
          (JacobiState.blochGaugeCombinedTangent
            κZ κPhi (S t) L (z t)).T3 t := by
      change
        HasDerivAt
          (fun s ↦ S s * (z s).T3)
          _ t
      convert hraw using 1
      simp only [
        JacobiState.blochGaugeCombinedTangent]
      ring
    rw [hcov] at htangent
    exact htangent
  · have hraw := hS.mul hz.T4
    have htangent :
        HasDerivAt
          (fun s ↦
            (jacobiBlochGaugePath S L z s).T4)
          (JacobiState.blochGaugeCombinedTangent
            κZ κPhi (S t) L (z t)).T4 t := by
      change
        HasDerivAt
          (fun s ↦ S s * (z s).T4)
          _ t
      convert hraw using 1
      simp only [
        JacobiState.blochGaugeCombinedTangent]
      ring
    rw [hcov] at htangent
    exact htangent
  · have hinside :=
      hz.Delta.add
        (HasDerivAt.const_mul L hz.T1)
    have hraw := hS.mul hinside
    have hraw' :
        HasDerivAt
          (fun s ↦
            S s * ((z s).Delta + L * (z s).T1))
          (g * S t *
              ((z t).Delta + L * (z t).T1) +
            S t *
              ((JacobiState.combinedVectorField
                (κZ - κPhi * L / 2) κPhi
                  (z t)).Delta +
                L *
                  (JacobiState.combinedVectorField
                    (κZ - κPhi * L / 2) κPhi
                      (z t)).T1)) t := by
      simpa only [Pi.add_apply, g] using hraw
    have htangent :
        HasDerivAt
          (fun s ↦
            (jacobiBlochGaugePath S L z s).Delta)
          (JacobiState.blochGaugeCombinedTangent
            κZ κPhi (S t) L (z t)).Delta t := by
      change
        HasDerivAt
          (fun s ↦
            S s * ((z s).Delta + L * (z s).T1))
          _ t
      convert hraw' using 1
      simp only [
        JacobiState.blochGaugeCombinedTangent, g]
      ring
    rw [hcov] at htangent
    exact htangent
  · have hinv :=
      (hasDerivAt_inv hSzero).scomp t hS
    have hraw := hz.U.mul hinv
    have htangent :
        HasDerivAt
          (fun s ↦
            (jacobiBlochGaugePath S L z s).U)
          (JacobiState.blochGaugeCombinedTangent
            κZ κPhi (S t) L (z t)).U t := by
      change
        HasDerivAt
          (fun s ↦ (z s).U * (S s)⁻¹)
          _ t
      convert hraw using 1
      simp only [
        JacobiState.blochGaugeCombinedTangent,
        Function.comp_apply, smul_eq_mul]
      field_simp [hSzero]
      ring
    rw [hcov] at htangent
    exact htangent

end

end HGAS.Modular
