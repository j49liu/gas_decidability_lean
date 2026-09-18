import HGAS.Modular.JacobiThetaInitialRank

/-!
# Joint continuity of the elliptic derivatives of the Jacobi theta vector

The theta vector itself is already known to be jointly continuous in its
elliptic argument and upper-half-plane modulus.  Coherent Bloch-parameter
reconstruction also uses the normalized first elliptic derivative.

Mathlib proves joint continuity of the differentiated two-variable theta
series at every point with positive modular imaginary part.  This file
transfers that result to the four characteristic conventions used by the
Jacobi compiler.
-/

namespace HGAS.Modular

open UpperHalfPlane hiding I
open Complex Real

noncomputable section

theorem continuous_jacobiTheta₂'_upperHalfPlane :
    Continuous
      (fun p : ℂ × ℍ ↦
        jacobiTheta₂' p.1 (p.2 : ℂ)) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hp :
      ContinuousAt
        (fun q : ℂ × ℍ ↦
          (q.1, (q.2 : ℂ))) p := by
    fun_prop
  simpa only [Function.comp_apply] using
    (continuousAt_jacobiTheta₂'
      p.1 p.2.im_pos).comp
        (f := fun q : ℂ × ℍ ↦
          (q.1, (q.2 : ℂ))) hp

theorem continuous_jacobiTheta3Prime_upperHalfPlane :
    Continuous
      (fun p : ℂ × ℍ ↦
        jacobiTheta3Prime p.1 (p.2 : ℂ)) := by
  simpa only [jacobiTheta3Prime] using
    continuous_jacobiTheta₂'_upperHalfPlane

theorem continuous_jacobiTheta4Prime_upperHalfPlane :
    Continuous
      (fun p : ℂ × ℍ ↦
        jacobiTheta4Prime p.1 (p.2 : ℂ)) := by
  have hcomp :=
    continuous_jacobiTheta₂'_upperHalfPlane.comp
      (show
        Continuous
          (fun p : ℂ × ℍ ↦
            (p.1 + 1 / 2, p.2)) by
        fun_prop)
  simpa only [jacobiTheta4Prime,
    Function.comp_apply] using hcomp

theorem continuous_jacobiTheta2Prime_upperHalfPlane :
    Continuous
      (fun p : ℂ × ℍ ↦
        jacobiTheta2Prime p.1 (p.2 : ℂ)) := by
  have htheta :
      Continuous
        (fun p : ℂ × ℍ ↦
          jacobiTheta₂
            (p.1 + (p.2 : ℂ) / 2)
            (p.2 : ℂ)) := by
    exact
      continuous_jacobiTheta₂_upperHalfPlane.comp
        (show
          Continuous
            (fun p : ℂ × ℍ ↦
              (p.1 + (p.2 : ℂ) / 2, p.2)) by
          fun_prop)
  have hprime :
      Continuous
        (fun p : ℂ × ℍ ↦
          jacobiTheta₂'
            (p.1 + (p.2 : ℂ) / 2)
            (p.2 : ℂ)) := by
    exact
      continuous_jacobiTheta₂'_upperHalfPlane.comp
        (show
          Continuous
            (fun p : ℂ × ℍ ↦
              (p.1 + (p.2 : ℂ) / 2, p.2)) by
          fun_prop)
  rw [show
      (fun p : ℂ × ℍ ↦
        jacobiTheta2Prime p.1 (p.2 : ℂ)) =
      fun p ↦
        cexp
            (π * I *
              ((p.2 : ℂ) / 4 + p.1)) *
          (π * I *
              jacobiTheta₂
                (p.1 + (p.2 : ℂ) / 2)
                (p.2 : ℂ) +
            jacobiTheta₂'
              (p.1 + (p.2 : ℂ) / 2)
              (p.2 : ℂ)) by
    funext p
    rfl]
  exact
    (Complex.continuous_exp.comp (by fun_prop)).mul
      ((continuous_const.mul htheta).add hprime)

theorem continuous_jacobiTheta1Prime_upperHalfPlane :
    Continuous
      (fun p : ℂ × ℍ ↦
        jacobiTheta1Prime p.1 (p.2 : ℂ)) := by
  have hcomp :=
    continuous_jacobiTheta2Prime_upperHalfPlane.comp
      (show
        Continuous
          (fun p : ℂ × ℍ ↦
            (p.1 + 1 / 2, p.2)) by
        fun_prop)
  simpa only [jacobiTheta1Prime,
    Function.comp_apply] using hcomp.neg

/-- Joint continuity of the differentiated four-theta vector on
`ℂ × ℍ`. -/
theorem continuous_jacobiThetaVectorPrime_upperHalfPlane :
    Continuous
      (fun p : ℂ × ℍ ↦
        jacobiThetaVectorPrime p.1 (p.2 : ℂ)) := by
  apply continuous_pi
  intro k
  fin_cases k
  · simpa only [jacobiThetaVectorPrime,
      Matrix.cons_val_zero] using
      continuous_jacobiTheta1Prime_upperHalfPlane
  · simpa only [jacobiThetaVectorPrime,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      continuous_jacobiTheta2Prime_upperHalfPlane
  · simpa only [jacobiThetaVectorPrime,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      continuous_jacobiTheta3Prime_upperHalfPlane
  · simpa only [jacobiThetaVectorPrime,
      Matrix.cons_val_one, Matrix.cons_val_zero] using
      continuous_jacobiTheta4Prime_upperHalfPlane

end

end HGAS.Modular
