import HGAS.Modular.JacobiSecondOrderAlgebra
import HGAS.Modular.JacobiThetaEllipticTrajectory

/-!
# Differentiating the elliptic Jacobi vector field

`JacobiSecondOrderAlgebra` computes the second iterate of the elliptic
derivation as a polynomial.  This file supplies the corresponding
calculus statement: along any genuine elliptic trajectory, differentiating
one of the theta-coordinate components of the elliptic vector field gives
the computed second iterate.

The lemmas are stated for an arbitrary complex scale `κ`; the canonical
theta trajectory later uses `κ = π`.
-/

namespace HGAS.Modular

open Complex

noncomputable section

namespace IsScaledJacobiEllipticTrajectoryAt

variable {κ : ℂ} {s : ℂ → JacobiState ℂ} {w : ℂ}

theorem elliptic_T1_hasDerivAt
    (h : IsScaledJacobiEllipticTrajectoryAt κ s w) :
    HasDerivAt
      (fun z =>
        (JacobiState.ellipticVectorField (s z)).T1)
      (κ * JacobiState.ellipticSecondT1 (s w)) w := by
  simpa only [JacobiState.ellipticVectorField,
    JacobiState.ellipticSecondT1] using h.Delta

theorem elliptic_T2_hasDerivAt
    (h : IsScaledJacobiEllipticTrajectoryAt κ s w) :
    HasDerivAt
      (fun z =>
        (JacobiState.ellipticVectorField (s z)).T2)
      (κ * JacobiState.ellipticSecondT2 (s w)) w := by
  have hraw :=
    h.U.mul
      ((h.Delta.mul h.T2).sub
        ((h.p2.mul h.T3).mul h.T4))
  convert hraw using 1
  simp only [JacobiState.ellipticSecondT2,
    JacobiState.ellipticVectorField, Pi.mul_apply,
    Pi.sub_apply]
  ring

theorem elliptic_T3_hasDerivAt
    (h : IsScaledJacobiEllipticTrajectoryAt κ s w) :
    HasDerivAt
      (fun z =>
        (JacobiState.ellipticVectorField (s z)).T3)
      (κ * JacobiState.ellipticSecondT3 (s w)) w := by
  have hraw :=
    h.U.mul
      ((h.Delta.mul h.T3).sub
        ((h.p3.mul h.T4).mul h.T2))
  convert hraw using 1
  simp only [JacobiState.ellipticSecondT3,
    JacobiState.ellipticVectorField, Pi.mul_apply,
    Pi.sub_apply]
  ring

theorem elliptic_T4_hasDerivAt
    (h : IsScaledJacobiEllipticTrajectoryAt κ s w) :
    HasDerivAt
      (fun z =>
        (JacobiState.ellipticVectorField (s z)).T4)
      (κ * JacobiState.ellipticSecondT4 (s w)) w := by
  have hraw :=
    h.U.mul
      ((h.Delta.mul h.T4).sub
        ((h.p4.mul h.T2).mul h.T3))
  convert hraw using 1
  simp only [JacobiState.ellipticSecondT4,
    JacobiState.ellipticVectorField, Pi.mul_apply,
    Pi.sub_apply]
  ring

theorem elliptic_Delta_hasDerivAt
    (h : IsScaledJacobiEllipticTrajectoryAt κ s w) :
    HasDerivAt
      (fun z =>
        (JacobiState.ellipticVectorField (s z)).Delta)
      (κ * JacobiState.ellipticSecondDelta (s w)) w := by
  have hK :
      HasDerivAt
        (fun z => JacobiState.K (s z))
        (κ *
          (JacobiState.ellipticVectorField
            (s w)).H +
          ((2 * (s w).p3 *
                (κ *
                  (JacobiState.ellipticVectorField
                    (s w)).p3) +
              2 * (s w).p4 *
                (κ *
                  (JacobiState.ellipticVectorField
                    (s w)).p4)) / 12)) w := by
    unfold JacobiState.K
    convert
      h.H.add
        (((h.p3.fun_pow 2).add
          (h.p4.fun_pow 2)).div_const 12) using 1
    ring
  have hraw :=
    (h.U.mul
      ((h.Delta.fun_pow 2).sub
        (((h.p3.mul h.p4).mul
          (h.T2.fun_pow 2))))).sub
      ((hK.const_mul 4).mul h.T1)
  convert hraw using 1
  simp only [JacobiState.ellipticSecondDelta,
    JacobiState.ellipticVectorField, Pi.mul_apply,
    Pi.sub_apply, Nat.reduceSub, pow_one]
  ring

end IsScaledJacobiEllipticTrajectoryAt

end

end HGAS.Modular
