import HGAS.Modular.JacobiAlgebra
import Mathlib.Tactic

/-!
# Second-order algebra of the elliptic Jacobi field

The modular part of the rational Jacobi system is not an unrelated list
of formulas.  On each theta coordinate it is minus one quarter of the
second iterate of the elliptic derivation.  This is the algebraic shadow
of the heat equation

```
                   4 π i ∂τ θ = ∂w² θ.
```

This file proves the polynomial identities independently of theta
functions.  They form a reusable bridge: an analytic function satisfying
the elliptic system and the heat equation automatically satisfies the
modular system.
-/

namespace HGAS.Modular

noncomputable section

namespace JacobiState

variable {R : Type*} [Field R] [CharZero R]

/-- The directional derivative, along the elliptic vector field, of its
`T1` coordinate. -/
def ellipticSecondT1 (z : JacobiState R) : R :=
  (ellipticVectorField z).Delta

/-- The directional derivative, along the elliptic vector field, of its
`T2` coordinate. -/
def ellipticSecondT2 (z : JacobiState R) : R :=
  let Z := ellipticVectorField z
  Z.U * (z.Delta * z.T2 - z.p2 * z.T3 * z.T4) +
    z.U *
      (Z.Delta * z.T2 + z.Delta * Z.T2 -
        z.p2 * (Z.T3 * z.T4 + z.T3 * Z.T4))

/-- The directional derivative, along the elliptic vector field, of its
`T3` coordinate. -/
def ellipticSecondT3 (z : JacobiState R) : R :=
  let Z := ellipticVectorField z
  Z.U * (z.Delta * z.T3 - z.p3 * z.T4 * z.T2) +
    z.U *
      (Z.Delta * z.T3 + z.Delta * Z.T3 -
        z.p3 * (Z.T4 * z.T2 + z.T4 * Z.T2))

/-- The directional derivative, along the elliptic vector field, of its
`T4` coordinate. -/
def ellipticSecondT4 (z : JacobiState R) : R :=
  let Z := ellipticVectorField z
  Z.U * (z.Delta * z.T4 - z.p4 * z.T2 * z.T3) +
    z.U *
      (Z.Delta * z.T4 + z.Delta * Z.T4 -
        z.p4 * (Z.T2 * z.T3 + z.T2 * Z.T3))

/-- The directional derivative, along the elliptic vector field, of its
`Delta` coordinate. -/
def ellipticSecondDelta (z : JacobiState R) : R :=
  let Z := ellipticVectorField z
  Z.U * (z.Delta ^ 2 - z.p3 * z.p4 * z.T2 ^ 2) +
    z.U *
      (2 * z.Delta * Z.Delta -
        z.p3 * z.p4 * (2 * z.T2 * Z.T2)) -
    4 * K z * Z.T1

theorem ellipticSecondT1_eq_modular
    (z : JacobiState R) :
    ellipticSecondT1 z =
      -4 * (modularVectorField z).T1 := by
  simp only [ellipticSecondT1, ellipticVectorField,
    modularVectorField]
  ring

theorem ellipticSecondT2_eq_modular
    (z : JacobiState R)
    (hreciprocal : z.U * z.T1 = 1) :
    ellipticSecondT2 z =
      -4 * (modularVectorField z).T2 := by
  simp only [ellipticSecondT2, ellipticVectorField,
    modularVectorField]
  linear_combination
    (-4 * z.K * z.T2) * hreciprocal

theorem ellipticSecondT3_eq_modular
    (z : JacobiState R)
    (hreciprocal : z.U * z.T1 = 1) :
    ellipticSecondT3 z =
      -4 * (modularVectorField z).T3 := by
  simp only [ellipticSecondT3, ellipticVectorField,
    modularVectorField]
  linear_combination
    (-4 * z.K * z.T3) * hreciprocal

theorem ellipticSecondT4_eq_modular
    (z : JacobiState R)
    (hreciprocal : z.U * z.T1 = 1) :
    ellipticSecondT4 z =
      -4 * (modularVectorField z).T4 := by
  simp only [ellipticSecondT4, ellipticVectorField,
    modularVectorField]
  linear_combination
    (-4 * z.K * z.T4) * hreciprocal

theorem ellipticSecondDelta_eq_modular
    (z : JacobiState R)
    (hreciprocal : z.U * z.T1 = 1) :
    ellipticSecondDelta z =
      -4 * (modularVectorField z).Delta := by
  simp only [ellipticSecondDelta, ellipticVectorField,
    modularVectorField]
  linear_combination
    (-8 * z.Delta * z.K) * hreciprocal

end JacobiState

end

end HGAS.Modular
