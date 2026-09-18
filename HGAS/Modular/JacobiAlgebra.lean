import Mathlib.Tactic

/-!
# Polynomial algebra of the rational two-variable Jacobi chart

This module encodes the two commuting derivations used by the Jacobi
selector, before any analytic theta-function interpretation is imposed.
It is intentionally algebraic and reusable.

The state consists of the four modular coefficient variables

```
                       p₂, p₃, p₄, H
```

and the six affine Jacobi-chart variables

```
                   T₁, T₂, T₃, T₄, Δ, U.
```

The vector fields `ellipticVectorField` and `modularVectorField` are the
rationally rescaled equations (7.7), (7.9), and (7.10) of the written
proof.  All coefficients are rational.

The central purpose of the file is to check the invariant algebraic
residuals

```
 R₀ = p₃²-p₂²-p₄²,
 R₁ = p₂T₄²-p₄T₂²-p₃T₁²,
 R₂ = p₂T₃²-p₃T₂²-p₄T₁²,
 Rᵁ = UT₁-1.
```

For the elliptic derivation the residual equations are short scalar
cocycles.  For the modular derivation, `R₁` and `R₂` satisfy the explicit
four-generator ideal certificates printed in the paper.  Those two large
identities are proved here by normalization in a polynomial ring; they are
not assumptions imported from the literature.
-/

namespace HGAS.Modular

noncomputable section

/-- Algebraic state of the reciprocal Jacobi chart. -/
@[ext]
structure JacobiState (R : Type*) where
  p2 : R
  p3 : R
  p4 : R
  H : R
  T1 : R
  T2 : R
  T3 : R
  T4 : R
  Delta : R
  U : R

namespace JacobiState

variable {R : Type*} [Field R] [CharZero R]

/-- The weight-two coefficient `K` occurring in both Jacobi
derivations. -/
def K (z : JacobiState R) : R :=
  z.H + (z.p3 ^ 2 + z.p4 ^ 2) / 12

/-- The rationally normalized elliptic derivation `𝒵`.  It fixes the
modular coefficients. -/
def ellipticVectorField (z : JacobiState R) : JacobiState R where
  p2 := 0
  p3 := 0
  p4 := 0
  H := 0
  T1 := z.Delta
  T2 := z.U *
    (z.Delta * z.T2 - z.p2 * z.T3 * z.T4)
  T3 := z.U *
    (z.Delta * z.T3 - z.p3 * z.T4 * z.T2)
  T4 := z.U *
    (z.Delta * z.T4 - z.p4 * z.T2 * z.T3)
  Delta := z.U *
      (z.Delta ^ 2 - z.p3 * z.p4 * z.T2 ^ 2) -
    4 * K z * z.T1
  U := -(z.U ^ 2 * z.Delta)

/-- The rationally normalized modular derivation `Φ` on the coefficient
and Jacobi variables. -/
def modularVectorField (z : JacobiState R) : JacobiState R where
  p2 := 2 * (z.H + (z.p3 ^ 2 + z.p4 ^ 2) / 12) * z.p2
  p3 := 2 * (z.H + (z.p2 ^ 2 - z.p4 ^ 2) / 12) * z.p3
  p4 := 2 * (z.H - (z.p2 ^ 2 + z.p3 ^ 2) / 12) * z.p4
  H := 2 * z.H ^ 2 -
    (z.p2 ^ 4 + z.p3 ^ 4 + z.p4 ^ 4) / 144
  T1 := -(1 / 4) * z.Delta ^ 2 * z.U +
      (1 / 4) * z.p3 * z.p4 * z.T2 ^ 2 * z.U +
    K z * z.T1
  T2 := -(1 / 4) * z.Delta ^ 2 * z.U ^ 2 * z.T2 +
      (1 / 2) * z.p2 * z.Delta * z.T3 * z.T4 * z.U ^ 2 +
      (1 / 4) *
        (z.p3 * z.p4 * z.T2 ^ 2 -
          z.p2 * z.p4 * z.T3 ^ 2 -
          z.p2 * z.p3 * z.T4 ^ 2) *
        z.U ^ 2 * z.T2 +
    K z * z.T2
  T3 := -(1 / 4) * z.Delta ^ 2 * z.U ^ 2 * z.T3 +
      (1 / 2) * z.p3 * z.Delta * z.T4 * z.T2 * z.U ^ 2 +
      (1 / 4) *
        (z.p3 * z.p4 * z.T2 ^ 2 -
          z.p3 * z.p2 * z.T4 ^ 2 -
          z.p3 * z.p4 * z.T2 ^ 2) *
        z.U ^ 2 * z.T3 +
    K z * z.T3
  T4 := -(1 / 4) * z.Delta ^ 2 * z.U ^ 2 * z.T4 +
      (1 / 2) * z.p4 * z.Delta * z.T2 * z.T3 * z.U ^ 2 +
      (1 / 4) *
        (z.p3 * z.p4 * z.T2 ^ 2 -
          z.p4 * z.p3 * z.T2 ^ 2 -
          z.p4 * z.p2 * z.T3 ^ 2) *
        z.U ^ 2 * z.T4 +
    K z * z.T4
  Delta := -(1 / 4) * z.Delta ^ 3 * z.U ^ 2 +
      3 * ((1 / 4) * z.p3 * z.p4 * z.T2 ^ 2 * z.U ^ 2 +
        K z) * z.Delta -
      (1 / 2) * z.p2 * z.p3 * z.p4 *
        z.T2 * z.T3 * z.T4 * z.U ^ 2
  U := -(z.U ^ 2 *
    (-(1 / 4) * z.Delta ^ 2 * z.U +
        (1 / 4) * z.p3 * z.p4 * z.T2 ^ 2 * z.U +
      K z * z.T1))

/-- A linear combination of the elliptic and modular derivations.  The
physical two-clock vector field is an instance of this construction. -/
def combinedVectorField
    (κZ κPhi : R) (z : JacobiState R) :
    JacobiState R :=
  let Z := ellipticVectorField z
  let P := modularVectorField z
  { p2 := κZ * Z.p2 + κPhi * P.p2
    p3 := κZ * Z.p3 + κPhi * P.p3
    p4 := κZ * Z.p4 + κPhi * P.p4
    H := κZ * Z.H + κPhi * P.H
    T1 := κZ * Z.T1 + κPhi * P.T1
    T2 := κZ * Z.T2 + κPhi * P.T2
    T3 := κZ * Z.T3 + κPhi * P.T3
    T4 := κZ * Z.T4 + κPhi * P.T4
    Delta := κZ * Z.Delta + κPhi * P.Delta
    U := κZ * Z.U + κPhi * P.U }

/-! ## Residuals -/

/-- The coefficient-theta quartic residual. -/
def residualR0 (z : JacobiState R) : R :=
  z.p3 ^ 2 - z.p2 ^ 2 - z.p4 ^ 2

/-- The first projective theta-curve quadric. -/
def residualR1 (z : JacobiState R) : R :=
  z.p2 * z.T4 ^ 2 -
    z.p4 * z.T2 ^ 2 -
      z.p3 * z.T1 ^ 2

/-- The second projective theta-curve quadric. -/
def residualR2 (z : JacobiState R) : R :=
  z.p2 * z.T3 ^ 2 -
    z.p3 * z.T2 ^ 2 -
      z.p4 * z.T1 ^ 2

/-- The reciprocal-chart residual. -/
def residualRU (z : JacobiState R) : R :=
  z.U * z.T1 - 1

/-! ## Differentials of the four residual polynomials -/

/-- Directional differential of `R₀`. -/
def residualR0Differential
    (z w : JacobiState R) : R :=
  2 * z.p3 * w.p3 -
    2 * z.p2 * w.p2 -
      2 * z.p4 * w.p4

/-- Directional differential of `R₁`. -/
def residualR1Differential
    (z w : JacobiState R) : R :=
  w.p2 * z.T4 ^ 2 +
      z.p2 * (2 * z.T4 * w.T4) -
    (w.p4 * z.T2 ^ 2 +
      z.p4 * (2 * z.T2 * w.T2)) -
    (w.p3 * z.T1 ^ 2 +
      z.p3 * (2 * z.T1 * w.T1))

/-- Directional differential of `R₂`. -/
def residualR2Differential
    (z w : JacobiState R) : R :=
  w.p2 * z.T3 ^ 2 +
      z.p2 * (2 * z.T3 * w.T3) -
    (w.p3 * z.T2 ^ 2 +
      z.p3 * (2 * z.T2 * w.T2)) -
    (w.p4 * z.T1 ^ 2 +
      z.p4 * (2 * z.T1 * w.T1))

/-- Directional differential of `Rᵁ`. -/
def residualRUDifferential
    (z w : JacobiState R) : R :=
  w.U * z.T1 + z.U * w.T1

/-! ## Short elliptic and coefficient certificates -/

omit [CharZero R] in
/-- The elliptic derivation preserves the first theta-curve quadric modulo
`R₁` and the reciprocal residual. -/
theorem elliptic_residualR1_certificate
    (z : JacobiState R) :
    residualR1Differential z (ellipticVectorField z) =
      2 * z.U * z.Delta * residualR1 z +
        2 * z.p3 * z.T1 * z.Delta * residualRU z := by
  simp only [residualR1Differential, ellipticVectorField,
    residualR1, residualRU]
  ring

omit [CharZero R] in
/-- The elliptic derivation preserves the second theta-curve quadric
modulo `R₂` and the reciprocal residual. -/
theorem elliptic_residualR2_certificate
    (z : JacobiState R) :
    residualR2Differential z (ellipticVectorField z) =
      2 * z.U * z.Delta * residualR2 z +
        2 * z.p4 * z.T1 * z.Delta * residualRU z := by
  simp only [residualR2Differential, ellipticVectorField,
    residualR2, residualRU]
  ring

omit [CharZero R] in
/-- The reciprocal residual is a scalar cocycle for the elliptic
derivation. -/
theorem elliptic_residualRU_certificate
    (z : JacobiState R) :
    residualRUDifferential z (ellipticVectorField z) =
      -z.U * z.Delta * residualRU z := by
  simp only [residualRUDifferential, ellipticVectorField,
    residualRU]
  ring

/-- The modular derivation carries the coefficient residual by the scalar
`4H`. -/
theorem modular_residualR0_certificate
    (z : JacobiState R) :
    residualR0Differential z (modularVectorField z) =
      4 * z.H * residualR0 z := by
  simp only [residualR0Differential, modularVectorField,
    residualR0]
  ring

/-- The reciprocal residual is also a scalar cocycle for the modular
derivation. -/
theorem modular_residualRU_certificate
    (z : JacobiState R) :
    residualRUDifferential z (modularVectorField z) =
      -z.U * (modularVectorField z).T1 *
        residualRU z := by
  simp only [residualRUDifferential, modularVectorField,
    residualRU, K]
  ring

/-! ## Explicit modular ideal certificates

The names and formulas below match equations (7.21)--(7.22) of the
written proof.  Keeping each coefficient separate makes the certificates
easy to inspect and lets downstream invariance arguments refer to them
without repeating a large expression.
-/

def q11 (z : JacobiState R) : R :=
  -(1 / 6) *
    (3 * z.Delta ^ 2 * z.U ^ 2 - 24 * z.H -
      3 * z.T2 ^ 2 * z.U ^ 2 * z.p3 * z.p4 +
      3 * z.T3 ^ 2 * z.U ^ 2 * z.p2 * z.p4 -
      2 * z.p3 ^ 2 - 2 * z.p4 ^ 2)

def q12 (z : JacobiState R) : R :=
  -(z.T1 ^ 2 * z.U ^ 2 * z.p3 * z.p4 / 2)

def q10 (z : JacobiState R) : R :=
  (z.T1 ^ 2 * z.p3 - z.T2 ^ 2 * z.p4) / 6

def q1U (z : JacobiState R) : R :=
  -(z.p3 / 2) *
    (z.Delta ^ 2 * z.T1 * z.U +
      z.T1 ^ 3 * z.U * z.p4 ^ 2 +
      z.T1 ^ 2 * z.p4 ^ 2 +
      z.T2 ^ 2 * z.p3 * z.p4)

def q21 (z : JacobiState R) : R :=
  z.U ^ 2 * z.p3 / 2 *
    (z.T2 ^ 2 * z.p3 - z.T3 ^ 2 * z.p2)

def q22 (z : JacobiState R) : R :=
  -(1 / 6) *
    (3 * z.Delta ^ 2 * z.U ^ 2 - 24 * z.H +
      3 * z.T1 ^ 2 * z.U ^ 2 * z.p3 ^ 2 -
      2 * z.p3 ^ 2 - 2 * z.p4 ^ 2)

def q20 (z : JacobiState R) : R :=
  (-z.T1 ^ 2 * z.p4 + z.T2 ^ 2 * z.p3) / 6

def q2U (z : JacobiState R) : R :=
  -(z.p4 / 2) *
    (z.Delta ^ 2 * z.T1 * z.U +
      z.T1 ^ 3 * z.U * z.p3 ^ 2 +
      z.T1 ^ 2 * z.p3 ^ 2 +
      z.T2 ^ 2 * z.p3 * z.p4)

/-- The full printed modular certificate for `R₁`. -/
theorem modular_residualR1_certificate
    (z : JacobiState R) :
    residualR1Differential z (modularVectorField z) =
      q11 z * residualR1 z +
        q12 z * residualR2 z +
          q10 z * residualR0 z +
            q1U z * residualRU z := by
  simp only [residualR1Differential, modularVectorField,
    residualR1, residualR2, residualR0, residualRU,
    q11, q12, q10, q1U, K]
  ring

/-- The full printed modular certificate for `R₂`. -/
theorem modular_residualR2_certificate
    (z : JacobiState R) :
    residualR2Differential z (modularVectorField z) =
      q21 z * residualR1 z +
        q22 z * residualR2 z +
          q20 z * residualR0 z +
            q2U z * residualRU z := by
  simp only [residualR2Differential, modularVectorField,
    residualR1, residualR2, residualR0, residualRU,
    q21, q22, q20, q2U, K]
  ring

/-! ## Certificates for an arbitrary linear combination -/

theorem combined_residualR0_certificate
    (κZ κPhi : R) (z : JacobiState R) :
    residualR0Differential z
        (combinedVectorField κZ κPhi z) =
      κPhi * (4 * z.H * residualR0 z) := by
  have hZ :
      residualR0Differential z
          (ellipticVectorField z) = 0 := by
    simp [residualR0Differential, ellipticVectorField]
  have hP := modular_residualR0_certificate z
  simp only [residualR0Differential,
    combinedVectorField]
  simp only [residualR0Differential] at hZ hP
  linear_combination κZ * hZ + κPhi * hP

theorem combined_residualR1_certificate
    (κZ κPhi : R) (z : JacobiState R) :
    residualR1Differential z
        (combinedVectorField κZ κPhi z) =
      κZ *
          (2 * z.U * z.Delta * residualR1 z +
            2 * z.p3 * z.T1 * z.Delta *
              residualRU z) +
        κPhi *
          (q11 z * residualR1 z +
            q12 z * residualR2 z +
              q10 z * residualR0 z +
                q1U z * residualRU z) := by
  have hZ := elliptic_residualR1_certificate z
  have hP := modular_residualR1_certificate z
  simp only [residualR1Differential,
    combinedVectorField]
  simp only [residualR1Differential] at hZ hP
  linear_combination κZ * hZ + κPhi * hP

theorem combined_residualR2_certificate
    (κZ κPhi : R) (z : JacobiState R) :
    residualR2Differential z
        (combinedVectorField κZ κPhi z) =
      κZ *
          (2 * z.U * z.Delta * residualR2 z +
            2 * z.p4 * z.T1 * z.Delta *
              residualRU z) +
        κPhi *
          (q21 z * residualR1 z +
            q22 z * residualR2 z +
              q20 z * residualR0 z +
                q2U z * residualRU z) := by
  have hZ := elliptic_residualR2_certificate z
  have hP := modular_residualR2_certificate z
  simp only [residualR2Differential,
    combinedVectorField]
  simp only [residualR2Differential] at hZ hP
  linear_combination κZ * hZ + κPhi * hP

theorem combined_residualRU_certificate
    (κZ κPhi : R) (z : JacobiState R) :
    residualRUDifferential z
        (combinedVectorField κZ κPhi z) =
      (κZ * (-z.U * z.Delta) +
        κPhi *
          (-z.U * (modularVectorField z).T1)) *
        residualRU z := by
  have hZ := elliptic_residualRU_certificate z
  have hP := modular_residualRU_certificate z
  simp only [residualRUDifferential,
    combinedVectorField]
  simp only [residualRUDifferential] at hZ hP
  linear_combination κZ * hZ + κPhi * hP

end JacobiState

end

end HGAS.Modular
