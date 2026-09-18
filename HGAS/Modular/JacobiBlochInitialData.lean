import HGAS.Modular.JacobiThetaInitialValueMap
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Jacobi--Bloch solutions through prescribed initial data

This file formalizes the elementary analytic part of equations (8.9)--(8.10).
For fixed `τ` in the upper half-plane, put

```text
  ξ(w) = w + a τ + b,
  S(w) = C exp(π i a (2w + aτ)).
```

The associated four-theta vector is `S(w) T(ξ(w),τ)`.  We prove its exact
complex derivative and then verify the manuscript's explicit inverse
parameter choice

```text
  a = L/(2i),  b = ξ-w-aτ,
  C = S exp(-π i a(2w+aτ)).
```

At the selected point the vector has value `S T(ξ,τ)`, and its derivative
divided by `π` has first coordinate

```text
  S (T₁'(ξ,τ)/π + L T₁(ξ,τ)).
```

The definitions are kept independent of the polynomial residual system, so
the module can be reused wherever a theta-valued Bloch solution is needed.
-/

namespace HGAS.Modular

open Complex Real

noncomputable section

/-- Elliptic argument of a fixed-modulus Jacobi--Bloch solution. -/
def jacobiBlochArgument
    (a b τ w : ℂ) : ℂ :=
  w + a * τ + b

/-- Exponent of the common scalar factor in a Jacobi--Bloch solution. -/
def jacobiBlochExponent
    (a τ w : ℂ) : ℂ :=
  π * I * a * (2 * w + a * τ)

/-- Common scalar factor in a Jacobi--Bloch solution. -/
def jacobiBlochScale
    (C a τ w : ℂ) : ℂ :=
  C * Complex.exp (jacobiBlochExponent a τ w)

/-- Four-coordinate fixed-modulus Jacobi--Bloch solution. -/
def jacobiBlochThetaVector
    (C a b τ w : ℂ) : Fin 4 → ℂ :=
  jacobiBlochScale C a τ w •
    jacobiThetaVector (jacobiBlochArgument a b τ w) τ

/-- Its explicit derivative with respect to the elliptic variable `w`. -/
def jacobiBlochThetaVectorPrime
    (C a b τ w : ℂ) : Fin 4 → ℂ :=
  jacobiBlochScale C a τ w •
      jacobiThetaVectorPrime
        (jacobiBlochArgument a b τ w) τ +
    (jacobiBlochScale C a τ w * (π * I * a * 2)) •
      jacobiThetaVector
        (jacobiBlochArgument a b τ w) τ

/-- The explicit Bloch vector has the displayed complex derivative. -/
theorem hasDerivAt_jacobiBlochThetaVector
    (C a b τ w : ℂ)
    (hτ : 0 < τ.im) :
    HasDerivAt
      (jacobiBlochThetaVector C a b τ)
      (jacobiBlochThetaVectorPrime C a b τ w)
      w := by
  have harg :
      HasDerivAt
        (jacobiBlochArgument a b τ)
        1 w := by
    exact
      ((hasDerivAt_id w).add_const (a * τ)).add_const b
  have hexponent :
      HasDerivAt
        (jacobiBlochExponent a τ)
        (π * I * a * 2) w := by
    simpa using
      (((hasDerivAt_id w).const_mul 2).add_const
        (a * τ)).const_mul (π * I * a)
  have hscale :
      HasDerivAt
        (jacobiBlochScale C a τ)
        (jacobiBlochScale C a τ w *
          (π * I * a * 2)) w := by
    convert hexponent.cexp.const_mul C using 1
    simp [jacobiBlochScale]
    ring
  have htheta :
      HasDerivAt
        (fun z ↦
          jacobiThetaVector
            (jacobiBlochArgument a b τ z) τ)
        (jacobiThetaVectorPrime
          (jacobiBlochArgument a b τ w) τ) w := by
    have hbase :=
      hasDerivAt_jacobiThetaVector
        (jacobiBlochArgument a b τ w) τ hτ
    have hcomp := hbase.scomp w harg
    simpa using hcomp
  simpa [jacobiBlochThetaVector,
    jacobiBlochThetaVectorPrime] using
    hscale.smul htheta

/-! ## Explicit inverse initial-data parameters -/

/-- Bloch parameter selected by a prescribed logarithmic slope. -/
def jacobiBlochParameterA (L : ℂ) : ℂ :=
  L / (2 * I)

/-- Additive elliptic parameter selected by a prescribed argument. -/
def jacobiBlochParameterB
    (ξ w τ L : ℂ) : ℂ :=
  ξ - w - jacobiBlochParameterA L * τ

/-- Common amplitude selected by a prescribed scale. -/
def jacobiBlochParameterC
    (S w τ L : ℂ) : ℂ :=
  S * Complex.exp
    (-jacobiBlochExponent (jacobiBlochParameterA L) τ w)

@[simp]
theorem jacobiBlochArgument_selected
    (ξ w τ L : ℂ) :
    jacobiBlochArgument
        (jacobiBlochParameterA L)
        (jacobiBlochParameterB ξ w τ L)
        τ w =
      ξ := by
  simp [jacobiBlochArgument,
    jacobiBlochParameterB]

@[simp]
theorem jacobiBlochScale_selected
    (S w τ L : ℂ) :
    jacobiBlochScale
        (jacobiBlochParameterC S w τ L)
        (jacobiBlochParameterA L) τ w =
      S := by
  simp [jacobiBlochScale,
    jacobiBlochParameterC, Complex.exp_neg]

/-- The selected parameters reproduce the prescribed scaled theta vector. -/
theorem jacobiBlochThetaVector_selected
    (S ξ w τ L : ℂ) :
    jacobiBlochThetaVector
        (jacobiBlochParameterC S w τ L)
        (jacobiBlochParameterA L)
        (jacobiBlochParameterB ξ w τ L)
        τ w =
      S • jacobiThetaVector ξ τ := by
  simp [jacobiBlochThetaVector]

/-- The selected parameter `a=L/(2i)` makes the derivative of the common
exponent exactly `πL`. -/
theorem jacobiBloch_exponentDerivative_selected
    (L : ℂ) :
    π * I * jacobiBlochParameterA L * 2 =
      π * L := by
  simp [jacobiBlochParameterA]
  field_simp

/-- At the selected point, the explicit derivative has the form used by
the initial-value map. -/
theorem jacobiBlochThetaVectorPrime_selected
    (S ξ w τ L : ℂ) :
    jacobiBlochThetaVectorPrime
        (jacobiBlochParameterC S w τ L)
        (jacobiBlochParameterA L)
        (jacobiBlochParameterB ξ w τ L)
        τ w =
      S • jacobiThetaVectorPrime ξ τ +
        (S * (π * L)) • jacobiThetaVector ξ τ := by
  simp [jacobiBlochThetaVectorPrime,
    jacobiBloch_exponentDerivative_selected]

/-- The normalized first derivative of the selected Bloch solution is the
last coordinate of the manuscript's initial-value map. -/
theorem jacobiBlochThetaVectorPrime_selected_zero_div_pi
    (S ξ w τ L : ℂ) :
    jacobiBlochThetaVectorPrime
          (jacobiBlochParameterC S w τ L)
          (jacobiBlochParameterA L)
          (jacobiBlochParameterB ξ w τ L)
          τ w 0 / π =
      S * (jacobiThetaVectorPrime ξ τ 0 / π +
        L * jacobiThetaVector ξ τ 0) := by
  rw [jacobiBlochThetaVectorPrime_selected]
  simp only [Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  field_simp

end

end HGAS.Modular
