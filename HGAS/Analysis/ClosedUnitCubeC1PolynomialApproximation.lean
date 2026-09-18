import HGAS.Analysis.C1PolynomialApproximation
import HGAS.Analysis.TensorBernsteinC1Approximation
import Mathlib.Tactic

/-!
# `C¹` polynomial approximation on the closed unit cube

This file packages the tensor Bernstein convergence theorem in the
abstract interface used by the Lyapunov arguments.

The hypotheses are deliberately coordinatewise.  The function `D x i`
is the intended derivative in coordinate `i`; its continuity on the
cube gives the uniform modulus needed in the Bernstein proof, and
`hderiv` says that the corresponding one-variable slice really has that
derivative.  The approximating polynomial is explicit: for a sufficiently
large `m`, it is the degree-`m+1` tensor Bernstein polynomial.
-/

namespace HGAS

open Filter Set

noncomputable section

variable {n : ℕ}

/-- Turn a real-coordinate point known to lie in `[0,1]^n` into the
subtype-valued cube point used by the tensor Bernstein construction. -/
def unitCubePointOfMem
    (x : Fin n → ℝ)
    (hx : x ∈ closedUnitCubeSet n) :
    UnitCube n :=
  fun i ↦
    ⟨x i, (mem_closedUnitCubeSet x).mp hx i⟩

@[simp]
theorem unitCubeRealPoint_unitCubePointOfMem
    (x : Fin n → ℝ)
    (hx : x ∈ closedUnitCubeSet n) :
    unitCubeRealPoint (unitCubePointOfMem x hx) = x := by
  rfl

/-- A `C¹` function on the real closed unit cube admits simultaneous
uniform polynomial approximation of its value and all coordinate
derivatives.

The proof chooses one member of the eventually uniformly convergent
tensor Bernstein sequence. -/
theorem hasC1MvPolynomialApproximationOn_closedUnitCube
    (f : (Fin n → ℝ) → ℝ)
    (D : (Fin n → ℝ) → Fin n → ℝ)
    (hf : ContinuousOn f (closedUnitCubeSet n))
    (hD :
      ∀ i,
        ContinuousOn (fun x ↦ D x i)
          (closedUnitCubeSet n))
    (hderiv :
      ∀ x ∈ closedUnitCubeSet n, ∀ i,
        HasDerivAt
          (fun t : ℝ ↦
            f (Function.update x i t))
          (D x i) (x i)) :
    HasC1MvPolynomialApproximationOn
      (closedUnitCubeSet n) f D := by
  intro ε hε
  have heventually :=
    eventually_tensorBernsteinPolynomial_c1_near
      f D hf hD hderiv hε
  obtain ⟨m, hmValue, hmDerivative⟩ :=
    heventually.exists
  refine
    ⟨tensorBernsteinPolynomial (m + 1) f,
      ?_, ?_⟩
  · intro x hx
    let xCube : UnitCube n :=
      unitCubePointOfMem x hx
    have h := hmValue xCube
    simpa only [xCube,
      unitCubeRealPoint_unitCubePointOfMem] using h
  · intro x hx i
    let xCube : UnitCube n :=
      unitCubePointOfMem x hx
    have h := hmDerivative xCube i
    simpa only [xCube,
      unitCubeRealPoint_unitCubePointOfMem] using h

/-- Uniform `C¹` polynomial approximability is inherited by subsets. -/
theorem HasC1MvPolynomialApproximationOn.mono
    {s t : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → ℝ}
    {D : (Fin n → ℝ) → Fin n → ℝ}
    (h : HasC1MvPolynomialApproximationOn s f D)
    (hts : t ⊆ s) :
    HasC1MvPolynomialApproximationOn t f D := by
  intro ε hε
  obtain ⟨p, hpValue, hpDerivative⟩ :=
    h hε
  exact
    ⟨p,
      fun x hx ↦ hpValue x (hts hx),
      fun x hx i ↦ hpDerivative x (hts hx) i⟩

end

end HGAS
