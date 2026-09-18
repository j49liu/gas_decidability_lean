import HGAS.Analysis.CoordinateBernsteinOperator
import Mathlib.Tactic

/-!
# Iterating coordinate Bernstein operators

This file isolates the finite-dimensional argument that turns uniform
one-coordinate approximation into uniform approximation on a cube.
Nothing probabilistic is hidden here.  If `Bᵢ` denotes Bernstein
averaging in coordinate `i`, positivity gives

```
|Bᵢ g - Bᵢ f| ≤ ‖g-f‖∞.
```

Consequently a telescoping argument bounds the error of a list of
coordinate operators by the sum of their individual errors on the
original function.  This formulation is useful beyond Bernstein
polynomials: the proof only uses the contraction property.
-/

namespace HGAS

open Filter
open scoped Topology

noncomputable section

variable {n : ℕ}

/-- Apply degree-`m` Bernstein averaging successively in the coordinates
listed in `l`.  The tail is applied first; this convention makes the
inductive error estimate especially direct. -/
def bernsteinAlongCoordinates
    (m : ℕ) : List (Fin n) → C(UnitCube n, ℝ) →
      C(UnitCube n, ℝ)
  | [], f => f
  | i :: l, f =>
      coordinateBernsteinApproximation m i
        (bernsteinAlongCoordinates m l f)

@[simp]
theorem bernsteinAlongCoordinates_nil
    (m : ℕ) (f : C(UnitCube n, ℝ)) :
    bernsteinAlongCoordinates m [] f = f :=
  rfl

@[simp]
theorem bernsteinAlongCoordinates_cons
    (m : ℕ) (i : Fin n) (l : List (Fin n))
    (f : C(UnitCube n, ℝ)) :
    bernsteinAlongCoordinates m (i :: l) f =
      coordinateBernsteinApproximation m i
        (bernsteinAlongCoordinates m l f) :=
  rfl

/-- Quantitative telescoping estimate for a finite list of coordinate
operators.  Repetitions are allowed; no commutativity hypothesis is
needed. -/
theorem abs_bernsteinAlongCoordinates_sub_le
    (m : ℕ) (l : List (Fin n))
    (f : C(UnitCube n, ℝ)) {δ : ℝ}
    (hcoordinate :
      ∀ i ∈ l, ∀ x : UnitCube n,
        |coordinateBernsteinApproximation m i f x -
          f x| ≤ δ)
    (x : UnitCube n) :
    |bernsteinAlongCoordinates m l f x - f x| ≤
      (l.length : ℝ) * δ := by
  induction l generalizing x with
  | nil =>
      simp
  | cons i l ih =>
      let g : C(UnitCube n, ℝ) :=
        bernsteinAlongCoordinates m l f
      have htail :
          ∀ j ∈ l, ∀ y : UnitCube n,
            |coordinateBernsteinApproximation m j f y -
              f y| ≤ δ := by
        intro j hj
        exact hcoordinate j (by simp [hj])
      have hig :
          |coordinateBernsteinApproximation m i g x -
              coordinateBernsteinApproximation m i f x| ≤
            (l.length : ℝ) * δ := by
        apply abs_coordinateBernsteinDifference_le
        intro y
        exact ih htail y
      have hif :
          |coordinateBernsteinApproximation m i f x -
              f x| ≤ δ :=
        hcoordinate i (by simp) x
      have htriangle :
          |coordinateBernsteinApproximation m i g x - f x| ≤
            |coordinateBernsteinApproximation m i g x -
                coordinateBernsteinApproximation m i f x| +
              |coordinateBernsteinApproximation m i f x -
                f x| := by
        calc
          |coordinateBernsteinApproximation m i g x - f x| =
              |(coordinateBernsteinApproximation m i g x -
                  coordinateBernsteinApproximation m i f x) +
                (coordinateBernsteinApproximation m i f x -
                  f x)| := by
            congr 1
            ring
          _ ≤ _ := abs_add_le _ _
      rw [bernsteinAlongCoordinates_cons]
      change
        |coordinateBernsteinApproximation m i g x - f x| ≤
          ((i :: l).length : ℝ) * δ
      norm_num only [List.length_cons, Nat.cast_add,
        Nat.cast_one]
      nlinarith

/-- Apply the same Bernstein degree in every coordinate, in the canonical
order `0, …, n-1`. -/
def iteratedTensorBernsteinApproximation
    (m : ℕ) (f : C(UnitCube n, ℝ)) :
    C(UnitCube n, ℝ) :=
  bernsteinAlongCoordinates m
    (List.ofFn (fun i : Fin n ↦ i)) f

/-- The iterated tensor Bernstein operator converges uniformly to every
continuous function on the unit cube. -/
theorem eventually_iteratedTensorBernsteinApproximation_near
    (f : C(UnitCube n, ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      ∀ x : UnitCube n,
        |iteratedTensorBernsteinApproximation m f x -
          f x| < ε := by
  let δ : ℝ := ε / (n + 1 : ℕ)
  have hdenom : 0 < ((n + 1 : ℕ) : ℝ) := by
    positivity
  have hδ : 0 < δ := by
    exact div_pos hε hdenom
  have hall :
      ∀ᶠ m : ℕ in atTop,
        ∀ i : Fin n, ∀ x : UnitCube n,
          |coordinateBernsteinApproximation m i f x -
            f x| < δ := by
    rw [Filter.eventually_all]
    intro i
    exact eventually_coordinateBernsteinApproximation_near
      i f hδ
  filter_upwards [hall] with m hm
  intro x
  have hcoord :
      ∀ i ∈ List.ofFn (fun i : Fin n ↦ i),
        ∀ y : UnitCube n,
          |coordinateBernsteinApproximation m i f y -
            f y| ≤ δ := by
    intro i hi y
    exact (hm i y).le
  have hbound :=
    abs_bernsteinAlongCoordinates_sub_le m
      (List.ofFn (fun i : Fin n ↦ i)) f
      hcoord x
  have hlength :
      (List.ofFn (fun i : Fin n ↦ i)).length = n := by
    simp
  have hbound' :
      |iteratedTensorBernsteinApproximation m f x -
          f x| ≤ (n : ℝ) * δ := by
    simpa only [iteratedTensorBernsteinApproximation,
      hlength] using hbound
  have hstrict : (n : ℝ) * δ < ε := by
    calc
      (n : ℝ) * δ =
          ((n : ℝ) * ε) /
            ((n + 1 : ℕ) : ℝ) := by
        dsimp only [δ]
        ring
      _ < ε := by
        rw [div_lt_iff₀ hdenom]
        norm_num only [Nat.cast_add, Nat.cast_one]
        nlinarith
  exact hbound'.trans_lt hstrict

end

end HGAS
