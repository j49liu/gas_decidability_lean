import HGAS.Analysis.TensorBernsteinDerivative
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

/-!
# Bernstein averaging in one coordinate of a cube

The tensor Bernstein operator is most transparent when it is built one
coordinate at a time.  This file develops that reusable analytic
operator.  A point of `UnitCube n` is an `n`-tuple of points of `[0,1]`.
For `i : Fin n`, `coordinateBernsteinApproximation m i f` freezes every
coordinate except `i` and applies the ordinary degree-`m` Bernstein
operator in that coordinate.

Two properties are the engine of tensorization:

* the coordinate operator converges uniformly to the identity;
* it is a positive averaging operator, hence it does not increase a
  pointwise uniform error.

The first property is obtained directly from Mathlib's vector-valued
Bernstein theorem by taking the codomain to be the Banach space of
continuous functions on the cube.
-/

namespace HGAS

open Filter ContinuousMap
open scoped BigOperators Topology unitInterval

noncomputable section

variable {n : ℕ}

/-- The closed unit cube, represented as a finite product of copies of
the unit interval. -/
abbrev UnitCube (n : ℕ) :=
  Fin n → Set.Icc (0 : ℝ) 1

/-- Replace coordinate `i` of a cube point by `t`. -/
def replaceCubeCoordinate
    (i : Fin n) (t : Set.Icc (0 : ℝ) 1)
    (x : UnitCube n) : UnitCube n :=
  Function.update x i t

@[simp]
theorem replaceCubeCoordinate_apply_same
    (i : Fin n) (t : Set.Icc (0 : ℝ) 1)
    (x : UnitCube n) :
    replaceCubeCoordinate i t x i = t := by
  simp [replaceCubeCoordinate]

@[simp]
theorem replaceCubeCoordinate_apply_of_ne
    (i j : Fin n) (hji : j ≠ i)
    (t : Set.Icc (0 : ℝ) 1) (x : UnitCube n) :
    replaceCubeCoordinate i t x j = x j := by
  simp [replaceCubeCoordinate, hji]

@[simp]
theorem replaceCubeCoordinate_self
    (i : Fin n) (x : UnitCube n) :
    replaceCubeCoordinate i (x i) x = x := by
  exact Function.update_eq_self i x

/-- Regard a continuous function on the cube as a continuous family of
one-dimensional slices in coordinate `i`.  The value at `t` is itself a
continuous function of the remaining cube point. -/
def coordinateSection
    (i : Fin n) (f : C(UnitCube n, ℝ)) :
    C(Set.Icc (0 : ℝ) 1, C(UnitCube n, ℝ)) :=
  ContinuousMap.curry
    { toFun := fun tx ↦
        f (replaceCubeCoordinate i tx.1 tx.2)
      continuous_toFun := by
        have hx :
            Continuous
              (fun tx :
                Set.Icc (0 : ℝ) 1 × UnitCube n ↦ tx.2) :=
          continuous_snd
        have ht :
            Continuous
              (fun tx :
                Set.Icc (0 : ℝ) 1 × UnitCube n ↦ tx.1) :=
          continuous_fst
        exact f.continuous.comp <| by
          simpa only [replaceCubeCoordinate] using
            (hx.update i ht) }

@[simp]
theorem coordinateSection_apply
    (i : Fin n) (f : C(UnitCube n, ℝ))
    (t : Set.Icc (0 : ℝ) 1) (x : UnitCube n) :
    coordinateSection i f t x =
      f (replaceCubeCoordinate i t x) :=
  rfl

/-- Apply the ordinary degree-`m` Bernstein operator in coordinate `i`,
leaving all other coordinates as parameters. -/
def coordinateBernsteinApproximation
    (m : ℕ) (i : Fin n) (f : C(UnitCube n, ℝ)) :
    C(UnitCube n, ℝ) where
  toFun x :=
    _root_.bernsteinApproximation m (coordinateSection i f) (x i) x
  continuous_toFun := by
    fun_prop

/-- Explicit positive-sum formula for coordinate Bernstein averaging. -/
theorem coordinateBernsteinApproximation_apply
    (m : ℕ) (i : Fin n) (f : C(UnitCube n, ℝ))
    (x : UnitCube n) :
    coordinateBernsteinApproximation m i f x =
      ∑ k : Fin (m + 1),
        _root_.bernstein m k (x i) *
          f (replaceCubeCoordinate i (_root_.bernstein.z k) x) := by
  change
    (_root_.bernsteinApproximation m
      (coordinateSection i f) (x i)) x = _
  rw [_root_.bernsteinApproximation.apply]
  let ev : C(UnitCube n, ℝ) →+ ℝ :=
    { toFun := fun h ↦ h x
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  change ev
      (∑ k : Fin (m + 1),
        _root_.bernstein m k (x i) •
          coordinateSection i f
            (_root_.bernstein.z k)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rfl

/-- A uniform pointwise error is not amplified by Bernstein averaging
in one coordinate. -/
theorem abs_coordinateBernsteinDifference_le
    (m : ℕ) (i : Fin n)
    (f g : C(UnitCube n, ℝ)) (C : ℝ)
    (hfg : ∀ x, |f x - g x| ≤ C)
    (x : UnitCube n) :
    |coordinateBernsteinApproximation m i f x -
        coordinateBernsteinApproximation m i g x| ≤ C := by
  rw [coordinateBernsteinApproximation_apply,
    coordinateBernsteinApproximation_apply]
  let d : Fin (m + 1) → ℝ :=
    fun k ↦ f
      (replaceCubeCoordinate i (_root_.bernstein.z k) x)
  let e : Fin (m + 1) → ℝ :=
    fun k ↦ g
      (replaceCubeCoordinate i (_root_.bernstein.z k) x)
  have hde : ∀ k, |d k - e k| ≤ C := by
    intro k
    exact hfg _
  simpa only [d, e, mul_comm] using
    abs_bernsteinWeightedDifference_le d e C hde (x i)

/-- Bernstein averaging in two distinct coordinates commutes. -/
theorem coordinateBernsteinApproximation_comm
    (m : ℕ) (i j : Fin n) (hij : i ≠ j)
    (f : C(UnitCube n, ℝ)) :
    coordinateBernsteinApproximation m i
        (coordinateBernsteinApproximation m j f) =
      coordinateBernsteinApproximation m j
        (coordinateBernsteinApproximation m i f) := by
  ext x
  rw [coordinateBernsteinApproximation_apply,
    coordinateBernsteinApproximation_apply]
  simp_rw [coordinateBernsteinApproximation_apply]
  have hji : j ≠ i := Ne.symm hij
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro kj hkj
  apply Finset.sum_congr rfl
  intro ki hki
  rw [replaceCubeCoordinate_apply_of_ne i j hji,
    replaceCubeCoordinate_apply_of_ne j i hij]
  have hupdate :
      replaceCubeCoordinate j (_root_.bernstein.z kj)
          (replaceCubeCoordinate i
            (_root_.bernstein.z ki) x) =
        replaceCubeCoordinate i (_root_.bernstein.z ki)
          (replaceCubeCoordinate j
            (_root_.bernstein.z kj) x) := by
    simpa only [replaceCubeCoordinate] using
      Function.update_comm hij
        (_root_.bernstein.z ki)
        (_root_.bernstein.z kj) x
  rw [hupdate]
  ring

/-- Coordinate Bernstein averaging converges uniformly to the identity.

This is a genuinely parameter-uniform statement: the other `n-1`
coordinates range over the whole cube.  It follows by applying the
vector-valued Bernstein theorem to `coordinateSection i f`, whose
codomain is the normed space `C(UnitCube n, ℝ)`. -/
theorem eventually_coordinateBernsteinApproximation_near
    (i : Fin n) (f : C(UnitCube n, ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      ∀ x : UnitCube n,
        |coordinateBernsteinApproximation m i f x - f x| < ε := by
  have hconv :=
    _root_.bernsteinApproximation_uniform
      (coordinateSection i f)
  have hconvUncurried :
      Tendsto
        (fun m : ℕ ↦
          ContinuousMap.uncurry
            (_root_.bernsteinApproximation m
              (coordinateSection i f)))
        atTop
        (𝓝 (ContinuousMap.uncurry
          (coordinateSection i f))) :=
    Continuous.continuousAt
      (ContinuousMap.continuous_uncurry
        (X := Set.Icc (0 : ℝ) 1)
        (Y := UnitCube n) (Z := ℝ)) |>.tendsto.comp hconv
  obtain ⟨N, hN⟩ :=
    Metric.tendsto_atTop.mp hconvUncurried ε hε
  filter_upwards [eventually_ge_atTop N] with m hm
  have hm' := hN m hm
  rw [dist_eq_norm, norm_lt_iff _ hε] at hm'
  intro x
  have hx := hm' (x i, x)
  change
    |_root_.bernsteinApproximation m
          (coordinateSection i f) (x i) x -
        coordinateSection i f (x i) x| < ε at hx
  change
    |coordinateBernsteinApproximation m i f x -
        f x| < ε
  simpa only [coordinateBernsteinApproximation,
    coordinateSection_apply,
    replaceCubeCoordinate_self] using hx

end

end HGAS
