import HGAS.Analysis.ClosedUnitCubeC1PolynomialApproximation
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Tactic

/-!
# `C¹` polynomial approximation on the centered cube

The tensor Bernstein construction is naturally stated on `[0,1]^n`.
This file transports it across the affine equivalence

`u = (x+1)/2`,  `x = 2u-1`

to obtain the form needed near the Euclidean unit sphere.  The transport
is performed inside `MvPolynomial`: `centeredPolynomialPullback`
substitutes `(X_i+1)/2` for every variable.  We prove both its evaluation
formula and the corresponding partial-derivative chain rule.
-/

namespace HGAS

open Filter Set
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- The centered closed cube `[-1,1]^n`. -/
def closedCenteredUnitCubeSet (n : ℕ) :
    Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ ↦ Set.Icc (-1 : ℝ) 1)

@[simp]
theorem mem_closedCenteredUnitCubeSet
    (x : Fin n → ℝ) :
    x ∈ closedCenteredUnitCubeSet n ↔
      ∀ i, -1 ≤ x i ∧ x i ≤ 1 := by
  simp only [closedCenteredUnitCubeSet, Set.mem_pi,
    Set.mem_univ, Set.mem_Icc, forall_const]

/-- Affine map from the centered cube to `[0,1]^n`. -/
def centeredToUnit (x : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i ↦ (x i + 1) / 2

/-- Affine map from `[0,1]^n` to the centered cube. -/
def unitToCentered (u : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i ↦ 2 * u i - 1

@[simp]
theorem centeredToUnit_unitToCentered
    (u : Fin n → ℝ) :
    centeredToUnit (unitToCentered u) = u := by
  funext i
  simp only [centeredToUnit, unitToCentered]
  ring

@[simp]
theorem unitToCentered_centeredToUnit
    (x : Fin n → ℝ) :
    unitToCentered (centeredToUnit x) = x := by
  funext i
  simp only [centeredToUnit, unitToCentered]
  ring

theorem continuous_centeredToUnit :
    Continuous (centeredToUnit :
      (Fin n → ℝ) → (Fin n → ℝ)) := by
  apply continuous_pi
  intro i
  change Continuous (fun x : Fin n → ℝ ↦
    (x i + 1) / 2)
  fun_prop

theorem continuous_unitToCentered :
    Continuous (unitToCentered :
      (Fin n → ℝ) → (Fin n → ℝ)) := by
  apply continuous_pi
  intro i
  change Continuous (fun u : Fin n → ℝ ↦
    2 * u i - 1)
  fun_prop

theorem centeredToUnit_mem_closedUnitCubeSet
    {x : Fin n → ℝ}
    (hx : x ∈ closedCenteredUnitCubeSet n) :
    centeredToUnit x ∈ closedUnitCubeSet n := by
  rw [mem_closedUnitCubeSet]
  intro i
  have hi :=
    (mem_closedCenteredUnitCubeSet x).mp hx i
  simp only [centeredToUnit]
  constructor <;> linarith

theorem unitToCentered_mem_closedCenteredUnitCubeSet
    {u : Fin n → ℝ}
    (hu : u ∈ closedUnitCubeSet n) :
    unitToCentered u ∈
      closedCenteredUnitCubeSet n := by
  rw [mem_closedCenteredUnitCubeSet]
  intro i
  have hi := (mem_closedUnitCubeSet u).mp hu i
  simp only [unitToCentered]
  constructor <;> linarith

/-- `unitToCentered` commutes with replacement of one coordinate. -/
theorem unitToCentered_update
    (u : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    unitToCentered (Function.update u i t) =
      Function.update (unitToCentered u) i
        (2 * t - 1) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [unitToCentered]
  · simp [unitToCentered, hji]

/-- The affine polynomial substituted for each variable. -/
def centeredAffineVariable (i : Fin n) :
    MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C (1 / 2 : ℝ) *
      MvPolynomial.X i +
    MvPolynomial.C (1 / 2 : ℝ)

/-- Pull a polynomial on `[0,1]^n` back to `[-1,1]^n` by substituting
`(X_i+1)/2` for every variable. -/
def centeredPolynomialPullback
    (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  MvPolynomial.bind₁ centeredAffineVariable p

@[simp]
theorem centeredPolynomialPullback_zero :
    centeredPolynomialPullback
        (0 : MvPolynomial (Fin n) ℝ) = 0 := by
  exact map_zero _

@[simp]
theorem centeredPolynomialPullback_one :
    centeredPolynomialPullback
        (1 : MvPolynomial (Fin n) ℝ) = 1 := by
  exact map_one _

@[simp]
theorem centeredPolynomialPullback_C (a : ℝ) :
    centeredPolynomialPullback
        (MvPolynomial.C a :
          MvPolynomial (Fin n) ℝ) =
      MvPolynomial.C a := by
  exact MvPolynomial.bind₁_C_right _ _

@[simp]
theorem centeredPolynomialPullback_X (i : Fin n) :
    centeredPolynomialPullback
        (MvPolynomial.X i :
          MvPolynomial (Fin n) ℝ) =
      centeredAffineVariable i := by
  exact MvPolynomial.bind₁_X_right _ _

@[simp]
theorem centeredPolynomialPullback_add
    (p q : MvPolynomial (Fin n) ℝ) :
    centeredPolynomialPullback (p + q) =
      centeredPolynomialPullback p +
        centeredPolynomialPullback q := by
  exact map_add _ _ _

@[simp]
theorem centeredPolynomialPullback_mul
    (p q : MvPolynomial (Fin n) ℝ) :
    centeredPolynomialPullback (p * q) =
      centeredPolynomialPullback p *
        centeredPolynomialPullback q := by
  exact map_mul _ _ _

/-- Evaluation of the polynomial pullback agrees with affine
precomposition. -/
theorem eval_centeredPolynomialPullback
    (p : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) :
    MvPolynomial.eval x
        (centeredPolynomialPullback p) =
      MvPolynomial.eval (centeredToUnit x) p := by
  rw [centeredPolynomialPullback]
  change
    MvPolynomial.eval₂Hom (RingHom.id ℝ) x
        (MvPolynomial.bind₁ centeredAffineVariable p) =
      MvPolynomial.eval₂Hom (RingHom.id ℝ)
        (centeredToUnit x) p
  rw [MvPolynomial.eval₂Hom_bind₁]
  apply MvPolynomial.eval₂Hom_congr rfl ?_ rfl
  funext i
  simp only [centeredAffineVariable,
    MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X',
    map_add, map_mul, RingHom.id_apply,
    centeredToUnit]
  ring

/-- The substituted affine variable has derivative `1/2` in its own
coordinate and zero in every other coordinate. -/
theorem pderiv_centeredAffineVariable
    (i j : Fin n) :
    MvPolynomial.pderiv i
        (centeredAffineVariable j) =
      if i = j then
        MvPolynomial.C (1 / 2 : ℝ)
      else 0 := by
  by_cases hij : i = j
  · subst j
    simp [centeredAffineVariable]
  · simp [centeredAffineVariable, hij,
      Ne.symm hij]

/-- Partial derivatives of the affine pullback obey the diagonal chain
rule: each derivative acquires the factor `1/2`. -/
theorem pderiv_centeredPolynomialPullback
    (i : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.pderiv i
        (centeredPolynomialPullback p) =
      MvPolynomial.C (1 / 2 : ℝ) *
        centeredPolynomialPullback
          (MvPolynomial.pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp only [centeredPolynomialPullback_C,
        MvPolynomial.pderiv_C,
        centeredPolynomialPullback_zero, mul_zero]
  | add p q hp hq =>
      simp only [centeredPolynomialPullback_add,
        map_add, hp, hq, mul_add]
  | mul_X p j hp =>
      simp only [centeredPolynomialPullback_mul,
        centeredPolynomialPullback_X,
        MvPolynomial.pderiv_mul,
        hp, pderiv_centeredAffineVariable,
        centeredPolynomialPullback_add,
        MvPolynomial.pderiv_X,
        Pi.single_apply,
        centeredPolynomialPullback_mul]
      by_cases hji : i = j
      · subst j
        simp only [↓reduceIte,
          centeredPolynomialPullback_one,
          mul_one]
        ring
      · have hjine : j ≠ i :=
          Ne.symm hji
        simp only [if_neg hji, if_neg hjine,
          mul_zero, add_zero,
          centeredPolynomialPullback_zero]
        ring

/-- Evaluation form of the partial-derivative chain rule. -/
theorem eval_pderiv_centeredPolynomialPullback
    (i : Fin n) (p : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) :
    MvPolynomial.eval x
        (MvPolynomial.pderiv i
          (centeredPolynomialPullback p)) =
      (1 / 2 : ℝ) *
        MvPolynomial.eval (centeredToUnit x)
          (MvPolynomial.pderiv i p) := by
  rw [pderiv_centeredPolynomialPullback,
    MvPolynomial.eval_mul,
    MvPolynomial.eval_C,
    eval_centeredPolynomialPullback]

/-- Transport of the unit-cube approximation theorem to the centered
cube.  The transformed derivative is
`2 * D (2u-1)`, and the polynomial pullback contributes the reciprocal
factor `1/2`. -/
theorem hasC1MvPolynomialApproximationOn_closedCenteredUnitCube
    (f : (Fin n → ℝ) → ℝ)
    (D : (Fin n → ℝ) → Fin n → ℝ)
    (hf :
      ContinuousOn f
        (closedCenteredUnitCubeSet n))
    (hD :
      ∀ i,
        ContinuousOn (fun x ↦ D x i)
          (closedCenteredUnitCubeSet n))
    (hderiv :
      ∀ x ∈ closedCenteredUnitCubeSet n, ∀ i,
        HasDerivAt
          (fun t : ℝ ↦
            f (Function.update x i t))
          (D x i) (x i)) :
    HasC1MvPolynomialApproximationOn
      (closedCenteredUnitCubeSet n) f D := by
  let g : (Fin n → ℝ) → ℝ :=
    fun u ↦ f (unitToCentered u)
  let G : (Fin n → ℝ) → Fin n → ℝ :=
    fun u i ↦ 2 * D (unitToCentered u) i
  have hmap :
      MapsTo unitToCentered
        (closedUnitCubeSet n)
        (closedCenteredUnitCubeSet n) :=
    fun _ hu ↦
      unitToCentered_mem_closedCenteredUnitCubeSet hu
  have hg :
      ContinuousOn g (closedUnitCubeSet n) := by
    exact hf.comp
      continuous_unitToCentered.continuousOn hmap
  have hG :
      ∀ i,
        ContinuousOn (fun u ↦ G u i)
          (closedUnitCubeSet n) := by
    intro i
    exact continuousOn_const.mul <|
      (hD i).comp
        continuous_unitToCentered.continuousOn hmap
  have hGderiv :
      ∀ u ∈ closedUnitCubeSet n, ∀ i,
        HasDerivAt
          (fun t : ℝ ↦
            g (Function.update u i t))
          (G u i) (u i) := by
    intro u hu i
    have hd :=
      hderiv (unitToCentered u) (hmap hu) i
    have haffine :
        HasDerivAt (fun t : ℝ ↦ 2 * t - 1)
          2 (u i) := by
      have hmul :=
        (hasDerivAt_id (𝕜 := ℝ) (u i)).const_mul 2
      simpa only [id_eq, one_mul, mul_comm] using
        hmul.sub_const 1
    have hcomp := hd.comp (u i) haffine
    have hfun :
        (fun t : ℝ ↦
          g (Function.update u i t)) =
        (fun t : ℝ ↦
          f (Function.update (unitToCentered u) i
            (2 * t - 1))) := by
      funext t
      change
        f (unitToCentered
          (Function.update u i t)) =
        f (Function.update (unitToCentered u) i
          (2 * t - 1))
      rw [unitToCentered_update]
    rw [hfun]
    convert hcomp using 1
    · ring
  have hunit :
      HasC1MvPolynomialApproximationOn
        (closedUnitCubeSet n) g G :=
    hasC1MvPolynomialApproximationOn_closedUnitCube
      g G hg hG hGderiv
  intro ε hε
  obtain ⟨q, hqValue, hqDerivative⟩ :=
    hunit hε
  refine
    ⟨centeredPolynomialPullback q, ?_, ?_⟩
  · intro x hx
    have hu :=
      centeredToUnit_mem_closedUnitCubeSet hx
    have hq := hqValue (centeredToUnit x) hu
    rw [eval_centeredPolynomialPullback]
    simpa only [g,
      unitToCentered_centeredToUnit] using hq
  · intro x hx i
    have hu :=
      centeredToUnit_mem_closedUnitCubeSet hx
    have hq := hqDerivative
      (centeredToUnit x) hu i
    have hq' :
        |MvPolynomial.eval (centeredToUnit x)
              (MvPolynomial.pderiv i q) -
            2 * D x i| < ε := by
      simpa only [G,
        unitToCentered_centeredToUnit] using hq
    rw [eval_pderiv_centeredPolynomialPullback]
    calc
      |(1 / 2 : ℝ) *
            MvPolynomial.eval (centeredToUnit x)
              (MvPolynomial.pderiv i q) -
          D x i| =
          (1 / 2 : ℝ) *
            |MvPolynomial.eval (centeredToUnit x)
                (MvPolynomial.pderiv i q) -
              2 * D x i| := by
        rw [← abs_of_nonneg
          (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ← abs_mul]
        congr 1
        ring
      _ < (1 / 2 : ℝ) * ε :=
        mul_lt_mul_of_pos_left hq' (by norm_num)
      _ < ε := by
        linarith

end

end HGAS
