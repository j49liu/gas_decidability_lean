import HGAS.Modular.JacobiAlgebra

/-!
# The Jacobian-rank calculation for the Jacobi residual curve

Fix nonzero complex coefficients `p₂,p₃,p₄` satisfying

```
                         p₃² = p₂² + p₄².
```

The residual curve used by the Jacobi selector is the projective
intersection

```
 Q₁ = p₂ X₄² - p₄ X₂² - p₃ X₁²,
 Q₂ = p₂ X₃² - p₃ X₂² - p₄ X₁².
```

This file formalizes the elementary Jacobian-rank core of the smoothness
argument.  We work on the affine cone `Fin 4 → ℂ`; the condition that the
point is projective is exactly the hypothesis `X ≠ 0`.

The main theorem says that at every nonzero common zero the two
differentials are linearly independent.  The proof follows equation
(8.2) of the manuscript coordinate by coordinate.  If both coefficients
of a putative dependence are nonzero, then `X₃=X₄=0`, and the remaining
two squared coordinates satisfy a two-by-two system whose determinant is

```
                         p₃²-p₄² = p₂² ≠ 0.
```

If exactly one dependence coefficient is nonzero, three coordinates
vanish directly and the remaining quadric kills the fourth.

No algebro-geometric irreducibility, connectedness, adjunction, or genus
calculation is asserted here.
-/

namespace HGAS.Modular

noncomputable section

/-- The first quadric defining the projective Jacobi residual curve.
The indices `0,1,2,3` represent `X₁,X₂,X₃,X₄`. -/
def jacobiResidualQ1
    (p2 p3 p4 : ℂ) (X : Fin 4 → ℂ) : ℂ :=
  p2 * X 3 ^ 2 - p4 * X 1 ^ 2 - p3 * X 0 ^ 2

/-- The second quadric defining the projective Jacobi residual curve.
The indices `0,1,2,3` represent `X₁,X₂,X₃,X₄`. -/
def jacobiResidualQ2
    (p2 p3 p4 : ℂ) (X : Fin 4 → ℂ) : ℂ :=
  p2 * X 2 ^ 2 - p3 * X 1 ^ 2 - p4 * X 0 ^ 2

/-- The four homogeneous coordinates extracted from an affine Jacobi
chart state. -/
def jacobiResidualProjectiveCoordinates
    (z : JacobiState ℂ) : Fin 4 → ℂ :=
  ![z.T1, z.T2, z.T3, z.T4]

/-- `Q₁` is exactly the previously defined affine-chart residual `R₁`
after inserting the four `T` coordinates. -/
@[simp] theorem jacobiResidualQ1_projectiveCoordinates
    (z : JacobiState ℂ) :
    jacobiResidualQ1 z.p2 z.p3 z.p4
        (jacobiResidualProjectiveCoordinates z) =
      JacobiState.residualR1 z := by
  simp [jacobiResidualQ1, jacobiResidualProjectiveCoordinates,
    JacobiState.residualR1]

/-- `Q₂` is exactly the previously defined affine-chart residual `R₂`
after inserting the four `T` coordinates. -/
@[simp] theorem jacobiResidualQ2_projectiveCoordinates
    (z : JacobiState ℂ) :
    jacobiResidualQ2 z.p2 z.p3 z.p4
        (jacobiResidualProjectiveCoordinates z) =
      JacobiState.residualR2 z := by
  simp [jacobiResidualQ2, jacobiResidualProjectiveCoordinates,
    JacobiState.residualR2]

/-- The differential of `jacobiResidualQ1` at `X`, bundled as a complex
linear functional on the affine cone. -/
def jacobiResidualQ1Differential
    (p2 p3 p4 : ℂ) (X : Fin 4 → ℂ) :
    (Fin 4 → ℂ) →ₗ[ℂ] ℂ where
  toFun V :=
    2 * p2 * X 3 * V 3 -
      2 * p4 * X 1 * V 1 -
        2 * p3 * X 0 * V 0
  map_add' V W := by
    simp only [Pi.add_apply]
    ring
  map_smul' c V := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The differential of `jacobiResidualQ2` at `X`, bundled as a complex
linear functional on the affine cone. -/
def jacobiResidualQ2Differential
    (p2 p3 p4 : ℂ) (X : Fin 4 → ℂ) :
    (Fin 4 → ℂ) →ₗ[ℂ] ℂ where
  toFun V :=
    2 * p2 * X 2 * V 2 -
      2 * p3 * X 1 * V 1 -
        2 * p4 * X 0 * V 0
  map_add' V W := by
    simp only [Pi.add_apply]
    ring
  map_smul' c V := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Evaluating `dQ₁` in an arbitrary direction gives the displayed
coordinate formula. -/
@[simp] theorem jacobiResidualQ1Differential_apply
    (p2 p3 p4 : ℂ) (X V : Fin 4 → ℂ) :
    jacobiResidualQ1Differential p2 p3 p4 X V =
      2 * p2 * X 3 * V 3 -
        2 * p4 * X 1 * V 1 -
          2 * p3 * X 0 * V 0 := rfl

/-- Evaluating `dQ₂` in an arbitrary direction gives the displayed
coordinate formula. -/
@[simp] theorem jacobiResidualQ2Differential_apply
    (p2 p3 p4 : ℂ) (X V : Fin 4 → ℂ) :
    jacobiResidualQ2Differential p2 p3 p4 X V =
      2 * p2 * X 2 * V 2 -
        2 * p3 * X 1 * V 1 -
          2 * p4 * X 0 * V 0 := rfl

/-- Quadratic expansion for `Q₁`.  In particular, the bundled functional
above is its first-order differential. -/
theorem jacobiResidualQ1_add
    (p2 p3 p4 : ℂ) (X V : Fin 4 → ℂ) :
    jacobiResidualQ1 p2 p3 p4 (X + V) =
      jacobiResidualQ1 p2 p3 p4 X +
        jacobiResidualQ1Differential p2 p3 p4 X V +
          jacobiResidualQ1 p2 p3 p4 V := by
  simp only [jacobiResidualQ1,
    jacobiResidualQ1Differential_apply, Pi.add_apply]
  ring

/-- Quadratic expansion for `Q₂`. -/
theorem jacobiResidualQ2_add
    (p2 p3 p4 : ℂ) (X V : Fin 4 → ℂ) :
    jacobiResidualQ2 p2 p3 p4 (X + V) =
      jacobiResidualQ2 p2 p3 p4 X +
        jacobiResidualQ2Differential p2 p3 p4 X V +
          jacobiResidualQ2 p2 p3 p4 V := by
  simp only [jacobiResidualQ2,
    jacobiResidualQ2Differential_apply, Pi.add_apply]
  ring

/-- **Jacobian rank on the nonzero residual cone.**

At a nonzero common zero of `Q₁,Q₂`, the two complex differentials are
linearly independent.  This is the complete explicit case split in
equation (8.2) of the manuscript. -/
theorem jacobiResidual_differentials_independent
    {p2 p3 p4 : ℂ}
    (hp : p2 * p3 * p4 ≠ 0)
    (hJacobi : p3 ^ 2 = p2 ^ 2 + p4 ^ 2)
    {X : Fin 4 → ℂ}
    (hX : X ≠ 0)
    (hQ1 : jacobiResidualQ1 p2 p3 p4 X = 0)
    (hQ2 : jacobiResidualQ2 p2 p3 p4 X = 0)
    {q s : ℂ}
    (hdependence :
      q • jacobiResidualQ1Differential p2 p3 p4 X +
          s • jacobiResidualQ2Differential p2 p3 p4 X =
        0) :
    q = 0 ∧ s = 0 := by
  have hp2 : p2 ≠ 0 := by
    intro hp2
    apply hp
    simp only [hp2, zero_mul]
  have hp3 : p3 ≠ 0 := by
    intro hp3
    apply hp
    simp only [hp3, mul_zero, zero_mul]
  have hp4 : p4 ≠ 0 := by
    intro hp4
    apply hp
    simp only [hp4, mul_zero]
  have hdet : p3 ^ 2 - p4 ^ 2 = p2 ^ 2 := by
    rw [hJacobi]
    ring
  have hcoord0raw :
      q * -(2 * p3 * X 0) +
          s * -(2 * p4 * X 0) = 0 := by
    have hraw :=
      DFunLike.congr_fun hdependence
        (![1, 0, 0, 0] : Fin 4 → ℂ)
    simpa only [LinearMap.add_apply, LinearMap.smul_apply,
      jacobiResidualQ1Differential_apply,
      jacobiResidualQ2Differential_apply, Matrix.cons_val,
      smul_eq_mul, LinearMap.zero_apply, mul_zero, mul_one,
      sub_zero, zero_sub, zero_mul, add_zero] using hraw
  have hcoord1raw :
      q * -(2 * p4 * X 1) +
          s * -(2 * p3 * X 1) = 0 := by
    have hraw :=
      DFunLike.congr_fun hdependence
        (![0, 1, 0, 0] : Fin 4 → ℂ)
    simpa only [LinearMap.add_apply, LinearMap.smul_apply,
      jacobiResidualQ1Differential_apply,
      jacobiResidualQ2Differential_apply, Matrix.cons_val,
      smul_eq_mul, LinearMap.zero_apply, mul_zero, mul_one,
      sub_zero, zero_sub, zero_mul, add_zero] using hraw
  have hcoord2raw :
      0 + s * (2 * p2 * X 2) = 0 := by
    have hraw :=
      DFunLike.congr_fun hdependence
        (![0, 0, 1, 0] : Fin 4 → ℂ)
    simpa only [LinearMap.add_apply, LinearMap.smul_apply,
      jacobiResidualQ1Differential_apply,
      jacobiResidualQ2Differential_apply, Matrix.cons_val,
      smul_eq_mul, LinearMap.zero_apply, mul_zero, mul_one,
      sub_zero, zero_sub, zero_mul, add_zero] using hraw
  have hcoord3raw :
      q * (2 * p2 * X 3) = 0 := by
    have hraw :=
      DFunLike.congr_fun hdependence
        (![0, 0, 0, 1] : Fin 4 → ℂ)
    simpa only [LinearMap.add_apply, LinearMap.smul_apply,
      jacobiResidualQ1Differential_apply,
      jacobiResidualQ2Differential_apply, Matrix.cons_val,
      smul_eq_mul, LinearMap.zero_apply, mul_zero, mul_one,
      sub_zero, zero_sub, zero_mul, add_zero] using hraw
  have hcoord0 :
      X 0 * (q * p3 + s * p4) = 0 := by
    linear_combination (-1 / 2 : ℂ) * hcoord0raw
  have hcoord1 :
      X 1 * (q * p4 + s * p3) = 0 := by
    linear_combination (-1 / 2 : ℂ) * hcoord1raw
  have hcoord2 : s * X 2 = 0 := by
    have hp2two : (2 : ℂ) * p2 ≠ 0 :=
      mul_ne_zero (by norm_num) hp2
    have hfactored : (2 * p2) * (s * X 2) = 0 := by
      linear_combination hcoord2raw
    exact (mul_eq_zero.mp hfactored).resolve_left hp2two
  have hcoord3 : q * X 3 = 0 := by
    have hp2two : (2 : ℂ) * p2 ≠ 0 :=
      mul_ne_zero (by norm_num) hp2
    have hfactored : (2 * p2) * (q * X 3) = 0 := by
      linear_combination hcoord3raw
    exact (mul_eq_zero.mp hfactored).resolve_left hp2two
  by_cases hq : q = 0
  · refine ⟨hq, ?_⟩
    by_contra hs
    have hX0 : X 0 = 0 := by
      have : X 0 * (s * p4) = 0 := by
        simpa only [hq, zero_mul, zero_add] using hcoord0
      exact (mul_eq_zero.mp this).resolve_right
        (mul_ne_zero hs hp4)
    have hX1 : X 1 = 0 := by
      have : X 1 * (s * p3) = 0 := by
        simpa only [hq, zero_mul, zero_add] using hcoord1
      exact (mul_eq_zero.mp this).resolve_right
        (mul_ne_zero hs hp3)
    have hX2 : X 2 = 0 :=
      (mul_eq_zero.mp hcoord2).resolve_left hs
    have hX3 : X 3 = 0 := by
      simp [jacobiResidualQ1, hX0, hX1] at hQ1
      exact hQ1.resolve_left hp2
    apply hX
    funext i
    fin_cases i
    · exact hX0
    · exact hX1
    · exact hX2
    · exact hX3
  · by_cases hs : s = 0
    · have hX0 : X 0 = 0 := by
        have : X 0 * (q * p3) = 0 := by
          simpa only [hs, zero_mul, add_zero] using hcoord0
        exact (mul_eq_zero.mp this).resolve_right
          (mul_ne_zero hq hp3)
      have hX1 : X 1 = 0 := by
        have : X 1 * (q * p4) = 0 := by
          simpa only [hs, zero_mul, add_zero] using hcoord1
        exact (mul_eq_zero.mp this).resolve_right
          (mul_ne_zero hq hp4)
      have hX3 : X 3 = 0 :=
        (mul_eq_zero.mp hcoord3).resolve_left hq
      have hX2 : X 2 = 0 := by
        simp [jacobiResidualQ2, hX0, hX1] at hQ2
        exact hQ2.resolve_left hp2
      exfalso
      apply hX
      funext i
      fin_cases i
      · exact hX0
      · exact hX1
      · exact hX2
      · exact hX3
    · have hX2 : X 2 = 0 :=
        (mul_eq_zero.mp hcoord2).resolve_left hs
      have hX3 : X 3 = 0 :=
        (mul_eq_zero.mp hcoord3).resolve_left hq
      have hsystem1 :
          p3 * X 0 ^ 2 + p4 * X 1 ^ 2 = 0 := by
        simp [jacobiResidualQ1, hX3] at hQ1
        linear_combination -hQ1
      have hsystem2 :
          p4 * X 0 ^ 2 + p3 * X 1 ^ 2 = 0 := by
        simp [jacobiResidualQ2, hX2] at hQ2
        linear_combination -hQ2
      have hX0sq : X 0 ^ 2 = 0 := by
        have hp2sq : p2 ^ 2 ≠ 0 :=
          pow_ne_zero 2 hp2
        apply (mul_left_cancel₀ hp2sq)
        rw [← hdet]
        linear_combination
          p3 * hsystem1 - p4 * hsystem2
      have hX1sq : X 1 ^ 2 = 0 := by
        have hp2sq : p2 ^ 2 ≠ 0 :=
          pow_ne_zero 2 hp2
        apply (mul_left_cancel₀ hp2sq)
        rw [← hdet]
        linear_combination
          p3 * hsystem2 - p4 * hsystem1
      have hX0 : X 0 = 0 := sq_eq_zero_iff.mp hX0sq
      have hX1 : X 1 = 0 := sq_eq_zero_iff.mp hX1sq
      exfalso
      apply hX
      funext i
      fin_cases i
      · exact hX0
      · exact hX1
      · exact hX2
      · exact hX3

end

end HGAS.Modular
