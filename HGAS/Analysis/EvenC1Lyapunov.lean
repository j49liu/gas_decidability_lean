import HGAS.Dynamics.AngularGAS
import Mathlib.Tactic

/-!
# Evenization of a homogeneous `C¹` Lyapunov function

For an odd vector field, a strict homogeneous Lyapunov function can be
replaced by its antipodal average

```
Vₑ(x) = (V(x) + V(-x)) / 2.
```

Both summands are positive away from the origin.  The chain rule gives

```
DVₑ(x)[v] = (DV(x)[v] - DV(-x)[v]) / 2.
```

When `F(-x) = -F(x)`, the two terms in the Lie derivative are precisely
the strict Lie derivatives of `V` at `x` and at `-x`.  Thus the average is
again a strict Lyapunov function.  This elementary reduction is what makes
the later even-total-degree polynomial symmetrization legitimate.
-/

namespace HGAS

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Antipodal average of a real-valued function. -/
def evenizeFunction (V : E → ℝ) (x : E) : ℝ :=
  (V x + V (-x)) / 2

omit [NormedSpace ℝ E] in
/-- The antipodal average is even, with no regularity assumptions. -/
@[simp]
theorem evenizeFunction_neg (V : E → ℝ) (x : E) :
    evenizeFunction V (-x) = evenizeFunction V x := by
  simp only [evenizeFunction, neg_neg]
  ring

/-- Exact differential of the antipodal average. -/
theorem fderiv_evenizeFunction_apply
    {V : E → ℝ} (hV : Differentiable ℝ V) (x v : E) :
    fderiv ℝ (evenizeFunction V) x v =
      (fderiv ℝ V x v - fderiv ℝ V (-x) v) / 2 := by
  have hneg :
      HasFDerivAt (fun y : E ↦ -y)
        (-(ContinuousLinearMap.id ℝ E)) x := by
    simpa only [id_eq] using
      (hasFDerivAt_id (𝕜 := ℝ) x).neg
  have hVx : HasFDerivAt V (fderiv ℝ V x) x :=
    (hV x).hasFDerivAt
  have hVneg :
      HasFDerivAt (fun y : E ↦ V (-y))
        ((fderiv ℝ V (-x)).comp
          (-(ContinuousLinearMap.id ℝ E))) x := by
    simpa only [Function.comp_apply] using
      ((hV (-x)).hasFDerivAt.comp x hneg)
  have havg :
      HasFDerivAt (evenizeFunction V)
        ((2 : ℝ)⁻¹ •
          (fderiv ℝ V x +
            (fderiv ℝ V (-x)).comp
              (-(ContinuousLinearMap.id ℝ E)))) x := by
    have hraw :=
      (hVx.add hVneg).const_smul ((2 : ℝ)⁻¹)
    convert hraw using 1
    funext y
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul,
      evenizeFunction]
    ring
  rw [havg.fderiv]
  simp only [ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply,
    map_neg, smul_eq_mul]
  ring

/-- The derivative of a differentiable even function is odd in its base
point.  We record the statement for the canonical antipodal average. -/
theorem fderiv_evenizeFunction_neg_apply
    {V : E → ℝ} (hV : Differentiable ℝ V) (x v : E) :
    fderiv ℝ (evenizeFunction V) (-x) v =
      -fderiv ℝ (evenizeFunction V) x v := by
  rw [fderiv_evenizeFunction_apply hV,
    fderiv_evenizeFunction_apply hV]
  simp only [neg_neg]
  ring

/-- The derivative of any differentiable even function is odd in its base
point. -/
theorem fderiv_neg_of_even
    {V : E → ℝ} (hV : Differentiable ℝ V)
    (heven : ∀ x : E, V (-x) = V x) (x : E) :
    fderiv ℝ V (-x) = -fderiv ℝ V x := by
  have hfun : evenizeFunction V = V := by
    funext y
    simp only [evenizeFunction, heven]
    ring
  ext v
  have hodd :=
    fderiv_evenizeFunction_neg_apply hV x v
  simpa only [hfun, ContinuousLinearMap.neg_apply] using hodd

namespace StrictHomogeneousC1Lyapunov

variable {F : E → E} {degree : ℕ}

/-- For an odd vector field, antipodal averaging preserves every field of
the strict homogeneous `C¹` Lyapunov structure. -/
def evenized
    (L : StrictHomogeneousC1Lyapunov F degree)
    (hFodd : ∀ x : E, F (-x) = -F x) :
    StrictHomogeneousC1Lyapunov F degree where
  V := evenizeFunction L.V
  contDiff := by
    exact
      (L.contDiff.add (L.contDiff.comp contDiff_neg)).div_const 2
  degree_pos := L.degree_pos
  homogeneous := by
    intro s hs x
    simp only [evenizeFunction]
    rw [L.homogeneous s hs x]
    have hnegsmul : -(s • x) = s • (-x) := by
      simp
    rw [hnegsmul, L.homogeneous s hs (-x)]
    ring
  positive := by
    intro x hx
    have hxpos := L.positive x hx
    have hnegpos := L.positive (-x) (neg_ne_zero.mpr hx)
    simp only [evenizeFunction]
    linarith
  decreases := by
    intro x hx
    have hxdec := L.decreases x hx
    have hnegdec := L.decreases (-x) (neg_ne_zero.mpr hx)
    rw [hFodd x, map_neg] at hnegdec
    rw [fderiv_evenizeFunction_apply
      (L.contDiff.differentiable (by norm_num))]
    linarith

/-- The Lyapunov function produced by `evenized` is definitionally the
antipodal average. -/
@[simp]
theorem evenized_V
    (L : StrictHomogeneousC1Lyapunov F degree)
    (hFodd : ∀ x : E, F (-x) = -F x) (x : E) :
    (L.evenized hFodd).V x = evenizeFunction L.V x :=
  rfl

/-- In particular, the produced Lyapunov function is even. -/
theorem evenized_V_neg
    (L : StrictHomogeneousC1Lyapunov F degree)
    (hFodd : ∀ x : E, F (-x) = -F x) (x : E) :
    (L.evenized hFodd).V (-x) = (L.evenized hFodd).V x :=
  evenizeFunction_neg L.V x

end StrictHomogeneousC1Lyapunov

end

end HGAS
