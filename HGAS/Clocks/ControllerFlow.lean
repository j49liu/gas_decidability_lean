import HGAS.Clocks.Controller
import HGAS.Dynamics.WanderingSupport
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# The polynomial controller flow and its invariant probabilities

For `p > 1`, the controller equation on the unit circle is

```
  r' = -s (p r² - 1),        s' = r (p r² - 1).
```

There is a particularly useful explicit realization.  Start with the
linear hyperbolic system

```
  u' = v,                    v' = (p - 1) u
```

and normalize every nonzero solution radially to the unit circle.  Its
tangential velocity is exactly the polynomial controller field above.
If `a = √(p-1)`, the two eigen-coordinates

```
  v + a u,                   v - a u
```

are multiplied by `exp(a t)` and `exp(-a t)`.  Away from the two
eigendirections (four oriented points on the circle), their logarithmic
absolute-value ratio therefore advances at the constant speed `2a`.

This makes the invariant-measure classification elementary and reusable:
partition the complement of the equilibria into unit-width strips of that
log-ratio.  Every strip is wandering under the time step `1/(2a)`, so an
invariant probability gives it mass zero.  Countably many strips cover the
complement.
-/

noncomputable section

open Complex Function MeasureTheory Metric Set
open scoped ENNReal

namespace HGAS.Clocks.ControllerFlow

local instance : MeasurableSpace Circle :=
  borel Circle

local instance : BorelSpace Circle :=
  ⟨rfl⟩

/-- The positive hyperbolic exponent of a controller with parameter
`p > 1`. -/
def controllerExponent (p : ℝ) : ℝ :=
  Real.sqrt (p - 1)

theorem controllerExponent_pos {p : ℝ} (hp : 1 < p) :
    0 < controllerExponent p := by
  exact Real.sqrt_pos.2 (sub_pos.mpr hp)

theorem controllerExponent_ne_zero {p : ℝ} (hp : 1 < p) :
    controllerExponent p ≠ 0 :=
  (controllerExponent_pos hp).ne'

theorem controllerExponent_sq {p : ℝ} (hp : 1 < p) :
    controllerExponent p ^ 2 = p - 1 := by
  exact Real.sq_sqrt (sub_nonneg.mpr hp.le)

/-- Expanding eigen-coordinate `s + a r`. -/
def expandingCoordinate (a : ℝ) (z : ℂ) : ℝ :=
  z.im + a * z.re

/-- Contracting eigen-coordinate `s - a r`. -/
def contractingCoordinate (a : ℝ) (z : ℂ) : ℝ :=
  z.im - a * z.re

/-- Recover the first coordinate from the two eigen-coordinates. -/
theorem re_eq_sub_eigen_div
    {a : ℝ} (ha : a ≠ 0) (z : ℂ) :
    z.re =
      (expandingCoordinate a z - contractingCoordinate a z) /
        (2 * a) := by
  simp only [expandingCoordinate, contractingCoordinate]
  field_simp
  ring

/-- Recover the second coordinate from the two eigen-coordinates. -/
theorem im_eq_add_eigen_div (a : ℝ) (z : ℂ) :
    z.im =
      (expandingCoordinate a z + contractingCoordinate a z) / 2 := by
  simp only [expandingCoordinate, contractingCoordinate]
  ring

/-- Equality of both eigen-coordinates determines the complex vector. -/
theorem eq_of_eigenCoordinates_eq
    {a : ℝ} (ha : a ≠ 0) {z w : ℂ}
    (hplus :
      expandingCoordinate a z = expandingCoordinate a w)
    (hminus :
      contractingCoordinate a z = contractingCoordinate a w) :
    z = w := by
  apply Complex.ext
  · rw [re_eq_sub_eigen_div ha z,
      re_eq_sub_eigen_div ha w, hplus, hminus]
  · rw [im_eq_add_eigen_div a z,
      im_eq_add_eigen_div a w, hplus, hminus]

/-- The unnormalized hyperbolic linear action, written in eigen-coordinates. -/
def controllerLinear (a t : ℝ) (z : ℂ) : ℂ :=
  Complex.ofReal
    ((Real.exp (a * t) * expandingCoordinate a z -
      Real.exp (-a * t) * contractingCoordinate a z) /
        (2 * a)) +
    Complex.ofReal
      ((Real.exp (a * t) * expandingCoordinate a z +
        Real.exp (-a * t) * contractingCoordinate a z) / 2) *
      Complex.I

@[simp]
theorem controllerLinear_re (a t : ℝ) (z : ℂ) :
    (controllerLinear a t z).re =
      (Real.exp (a * t) * expandingCoordinate a z -
        Real.exp (-a * t) * contractingCoordinate a z) /
          (2 * a) := by
  simp only [controllerLinear, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

@[simp]
theorem controllerLinear_im (a t : ℝ) (z : ℂ) :
    (controllerLinear a t z).im =
      (Real.exp (a * t) * expandingCoordinate a z +
        Real.exp (-a * t) * contractingCoordinate a z) / 2 := by
  simp only [controllerLinear, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_add, add_zero]

@[simp]
theorem expandingCoordinate_controllerLinear
    {a : ℝ} (ha : a ≠ 0) (t : ℝ) (z : ℂ) :
    expandingCoordinate a (controllerLinear a t z) =
      Real.exp (a * t) * expandingCoordinate a z := by
  simp only [expandingCoordinate, controllerLinear, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
  field_simp
  ring

@[simp]
theorem contractingCoordinate_controllerLinear
    {a : ℝ} (ha : a ≠ 0) (t : ℝ) (z : ℂ) :
    contractingCoordinate a (controllerLinear a t z) =
      Real.exp (-a * t) * contractingCoordinate a z := by
  simp only [contractingCoordinate, controllerLinear, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
  field_simp
  ring

/-- The unnormalized action is a one-parameter group. -/
theorem controllerLinear_add
    {a : ℝ} (ha : a ≠ 0) (t u : ℝ) (z : ℂ) :
    controllerLinear a (t + u) z =
      controllerLinear a t (controllerLinear a u z) := by
  apply eq_of_eigenCoordinates_eq ha
  · rw [expandingCoordinate_controllerLinear ha,
      expandingCoordinate_controllerLinear ha,
      expandingCoordinate_controllerLinear ha, ← mul_assoc,
      ← Real.exp_add]
    congr 2
    ring
  · rw [contractingCoordinate_controllerLinear ha,
      contractingCoordinate_controllerLinear ha,
      contractingCoordinate_controllerLinear ha, ← mul_assoc,
      ← Real.exp_add]
    congr 2
    ring

/-- At time zero the unnormalized action is the identity. -/
theorem controllerLinear_zero
    {a : ℝ} (ha : a ≠ 0) (z : ℂ) :
    controllerLinear a 0 z = z := by
  apply eq_of_eigenCoordinates_eq ha
  · rw [expandingCoordinate_controllerLinear ha]
    simp
  · rw [contractingCoordinate_controllerLinear ha]
    simp

/-- Eigen-coordinates are real-linear. -/
@[simp]
theorem expandingCoordinate_real_smul
    (a c : ℝ) (z : ℂ) :
    expandingCoordinate a (c • z) =
      c * expandingCoordinate a z := by
  simp only [expandingCoordinate, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  ring

@[simp]
theorem contractingCoordinate_real_smul
    (a c : ℝ) (z : ℂ) :
    contractingCoordinate a (c • z) =
      c * contractingCoordinate a z := by
  simp only [contractingCoordinate, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  ring

/-- The action is real-linear in the vector variable. -/
theorem controllerLinear_real_smul
    {a : ℝ} (ha : a ≠ 0) (t c : ℝ) (z : ℂ) :
    controllerLinear a t (c • z) =
      c • controllerLinear a t z := by
  apply eq_of_eigenCoordinates_eq ha
  · simp only [expandingCoordinate_controllerLinear ha,
      expandingCoordinate_real_smul]
    ring
  · simp only [contractingCoordinate_controllerLinear ha,
      contractingCoordinate_real_smul]
    ring

/-- The hyperbolic linear action never sends a nonzero vector to zero. -/
theorem controllerLinear_ne_zero
    {a : ℝ} (ha : a ≠ 0) (t : ℝ) {z : ℂ} (hz : z ≠ 0) :
    controllerLinear a t z ≠ 0 := by
  intro hzero
  have hplus :
      expandingCoordinate a z = 0 := by
    have h :=
      expandingCoordinate_controllerLinear ha t z
    rw [hzero] at h
    simp only [Complex.zero_im, Complex.zero_re,
      expandingCoordinate, zero_add, mul_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (Real.exp_ne_zero _)
  have hminus :
      contractingCoordinate a z = 0 := by
    have h :=
      contractingCoordinate_controllerLinear ha t z
    rw [hzero] at h
    simp only [Complex.zero_im, Complex.zero_re,
      contractingCoordinate, sub_zero, mul_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (Real.exp_ne_zero _)
  apply hz
  apply Complex.ext
  · rw [re_eq_sub_eigen_div ha z]
    simp [hplus, hminus]
  · rw [im_eq_add_eigen_div a z]
    simp [hplus, hminus]

/-! The derivative of the unnormalized hyperbolic action at time zero.
These two coordinate lemmas are also useful independently of the radial
normalization. -/

theorem hasDerivAt_controllerLinear_re_zero
    {a : ℝ} (ha : a ≠ 0) (z : ℂ) :
    HasDerivAt
      (fun t : ℝ ↦ (controllerLinear a t z).re)
      z.im 0 := by
  have hpos :
      HasDerivAt (fun t : ℝ ↦ Real.exp (a * t)) a 0 := by
    simpa using ((hasDerivAt_id (𝕜 := ℝ) 0).const_mul a).exp
  have hneg :
      HasDerivAt (fun t : ℝ ↦ Real.exp (-a * t)) (-a) 0 := by
    simpa [neg_mul] using
      ((hasDerivAt_id (𝕜 := ℝ) 0).const_mul (-a)).exp
  have h :=
    ((hpos.mul_const (expandingCoordinate a z)).sub
      (hneg.mul_const (contractingCoordinate a z))).div_const
        (2 * a)
  convert h using 1
  · funext t
    simp only [controllerLinear_re, Pi.sub_apply]
  · simp only [expandingCoordinate, contractingCoordinate]
    field_simp
    ring

theorem hasDerivAt_controllerLinear_im_zero
    (a : ℝ) (z : ℂ) :
    HasDerivAt
      (fun t : ℝ ↦ (controllerLinear a t z).im)
      (a ^ 2 * z.re) 0 := by
  have hpos :
      HasDerivAt (fun t : ℝ ↦ Real.exp (a * t)) a 0 := by
    simpa using ((hasDerivAt_id (𝕜 := ℝ) 0).const_mul a).exp
  have hneg :
      HasDerivAt (fun t : ℝ ↦ Real.exp (-a * t)) (-a) 0 := by
    simpa [neg_mul] using
      ((hasDerivAt_id (𝕜 := ℝ) 0).const_mul (-a)).exp
  have h :=
    ((hpos.mul_const (expandingCoordinate a z)).add
      (hneg.mul_const (contractingCoordinate a z))).div_const 2
  convert h using 1
  · funext t
    simp only [controllerLinear_im, Pi.add_apply]
  · simp only [expandingCoordinate, contractingCoordinate]
    ring

/-- At time zero, the derivative of the squared Euclidean norm of the
unnormalized orbit is obtained by differentiating its two coordinates.
We keep the formula in a factored form because it is useful before the
specialization `a² = p - 1`. -/
theorem hasDerivAt_controllerLinear_normSq_zero
    {a : ℝ} (ha : a ≠ 0) (z : ℂ) :
    HasDerivAt
      (fun t : ℝ ↦
        (controllerLinear a t z).re ^ 2 +
          (controllerLinear a t z).im ^ 2)
      (2 * z.re * z.im +
        2 * z.im * (a ^ 2 * z.re)) 0 := by
  have hre :=
    hasDerivAt_controllerLinear_re_zero ha z
  have him :=
    hasDerivAt_controllerLinear_im_zero a z
  have h := (hre.pow 2).add (him.pow 2)
  convert h using 1
  rw [controllerLinear_zero ha]
  ring

/-- Radial normalization of a nonzero complex vector to the unit circle. -/
def normalizeToCircle (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨(‖z‖⁻¹ : ℝ) • z, by
    change (‖z‖⁻¹ : ℝ) • z ∈ sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg z))]
    field_simp [norm_ne_zero_iff.mpr hz]⟩

@[simp]
theorem coe_normalizeToCircle (z : ℂ) (hz : z ≠ 0) :
    ((normalizeToCircle z hz : Circle) : ℂ) =
      (‖z‖⁻¹ : ℝ) • z :=
  rfl

/-- Positive radial rescaling does not change the normalized point. -/
theorem normalizeToCircle_pos_smul
    (z : ℂ) (hz : z ≠ 0) {c : ℝ} (hc : 0 < c) :
    normalizeToCircle (c • z) (smul_ne_zero hc.ne' hz) =
      normalizeToCircle z hz := by
  apply Circle.ext
  simp only [coe_normalizeToCircle, norm_smul,
    Real.norm_of_nonneg hc.le, smul_smul]
  congr 1
  field_simp

/-- A point already on the unit circle is unchanged by normalization. -/
theorem normalizeToCircle_coe (z : Circle) :
    normalizeToCircle (z : ℂ) z.coe_ne_zero = z := by
  apply Circle.ext
  simp [coe_normalizeToCircle]

/-- Radial normalization is independent of the proof supplied that its
argument is nonzero. -/
theorem normalizeToCircle_congr
    {z w : ℂ} (h : z = w) (hz : z ≠ 0) (hw : w ≠ 0) :
    normalizeToCircle z hz = normalizeToCircle w hw := by
  subst w
  rfl

/-! ## The normalized hyperbolic flow -/

/-- The normalized hyperbolic action is the controller flow on the
oriented unit circle. -/
def controllerFlow (p : ℝ) (hp : 1 < p) : Flow ℝ Circle := by
  let a := controllerExponent p
  have ha : a ≠ 0 := controllerExponent_ne_zero hp
  exact
    { toFun := fun t z ↦
        normalizeToCircle
          (controllerLinear a t (z : ℂ))
          (controllerLinear_ne_zero ha t z.coe_ne_zero)
      cont' := by
        have hlinear :
            Continuous
              (fun q : ℝ × Circle ↦
                controllerLinear a q.1 (q.2 : ℂ)) := by
          unfold controllerLinear expandingCoordinate
            contractingCoordinate
          fun_prop
        apply Continuous.subtype_mk
        change Continuous
          (fun q : ℝ × Circle ↦
            (‖controllerLinear a q.1 (q.2 : ℂ)‖⁻¹ : ℝ) •
              controllerLinear a q.1 (q.2 : ℂ))
        apply Continuous.smul
        · apply (continuous_norm.comp hlinear).inv₀
          intro q
          exact norm_ne_zero_iff.mpr
            (controllerLinear_ne_zero ha q.1 q.2.coe_ne_zero)
        · exact hlinear
      map_add' := by
        intro t u z
        let w : ℂ := controllerLinear a u (z : ℂ)
        have hw : w ≠ 0 :=
          controllerLinear_ne_zero ha u z.coe_ne_zero
        let c : ℝ := ‖w‖⁻¹
        have hc : 0 < c := by
          exact inv_pos.mpr (norm_pos_iff.mpr hw)
        calc
          normalizeToCircle
              (controllerLinear a (t + u) (z : ℂ)) _ =
            normalizeToCircle
              (controllerLinear a t w) _ :=
            normalizeToCircle_congr
              (controllerLinear_add ha t u (z : ℂ))
              _ _
          _ = normalizeToCircle
              (c • controllerLinear a t w) _ :=
            (normalizeToCircle_pos_smul
              (controllerLinear a t w)
              (controllerLinear_ne_zero ha t hw) hc).symm
          _ = normalizeToCircle
              (controllerLinear a t (c • w)) _ :=
            normalizeToCircle_congr
              (controllerLinear_real_smul ha t c w).symm _ _
          _ = normalizeToCircle
              (controllerLinear a t
                ((normalizeToCircle w hw : Circle) : ℂ)) _ := by
            rfl
      map_zero' := by
        intro z
        change
          normalizeToCircle
              (controllerLinear a 0 (z : ℂ)) _ = z
        simpa only [controllerLinear_zero ha] using
          normalizeToCircle_coe z }

@[simp]
theorem controllerFlow_apply
    (p : ℝ) (hp : 1 < p) (t : ℝ) (z : Circle) :
    controllerFlow p hp t z =
      normalizeToCircle
        (controllerLinear (controllerExponent p) t (z : ℂ))
        (controllerLinear_ne_zero
          (controllerExponent_ne_zero hp) t z.coe_ne_zero) :=
  rfl

/-! ## Infinitesimal identification with the polynomial field

The group law above already defines the normalized dynamics globally.
For the reduction, however, it is important to verify that this explicit
flow really integrates the displayed polynomial controller ODE.  The next
lemmas carry out that calculation at time zero. -/

/-- Along a unit-circle orbit of the unnormalized hyperbolic system, the
instantaneous change of the Euclidean norm is `p r s`. -/
theorem hasDerivAt_controllerLinear_norm_zero
    (p : ℝ) (hp : 1 < p) (z : Circle) :
    HasDerivAt
      (fun t : ℝ ↦
        ‖controllerLinear (controllerExponent p) t (z : ℂ)‖)
      (p * (z : ℂ).re * (z : ℂ).im) 0 := by
  have hsq :=
    hasDerivAt_controllerLinear_normSq_zero
      (controllerExponent_ne_zero hp) (z : ℂ)
  have hunit :
      (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
    simpa only [Complex.normSq_apply, pow_two] using Circle.normSq_coe z
  have hradicand :
      (controllerLinear (controllerExponent p) 0 (z : ℂ)).re ^ 2 +
          (controllerLinear (controllerExponent p) 0 (z : ℂ)).im ^ 2 ≠
        0 := by
    rw [controllerLinear_zero (controllerExponent_ne_zero hp)]
    linarith
  have hsqrt := hsq.sqrt hradicand
  convert hsqrt using 1
  · funext t
    exact Complex.norm_eq_sqrt_sq_add_sq _
  · rw [controllerLinear_zero (controllerExponent_ne_zero hp)]
    rw [hunit, Real.sqrt_one]
    rw [controllerExponent_sq hp]
    ring

/-- The reciprocal normalization factor therefore has derivative
`-p r s` at time zero. -/
theorem hasDerivAt_controllerLinear_invNorm_zero
    (p : ℝ) (hp : 1 < p) (z : Circle) :
    HasDerivAt
      (fun t : ℝ ↦
        ‖controllerLinear (controllerExponent p) t (z : ℂ)‖⁻¹)
      (-p * (z : ℂ).re * (z : ℂ).im) 0 := by
  have hnorm :=
    hasDerivAt_controllerLinear_norm_zero p hp z
  have hnonzero :
      ‖controllerLinear (controllerExponent p) 0 (z : ℂ)‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr
      (controllerLinear_ne_zero
        (controllerExponent_ne_zero hp) 0 z.coe_ne_zero)
  have hinv := hnorm.inv hnonzero
  convert hinv using 1
  rw [controllerLinear_zero (controllerExponent_ne_zero hp),
    Circle.norm_coe]
  ring

/-- The first coordinate of the explicit flow has exactly the first
coordinate of the polynomial controller field as its time derivative. -/
theorem hasDerivAt_controllerFlow_re_zero
    (p : ℝ) (hp : 1 < p) (z : Circle) :
    HasDerivAt
      (fun t : ℝ ↦
        ((controllerFlow p hp t z : Circle) : ℂ).re)
      (-(z : ℂ).im * (p * (z : ℂ).re ^ 2 - 1)) 0 := by
  have hinv :=
    hasDerivAt_controllerLinear_invNorm_zero p hp z
  have hre :=
    hasDerivAt_controllerLinear_re_zero
      (controllerExponent_ne_zero hp) (z : ℂ)
  have hprod := hinv.mul hre
  convert hprod using 1
  · funext t
    rw [controllerFlow_apply, coe_normalizeToCircle]
    simp only [Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Pi.mul_apply]
  · rw [controllerLinear_zero (controllerExponent_ne_zero hp),
      Circle.norm_coe]
    ring

/-- The second coordinate of the explicit flow has exactly the second
coordinate of the polynomial controller field as its time derivative. -/
theorem hasDerivAt_controllerFlow_im_zero
    (p : ℝ) (hp : 1 < p) (z : Circle) :
    HasDerivAt
      (fun t : ℝ ↦
        ((controllerFlow p hp t z : Circle) : ℂ).im)
      ((z : ℂ).re * (p * (z : ℂ).re ^ 2 - 1)) 0 := by
  have hinv :=
    hasDerivAt_controllerLinear_invNorm_zero p hp z
  have him :=
    hasDerivAt_controllerLinear_im_zero
      (controllerExponent p) (z : ℂ)
  have hprod := hinv.mul him
  convert hprod using 1
  · funext t
    rw [controllerFlow_apply, coe_normalizeToCircle]
    simp only [Complex.real_smul, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Pi.mul_apply]
  · rw [controllerLinear_zero (controllerExponent_ne_zero hp),
      Circle.norm_coe, controllerExponent_sq hp]
    have hunit :
        (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
      simpa only [Complex.normSq_apply, pow_two] using
        Circle.normSq_coe z
    linear_combination p * (z : ℂ).re * hunit

/-- The first coordinate satisfies the controller ODE at every time, not
only at the initial instant.  This follows from the flow law by shifting
the time variable back to zero. -/
theorem hasDerivAt_controllerFlow_re
    (p : ℝ) (hp : 1 < p) (z : Circle) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ ↦
        ((controllerFlow p hp u z : Circle) : ℂ).re)
      (-((controllerFlow p hp t z : Circle) : ℂ).im *
        (p * ((controllerFlow p hp t z : Circle) : ℂ).re ^ 2 - 1))
      t := by
  let w : Circle := controllerFlow p hp t z
  have hzero := hasDerivAt_controllerFlow_re_zero p hp w
  have hshift :
      HasDerivAt (fun u : ℝ ↦ u - t) 1 t := by
    simpa using (hasDerivAt_id t).sub_const t
  have h := hzero.comp_of_eq t hshift (by simp)
  convert h using 1
  · funext u
    simp only [Function.comp_apply]
    have hadd :=
      (controllerFlow p hp).map_add (u - t) t z
    simpa [w] using congrArg
      (fun q : Circle ↦ (q : ℂ).re) hadd
  · simp [w]

/-- The second coordinate likewise satisfies the controller ODE at every
time. -/
theorem hasDerivAt_controllerFlow_im
    (p : ℝ) (hp : 1 < p) (z : Circle) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ ↦
        ((controllerFlow p hp u z : Circle) : ℂ).im)
      (((controllerFlow p hp t z : Circle) : ℂ).re *
        (p * ((controllerFlow p hp t z : Circle) : ℂ).re ^ 2 - 1))
      t := by
  let w : Circle := controllerFlow p hp t z
  have hzero := hasDerivAt_controllerFlow_im_zero p hp w
  have hshift :
      HasDerivAt (fun u : ℝ ↦ u - t) 1 t := by
    simpa using (hasDerivAt_id t).sub_const t
  have h := hzero.comp_of_eq t hshift (by simp)
  convert h using 1
  · funext u
    simp only [Function.comp_apply]
    have hadd :=
      (controllerFlow p hp).map_add (u - t) t z
    simpa [w] using congrArg
      (fun q : Circle ↦ (q : ℂ).im) hadd
  · simp [w]

/-! ## Eigen-directions and affine height motion -/

/-- The four oriented eigenvectors on the unit circle.  They will be
identified below with the four polynomial-controller equilibria. -/
def controllerEquilibria (p : ℝ) : Set Circle :=
  {z | expandingCoordinate (controllerExponent p) (z : ℂ) = 0 ∨
    contractingCoordinate (controllerExponent p) (z : ℂ) = 0}

theorem mem_controllerEquilibria_iff
    (p : ℝ) (z : Circle) :
    z ∈ controllerEquilibria p ↔
      expandingCoordinate (controllerExponent p) (z : ℂ) = 0 ∨
      contractingCoordinate (controllerExponent p) (z : ℂ) = 0 :=
  Iff.rfl

/-- Both eigen-coordinates transform by their expected exponential factor
and by the common positive normalization factor. -/
theorem expandingCoordinate_controllerFlow
    (p : ℝ) (hp : 1 < p) (t : ℝ) (z : Circle) :
    expandingCoordinate (controllerExponent p)
        ((controllerFlow p hp t z : Circle) : ℂ) =
      ‖controllerLinear (controllerExponent p) t (z : ℂ)‖⁻¹ *
        (Real.exp (controllerExponent p * t) *
          expandingCoordinate (controllerExponent p) (z : ℂ)) := by
  rw [controllerFlow_apply, coe_normalizeToCircle,
    expandingCoordinate_real_smul,
    expandingCoordinate_controllerLinear
      (controllerExponent_ne_zero hp)]

theorem contractingCoordinate_controllerFlow
    (p : ℝ) (hp : 1 < p) (t : ℝ) (z : Circle) :
    contractingCoordinate (controllerExponent p)
        ((controllerFlow p hp t z : Circle) : ℂ) =
      ‖controllerLinear (controllerExponent p) t (z : ℂ)‖⁻¹ *
        (Real.exp (-(controllerExponent p * t)) *
          contractingCoordinate (controllerExponent p) (z : ℂ)) := by
  rw [controllerFlow_apply, coe_normalizeToCircle,
    contractingCoordinate_real_smul,
    contractingCoordinate_controllerLinear
      (controllerExponent_ne_zero hp)]
  congr 3
  ring

/-- Every eigen-direction is a fixed point of the normalized flow. -/
theorem isFlowFixedPoint_of_mem_controllerEquilibria
    (p : ℝ) (hp : 1 < p) {z : Circle}
    (hz : z ∈ controllerEquilibria p) :
    HGAS.Dynamics.InvariantProbabilityMeasure.IsFlowFixedPoint
      (controllerFlow p hp) z := by
  intro t
  rcases hz with hplus | hminus
  · have hlinear :
        controllerLinear (controllerExponent p) t (z : ℂ) =
          Real.exp (-(controllerExponent p * t)) • (z : ℂ) := by
      apply eq_of_eigenCoordinates_eq
        (controllerExponent_ne_zero hp)
      · rw [expandingCoordinate_controllerLinear
          (controllerExponent_ne_zero hp),
          expandingCoordinate_real_smul, hplus]
        ring
      · rw [contractingCoordinate_controllerLinear
          (controllerExponent_ne_zero hp),
          contractingCoordinate_real_smul]
        congr 2
        ring
    change controllerFlow p hp t z = z
    rw [controllerFlow_apply]
    exact
      (normalizeToCircle_congr hlinear _ _).trans
        ((normalizeToCircle_pos_smul (z : ℂ) z.coe_ne_zero
          (Real.exp_pos _)).trans (normalizeToCircle_coe z))
  · have hlinear :
        controllerLinear (controllerExponent p) t (z : ℂ) =
          Real.exp (controllerExponent p * t) • (z : ℂ) := by
      apply eq_of_eigenCoordinates_eq
        (controllerExponent_ne_zero hp)
      · rw [expandingCoordinate_controllerLinear
          (controllerExponent_ne_zero hp),
          expandingCoordinate_real_smul]
      · rw [contractingCoordinate_controllerLinear
          (controllerExponent_ne_zero hp),
          contractingCoordinate_real_smul, hminus]
        ring
    change controllerFlow p hp t z = z
    rw [controllerFlow_apply]
    exact
      (normalizeToCircle_congr hlinear _ _).trans
        ((normalizeToCircle_pos_smul (z : ℂ) z.coe_ne_zero
          (Real.exp_pos _)).trans (normalizeToCircle_coe z))

/-- Logarithmic eigen-coordinate ratio.  Its values at the equilibria are
irrelevant; all uses below are on their complement. -/
def controllerHeight (p : ℝ) (z : Circle) : ℝ :=
  Real.log
      (expandingCoordinate (controllerExponent p) (z : ℂ)) -
    Real.log
      (contractingCoordinate (controllerExponent p) (z : ℂ))

/-- Off the eigen-directions, controller height advances affinely at speed
`2 √(p-1)`. -/
theorem controllerHeight_flow
    (p : ℝ) (hp : 1 < p) (t : ℝ) (z : Circle)
    (hplus :
      expandingCoordinate (controllerExponent p) (z : ℂ) ≠ 0)
    (hminus :
      contractingCoordinate (controllerExponent p) (z : ℂ) ≠ 0) :
    controllerHeight p (controllerFlow p hp t z) =
      controllerHeight p z + 2 * controllerExponent p * t := by
  let w : ℂ :=
    controllerLinear (controllerExponent p) t (z : ℂ)
  have hw : w ≠ 0 :=
    controllerLinear_ne_zero (controllerExponent_ne_zero hp)
      t z.coe_ne_zero
  have hnormInv : ‖w‖⁻¹ ≠ 0 :=
    inv_ne_zero (norm_ne_zero_iff.mpr hw)
  rw [controllerHeight, controllerHeight,
    expandingCoordinate_controllerFlow,
    contractingCoordinate_controllerFlow]
  rw [Real.log_mul hnormInv
      (mul_ne_zero (Real.exp_ne_zero _) hplus),
    Real.log_mul (Real.exp_ne_zero _) hplus,
    Real.log_mul hnormInv
      (mul_ne_zero (Real.exp_ne_zero _) hminus),
    Real.log_mul (Real.exp_ne_zero _) hminus,
    Real.log_exp, Real.log_exp]
  ring

theorem measurable_controllerHeight (p : ℝ) :
    Measurable (controllerHeight p) := by
  unfold controllerHeight expandingCoordinate contractingCoordinate
  fun_prop

/-! ## Wandering strips and invariant-measure support -/

/-- A unit-width strip for the affine controller height, restricted away
from the two eigenlines. -/
def controllerStrip (p : ℝ) (k : ℤ) : Set Circle :=
  {z |
    expandingCoordinate (controllerExponent p) (z : ℂ) ≠ 0 ∧
    contractingCoordinate (controllerExponent p) (z : ℂ) ≠ 0 ∧
    (k : ℝ) ≤ controllerHeight p z ∧
    controllerHeight p z < (k : ℝ) + 1}

theorem measurableSet_controllerStrip (p : ℝ) (k : ℤ) :
    MeasurableSet (controllerStrip p k) := by
  have hplus :
      Measurable
        (fun z : Circle ↦
          expandingCoordinate (controllerExponent p) (z : ℂ)) := by
    unfold expandingCoordinate
    fun_prop
  have hminus :
      Measurable
        (fun z : Circle ↦
          contractingCoordinate (controllerExponent p) (z : ℂ)) := by
    unfold contractingCoordinate
    fun_prop
  have hheight := measurable_controllerHeight p
  change MeasurableSet
    ({z : Circle |
        expandingCoordinate (controllerExponent p) (z : ℂ) ≠ 0} ∩
      ({z : Circle |
          contractingCoordinate (controllerExponent p) (z : ℂ) ≠ 0} ∩
        ({z : Circle | (k : ℝ) ≤ controllerHeight p z} ∩
          {z : Circle |
            controllerHeight p z < (k : ℝ) + 1})))
  exact
    (hplus (measurableSet_singleton 0).compl).inter
      ((hminus (measurableSet_singleton 0).compl).inter
        ((hheight measurableSet_Ici).inter
          (hheight measurableSet_Iio)))

/-- The natural time step makes controller height advance by exactly one. -/
def controllerStripStep (p : ℝ) : ℝ :=
  1 / (2 * controllerExponent p)

theorem controllerHeight_nsmul_stripStep
    (p : ℝ) (hp : 1 < p) (n : ℕ) (z : Circle)
    (hplus :
      expandingCoordinate (controllerExponent p) (z : ℂ) ≠ 0)
    (hminus :
      contractingCoordinate (controllerExponent p) (z : ℂ) ≠ 0) :
    controllerHeight p
        (controllerFlow p hp
          ((n : ℝ) * controllerStripStep p) z) =
      controllerHeight p z + n := by
  rw [controllerHeight_flow p hp _ z hplus hminus]
  unfold controllerStripStep
  field_simp [controllerExponent_ne_zero hp]

/-- Every unit-height strip is wandering under the natural controller time
step. -/
theorem pairwise_disjoint_inverseTimeTranslate_controllerStrip
    (p : ℝ) (hp : 1 < p) (k : ℤ) :
    Pairwise (Disjoint on
      HGAS.Dynamics.inverseTimeTranslate
        (controllerFlow p hp) (controllerStripStep p)
        (controllerStrip p k)) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro z hzn hzm
  change
    controllerFlow p hp
        ((n : ℝ) * controllerStripStep p) z ∈
      controllerStrip p k at hzn
  change
    controllerFlow p hp
        ((m : ℝ) * controllerStripStep p) z ∈
      controllerStrip p k at hzm
  rcases hzn with
    ⟨hplusN, hminusN, hlowerN, hupperN⟩
  rcases hzm with
    ⟨hplusM, hminusM, hlowerM, hupperM⟩
  have hplus :
      expandingCoordinate (controllerExponent p) (z : ℂ) ≠ 0 := by
    intro hzero
    apply hplusN
    rw [expandingCoordinate_controllerFlow, hzero]
    ring
  have hminus :
      contractingCoordinate (controllerExponent p) (z : ℂ) ≠ 0 := by
    intro hzero
    apply hminusN
    rw [contractingCoordinate_controllerFlow, hzero]
    ring
  rw [controllerHeight_nsmul_stripStep p hp n z hplus hminus]
    at hlowerN hupperN
  rw [controllerHeight_nsmul_stripStep p hp m z hplus hminus]
    at hlowerM hupperM
  have hnmReal : (n : ℝ) < (m : ℝ) + 1 := by
    linarith
  have hmnReal : (m : ℝ) < (n : ℝ) + 1 := by
    linarith
  have hnmNat : n < m + 1 := by
    exact_mod_cast hnmReal
  have hmnNat : m < n + 1 := by
    exact_mod_cast hmnReal
  omega

/-- Enumerate all integer-indexed height strips by natural numbers. -/
def indexedControllerStrip (p : ℝ) (n : ℕ) : Set Circle :=
  controllerStrip p (Equiv.intEquivNat.symm n)

/-- The complement of the controller equilibria is covered by the
countable family of height strips. -/
theorem compl_controllerEquilibria_subset_iUnion_strips
    (p : ℝ) :
    (controllerEquilibria p)ᶜ ⊆
      ⋃ n : ℕ, indexedControllerStrip p n := by
  intro z hz
  have hplus :
      expandingCoordinate (controllerExponent p) (z : ℂ) ≠ 0 := by
    intro hzero
    exact hz (Or.inl hzero)
  have hminus :
      contractingCoordinate (controllerExponent p) (z : ℂ) ≠ 0 := by
    intro hzero
    exact hz (Or.inr hzero)
  let k : ℤ := ⌊controllerHeight p z⌋
  let n : ℕ := Equiv.intEquivNat k
  apply Set.mem_iUnion.mpr
  refine ⟨n, ?_⟩
  change z ∈ controllerStrip p (Equiv.intEquivNat.symm n)
  have hkn : Equiv.intEquivNat.symm n = k := by
    exact Equiv.symm_apply_apply Equiv.intEquivNat k
  rw [hkn]
  exact ⟨hplus, hminus, Int.floor_le _, Int.lt_floor_add_one _⟩

/-- Literal support clause of the radical-clock lemma: every invariant
probability of the controller flow is concentrated on its four
eigen-directions. -/
theorem invariantProbability_controllerEquilibria_compl_eq_zero
    (p : ℝ) (hp : 1 < p)
    (μ : HGAS.Dynamics.InvariantProbabilityMeasure
      (controllerFlow p hp)) :
    (μ.measure : Measure Circle) ((controllerEquilibria p)ᶜ) = 0 := by
  apply
    HGAS.Dynamics.measure_eq_zero_of_subset_iUnion_wandering
      μ (controllerEquilibria p)ᶜ
      (fun _ ↦ controllerStripStep p)
      (indexedControllerStrip p)
      (compl_controllerEquilibria_subset_iUnion_strips p)
  · intro n
    exact measurableSet_controllerStrip p
      (Equiv.intEquivNat.symm n)
  · intro n
    exact
      pairwise_disjoint_inverseTimeTranslate_controllerStrip
        p hp (Equiv.intEquivNat.symm n)

/-! ## Identification with the polynomial controller -/

/-- Read a unit complex number as the controller coordinates `(r,s)`. -/
def circleControllerState (z : Circle) :
    HGAS.Clocks.Controller.ControllerState ℝ :=
  ⟨(z : ℂ).re, (z : ℂ).im⟩

@[simp]
theorem circleControllerState_r (z : Circle) :
    (circleControllerState z).r = (z : ℂ).re :=
  rfl

@[simp]
theorem circleControllerState_s (z : Circle) :
    (circleControllerState z).s = (z : ℂ).im :=
  rfl

/-- Bundled ODE statement: in the manuscript's `(r,s)` coordinates, every
orbit of `controllerFlow` has derivative equal to `controllerField` at
every time.  The two conjuncts are deliberately coordinatewise so that
later modules can use them without introducing a manifold derivative on
the circle. -/
theorem controllerFlow_solves_controllerField
    (p : ℝ) (hp : 1 < p) (z : Circle) (t : ℝ) :
    HasDerivAt
        (fun u : ℝ ↦
          (circleControllerState (controllerFlow p hp u z)).r)
        (HGAS.Clocks.Controller.controllerField p
          (circleControllerState (controllerFlow p hp t z))).r t ∧
      HasDerivAt
        (fun u : ℝ ↦
          (circleControllerState (controllerFlow p hp u z)).s)
        (HGAS.Clocks.Controller.controllerField p
          (circleControllerState (controllerFlow p hp t z))).s t := by
  constructor
  · simpa only [circleControllerState_r,
      HGAS.Clocks.Controller.controllerField_r,
      HGAS.Clocks.Controller.mismatch,
      circleControllerState_s] using
      hasDerivAt_controllerFlow_re p hp z t
  · simpa only [circleControllerState_s,
      HGAS.Clocks.Controller.controllerField_s,
      HGAS.Clocks.Controller.mismatch,
      circleControllerState_r] using
      hasDerivAt_controllerFlow_im p hp z t

/-- The complex unit-circle condition is exactly the controller unit-circle
condition. -/
theorem controllerRadiusSq_circleControllerState (z : Circle) :
    HGAS.Clocks.Controller.controllerRadiusSq
      (circleControllerState z) = 1 := by
  have hnorm := Circle.normSq_coe z
  simpa only [HGAS.Clocks.Controller.controllerRadiusSq,
    circleControllerState_r, circleControllerState_s,
    Complex.normSq_apply, pow_two] using hnorm

/-- Product of the two hyperbolic eigen-coordinates. -/
theorem expanding_mul_contracting_eq
    (p : ℝ) (hp : 1 < p) (z : Circle) :
    expandingCoordinate (controllerExponent p) (z : ℂ) *
        contractingCoordinate (controllerExponent p) (z : ℂ) =
      1 - p * (z : ℂ).re ^ 2 := by
  have hunit :
      (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
    simpa only [HGAS.Clocks.Controller.controllerRadiusSq,
      circleControllerState_r, circleControllerState_s] using
      controllerRadiusSq_circleControllerState z
  have hexponent := controllerExponent_sq hp
  simp only [expandingCoordinate, contractingCoordinate]
  nlinarith

/-- The eigen-directions used in the explicit flow are precisely the
equilibria of the polynomial controller field (5.1). -/
theorem mem_controllerEquilibria_iff_polynomialEquilibrium
    (p : ℝ) (hp : 1 < p) (z : Circle) :
    z ∈ controllerEquilibria p ↔
      HGAS.Clocks.Controller.IsControllerEquilibrium p
        (circleControllerState z) := by
  rw [HGAS.Clocks.Controller.isControllerEquilibrium_iff_lock_of_unit p
      (circleControllerState z)
      (controllerRadiusSq_circleControllerState z)]
  change
    (expandingCoordinate (controllerExponent p) (z : ℂ) = 0 ∨
      contractingCoordinate (controllerExponent p) (z : ℂ) = 0) ↔
        p * (z : ℂ).re ^ 2 = 1
  rw [← mul_eq_zero, expanding_mul_contracting_eq p hp z]
  constructor <;> intro h <;> linarith

/-- Coordinate form of the displayed four equilibria: on the equilibrium
set, the two coordinate squares are exactly `1/p` and `1-1/p`, and these
two equations conversely characterize the equilibrium set. -/
theorem mem_controllerEquilibria_iff_coordinate_squares
    (p : ℝ) (hp : 1 < p) (z : Circle) :
    z ∈ controllerEquilibria p ↔
      (z : ℂ).re ^ 2 = 1 / p ∧
      (z : ℂ).im ^ 2 = 1 - 1 / p := by
  rw [mem_controllerEquilibria_iff_polynomialEquilibrium p hp z,
    HGAS.Clocks.Controller.isControllerEquilibrium_iff_lock_of_unit p
        (circleControllerState z)
        (controllerRadiusSq_circleControllerState z)]
  have hunit :
      (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
    simpa only [HGAS.Clocks.Controller.controllerRadiusSq,
      circleControllerState_r, circleControllerState_s] using
      controllerRadiusSq_circleControllerState z
  have hpne : p ≠ 0 := ne_of_gt (zero_lt_one.trans hp)
  constructor
  · intro hlock
    constructor
    · apply (eq_div_iff hpne).2
      simpa only [mul_comm] using hlock
    · have hre :
          (z : ℂ).re ^ 2 = 1 / p := by
        apply (eq_div_iff hpne).2
        simpa only [mul_comm] using hlock
      linarith
  · rintro ⟨hre, _⟩
    change p * (z : ℂ).re ^ 2 = 1
    rw [hre]
    field_simp

/-- Manuscript-facing support statement in polynomial language: every
invariant probability of the literal polynomial controller flow is
concentrated on states where `controllerField p = 0`. -/
theorem invariantProbability_polynomialEquilibria_compl_eq_zero
    (p : ℝ) (hp : 1 < p)
    (μ : HGAS.Dynamics.InvariantProbabilityMeasure
      (controllerFlow p hp)) :
    (μ.measure : Measure Circle)
        ({z : Circle |
          HGAS.Clocks.Controller.IsControllerEquilibrium p
            (circleControllerState z)}ᶜ) = 0 := by
  have hset :
      {z : Circle |
        HGAS.Clocks.Controller.IsControllerEquilibrium p
          (circleControllerState z)} =
        controllerEquilibria p := by
    ext z
    exact
      (mem_controllerEquilibria_iff_polynomialEquilibrium
        p hp z).symm
  rw [hset]
  exact invariantProbability_controllerEquilibria_compl_eq_zero
    p hp μ

/-- Equivalent coordinate version of the support conclusion. -/
theorem invariantProbability_lockedCoordinateSquares_compl_eq_zero
    (p : ℝ) (hp : 1 < p)
    (μ : HGAS.Dynamics.InvariantProbabilityMeasure
      (controllerFlow p hp)) :
    (μ.measure : Measure Circle)
        ({z : Circle |
          (z : ℂ).re ^ 2 = 1 / p ∧
          (z : ℂ).im ^ 2 = 1 - 1 / p}ᶜ) = 0 := by
  have hset :
      {z : Circle |
        (z : ℂ).re ^ 2 = 1 / p ∧
        (z : ℂ).im ^ 2 = 1 - 1 / p} =
        controllerEquilibria p := by
    ext z
    exact
      (mem_controllerEquilibria_iff_coordinate_squares
        p hp z).symm
  rw [hset]
  exact invariantProbability_controllerEquilibria_compl_eq_zero
    p hp μ

end HGAS.Clocks.ControllerFlow
