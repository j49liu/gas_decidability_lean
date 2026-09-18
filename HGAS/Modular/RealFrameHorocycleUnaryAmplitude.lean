import HGAS.Modular.GammaTwoScaledH4SquareObservable
import HGAS.Modular.UpperHalfPlaneCurve
import HGAS.Modular.CanonicalLambdaLocal
import Mathlib.Tactic

/-!
# Exact unary amplitude along an arbitrary real-frame horocycle

Let `g ∈ SL(2,ℝ)` and let

```text
  T(t) = basePoint (g · u(σt)).
```

The Möbius derivative and imaginary-part formulas give the intrinsic
identity

```text
  ‖T'(t)‖ = |σ| · Im(T(t)).
```

If `T` is a canonical-lambda lift of a generic unary modular trajectory
`z`, the lift reconstruction theorem identifies the relative theta scale
with `T'`.  Since the canonical `C` coordinate is `H₄`, it follows that

```text
  ‖z.C‖ = |σ| · Im(T) · ‖H₄(T)‖.
```

The last theorem rewrites this as an exact equality with the continuous
speed-normalized quotient observable from
`GammaTwoScaledH4SquareObservable`.  Unlike the closed-cusp amplitude
theorems, nothing here assumes periodicity or an integral
horizontalization; this is the form used on the nonperiodic Haar branch.
-/

namespace HGAS.Modular

open Complex Matrix
open UpperHalfPlane hiding I
open scoped MatrixGroups NNReal

noncomputable section

/-- The upper-unipotent base orbit is the unit-height horizontal line. -/
theorem upperUnipotent_basePoint
    (s t : ℝ) :
    realModularFrameBasePoint (upperUnipotent (s * t)) =
      horizontalLine 0 1 s (by norm_num) t := by
  apply UpperHalfPlane.ext
  simp only [realModularFrameBasePoint, upperUnipotent,
    horizontalLine,
    UpperHalfPlane.coe_specialLinearGroup_apply]
  norm_num [Matrix.of_apply]
  apply Complex.ext <;> simp

/-- A real-frame horocycle is the Möbius image of the unit-height
horizontal line. -/
theorem realFrameHorocycle_basePoint
    (g : RealModularFrame) (s t : ℝ) :
    realModularFrameBasePoint (g * upperUnipotent (s * t)) =
      g • horizontalLine 0 1 s (by norm_num) t := by
  rw [realModularFrameBasePoint, mul_smul,
    ← realModularFrameBasePoint]
  rw [upperUnipotent_basePoint]

/-- Exact complex derivative of an arbitrary real-frame horocycle. -/
theorem hasDerivAt_realFrameHorocycle_basePoint
    (g : RealModularFrame) (s t : ℝ) :
    HasDerivAt
      (fun u : ℝ ↦
        (realModularFrameBasePoint
          (g * upperUnipotent (s * u)) : ℂ))
      ((s : ℂ) /
        UpperHalfPlane.denom
          (Matrix.SpecialLinearGroup.toGL g)
          (horizontalLine 0 1 s (by norm_num) t) ^ 2) t := by
  let T : ℝ → ℍ := horizontalLine 0 1 s (by norm_num)
  have hinner :
      HasDerivAt (fun u : ℝ ↦ (T u : ℂ)) (s : ℂ) t := by
    convert
      (complexHorizontalAffine_hasDerivAt 0 1 s (t : ℂ)).comp_ofReal
        using 1
    funext u
    exact (complexHorizontalAffine_ofReal 0 1 s u (by norm_num)).symm
  let gl : GL (Fin 2) ℝ :=
    Matrix.SpecialLinearGroup.toGL g
  have hdet : gl.val.det = 1 := by
    change ((gl.det : ℝˣ) : ℝ) = 1
    simp [gl]
  have houter :
      HasDerivAt
        (fun z : ℂ ↦
          ((gl • UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ))
        (gl.val.det /
          UpperHalfPlane.denom gl (T t) ^ 2)
        (T t : ℂ) :=
    (UpperHalfPlane.hasStrictDerivAt_smul
      (by rw [hdet]; norm_num) (T t)).hasDerivAt
  have hcomp := houter.scomp t hinner
  rw [hdet] at hcomp
  have hgl :
      gl = Matrix.SpecialLinearGroup.mapGL ℝ g := by
    ext i j
    rfl
  convert hcomp using 1
  · funext u
    rw [realFrameHorocycle_basePoint]
    change
      ((Matrix.SpecialLinearGroup.mapGL ℝ g • T u :
        UpperHalfPlane) : ℂ) =
        ((gl • UpperHalfPlane.ofComplex (T u : ℂ) :
          UpperHalfPlane) : ℂ)
    rw [hgl]
    simp only [UpperHalfPlane.ofComplex_apply]
  · simp [smul_eq_mul, div_eq_mul_inv, gl, T]

/-- The speed norm equals signed-speed magnitude times hyperbolic
height. -/
theorem norm_realFrameHorocycle_velocity
    (g : RealModularFrame) (s t : ℝ) :
    ‖(s : ℂ) /
        UpperHalfPlane.denom
          (Matrix.SpecialLinearGroup.toGL g)
          (horizontalLine 0 1 s (by norm_num) t) ^ 2‖ =
      |s| *
        (realModularFrameBasePoint
          (g * upperUnipotent (s * t))).im := by
  let τ : ℍ := horizontalLine 0 1 s (by norm_num) t
  let d : ℂ :=
    UpperHalfPlane.denom
      (Matrix.SpecialLinearGroup.toGL g) τ
  have him :
      (realModularFrameBasePoint
          (g * upperUnipotent (s * t))).im =
        1 / Complex.normSq d := by
    rw [realFrameHorocycle_basePoint]
    have hraw :=
      UpperHalfPlane.im_smul_eq_div_normSq
        (Matrix.SpecialLinearGroup.toGL g) τ
    have hgl :
        Matrix.SpecialLinearGroup.toGL g =
          Matrix.SpecialLinearGroup.mapGL ℝ g := by
      ext i j
      rfl
    have hbase :
        Matrix.SpecialLinearGroup.toGL g • τ =
          g • τ := by
      change
        Matrix.SpecialLinearGroup.toGL g • τ =
          Matrix.SpecialLinearGroup.mapGL ℝ g • τ
      rw [hgl]
    rw [hbase] at hraw
    simpa only [τ, horizontalLine_im,
      Matrix.SpecialLinearGroup.coeToGL_det,
      Units.val_one, abs_one, one_mul, one_div, d] using hraw
  rw [him, norm_div, norm_pow, norm_real, Real.norm_eq_abs,
    Complex.normSq_eq_norm_sq]
  have hd :
      ‖d‖ ≠ 0 :=
    norm_ne_zero_iff.mpr
      (UpperHalfPlane.denom_ne_zero
        (Matrix.SpecialLinearGroup.toGL g) τ)
  change |s| / ‖d‖ ^ 2 = |s| * (1 / ‖d‖ ^ 2)
  ring

/-- Exact `C`-coordinate amplitude for a generic unary trajectory whose
canonical-lambda lift is a real-frame horocycle. -/
theorem unaryC_norm_eq_realFrameHorocycle_amplitude
    {z : ℝ → UnaryModularState ℂ}
    {T : ℝ → ℍ}
    (hz :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock z)
    (hB : ∀ t, UnaryModularState.B (z t) ≠ 0)
    (hlambda :
      ∀ t,
        UnaryModularState.lambdaCoordinate (z t) =
          canonicalLambda (T t))
    (g : RealModularFrame) (s : ℝ)
    (hframe :
      ∀ t,
        T t =
          realModularFrameBasePoint
            (g * upperUnipotent (s * t)))
    (t : ℝ) :
    ‖(z t).C‖ =
      |s| *
        (realModularFrameBasePoint
          (g * upperUnipotent (s * t))).im *
        ‖H₄
          (realModularFrameBasePoint
            (g * upperUnipotent (s * t)))‖ := by
  let r : ℝ → UnaryModularState ℂ :=
    fun u ↦ canonicalUnaryTheta (T u)
  have hBr :
      UnaryModularState.B (r t) ≠ 0 := by
    have hJacobi :
        H₂ (T t) + H₄ (T t) = H₃ (T t) := by
      simpa only [Pi.add_apply] using
        congrFun jacobi_quartic_identity (T t)
    have hBr_eq :
        UnaryModularState.B (r t) = H₃ (T t) := by
      simpa only [r, UnaryModularState.B,
        canonicalUnaryTheta_A,
        canonicalUnaryTheta_C] using hJacobi
    rw [hBr_eq]
    exact H₃_ne_zero (T t)
  have hlambda_r :
      UnaryModularState.lambdaCoordinate (z t) =
        UnaryModularState.lambdaCoordinate (r t) := by
    rw [hlambda t]
    exact (canonicalUnaryTheta_lambdaCoordinate (T t)).symm
  have hC :
      (z t).C =
        unaryComparisonV z r t * H₄ (T t) := by
    simpa only [r, canonicalUnaryTheta_C] using
      unaryComparison_C_eq z r t
        (hB t) hBr hlambda_r
  have hTdiff :
      ∀ u, ∃ v : ℂ,
        HasDerivAt
          (fun a : ℝ ↦ (T a : ℂ)) v u := by
    intro u
    let v : ℂ :=
      (s : ℂ) /
        UpperHalfPlane.denom
          (Matrix.SpecialLinearGroup.toGL g)
          (horizontalLine 0 1 s (by norm_num) u) ^ 2
    refine ⟨v, ?_⟩
    have hraw := hasDerivAt_realFrameHorocycle_basePoint g s u
    exact hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun a ↦ by
        exact congrArg
          (fun q : ℍ ↦ (q : ℂ))
          (hframe a))
  have hvDeriv :=
    canonicalLambdaLift_hasDerivAt_comparisonV
      hz hB hlambda hTdiff t
  have hframeDeriv := hasDerivAt_realFrameHorocycle_basePoint g s t
  have hTframeDeriv :
      HasDerivAt
        (fun u : ℝ ↦ (T u : ℂ))
        ((s : ℂ) /
          UpperHalfPlane.denom
            (Matrix.SpecialLinearGroup.toGL g)
            (horizontalLine 0 1 s (by norm_num) t) ^ 2) t :=
    hframeDeriv.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u ↦ by
        exact congrArg
          (fun q : ℍ ↦ (q : ℂ))
          (hframe u))
  have hv :
      unaryComparisonV z r t =
        (s : ℂ) /
          UpperHalfPlane.denom
            (Matrix.SpecialLinearGroup.toGL g)
            (horizontalLine 0 1 s (by norm_num) t) ^ 2 :=
    hvDeriv.unique hTframeDeriv
  rw [hC, norm_mul, hv, norm_realFrameHorocycle_velocity,
    hframe t]

/-- Absolute value of a signed horocycle speed as a nonnegative real. -/
def horocycleSpeedNorm (s : ℝ) : ℝ≥0 :=
  ⟨|s|, abs_nonneg s⟩

@[simp]
theorem horocycleSpeedNorm_coe (s : ℝ) :
    (horocycleSpeedNorm s : ℝ) = |s| :=
  rfl

theorem horocycleSpeedNorm_ne_zero
    {s : ℝ} (hs : s ≠ 0) :
    horocycleSpeedNorm s ≠ 0 := by
  apply ne_of_gt
  change 0 < |s|
  exact abs_pos.mpr hs

/-- Exact match between the speed-normalized quotient observable and the
even power of the unary `C` coordinate along the frame orbit. -/
theorem
    gammaTwoScaledH4SquareNormPower_eq_unaryC_norm_pow
    {z : ℝ → UnaryModularState ℂ}
    {T : ℝ → ℍ}
    (hz :
      IsScaledUnaryModularTrajectory
        modularIndependentVariableClock z)
    (hB : ∀ t, UnaryModularState.B (z t) ≠ 0)
    (hlambda :
      ∀ t,
        UnaryModularState.lambdaCoordinate (z t) =
          canonicalLambda (T t))
    (g : RealModularFrame) (s : ℝ)
    (hframe :
      ∀ t,
        T t =
          realModularFrameBasePoint
            (g * upperUnipotent (s * t)))
    (K : ℕ) (t : ℝ) :
    gammaTwoScaledH4SquareNormPower
        (horocycleSpeedNorm s) K
        (scaledGammaTwoHorocycleFlow s t
          (gammaTwoFrameQuotientMk g)) =
      ‖(z t).C‖ ^ (2 * K) := by
  rw [scaledGammaTwoHorocycleFlow_apply,
    gammaTwoHorocycleFlow_mk,
    gammaTwoScaledH4SquareNormPower_mk]
  rw [horocycleSpeedNorm_coe]
  rw [unaryC_norm_eq_realFrameHorocycle_amplitude
    hz hB hlambda g s hframe t]
  rfl

end

end HGAS.Modular
