import HGAS.Compiler.AllAffineCompactSourceChart
import HGAS.Dynamics.StateTimeChange
import Mathlib.Tactic

/-!
# Recovering the all-affine source trajectory

This module proves the dynamical counterpart of
`AllAffineCompactSourceChart`.

For a one-block compactification with clearing exponent `2K`, every orbit
in the invariant finite chart recovers an affine curve

```
                         z(t) = x(t) / w(t)
```

which solves the autonomous time-changed equation

```
             z' = a_K(z) P(z),
             a_K(z) = (1 + ‖z‖²)⁻ᴷ.
```

The proof uses the quotient-rule theorem from `CentralSphere`; the only
compiler-specific work is to identify the literal emitted coordinate
velocities with the central compactification field.
-/

namespace HGAS

open _root_.MvPolynomial
open Set

noncomputable section

namespace CompactAccumulatorPipelineCode

namespace AllAffineCompactSourceTrajectory

open AllAffineCompactSourceChart

variable {n m : ℕ}

/-- In the one-block layout the affine-block dot product is the ordinary
finite dot product. -/
theorem affineBlockDot_eq_dot
    (x p : Fin n → ℝ) :
    MixedCentralPolynomialCode.affineBlockDot
        (layout n) x p 0 =
      dot x p := by
  simp [MixedCentralPolynomialCode.affineBlockDot,
    dot]

/-- The abstract product slowdown has one factor. -/
theorem slowdown_eq_weight_pow
    (M : ℕ) (w : Fin 1 → ℝ) :
    MixedCentralPolynomialCode.slowdown M w = w 0 ^ M := by
  simp [MixedCentralPolynomialCode.slowdown]

/-- The mixed old-coordinate field is the reusable one-block central
field. -/
theorem mixedXField_eq_centralCompactXField
    (f w : ℝ) (x p : Fin n → ℝ) :
    MixedCentralPolynomialCode.mixedXField
        (layout n) f (fun _ ↦ w) x p =
      centralCompactXField f w x p := by
  funext j
  simp [MixedCentralPolynomialCode.mixedXField,
    centralCompactXField, affineBlockDot_eq_dot]

/-- The mixed chart-coordinate field is the reusable central scalar
field. -/
theorem mixedWField_eq_centralCompactWField
    (f w : ℝ) (x p : Fin n → ℝ) :
    MixedCentralPolynomialCode.mixedWField
        (layout n) f (fun _ ↦ w) x p 0 =
      centralCompactWField f w x p := by
  simp [MixedCentralPolynomialCode.mixedWField,
    centralCompactWField, affineBlockDot_eq_dot]

variable
  (K : ℕ) (κ : RationalCode)
  (P : PolynomialFieldCode n)
  (h : Fin m → PolynomialCode n)

variable
  (hP :
    ∀ j,
      MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
        (layout n) (2 * K) (P j))

include hP

/-- Literal velocity of one old compact coordinate, expressed in the
canonical central field at the recovered affine point. -/
theorem realize_fieldCode_oldPoint
    (v : FiniteSourceSpace n m) (j : Fin n) :
    PolynomialFieldCode.realize
        (fieldCode (layout n) (2 * K) κ P h) v.1.1
        (AccumulatorPolynomialCode.baseIndex
          (m := m)
          (MixedCentralPolynomialCode.xIndex (k := 1) j)) =
      centralCompactXField
        (affineSpeed K (affinePoint v))
        (weight v.1) (oldPoint v.1)
        (PolynomialFieldCode.realize P (affinePoint v)) j := by
  rw [realize_fieldCode_baseIndex]
  rw [PolynomialFieldCode.realize_apply, baseFieldCode]
  rw [← scaledChartPoint_affinePoint v]
  rw [MixedCentralPolynomialCode.eval₂Hom_fieldCode_scaledChart
    (layout n) (2 * K) P hP
    (MixedCentralPolynomialCode.xIndex (k := 1) j)
    (fun _ ↦ weight v.1) (affinePoint v)]
  simp only [MixedCentralPolynomialCode.mixedAmbientField,
    MixedCentralPolynomialCode.finSumFinEquiv_symm_xIndex]
  rw [slowdown_eq_weight_pow, weight_evenPow_eq_affineSpeed]
  rw [mixedXField_eq_centralCompactXField]
  rw [scaledSourcePoint_affinePoint]
  rfl

/-- Literal velocity of the unique central coordinate. -/
theorem realize_fieldCode_weight
    (v : FiniteSourceSpace n m) :
    PolynomialFieldCode.realize
        (fieldCode (layout n) (2 * K) κ P h) v.1.1
        (AccumulatorPolynomialCode.baseIndex
          (m := m)
          (MixedCentralPolynomialCode.wIndex (n := n) 0)) =
      centralCompactWField
        (affineSpeed K (affinePoint v))
        (weight v.1) (oldPoint v.1)
        (PolynomialFieldCode.realize P (affinePoint v)) := by
  rw [realize_fieldCode_baseIndex]
  rw [PolynomialFieldCode.realize_apply, baseFieldCode]
  rw [← scaledChartPoint_affinePoint v]
  rw [MixedCentralPolynomialCode.eval₂Hom_fieldCode_scaledChart
    (layout n) (2 * K) P hP
    (MixedCentralPolynomialCode.wIndex (n := n) 0)
    (fun _ ↦ weight v.1) (affinePoint v)]
  simp only [MixedCentralPolynomialCode.mixedAmbientField,
    MixedCentralPolynomialCode.finSumFinEquiv_symm_wIndex]
  rw [slowdown_eq_weight_pow, weight_evenPow_eq_affineSpeed]
  rw [scaledSourcePoint_affinePoint]
  exact mixedWField_eq_centralCompactWField
    (affineSpeed K (affinePoint v))
    (weight v.1) (oldPoint v.1)
    (PolynomialFieldCode.realize P (affinePoint v))

variable
  (ϕ : Flow ℝ (SourceSpace n m))
  (hcurve :
    ∀ v,
      IsIntegralCurve
        (fun t ↦ (ϕ t v).1)
        (fun _ x ↦
          PolynomialFieldCode.realize
            (fieldCode (layout n) (2 * K) κ P h) x))
  (hinv :
    IsInvariant ϕ (sourceFiniteInteriorSet (m := m) (layout n)))

include hcurve

/-- The recovered affine coordinate has the exact intrinsic slowed
velocity along every finite-chart orbit. -/
theorem affinePoint_hasDerivAt
    (v : FiniteSourceSpace n m) (t : ℝ) :
    HasDerivAt
      (fun s ↦ affinePoint ((ϕ.restrict hinv) s v))
      (affineSpeed K
          (affinePoint ((ϕ.restrict hinv) t v)) •
        PolynomialFieldCode.realize P
          (affinePoint ((ϕ.restrict hinv) t v))) t := by
  let q : ℝ → FiniteCentralChart n :=
    fun s ↦ finiteCentralChartPoint ((ϕ.restrict hinv) s v)
  let f : ℝ → ℝ :=
    fun s ↦ affineSpeed K
      (affinePoint ((ϕ.restrict hinv) s v))
  let p : ℝ → (Fin n → ℝ) :=
    fun s ↦ PolynomialFieldCode.realize P
      (affinePoint ((ϕ.restrict hinv) s v))
  have hX :
      ∀ j,
        HasDerivAt
          (fun s ↦ (q s).1.1.1 j)
          (centralCompactXField
            (f t) (q t).1.1.2 (q t).1.1.1 (p t) j) t := by
    intro j
    have hcoord :=
      (hasDerivAt_pi.mp (hcurve v.1 t))
        (AccumulatorPolynomialCode.baseIndex
          (m := m)
          (MixedCentralPolynomialCode.xIndex (k := 1) j))
    have hvelocity :=
      realize_fieldCode_oldPoint K κ P h hP
        ((ϕ.restrict hinv) t v) j
    have hcoord' := hcoord.congr_deriv (by
      simpa only [Flow.coe_restrict_apply] using hvelocity)
    simpa only [q, f, p, finiteCentralChartPoint,
      centralSpherePoint_x, centralSpherePoint_w,
      Flow.coe_restrict_apply, oldPoint, sourceOldPoint,
      sourceBasePoint] using hcoord'
  have hW :
      HasDerivAt
        (fun s ↦ (q s).1.1.2)
        (centralCompactWField
          (f t) (q t).1.1.2 (q t).1.1.1 (p t)) t := by
    have hcoord :=
      (hasDerivAt_pi.mp (hcurve v.1 t))
        (AccumulatorPolynomialCode.baseIndex
          (m := m)
          (MixedCentralPolynomialCode.wIndex (n := n) 0))
    have hvelocity :=
      realize_fieldCode_weight K κ P h hP
        ((ϕ.restrict hinv) t v)
    have hcoord' := hcoord.congr_deriv (by
      simpa only [Flow.coe_restrict_apply] using hvelocity)
    simpa only [q, f, p, finiteCentralChartPoint,
      centralSpherePoint_x, centralSpherePoint_w,
      Flow.coe_restrict_apply, weight, sourceChartWeight,
      sourceBasePoint] using hcoord'
  have hchart :=
    centralChartCoordinate_hasDerivAt q f p t hX hW
  rw [hasDerivAt_pi]
  intro j
  simpa only [q, f, p, affinePoint, Pi.smul_apply,
    smul_eq_mul] using hchart j

/-- Vector-field form: the finite-chart affine observation solves
`z' = a_K(z) P(z)` at every real time. -/
theorem affinePoint_isIntegralCurve
    (v : FiniteSourceSpace n m) :
    IsIntegralCurve
      (fun t ↦ affinePoint ((ϕ.restrict hinv) t v))
      (fun _ z ↦
        timeScaledField (affineSpeed K)
          (PolynomialFieldCode.realize P) z) := by
  intro t
  have hderiv :=
    affinePoint_hasDerivAt K κ P h hP ϕ hcurve hinv v t
  simpa only [timeScaledField] using hderiv

end AllAffineCompactSourceTrajectory

end CompactAccumulatorPipelineCode

end

end HGAS
