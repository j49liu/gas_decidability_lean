import HGAS.Accumulator.PolynomialDegrees
import HGAS.Compactification.MixedCentralPolynomialComputability
import Mathlib.Tactic

/-!
# Finite-code compactification and accumulator pipeline

This module composes the two paper-exact sparse compilers:

1. mixed central compactification of the affine source blocks, with common
   slowdown `f = ∏ᵦ wᵦᴹ`;
2. one-point stereographic compactification of the complete vector drift
   accumulator.

For a rational scale `κ` and an affine drift observable `h`, the emitted
accumulator velocity is the polynomial code of

```
                       g = κ f h.
```

It also emits the strict-sign reward

```
                 R = W + 2 ∏ᵦ wᵦ² - 1 - ε,
```

where `W` is the stereographic accumulator coordinate.  The evaluation
theorems below prove these identities literally at every mixed central
chart point.  Thus Sections 10 and 11 are connected at finite-syntax
level; no semantic polynomial equality or hidden simplification is used
by the compiler.
-/

namespace HGAS

open _root_.MvPolynomial
open scoped BigOperators

namespace CompactAccumulatorPipelineCode

variable {n k l m : ℕ}

/-- Centrally compactified base field. -/
def baseFieldCode
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (P : PolynomialFieldCode n) :
    PolynomialFieldCode (n + k) :=
  MixedCentralPolynomialCode.fieldCode layout M P

/-- Polynomial code of one slowed drift coordinate `κ f hᵢ`. -/
def slowedDriftCode
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (κ : RationalCode)
    (h : Fin m → PolynomialCode n) (i : Fin m) :
    PolynomialCode (n + k) :=
  PolynomialCode.mul
    (PolynomialCode.constant κ)
    (MixedCentralPolynomialCode.homogenize layout M (h i))

/-- Complete centrally compactified source with one vector accumulator
sphere adjoined. -/
def fieldCode
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (h : Fin m → PolynomialCode n) :
    PolynomialFieldCode ((n + k) + (m + 1)) :=
  AccumulatorPolynomialCode.fieldCode
    (baseFieldCode layout M P)
    (slowedDriftCode layout M κ h)

/-- Code of `∏ᵦ wᵦ²` in the mixed-central base variables. -/
def centralWeightProductCode :
    PolynomialCode (n + k) :=
  (List.ofFn fun b : Fin k ↦
    PolynomialCode.pow
      (PolynomialCode.varCode
        (MixedCentralPolynomialCode.wIndex (n := n) b)) 2).foldr
      PolynomialCode.mul PolynomialCode.one

/-- The central weight product embedded past the accumulator variables. -/
def liftedCentralWeightProductCode :
    PolynomialCode ((n + k) + (m + 1)) :=
  AccumulatorPolynomialCode.liftBase
    (m := m) (centralWeightProductCode (n := n) (k := k))

/-- Exact strict-sign reward
`W + 2 W₀ - 1 - ε` on the final compact source. -/
def rewardCode
    (ε : RationalCode) :
    PolynomialCode ((n + k) + (m + 1)) :=
  PolynomialCode.sub
    (PolynomialCode.add
      (PolynomialCode.varCode
        (AccumulatorPolynomialCode.wIndex (n + k) m))
      (PolynomialCode.mul
        (PolynomialCode.constant (RationalCode.ofNat 2))
        (liftedCentralWeightProductCode
          (n := n) (k := k) (m := m))))
    (PolynomialCode.add PolynomialCode.one
      (PolynomialCode.constant ε))

/-! ## Exact chart semantics -/

/-- The coded drift is exactly `κ f hᵢ`. -/
theorem eval₂Hom_slowedDriftCode_scaledChart
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (κ : RationalCode)
    (h : Fin m → PolynomialCode n)
    (hh :
      ∀ i,
        MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
          layout M (h i))
    (i : Fin m) (w : Fin k → ℝ) (z : Fin n → ℝ) :
    eval₂Hom (algebraMap ℚ ℝ)
        (MixedCentralPolynomialCode.scaledChartPoint layout w z)
        (PolynomialCode.decode
          (slowedDriftCode layout M κ h i)) =
      (RationalCode.decode κ : ℝ) *
        MixedCentralPolynomialCode.slowdown M w *
          eval₂Hom (algebraMap ℚ ℝ) z
            (PolynomialCode.decode (h i)) := by
  simp only [slowedDriftCode,
    PolynomialCode.decode_mul_code,
    PolynomialCode.decode_constant, map_mul,
    eval₂Hom_C]
  rw [MixedCentralPolynomialCode.eval₂Hom_homogenize_scaledChart
    layout M (h i) (hh i) w z]
  have hκ :
      (algebraMap ℚ ℝ) κ.decode = (κ.decode : ℝ) := by
    rfl
  rw [hκ]
  ring

/-- Base coordinates of the composed compiler retain the exact mixed
central field semantics. -/
theorem eval₂Hom_fieldCode_base_scaledChart
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (hP :
      ∀ j,
        MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
          layout M (P j))
    (h : Fin m → PolynomialCode n)
    (q : Fin (n + k))
    (w : Fin k → ℝ) (z : Fin n → ℝ)
    (u : Fin m → ℝ) (W : ℝ) :
    eval₂Hom (algebraMap ℚ ℝ)
        (AccumulatorPolynomialCode.combinedPoint
          (MixedCentralPolynomialCode.scaledChartPoint layout w z)
          u W)
        (PolynomialCode.decode
          (fieldCode layout M κ P h
            (AccumulatorPolynomialCode.baseIndex
              (n := n + k) (m := m) q))) =
      MixedCentralPolynomialCode.mixedAmbientField
        layout (MixedCentralPolynomialCode.slowdown M w) w
        (MixedCentralPolynomialCode.scaledSourcePoint layout w z)
        (fun i ↦
          eval₂Hom (algebraMap ℚ ℝ) z
            (PolynomialCode.decode (P i))) q := by
  rw [fieldCode,
    AccumulatorPolynomialCode.eval₂Hom_fieldCode_base]
  exact
    MixedCentralPolynomialCode.eval₂Hom_fieldCode_scaledChart
      layout M P hP q w z

/-- Accumulator vector coordinates realize the compactified translation
field driven by the literal slowed drift. -/
theorem eval₂Hom_fieldCode_u_scaledChart
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (h : Fin m → PolynomialCode n)
    (hh :
      ∀ i,
        MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
          layout M (h i))
    (w : Fin k → ℝ) (z : Fin n → ℝ)
    (u : Fin m → ℝ) (W : ℝ) (i : Fin m) :
    eval₂Hom (algebraMap ℚ ℝ)
        (AccumulatorPolynomialCode.combinedPoint
          (MixedCentralPolynomialCode.scaledChartPoint layout w z)
          u W)
        (PolynomialCode.decode
          (fieldCode layout M κ P h
            (AccumulatorPolynomialCode.uIndex
              (n := n + k) i))) =
      accumulatorUField u W
        (fun j ↦
          (RationalCode.decode κ : ℝ) *
            MixedCentralPolynomialCode.slowdown M w *
              eval₂Hom (algebraMap ℚ ℝ) z
                (PolynomialCode.decode (h j))) i := by
  rw [fieldCode,
    AccumulatorPolynomialCode.eval₂Hom_fieldCode_u]
  congr 1
  funext j
  exact
    eval₂Hom_slowedDriftCode_scaledChart
      layout M κ h hh j w z

/-- The stereographic scalar coordinate has the matching compactified
translation equation. -/
theorem eval₂Hom_fieldCode_w_scaledChart
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (κ : RationalCode)
    (P : PolynomialFieldCode n)
    (h : Fin m → PolynomialCode n)
    (hh :
      ∀ i,
        MixedCentralPolynomialCode.TermsAffineBlockDegreeLE
          layout M (h i))
    (w : Fin k → ℝ) (z : Fin n → ℝ)
    (u : Fin m → ℝ) (W : ℝ) :
    eval₂Hom (algebraMap ℚ ℝ)
        (AccumulatorPolynomialCode.combinedPoint
          (MixedCentralPolynomialCode.scaledChartPoint layout w z)
          u W)
        (PolynomialCode.decode
          (fieldCode layout M κ P h
            (AccumulatorPolynomialCode.wIndex (n + k) m))) =
      accumulatorWField u W
        (fun j ↦
          (RationalCode.decode κ : ℝ) *
            MixedCentralPolynomialCode.slowdown M w *
              eval₂Hom (algebraMap ℚ ℝ) z
                (PolynomialCode.decode (h j))) := by
  rw [fieldCode,
    AccumulatorPolynomialCode.eval₂Hom_fieldCode_w]
  congr 1
  funext j
  exact
    eval₂Hom_slowedDriftCode_scaledChart
      layout M κ h hh j w z

/-- Evaluation of the central weight product. -/
theorem eval₂Hom_centralWeightProductCode
    (w : Fin k → ℝ) (z : Fin n → ℝ)
    (layout : Fin n → Fin k ⊕ Fin l) :
    eval₂Hom (algebraMap ℚ ℝ)
        (MixedCentralPolynomialCode.scaledChartPoint layout w z)
        (PolynomialCode.decode
          (centralWeightProductCode (n := n) (k := k))) =
      ∏ b, w b ^ 2 := by
  have hfold :
      ∀ ps : List (PolynomialCode (n + k)),
        eval₂Hom (algebraMap ℚ ℝ)
            (MixedCentralPolynomialCode.scaledChartPoint layout w z)
            (PolynomialCode.decode
              (ps.foldr PolynomialCode.mul PolynomialCode.one)) =
          (ps.map fun p ↦
            eval₂Hom (algebraMap ℚ ℝ)
              (MixedCentralPolynomialCode.scaledChartPoint layout w z)
              (PolynomialCode.decode p)).prod := by
    intro ps
    induction ps with
    | nil => simp
    | cons p ps ih =>
        simp only [List.foldr_cons,
          PolynomialCode.decode_mul_code, map_mul,
          List.map_cons, List.prod_cons]
        rw [ih]
  rw [centralWeightProductCode, hfold, List.map_ofFn,
    List.prod_ofFn]
  simp

/-- The emitted reward evaluates literally to
`W + 2∏wᵦ² - 1 - ε`. -/
theorem eval₂Hom_rewardCode
    (ε : RationalCode)
    (layout : Fin n → Fin k ⊕ Fin l)
    (w : Fin k → ℝ) (z : Fin n → ℝ)
    (u : Fin m → ℝ) (W : ℝ) :
    eval₂Hom (algebraMap ℚ ℝ)
        (AccumulatorPolynomialCode.combinedPoint
          (MixedCentralPolynomialCode.scaledChartPoint layout w z)
          u W)
        (PolynomialCode.decode
          (rewardCode (n := n) (k := k) (m := m) ε)) =
      W + 2 * (∏ b, w b ^ 2) - 1 -
        (RationalCode.decode ε : ℝ) := by
  simp only [rewardCode, PolynomialCode.decode_sub_code,
    PolynomialCode.decode_add_code,
    PolynomialCode.decode_mul_code,
    PolynomialCode.decode_varCode,
    PolynomialCode.decode_constant,
    PolynomialCode.decode_one_code,
    map_sub, map_add, map_mul, map_one,
    eval₂Hom_X', eval₂Hom_C,
    AccumulatorPolynomialCode.combinedPoint_wIndex,
    RationalCode.decode_ofNat]
  unfold liftedCentralWeightProductCode
  rw [AccumulatorPolynomialCode.eval₂Hom_liftBase,
    eval₂Hom_centralWeightProductCode w z layout]
  have hε :
      (algebraMap ℚ ℝ) ε.decode = (ε.decode : ℝ) := by
    rfl
  rw [hε]
  norm_num
  ring

end CompactAccumulatorPipelineCode

end HGAS
