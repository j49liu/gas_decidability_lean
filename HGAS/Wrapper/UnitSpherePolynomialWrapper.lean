import HGAS.Wrapper.ParityHomogenizationCode
import HGAS.Wrapper.RadiusCleanup
import HGAS.Wrapper.Reward
import Mathlib.Tactic

/-!
# The rational polynomial product-sphere wrapper on the unit sphere

This is the concrete finite-polynomial layer behind the semantic wrapper
theorem.

The manuscript writes the intermediate construction on the sphere
`q = L`, where `L` is the number of blocks.  The analytic GAS theorem in
this development uses the ordinary Euclidean unit sphere.  Rescaling by
`√L` would introduce irrational coefficients.  Instead we keep the unit
sphere and use the *scaled* squared block radii

```
sᵢ = L ∑_{j in block i} xⱼ².
```

Thus `∑sᵢ=L`, and the intended stratum is still `sᵢ=1` for every block.
For an odd chart degree `D=2m+1`, multiplying the chart polynomials by the
rational integer `L^m` exactly cancels the factor
`z^(D-1)` on the two sheets `L z²=1`.  This is the key normalization that
keeps the entire compiler rational while matching the unit-sphere GAS
bridge.

Coordinates are canonical: coordinate `0` is the projective scalar `z`;
old source coordinate `j : Fin n` becomes `j.succ`.  A function
`sourceBlock : Fin n → Fin k` assigns source coordinates to the `k`
source sphere blocks.  Ambient block zero is the singleton chart block,
and source block `i` becomes ambient block `i.succ`.

All polynomial constructions below operate on `PolynomialCode`, hence on
literal finite rational syntax.
-/

namespace HGAS

open _root_.MvPolynomial
open scoped BigOperators

noncomputable section

namespace UnitSpherePolynomialWrapper

variable {n k : ℕ}

/-- Evaluation commutes with the finite `sumCodes (List.ofFn ...)`
pattern used throughout the compiler. -/
theorem eval_sumCodes_ofFn
    {m N : ℕ} (p : Fin m → PolynomialCode N)
    (x : Fin N → ℝ) :
    eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode
          (PolynomialCode.sumCodes (List.ofFn p))) =
      ∑ i, eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (p i)) := by
  rw [PolynomialCode.decode_sumCodes, List.map_ofFn,
    List.sum_ofFn, map_sum]
  rfl

/-- Number of ambient blocks: one chart block plus `k` source blocks. -/
def blockCount (k : ℕ) : ℕ :=
  k + 1

/-- The canonical ambient block of a coordinate. -/
def ambientBlock (sourceBlock : Fin n → Fin k) :
    Fin (n + 1) → Fin (k + 1) :=
  Fin.cases 0 (fun j ↦ (sourceBlock j).succ)

@[simp]
theorem ambientBlock_zero (sourceBlock : Fin n → Fin k) :
    ambientBlock sourceBlock 0 = 0 :=
  rfl

@[simp]
theorem ambientBlock_succ
    (sourceBlock : Fin n → Fin k) (j : Fin n) :
    ambientBlock sourceBlock j.succ = (sourceBlock j).succ :=
  rfl

/-- Every finite family is the sum of its coordinate-block restrictions. -/
theorem sum_block_partition
    (sourceBlock : Fin n → Fin k)
    (f : Fin (n + 1) → ℝ) :
    (∑ b, ∑ j,
      if ambientBlock sourceBlock j = b then f j else 0) =
      ∑ j, f j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [eq_comm, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte]

/-- Raw squared norm of one ambient coordinate block. -/
def rawBlockNormSq
    (sourceBlock : Fin n → Fin k)
    (x : Fin (n + 1) → ℝ) (b : Fin (k + 1)) : ℝ :=
  ∑ j, if ambientBlock sourceBlock j = b then x j ^ 2 else 0

/-- Scaled squared block radius `sᵢ=L‖vᵢ‖²`. -/
def scaledBlockRadius
    (sourceBlock : Fin n → Fin k)
    (x : Fin (n + 1) → ℝ) (b : Fin (k + 1)) : ℝ :=
  (k + 1 : ℝ) * rawBlockNormSq sourceBlock x b

/-- The block radii sum to `L` on the Euclidean unit sphere. -/
theorem sum_scaledBlockRadius
    (sourceBlock : Fin n → Fin k)
    (x : Fin (n + 1) → ℝ) :
    ∑ b, scaledBlockRadius sourceBlock x b =
      (k + 1 : ℝ) * normSq x := by
  simp only [scaledBlockRadius, ← Finset.mul_sum, rawBlockNormSq]
  congr 1
  rw [sum_block_partition]
  simp [normSq, dot, pow_two]

/-- Sparse code for the unscaled squared norm of one block. -/
def rawBlockNormSqCode
    (sourceBlock : Fin n → Fin k) (b : Fin (k + 1)) :
    PolynomialCode (n + 1) :=
  PolynomialCode.sumCodes
    (List.ofFn fun j : Fin (n + 1) ↦
      if ambientBlock sourceBlock j = b then
        PolynomialCode.pow (PolynomialCode.varCode j) 2
      else
        PolynomialCode.zero)

/-- Sparse code for `sᵢ=L‖vᵢ‖²`. -/
def scaledBlockRadiusCode
    (sourceBlock : Fin n → Fin k) (b : Fin (k + 1)) :
    PolynomialCode (n + 1) :=
  PolynomialCode.mul
    (PolynomialCode.constant (RationalCode.ofNat (k + 1)))
    (rawBlockNormSqCode sourceBlock b)

@[simp]
theorem eval_rawBlockNormSqCode
    (sourceBlock : Fin n → Fin k)
    (x : Fin (n + 1) → ℝ) (b : Fin (k + 1)) :
    eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode
          (rawBlockNormSqCode sourceBlock b)) =
      rawBlockNormSq sourceBlock x b := by
  rw [rawBlockNormSqCode, eval_sumCodes_ofFn, rawBlockNormSq]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : ambientBlock sourceBlock j = b
  · simp [hj]
  · simp [hj]

@[simp]
theorem eval_scaledBlockRadiusCode
    (sourceBlock : Fin n → Fin k)
    (x : Fin (n + 1) → ℝ) (b : Fin (k + 1)) :
    eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode
          (scaledBlockRadiusCode sourceBlock b)) =
      scaledBlockRadius sourceBlock x b := by
  simp only [scaledBlockRadiusCode, PolynomialCode.decode_mul_code,
    map_mul, PolynomialCode.decode_constant,
    RationalCode.decode_ofNat, map_natCast]
  rw [eval_rawBlockNormSqCode]
  rw [scaledBlockRadius]
  norm_num

/-- Integer chart normalization `L^((D-1)/2)`. -/
def chartScale (k D : ℕ) : ℕ :=
  (k + 1) ^ ((D - 1) / 2)

/-- Homogenize one source polynomial into the chart and apply the rational
unit-sphere normalization. -/
def chartPolynomialCode
    (k D : ℕ) (p : PolynomialCode n) :
    PolynomialCode (n + 1) :=
  PolynomialCode.mul
    (PolynomialCode.constant
      (RationalCode.ofNat (chartScale k D)))
    (PolynomialCode.twoSheetHomogenize D p)

/-- Chart field.  Its zeroth component is zero. -/
def chartFieldCode
    (k D : ℕ) (P : PolynomialFieldCode n) :
    PolynomialFieldCode (n + 1) :=
  Fin.cases PolynomialCode.zero
    (fun j ↦ chartPolynomialCode k D (P j))

/-- Chart observable, homogenized to the even degree `D-1`. -/
def chartRewardCode
    (k D : ℕ) (a : PolynomialCode n) :
    PolynomialCode (n + 1) :=
  PolynomialCode.mul
    (PolynomialCode.constant
      (RationalCode.ofNat (chartScale k D)))
    (PolynomialCode.twoSheetHomogenize (D - 1) a)

@[simp]
theorem eval_chartPolynomialCode_scaled
    (D : ℕ) (p : PolynomialCode n)
    (hp : PolynomialCode.TermsDegreeLE D p)
    (z : ℝ) (y : Fin n → ℝ) :
    eval₂Hom (algebraMap ℚ ℝ)
        (PolynomialCode.unitChartPoint z (z • y))
        (PolynomialCode.decode (chartPolynomialCode k D p)) =
      (chartScale k D : ℝ) * z ^ D *
        eval₂Hom (algebraMap ℚ ℝ) y
          (PolynomialCode.decode p) := by
  simp only [chartPolynomialCode, PolynomialCode.decode_mul_code,
    map_mul, PolynomialCode.decode_constant,
    RationalCode.decode_ofNat, map_natCast]
  rw [PolynomialCode.eval₂Hom_twoSheetHomogenize_scaledChart
    D p hp z y]
  ring

@[simp]
theorem eval_chartFieldCode_zero
    (D : ℕ) (P : PolynomialFieldCode n)
    (x : Fin (n + 1) → ℝ) :
    PolynomialFieldCode.realize (chartFieldCode k D P) x 0 = 0 := by
  simp [PolynomialFieldCode.realize_apply, chartFieldCode]

@[simp]
theorem eval_chartFieldCode_succ_scaled
    (D : ℕ) (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j))
    (z : ℝ) (y : Fin n → ℝ) (j : Fin n) :
    PolynomialFieldCode.realize (chartFieldCode k D P)
        (PolynomialCode.unitChartPoint z (z • y)) j.succ =
      (chartScale k D : ℝ) * z ^ D *
        PolynomialFieldCode.realize P y j := by
  exact eval_chartPolynomialCode_scaled D (P j) (hP j) z y

@[simp]
theorem eval_chartRewardCode_scaled
    (D : ℕ) (a : PolynomialCode n)
    (ha : PolynomialCode.TermsDegreeLE (D - 1) a)
    (z : ℝ) (y : Fin n → ℝ) :
    eval₂Hom (algebraMap ℚ ℝ)
        (PolynomialCode.unitChartPoint z (z • y))
        (PolynomialCode.decode (chartRewardCode k D a)) =
      (chartScale k D : ℝ) * z ^ (D - 1) *
        eval₂Hom (algebraMap ℚ ℝ) y
          (PolynomialCode.decode a) := by
  simp only [chartRewardCode, PolynomialCode.decode_mul_code,
    map_mul, PolynomialCode.decode_constant,
    RationalCode.decode_ofNat, map_natCast]
  rw [PolynomialCode.eval₂Hom_twoSheetHomogenize_scaledChart
    (D - 1) a ha z y]
  ring

/-- On either normalized sheet, the rational chart factor is exactly one.
This is where oddness of `D` is used. -/
theorem chartScale_mul_zpow_eq_one
    (D : ℕ) (hDodd : D % 2 = 1)
    (z : ℝ) (hz : (k + 1 : ℝ) * z ^ 2 = 1) :
    (chartScale k D : ℝ) * z ^ (D - 1) = 1 := by
  let m := (D - 1) / 2
  have hdegree : D - 1 = 2 * m := by
    have hmod : (D - 1) % 2 = 0 := by omega
    have hdivision := Nat.mod_add_div (D - 1) 2
    dsimp [m]
    omega
  simp only [chartScale, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  change ((k + 1 : ℝ) ^ m) * z ^ (D - 1) = 1
  calc
    (k + 1 : ℝ) ^ m * z ^ (D - 1) =
        (k + 1 : ℝ) ^ m * z ^ (2 * m) := by rw [hdegree]
    _ = ((k + 1 : ℝ) * z ^ 2) ^ m := by
      rw [pow_mul, mul_pow]
    _ = 1 := by rw [hz, one_pow]

/-- Exact source chart velocity on both normalized sheets. -/
theorem eval_chartFieldCode_succ_on_sheet
    (D : ℕ) (hDodd : D % 2 = 1)
    (P : PolynomialFieldCode n)
    (hP : ∀ j, PolynomialCode.TermsDegreeLE D (P j))
    (z : ℝ) (hz : (k + 1 : ℝ) * z ^ 2 = 1)
    (y : Fin n → ℝ) (j : Fin n) :
    PolynomialFieldCode.realize (chartFieldCode k D P)
        (PolynomialCode.unitChartPoint z (z • y)) j.succ =
      z * PolynomialFieldCode.realize P y j := by
  rw [eval_chartFieldCode_succ_scaled D P hP z y j]
  have hfactor := chartScale_mul_zpow_eq_one
    (k := k) D hDodd z hz
  have hzpow : z ^ D = z ^ (D - 1) * z := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ D)]
  calc
    (chartScale k D : ℝ) * z ^ D *
          PolynomialFieldCode.realize P y j =
        ((chartScale k D : ℝ) * z ^ (D - 1)) * z *
          PolynomialFieldCode.realize P y j := by
            rw [hzpow]
            ring
    _ = z * PolynomialFieldCode.realize P y j := by
      rw [hfactor]
      ring

/-- The normalized chart reward equals the source reward on both sheets. -/
theorem eval_chartRewardCode_on_sheet
    (D : ℕ) (hDodd : D % 2 = 1)
    (a : PolynomialCode n)
    (ha : PolynomialCode.TermsDegreeLE (D - 1) a)
    (z : ℝ) (hz : (k + 1 : ℝ) * z ^ 2 = 1)
    (y : Fin n → ℝ) :
    eval₂Hom (algebraMap ℚ ℝ)
        (PolynomialCode.unitChartPoint z (z • y))
        (PolynomialCode.decode (chartRewardCode k D a)) =
      eval₂Hom (algebraMap ℚ ℝ) y
        (PolynomialCode.decode a) := by
  rw [eval_chartRewardCode_scaled D a ha z y,
    chartScale_mul_zpow_eq_one (k := k) D hDodd z hz,
    one_mul]

/-! ## Block tangentialization -/

/-- Coded block dot product `∑_{j in b} Xⱼ Πⱼ`. -/
def blockDotCode
    (sourceBlock : Fin n → Fin k)
    (PiField : PolynomialFieldCode (n + 1))
    (b : Fin (k + 1)) : PolynomialCode (n + 1) :=
  PolynomialCode.sumCodes
    (List.ofFn fun j : Fin (n + 1) ↦
      if ambientBlock sourceBlock j = b then
        PolynomialCode.mul (PolynomialCode.varCode j) (PiField j)
      else
        PolynomialCode.zero)

/-- Semantic block dot product. -/
def blockDotValue
    (sourceBlock : Fin n → Fin k)
    (x p : Fin (n + 1) → ℝ) (b : Fin (k + 1)) : ℝ :=
  ∑ j, if ambientBlock sourceBlock j = b then x j * p j else 0

@[simp]
theorem eval_blockDotCode
    (sourceBlock : Fin n → Fin k)
    (PiField : PolynomialFieldCode (n + 1))
    (x : Fin (n + 1) → ℝ) (b : Fin (k + 1)) :
    eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (blockDotCode sourceBlock PiField b)) =
      blockDotValue sourceBlock x
        (PolynomialFieldCode.realize PiField x) b := by
  rw [blockDotCode, eval_sumCodes_ofFn]
  simp only [blockDotValue]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : ambientBlock sourceBlock j = b
  · simp [hj, PolynomialFieldCode.realize_apply]
  · simp [hj]

/-- Division-free block tangentialization adapted to scaled radii:

`Tⱼ = s_b Πⱼ - L (v_b·Π_b) Xⱼ`.
-/
def tangentFieldCode
    (sourceBlock : Fin n → Fin k)
    (PiField : PolynomialFieldCode (n + 1)) :
    PolynomialFieldCode (n + 1) :=
  fun j ↦
    let b := ambientBlock sourceBlock j
    PolynomialCode.sub
      (PolynomialCode.mul
        (scaledBlockRadiusCode sourceBlock b) (PiField j))
      (PolynomialCode.mul
        (PolynomialCode.mul
          (PolynomialCode.constant (RationalCode.ofNat (k + 1)))
          (blockDotCode sourceBlock PiField b))
        (PolynomialCode.varCode j))

@[simp]
theorem eval_tangentFieldCode
    (sourceBlock : Fin n → Fin k)
    (PiField : PolynomialFieldCode (n + 1))
    (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    PolynomialFieldCode.realize (tangentFieldCode sourceBlock PiField) x j =
      scaledBlockRadius sourceBlock x
          (ambientBlock sourceBlock j) *
        PolynomialFieldCode.realize PiField x j -
      (k + 1 : ℝ) *
        blockDotValue sourceBlock x
          (PolynomialFieldCode.realize PiField x)
          (ambientBlock sourceBlock j) * x j := by
  rw [PolynomialFieldCode.realize_apply]
  simp only [tangentFieldCode, PolynomialCode.decode_sub_code,
    map_sub, PolynomialCode.decode_mul_code, map_mul,
    PolynomialCode.decode_constant, RationalCode.decode_ofNat,
    map_natCast, PolynomialCode.decode_varCode, eval₂Hom_X']
  rw [eval_scaledBlockRadiusCode, eval_blockDotCode]
  simp only [PolynomialFieldCode.realize_apply]
  norm_cast

/-- Tangentialization has zero dot product inside every block. -/
theorem blockDotValue_tangentFieldCode_eq_zero
    (sourceBlock : Fin n → Fin k)
    (PiField : PolynomialFieldCode (n + 1))
    (x : Fin (n + 1) → ℝ) (b : Fin (k + 1)) :
    blockDotValue sourceBlock x
      (PolynomialFieldCode.realize
        (tangentFieldCode sourceBlock PiField) x) b = 0 := by
  classical
  have hrewrite :
      blockDotValue sourceBlock x
          (PolynomialFieldCode.realize
            (tangentFieldCode sourceBlock PiField) x) b =
        scaledBlockRadius sourceBlock x b *
            blockDotValue sourceBlock x
              (PolynomialFieldCode.realize PiField x) b -
          (k + 1 : ℝ) *
            blockDotValue sourceBlock x
              (PolynomialFieldCode.realize PiField x) b *
            rawBlockNormSq sourceBlock x b := by
    rw [blockDotValue, blockDotValue, rawBlockNormSq]
    calc
      (∑ j,
          if ambientBlock sourceBlock j = b then
            x j *
              PolynomialFieldCode.realize
                (tangentFieldCode sourceBlock PiField) x j
          else 0) =
          ∑ j, (
            (if ambientBlock sourceBlock j = b then
              scaledBlockRadius sourceBlock x b *
                (x j * PolynomialFieldCode.realize PiField x j)
            else 0) -
            (if ambientBlock sourceBlock j = b then
              (k + 1 : ℝ) *
                blockDotValue sourceBlock x
                  (PolynomialFieldCode.realize PiField x) b * x j ^ 2
            else 0)) := by
              apply Finset.sum_congr rfl
              intro j _
              by_cases hj : ambientBlock sourceBlock j = b
              · simp only [hj, ↓reduceIte, eval_tangentFieldCode]
                ring
              · simp [hj]
      _ =
          scaledBlockRadius sourceBlock x b *
              (∑ j, if ambientBlock sourceBlock j = b then
                x j * PolynomialFieldCode.realize PiField x j else 0) -
            (k + 1 : ℝ) *
              blockDotValue sourceBlock x
                (PolynomialFieldCode.realize PiField x) b *
              (∑ j, if ambientBlock sourceBlock j = b then
                x j ^ 2 else 0) := by
                  rw [Finset.sum_sub_distrib]
                  congr 1
                  · rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro j _
                    by_cases hj : ambientBlock sourceBlock j = b
                    · simp [hj]
                    · simp [hj]
                  · rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro j _
                    by_cases hj : ambientBlock sourceBlock j = b
                    · simp [hj]
                    · simp [hj]
  rw [hrewrite]
  change
    scaledBlockRadius sourceBlock x b *
        blockDotValue sourceBlock x
          (PolynomialFieldCode.realize PiField x) b -
      (k + 1 : ℝ) *
        blockDotValue sourceBlock x
          (PolynomialFieldCode.realize PiField x) b *
        rawBlockNormSq sourceBlock x b = 0
  simp only [scaledBlockRadius]
  ring

/-! ## Radius cleanup -/

/-- Code of the common radius average
`L⁻¹ ∑ᵢ sᵢ(1-sᵢ)`.  Since `L=k+1`, the denominator-minus-one code is
literally `k`. -/
def radiusAverageCode
    (sourceBlock : Fin n → Fin k) :
    PolynomialCode (n + 1) :=
  PolynomialCode.mul
    (PolynomialCode.constant (((false, 1), k) : RationalCode))
    (PolynomialCode.sumCodes
      (List.ofFn fun b : Fin (k + 1) ↦
        PolynomialCode.mul
          (scaledBlockRadiusCode sourceBlock b)
          (PolynomialCode.sub PolynomialCode.one
            (scaledBlockRadiusCode sourceBlock b))))

@[simp]
theorem decode_inverseBlockCountCode :
    RationalCode.decode (((false, 1), k) : RationalCode) =
      ((k + 1 : ℚ)⁻¹) := by
  rw [RationalCode.decode]
  simp only [SignedMagnitudeCode.decode, Bool.false_eq_true, ↓reduceIte]
  rw [← Rat.natCast_div_eq_divInt]
  simp [div_eq_mul_inv]

/-- Code of `1-sᵢ-f̄`. -/
def radiusDeviationCode
    (sourceBlock : Fin n → Fin k) (b : Fin (k + 1)) :
    PolynomialCode (n + 1) :=
  PolynomialCode.sub
    (PolynomialCode.sub PolynomialCode.one
      (scaledBlockRadiusCode sourceBlock b))
    (radiusAverageCode sourceBlock)

/-- Radial cleanup field `Nⱼ=(1-s_b-f̄)Xⱼ`. -/
def cleanupFieldCode
    (sourceBlock : Fin n → Fin k) :
    PolynomialFieldCode (n + 1) :=
  fun j ↦
    PolynomialCode.mul
      (radiusDeviationCode sourceBlock
        (ambientBlock sourceBlock j))
      (PolynomialCode.varCode j)

@[simp]
theorem eval_radiusAverageCode
    (sourceBlock : Fin n → Fin k)
    (x : Fin (n + 1) → ℝ) :
    eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (radiusAverageCode sourceBlock)) =
      radiusAverage (k + 1 : ℝ)
        (fun b ↦ scaledBlockRadius sourceBlock x b) := by
  simp only [radiusAverageCode, PolynomialCode.decode_mul_code,
    map_mul, PolynomialCode.decode_constant, decode_inverseBlockCountCode,
    eval₂Hom_C, map_inv₀]
  rw [eval_sumCodes_ofFn]
  simp_rw [PolynomialCode.decode_mul_code, map_mul,
    PolynomialCode.decode_sub_code, map_sub,
    PolynomialCode.decode_one_code, map_one,
    eval_scaledBlockRadiusCode]
  rw [radiusAverage]
  norm_cast
  field_simp

@[simp]
theorem eval_radiusDeviationCode
    (sourceBlock : Fin n → Fin k)
    (x : Fin (n + 1) → ℝ) (b : Fin (k + 1)) :
    eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode
          (radiusDeviationCode sourceBlock b)) =
      radiusDeviation (k + 1 : ℝ)
        (fun i ↦ scaledBlockRadius sourceBlock x i) b := by
  simp only [radiusDeviationCode, PolynomialCode.decode_sub_code,
    map_sub, PolynomialCode.decode_one_code, map_one]
  rw [eval_scaledBlockRadiusCode, eval_radiusAverageCode]
  rfl

@[simp]
theorem eval_cleanupFieldCode
    (sourceBlock : Fin n → Fin k)
    (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    PolynomialFieldCode.realize (cleanupFieldCode sourceBlock) x j =
      radiusDeviation (k + 1 : ℝ)
          (fun b ↦ scaledBlockRadius sourceBlock x b)
          (ambientBlock sourceBlock j) * x j := by
  rw [PolynomialFieldCode.realize_apply]
  simp only [cleanupFieldCode, PolynomialCode.decode_mul_code, map_mul,
    PolynomialCode.decode_varCode, eval₂Hom_X']
  rw [eval_radiusDeviationCode]

/-- Raw wrapper angular field `B=T+N`. -/
def rawWrapperFieldCode
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n) :
    PolynomialFieldCode (n + 1) :=
  fun j ↦
    PolynomialCode.add
      (tangentFieldCode sourceBlock (chartFieldCode k D P) j)
      (cleanupFieldCode sourceBlock j)

@[simp]
theorem eval_rawWrapperFieldCode
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    PolynomialFieldCode.realize
        (rawWrapperFieldCode sourceBlock D P) x j =
      PolynomialFieldCode.realize
          (tangentFieldCode sourceBlock (chartFieldCode k D P)) x j +
        radiusDeviation (k + 1 : ℝ)
          (fun b ↦ scaledBlockRadius sourceBlock x b)
          (ambientBlock sourceBlock j) * x j := by
  rw [PolynomialFieldCode.realize_apply]
  simp only [rawWrapperFieldCode, PolynomialCode.decode_add_code, map_add]
  change
    PolynomialFieldCode.realize
        (tangentFieldCode sourceBlock (chartFieldCode k D P)) x j +
      PolynomialFieldCode.realize (cleanupFieldCode sourceBlock) x j =
        _ + _
  rw [eval_cleanupFieldCode]

/-- Algebraic squared-radius derivative generated by the raw wrapper. -/
def blockRadiusDirectionalDerivative
    (sourceBlock : Fin n → Fin k)
    (x v : Fin (n + 1) → ℝ) (b : Fin (k + 1)) : ℝ :=
  2 * (k + 1 : ℝ) *
    blockDotValue sourceBlock x v b

/-- The raw wrapper gives exactly the radius cleanup system. -/
theorem blockRadiusDirectionalDerivative_rawWrapper
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (x : Fin (n + 1) → ℝ) (b : Fin (k + 1)) :
    blockRadiusDirectionalDerivative sourceBlock x
        (PolynomialFieldCode.realize
          (rawWrapperFieldCode sourceBlock D P) x) b =
      radiusRhs (k + 1 : ℝ)
        (fun i ↦ scaledBlockRadius sourceBlock x i) b := by
  classical
  have hT :=
    blockDotValue_tangentFieldCode_eq_zero sourceBlock
      (chartFieldCode k D P) x b
  have hsplit :
      blockDotValue sourceBlock x
          (PolynomialFieldCode.realize
            (rawWrapperFieldCode sourceBlock D P) x) b =
        blockDotValue sourceBlock x
          (PolynomialFieldCode.realize
            (tangentFieldCode sourceBlock
              (chartFieldCode k D P)) x) b +
        radiusDeviation (k + 1 : ℝ)
            (fun i ↦ scaledBlockRadius sourceBlock x i) b *
          rawBlockNormSq sourceBlock x b := by
    simp only [blockDotValue, rawBlockNormSq]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : ambientBlock sourceBlock j = b
    · simp only [hj, ↓reduceIte, eval_rawWrapperFieldCode]
      ring
    · simp [hj]
  rw [blockRadiusDirectionalDerivative, radiusRhs,
    hsplit, hT, zero_add, scaledBlockRadius]
  ring

/-- On the unit sphere the raw wrapper is tangent to the sphere. -/
theorem dot_rawWrapperFieldCode_eq_zero_of_normSq_one
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (x : Fin (n + 1) → ℝ) (hx : normSq x = 1) :
    dot x
      (PolynomialFieldCode.realize
        (rawWrapperFieldCode sourceBlock D P) x) = 0 := by
  classical
  have hsum :
      ∑ b, scaledBlockRadius sourceBlock x b = (k + 1 : ℝ) := by
    rw [sum_scaledBlockRadius, hx, mul_one]
  have hdev :
      ∑ b,
        scaledBlockRadius sourceBlock x b *
          radiusDeviation (k + 1 : ℝ)
            (fun i ↦ scaledBlockRadius sourceBlock x i) b = 0 :=
    weighted_radiusDeviation_sum_zero
      (k + 1 : ℝ)
      (fun i ↦ scaledBlockRadius sourceBlock x i)
      (by positivity) hsum
  have hpartition :
      ∀ v : Fin (n + 1) → ℝ,
        dot x v =
          ∑ b, blockDotValue sourceBlock x v b := by
    intro v
    rw [dot]
    symm
    exact sum_block_partition sourceBlock (fun j ↦ x j * v j)
  rw [hpartition]
  calc
    (∑ b, blockDotValue sourceBlock x
        (PolynomialFieldCode.realize
          (rawWrapperFieldCode sourceBlock D P) x) b) =
        (k + 1 : ℝ)⁻¹ *
          ∑ b,
            scaledBlockRadius sourceBlock x b *
              radiusDeviation (k + 1 : ℝ)
                (fun i ↦ scaledBlockRadius sourceBlock x i) b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      have hrhs :=
        blockRadiusDirectionalDerivative_rawWrapper
          sourceBlock D P x b
      simp only [blockRadiusDirectionalDerivative, radiusRhs] at hrhs
      have hL : (k + 1 : ℝ) ≠ 0 := by positivity
      field_simp
      nlinarith
    _ = 0 := by rw [hdev, mul_zero]

/-! ## Reward and final homogeneous field -/

/-- Code of `H=∏ᵢsᵢ`. -/
def blockRadiusProductCode
    (sourceBlock : Fin n → Fin k) :
    PolynomialCode (n + 1) :=
  (List.ofFn fun b : Fin (k + 1) ↦
    scaledBlockRadiusCode sourceBlock b).foldr
      PolynomialCode.mul PolynomialCode.one

/-- Raw reward `b=Hα-(1-H)`. -/
def rawWrapperRewardCode
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (a : PolynomialCode n) :
    PolynomialCode (n + 1) :=
  let H := blockRadiusProductCode sourceBlock
  PolynomialCode.sub
    (PolynomialCode.mul H (chartRewardCode k D a))
    (PolynomialCode.sub PolynomialCode.one H)

@[simp]
theorem eval_blockRadiusProductCode
    (sourceBlock : Fin n → Fin k)
    (x : Fin (n + 1) → ℝ) :
    eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode
          (blockRadiusProductCode sourceBlock)) =
      blockRadiusProduct
        (fun b ↦ scaledBlockRadius sourceBlock x b) := by
  have hfold :
      ∀ ps : List (PolynomialCode (n + 1)),
        eval₂Hom (algebraMap ℚ ℝ) x
            (PolynomialCode.decode
              (ps.foldr PolynomialCode.mul PolynomialCode.one)) =
          (ps.map fun p ↦
            eval₂Hom (algebraMap ℚ ℝ) x
              (PolynomialCode.decode p)).prod := by
    intro ps
    induction ps with
    | nil => simp
    | cons p ps ih =>
        simp only [List.foldr_cons, PolynomialCode.decode_mul_code,
          map_mul, List.map_cons, List.prod_cons]
        rw [ih]
  rw [blockRadiusProductCode, hfold, List.map_ofFn,
    List.prod_ofFn]
  simp only [Function.comp_apply, eval_scaledBlockRadiusCode,
    blockRadiusProduct]

@[simp]
theorem eval_rawWrapperRewardCode
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (a : PolynomialCode n)
    (x : Fin (n + 1) → ℝ) :
    eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode
          (rawWrapperRewardCode sourceBlock D a)) =
      wrapperReward
        (fun b ↦ scaledBlockRadius sourceBlock x b)
        (eval₂Hom (algebraMap ℚ ℝ) x
          (PolynomialCode.decode (chartRewardCode k D a))) := by
  simp only [rawWrapperRewardCode, wrapperReward,
    PolynomialCode.decode_sub_code, map_sub,
    PolynomialCode.decode_mul_code, map_mul,
    PolynomialCode.decode_one_code, map_one]
  rw [eval_blockRadiusProductCode]

/-- Target odd degree from the manuscript, with `L=k+1`. -/
def targetDegree (k D : ℕ) : ℕ :=
  D + 2 * (k + 1)

/-- Homogeneous angular code `Y`. -/
def homogeneousAngularCode
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n) :
    PolynomialFieldCode (n + 1) :=
  fun j ↦
    PolynomialCode.parityHomogenizeCode
      (targetDegree k D)
      (rawWrapperFieldCode sourceBlock D P j)

/-- Homogeneous radial reward code `A`. -/
def homogeneousRewardCode
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (a : PolynomialCode n) :
    PolynomialCode (n + 1) :=
  PolynomialCode.parityHomogenizeCode
    (targetDegree k D - 1)
    (rawWrapperRewardCode sourceBlock D a)

/-- Final finite rational field code `F=Y+A x`. -/
def finalFieldCode
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n) :
    PolynomialFieldCode (n + 1) :=
  fun j ↦
    PolynomialCode.add
      (homogeneousAngularCode sourceBlock D P j)
      (PolynomialCode.mul
        (homogeneousRewardCode sourceBlock D a)
        (PolynomialCode.varCode j))

/-- The final sparse output is homogeneous once the two explicit,
decidable raw-term eligibility conditions hold. -/
theorem finalFieldCode_isHomogeneous
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (hB : ∀ j,
      PolynomialCode.TermsParityEligible
        (targetDegree k D)
        (rawWrapperFieldCode sourceBlock D P j))
    (hb :
      PolynomialCode.TermsParityEligible
        (targetDegree k D - 1)
        (rawWrapperRewardCode sourceBlock D a)) :
    ∀ j,
      (PolynomialCode.decode
        (finalFieldCode sourceBlock D P a j)).IsHomogeneous
          (targetDegree k D) := by
  intro j
  simp only [finalFieldCode, PolynomialCode.decode_add_code,
    PolynomialCode.decode_mul_code,
    PolynomialCode.decode_varCode]
  have hY :=
    PolynomialCode.decode_parityHomogenizeCode_isHomogeneous
      (targetDegree k D)
      (rawWrapperFieldCode sourceBlock D P j) (hB j)
  have hA :=
    PolynomialCode.decode_parityHomogenizeCode_isHomogeneous
      (targetDegree k D - 1)
      (rawWrapperRewardCode sourceBlock D a) hb
  have hX : (X j : MvPolynomial (Fin (n + 1)) ℚ).IsHomogeneous 1 :=
    isHomogeneous_X ℚ j
  apply hY.add
  convert hA.mul hX using 1

/-- On the Euclidean unit sphere, the homogeneous angular code agrees
exactly with the raw cleanup field. -/
theorem realize_homogeneousAngularCode_of_normSq_one
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (x : Fin (n + 1) → ℝ) (hx : normSq x = 1) :
    PolynomialFieldCode.realize
        (homogeneousAngularCode sourceBlock D P) x =
      PolynomialFieldCode.realize
        (rawWrapperFieldCode sourceBlock D P) x := by
  funext j
  exact
    PolynomialCode.eval₂Hom_parityHomogenizeCode_of_normSq_one
      (targetDegree k D)
      (rawWrapperFieldCode sourceBlock D P j) x hx

/-- On the Euclidean unit sphere, the homogeneous reward code agrees
exactly with the raw wrapper reward. -/
theorem eval_homogeneousRewardCode_of_normSq_one
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (a : PolynomialCode n)
    (x : Fin (n + 1) → ℝ) (hx : normSq x = 1) :
    eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode
          (homogeneousRewardCode sourceBlock D a)) =
      eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode
          (rawWrapperRewardCode sourceBlock D a)) :=
  PolynomialCode.eval₂Hom_parityHomogenizeCode_of_normSq_one
    (targetDegree k D - 1)
    (rawWrapperRewardCode sourceBlock D a) x hx

/-- Exact pointwise `F=Y+A x` realization identity. -/
theorem realize_finalFieldCode
    (sourceBlock : Fin n → Fin k)
    (D : ℕ) (P : PolynomialFieldCode n)
    (a : PolynomialCode n)
    (x : Fin (n + 1) → ℝ) :
    PolynomialFieldCode.realize
        (finalFieldCode sourceBlock D P a) x =
      PolynomialFieldCode.realize
          (homogeneousAngularCode sourceBlock D P) x +
        eval₂Hom (algebraMap ℚ ℝ) x
            (PolynomialCode.decode
              (homogeneousRewardCode sourceBlock D a)) • x := by
  funext j
  simp [finalFieldCode, PolynomialFieldCode.realize_apply]

end UnitSpherePolynomialWrapper

end

end HGAS
