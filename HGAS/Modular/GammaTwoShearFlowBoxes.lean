import HGAS.Modular.GammaTwoGeodesicRecurrence
import HGAS.Modular.GammaTwoHaarErgodic
import Mathlib.Tactic

/-!
# Shear flow boxes and their uniform Haar mass

This module supplies the local-product geometry used by the
Hubbard--Miller good-return-time argument.

Every element in the positive Gauss cell of `SL(2,ℝ)` has unique
lower--diagonal--upper coordinates

```text
  v(r) a(t) u(s).
```

We define an explicit open rectangular box by requiring
`|r| < R`, `|t| < A`, and `|s| < H`.  The definition itself is given by
matrix-entry inequalities, which makes openness immediate; the exact
coordinate characterization is then proved from Gauss decomposition.
Its orbit at `q ∈ Γ(2) \ SL(2,ℝ)` is the shear box
`gammaTwoShearBox q R A H`.

The central covariance identity is

```text
  (v(r) a(t) u(s)) a(L)
    = a(L) (v(exp(L)r) a(t) u(exp(-L)s)).
```

Thus geodesic time `L` sends the anisotropic box with widths
`R exp(-L)` and `H exp(L)` exactly onto the fixed-size box with widths
`R` and `H`.

The final theorem gives the measure-theoretic fact needed for the
good-times proof: on every nonempty compact set, fixed-size shear boxes
have a uniform positive Haar-mass lower bound.  The proof uses only:

* openness of the quotient orbit map;
* positivity of every nonempty open set for a transitive
  right-invariant probability;
* a small symmetric group neighborhood `W` with `W W` contained in the
  prescribed box;
* a finite subcover of the compact set.

No coordinate formula for Haar density and no local injectivity radius
calculation is required.
-/

namespace HGAS.Modular

open Filter Function Matrix _root_.MeasureTheory Set Topology
open scoped MatrixGroups Pointwise

noncomputable section

def lowerGeodesicUpperBox
    (R A H : ℝ) : Set RealModularFrame :=
  {g |
    0 < g 0 0 ∧
    |g 1 0| < R * g 0 0 ∧
    Real.exp (-A / 2) < g 0 0 ∧
    g 0 0 < Real.exp (A / 2) ∧
    |g 0 1| < H * g 0 0}

theorem isOpen_lowerGeodesicUpperBox
    (R A H : ℝ) :
    IsOpen (lowerGeodesicUpperBox R A H) := by
  have hentry (i j : Fin 2) :
      Continuous (fun g : RealModularFrame ↦ g i j) :=
    (continuous_apply j).comp
      ((continuous_apply i).comp continuous_subtype_val)
  unfold lowerGeodesicUpperBox
  repeat' apply IsOpen.inter
  · exact isOpen_lt continuous_const (hentry 0 0)
  · exact isOpen_lt
      ((hentry 1 0).abs)
      (continuous_const.mul (hentry 0 0))
  · exact isOpen_lt continuous_const (hentry 0 0)
  · exact isOpen_lt (hentry 0 0) continuous_const
  · exact isOpen_lt
      ((hentry 0 1).abs)
      (continuous_const.mul (hentry 0 0))

theorem one_mem_lowerGeodesicUpperBox
    {R A H : ℝ}
    (hR : 0 < R) (hA : 0 < A) (hH : 0 < H) :
    (1 : RealModularFrame) ∈
      lowerGeodesicUpperBox R A H := by
  change
    0 < (1 : ℝ) ∧
      |(0 : ℝ)| < R * 1 ∧
      Real.exp (-A / 2) < 1 ∧
      1 < Real.exp (A / 2) ∧
      |(0 : ℝ)| < H * 1
  refine ⟨zero_lt_one, by simpa using hR, ?_, ?_,
    by simpa using hH⟩
  · rw [Real.exp_lt_one_iff]
    nlinarith [half_pos hA]
  · simpa only [Real.one_lt_exp_iff] using half_pos hA

theorem lower_geodesic_upper_mem_box_iff
    {R A H r t s : ℝ} :
    lowerUnipotent r * geodesicFrame t *
          upperUnipotent s ∈
        lowerGeodesicUpperBox R A H ↔
      |r| < R ∧ |t| < A ∧ |s| < H := by
  have hexp : 0 < Real.exp (t / 2) :=
    Real.exp_pos _
  have hneg :
      Real.exp (-A / 2) < Real.exp (t / 2) ↔
        -A / 2 < t / 2 :=
    Real.exp_lt_exp
  have hpos :
      Real.exp (t / 2) < Real.exp (A / 2) ↔
        t / 2 < A / 2 :=
    Real.exp_lt_exp
  simp only [lowerGeodesicUpperBox, mem_setOf_eq,
    Matrix.SpecialLinearGroup.coe_mul, lowerUnipotent_coe,
    geodesicFrame_coe, upperUnipotent_coe,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, zero_mul, one_mul, mul_zero,
    mul_one, zero_add, add_zero, abs_mul,
    abs_of_pos hexp, hneg, hpos]
  constructor
  · rintro ⟨_, hr, htlow, hthigh, hs⟩
    constructor
    · nlinarith
    constructor
    · rw [abs_lt]
      constructor <;> linarith
    · nlinarith
  · rintro ⟨hr, ht, hs⟩
    refine ⟨hexp, ?_, ?_, ?_, ?_⟩
    · nlinarith
    · nlinarith [(abs_lt.mp ht).1]
    · nlinarith [(abs_lt.mp ht).2]
    · nlinarith

theorem exists_lower_geodesic_upper_of_mem_box
    {R A H : ℝ} {g : RealModularFrame}
    (hg : g ∈ lowerGeodesicUpperBox R A H) :
    ∃ r t s : ℝ,
      |r| < R ∧ |t| < A ∧ |s| < H ∧
      lowerUnipotent r * geodesicFrame t *
          upperUnipotent s = g := by
  have hg00 : 0 < g 0 0 := hg.1
  let r : ℝ := g 1 0 / g 0 0
  let t : ℝ := 2 * Real.log (g 0 0)
  let s : ℝ := g 0 1 / g 0 0
  have hr : |r| < R := by
    dsimp only [r]
    rw [abs_div, abs_of_pos hg00,
      div_lt_iff₀ hg00]
    exact hg.2.1
  have hs : |s| < H := by
    dsimp only [s]
    rw [abs_div, abs_of_pos hg00,
      div_lt_iff₀ hg00]
    exact hg.2.2.2.2
  have htlow :
      -A / 2 < Real.log (g 0 0) := by
    rw [← Real.exp_lt_exp]
    simpa only [Real.exp_log hg00] using hg.2.2.1
  have hthigh :
      Real.log (g 0 0) < A / 2 := by
    rw [← Real.exp_lt_exp]
    simpa only [Real.exp_log hg00] using hg.2.2.2.1
  have ht : |t| < A := by
    dsimp only [t]
    rw [abs_lt]
    constructor <;> linarith
  refine ⟨r, t, s, hr, ht, hs, ?_⟩
  rw [← mautnerDiagonal_pos_eq_geodesic hg00]
  exact lower_diagonal_upper_eq g hg00.ne'

theorem lowerGeodesicUpperBox_eq_parameter_image
    {R A H : ℝ} :
    lowerGeodesicUpperBox R A H =
      {g |
        ∃ r t s : ℝ,
          |r| < R ∧ |t| < A ∧ |s| < H ∧
          lowerUnipotent r * geodesicFrame t *
              upperUnipotent s = g} := by
  ext g
  constructor
  · exact exists_lower_geodesic_upper_of_mem_box
  · rintro ⟨r, t, s, hr, ht, hs, rfl⟩
    exact
      lower_geodesic_upper_mem_box_iff.mpr
        ⟨hr, ht, hs⟩

def gammaTwoShearBox
    (q : GammaTwoFrameQuotient)
    (R A H : ℝ) : Set GammaTwoFrameQuotient :=
  (fun a : RealModularFrame ↦
    gammaTwoFrameRightMul a q) ''
      lowerGeodesicUpperBox R A H

theorem isOpenMap_gammaTwoFrameRightMul_orbit
    (q : GammaTwoFrameQuotient) :
    IsOpenMap
      (fun a : RealModularFrame ↦
        gammaTwoFrameRightMul a q) := by
  induction q using Quotient.inductionOn with
  | _ g =>
      intro U hU
      change IsOpen
        ((fun a : RealModularFrame ↦
          gammaTwoFrameQuotientMk (g * a)) '' U)
      rw [show
        (fun a : RealModularFrame ↦
          gammaTwoFrameQuotientMk (g * a)) '' U =
        gammaTwoFrameQuotientMk ''
          ((fun a : RealModularFrame ↦ g * a) '' U) by
            rw [image_image]]
      apply gammaTwoFrameQuotientMk_isOpenQuotientMap.isOpenMap
      exact (Homeomorph.mulLeft g).isOpenMap U hU

theorem isOpen_gammaTwoShearBox
    (q : GammaTwoFrameQuotient)
    (R A H : ℝ) :
    IsOpen (gammaTwoShearBox q R A H) :=
  isOpenMap_gammaTwoFrameRightMul_orbit q _
    (isOpen_lowerGeodesicUpperBox R A H)

theorem self_mem_gammaTwoShearBox
    (q : GammaTwoFrameQuotient)
    {R A H : ℝ}
    (hR : 0 < R) (hA : 0 < A) (hH : 0 < H) :
    q ∈ gammaTwoShearBox q R A H := by
  refine ⟨1, one_mem_lowerGeodesicUpperBox hR hA hH, ?_⟩
  change gammaTwoFrameRightMul 1 q = q
  rw [gammaTwoFrameRightMul_one]
  rfl

/-- Right multiplication by a frame is a homeomorphism of the
level-two quotient. -/
def gammaTwoFrameRightMulHomeomorph
    (a : RealModularFrame) :
    GammaTwoFrameQuotient ≃ₜ GammaTwoFrameQuotient where
  toFun := gammaTwoFrameRightMul a
  invFun := gammaTwoFrameRightMul a⁻¹
  left_inv q := by
    have h :=
      congrFun (gammaTwoFrameRightMul_mul a a⁻¹) q
    simpa only [mul_inv_cancel, gammaTwoFrameRightMul_one,
      id_eq, Function.comp_apply] using h.symm
  right_inv q := by
    have h :=
      congrFun (gammaTwoFrameRightMul_mul a⁻¹ a) q
    simpa only [inv_mul_cancel, gammaTwoFrameRightMul_one,
      id_eq, Function.comp_apply] using h.symm
  continuous_toFun := gammaTwoFrameRightMul_continuous a
  continuous_invFun := gammaTwoFrameRightMul_continuous a⁻¹

/-- A right-invariant probability assigns the same mass to the image of
a measurable set under any descended right translation. -/
theorem IsRightInvariantFrameProbability.measure_image_rightMul
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν)
    (a : RealModularFrame)
    {U : Set GammaTwoFrameQuotient}
    (hU : MeasurableSet U) :
    (ν : Measure GammaTwoFrameQuotient)
        (gammaTwoFrameRightMul a '' U) =
      (ν : Measure GammaTwoFrameQuotient) U := by
  let f := gammaTwoFrameRightMulHomeomorph a
  have himage :
      gammaTwoFrameRightMul a '' U = f '' U :=
    rfl
  have hmeasImage : MeasurableSet (f '' U) :=
    by
      rw [f.image_eq_preimage_symm]
      exact hU.preimage f.symm.continuous.measurable
  have hmap :=
    congrArg ProbabilityMeasure.toMeasure (hν a)
  change
    Measure.map f (ν : Measure GammaTwoFrameQuotient) =
      (ν : Measure GammaTwoFrameQuotient) at hmap
  have heval :=
    congrArg
      (fun μ : Measure GammaTwoFrameQuotient ↦
        μ (f '' U)) hmap
  change
    (Measure.map f (ν : Measure GammaTwoFrameQuotient))
        (f '' U) =
      (ν : Measure GammaTwoFrameQuotient) (f '' U)
      at heval
  rw [Measure.map_apply f.continuous.measurable
    hmeasImage] at heval
  rw [f.preimage_image] at heval
  rw [himage]
  exact heval.symm

/-- Every nonempty open subset has positive mass for a right-invariant
probability on the transitive level-two frame quotient. -/
theorem IsRightInvariantFrameProbability.measure_pos_of_isOpen_nonempty
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν)
    {U : Set GammaTwoFrameQuotient}
    (hUopen : IsOpen U)
    (hUne : U.Nonempty) :
    0 < (ν : Measure GammaTwoFrameQuotient) U := by
  by_contra hnot
  have hUzero :
      (ν : Measure GammaTwoFrameQuotient) U = 0 :=
    nonpos_iff_eq_zero.mp (not_lt.mp hnot)
  obtain ⟨u, huU⟩ := hUne
  choose a ha using
    fun x : GammaTwoFrameQuotient ↦
      MulAction.exists_smul_eq
        RealModularFrameᵐᵒᵖ u x
  let N : GammaTwoFrameQuotient →
      Set GammaTwoFrameQuotient :=
    fun x ↦ gammaTwoFrameRightMul (a x).unop '' U
  have hNopen (x : GammaTwoFrameQuotient) :
      IsOpen (N x) := by
    exact
      (gammaTwoFrameRightMulHomeomorph (a x).unop).isOpenMap
        U hUopen
  have hxN (x : GammaTwoFrameQuotient) :
      x ∈ N x := by
    refine ⟨u, huU, ?_⟩
    exact ha x
  obtain ⟨S, hScountable, hScover⟩ :=
    countable_cover_nhds
      (fun x ↦ (hNopen x).mem_nhds (hxN x))
  have hNzero (x : GammaTwoFrameQuotient) :
      (ν : Measure GammaTwoFrameQuotient) (N x) = 0 := by
    exact
      (hν.measure_image_rightMul (a x).unop
        hUopen.measurableSet).trans hUzero
  have hunionZero :
      (ν : Measure GammaTwoFrameQuotient)
          (⋃ x ∈ S, N x) = 0 :=
    (measure_biUnion_null_iff hScountable).mpr
      (fun x _ ↦ hNzero x)
  rw [hScover] at hunionZero
  have hone : (1 : ENNReal) = 0 := by
    simpa only [measure_univ] using hunionZero
  exact one_ne_zero hone

/-- Multiplying an anisotropic lower--diagonal--upper box by geodesic
time `L` produces a fixed-size box. -/
theorem lower_geodesic_upper_mul_geodesicFrame
    (r t s L : ℝ) :
    (lowerUnipotent r * geodesicFrame t *
        upperUnipotent s) * geodesicFrame L =
      geodesicFrame L *
        (lowerUnipotent (Real.exp L * r) *
          geodesicFrame t *
            upperUnipotent (Real.exp (-L) * s)) := by
  have hinv :
      geodesicFrame (-L) =
        (geodesicFrame L)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← geodesicFrame_add]
    simp
  have hupper :
      upperUnipotent s * geodesicFrame L =
        geodesicFrame L *
          upperUnipotent (Real.exp (-L) * s) := by
    calc
      upperUnipotent s * geodesicFrame L =
          geodesicFrame L *
            (geodesicFrame (-L) *
              upperUnipotent s * geodesicFrame L) := by
                rw [hinv]
                group
      _ = geodesicFrame L *
          upperUnipotent (Real.exp (-L) * s) := by
            rw [geodesicFrame_upperUnipotent_conjugation]
  have hlower :
      lowerUnipotent r * geodesicFrame L =
        geodesicFrame L *
          lowerUnipotent (Real.exp L * r) := by
    calc
      lowerUnipotent r * geodesicFrame L =
          geodesicFrame L *
            (geodesicFrame (-L) *
              lowerUnipotent r * geodesicFrame L) := by
                rw [hinv]
                group
      _ = geodesicFrame L *
          lowerUnipotent (Real.exp L * r) := by
            rw [geodesicFrame_lowerUnipotent_conjugation]
  have hcomm :
      geodesicFrame t * geodesicFrame L =
        geodesicFrame L * geodesicFrame t := by
    rw [← geodesicFrame_add, ← geodesicFrame_add]
    congr 1
    ring
  calc
    (lowerUnipotent r * geodesicFrame t *
        upperUnipotent s) * geodesicFrame L =
        lowerUnipotent r * geodesicFrame t *
          (upperUnipotent s * geodesicFrame L) := by
            simp only [mul_assoc]
    _ = lowerUnipotent r * geodesicFrame t *
        (geodesicFrame L *
          upperUnipotent (Real.exp (-L) * s)) := by rw [hupper]
    _ = lowerUnipotent r *
        (geodesicFrame t * geodesicFrame L) *
          upperUnipotent (Real.exp (-L) * s) := by
            simp only [mul_assoc]
    _ = lowerUnipotent r *
        (geodesicFrame L * geodesicFrame t) *
          upperUnipotent (Real.exp (-L) * s) := by
            rw [hcomm]
    _ = (lowerUnipotent r * geodesicFrame L) *
        geodesicFrame t *
          upperUnipotent (Real.exp (-L) * s) := by
            simp only [mul_assoc]
    _ = geodesicFrame L *
        (lowerUnipotent (Real.exp L * r) *
          geodesicFrame t *
            upperUnipotent (Real.exp (-L) * s)) := by
              rw [hlower]
              simp only [mul_assoc]

theorem mem_gammaTwoShearBox_iff
    {q z : GammaTwoFrameQuotient}
    {R A H : ℝ} :
    z ∈ gammaTwoShearBox q R A H ↔
      ∃ r t s : ℝ,
        |r| < R ∧ |t| < A ∧ |s| < H ∧
        gammaTwoFrameRightMul
            (lowerUnipotent r * geodesicFrame t *
              upperUnipotent s) q = z := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨r, t, s, hr, ht, hs, rfl⟩ :=
      exists_lower_geodesic_upper_of_mem_box ha
    exact ⟨r, t, s, hr, ht, hs, rfl⟩
  · rintro ⟨r, t, s, hr, ht, hs, rfl⟩
    refine
      ⟨lowerUnipotent r * geodesicFrame t *
          upperUnipotent s, ?_, rfl⟩
    exact
      lower_geodesic_upper_mem_box_iff.mpr
        ⟨hr, ht, hs⟩

/-- Exact set-level covariance of anisotropic shear boxes under positive
geodesic translation. -/
theorem image_gammaTwoShearBox_geodesicFrame
    (q : GammaTwoFrameQuotient)
    (R A H L : ℝ) :
    gammaTwoFrameRightMul (geodesicFrame L) ''
        gammaTwoShearBox q
          (R * Real.exp (-L)) A
          (H * Real.exp L) =
      gammaTwoShearBox
        (gammaTwoFrameRightMul (geodesicFrame L) q)
        R A H := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨r, t, s, hr, ht, hs, hy⟩ :=
      mem_gammaTwoShearBox_iff.mp hy
    subst y
    apply mem_gammaTwoShearBox_iff.mpr
    refine
      ⟨Real.exp L * r, t, Real.exp (-L) * s,
        ?_, ht, ?_, ?_⟩
    · rw [abs_mul, abs_of_pos (Real.exp_pos L)]
      have hcancel :
          Real.exp L * Real.exp (-L) = 1 := by
        rw [← Real.exp_add]
        simp
      calc
        Real.exp L * |r| <
            Real.exp L * (R * Real.exp (-L)) :=
          mul_lt_mul_of_pos_left hr (Real.exp_pos L)
        _ = R := by
          calc
            Real.exp L * (R * Real.exp (-L)) =
                R * (Real.exp L * Real.exp (-L)) := by ring
            _ = R := by rw [hcancel, mul_one]
    · rw [abs_mul, abs_of_pos (Real.exp_pos (-L))]
      have hcancel :
          Real.exp (-L) * Real.exp L = 1 := by
        rw [← Real.exp_add]
        simp
      calc
        Real.exp (-L) * |s| <
            Real.exp (-L) * (H * Real.exp L) :=
          mul_lt_mul_of_pos_left hs (Real.exp_pos (-L))
        _ = H := by
          calc
            Real.exp (-L) * (H * Real.exp L) =
                H * (Real.exp (-L) * Real.exp L) := by ring
            _ = H := by rw [hcancel, mul_one]
    · let a :=
        lowerUnipotent r * geodesicFrame t *
          upperUnipotent s
      let b :=
        lowerUnipotent (Real.exp L * r) *
          geodesicFrame t *
            upperUnipotent (Real.exp (-L) * s)
      calc
        gammaTwoFrameRightMul b
            (gammaTwoFrameRightMul (geodesicFrame L) q) =
            gammaTwoFrameRightMul
              (geodesicFrame L * b) q := by
                simpa only [Function.comp_apply] using
                  congrFun
                    (gammaTwoFrameRightMul_mul
                      (geodesicFrame L) b) q |>.symm
        _ = gammaTwoFrameRightMul
              (a * geodesicFrame L) q := by
                rw [show
                  geodesicFrame L * b =
                    a * geodesicFrame L by
                      exact
                        (lower_geodesic_upper_mul_geodesicFrame
                          r t s L).symm]
        _ = gammaTwoFrameRightMul (geodesicFrame L)
            (gammaTwoFrameRightMul a q) := by
              simpa only [Function.comp_apply] using
                congrFun
                  (gammaTwoFrameRightMul_mul
                    a (geodesicFrame L)) q
  · intro hz
    obtain ⟨r, t, s, hr, ht, hs, hz⟩ :=
      mem_gammaTwoShearBox_iff.mp hz
    let r₀ : ℝ := Real.exp (-L) * r
    let s₀ : ℝ := Real.exp L * s
    let y : GammaTwoFrameQuotient :=
      gammaTwoFrameRightMul
        (lowerUnipotent r₀ * geodesicFrame t *
          upperUnipotent s₀) q
    refine ⟨y, ?_, ?_⟩
    · apply mem_gammaTwoShearBox_iff.mpr
      refine ⟨r₀, t, s₀, ?_, ht, ?_, rfl⟩
      · dsimp only [r₀]
        rw [abs_mul, abs_of_pos (Real.exp_pos (-L))]
        simpa only [mul_comm] using
          mul_lt_mul_of_pos_left hr (Real.exp_pos (-L))
      · dsimp only [s₀]
        rw [abs_mul, abs_of_pos (Real.exp_pos L)]
        simpa only [mul_comm] using
          mul_lt_mul_of_pos_left hs (Real.exp_pos L)
    · dsimp only [y, r₀, s₀]
      have hrscale :
          Real.exp L * (Real.exp (-L) * r) = r := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
      have hsscale :
          Real.exp (-L) * (Real.exp L * s) = s := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
      let a :=
        lowerUnipotent (Real.exp (-L) * r) *
          geodesicFrame t *
            upperUnipotent (Real.exp L * s)
      calc
        gammaTwoFrameRightMul (geodesicFrame L)
            (gammaTwoFrameRightMul a q) =
            gammaTwoFrameRightMul
              (a * geodesicFrame L) q := by
                simpa only [Function.comp_apply] using
                  congrFun
                    (gammaTwoFrameRightMul_mul
                      a (geodesicFrame L)) q |>.symm
        _ = gammaTwoFrameRightMul
            (geodesicFrame L *
              (lowerUnipotent r * geodesicFrame t *
                upperUnipotent s)) q := by
              rw [lower_geodesic_upper_mul_geodesicFrame,
                hrscale, hsscale]
        _ = gammaTwoFrameRightMul
              (lowerUnipotent r * geodesicFrame t *
                upperUnipotent s)
            (gammaTwoFrameRightMul
              (geodesicFrame L) q) := by
                simpa only [Function.comp_apply] using
                  congrFun
                    (gammaTwoFrameRightMul_mul
                      (geodesicFrame L)
                      (lowerUnipotent r * geodesicFrame t *
                        upperUnipotent s)) q
        _ = z := hz

/-- Haar mass of an anisotropic box equals Haar mass of the corresponding
fixed-size box at the geodesically translated center. -/
theorem IsRightInvariantFrameProbability.measure_gammaTwoShearBox_scaled
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν)
    (q : GammaTwoFrameQuotient)
    (R A H L : ℝ) :
    (ν : Measure GammaTwoFrameQuotient)
        (gammaTwoShearBox q
          (R * Real.exp (-L)) A
          (H * Real.exp L)) =
      (ν : Measure GammaTwoFrameQuotient)
        (gammaTwoShearBox
          (gammaTwoFrameRightMul (geodesicFrame L) q)
          R A H) := by
  rw [← image_gammaTwoShearBox_geodesicFrame]
  exact
    hν.measure_image_rightMul (geodesicFrame L)
      (isOpen_gammaTwoShearBox q
        (R * Real.exp (-L)) A
        (H * Real.exp L)).measurableSet |>.symm

/-- The orbit of a set of frame multipliers based at a quotient point. -/
def gammaTwoFrameOrbitSet
    (q : GammaTwoFrameQuotient)
    (W : Set RealModularFrame) :
    Set GammaTwoFrameQuotient :=
  (fun a : RealModularFrame ↦
    gammaTwoFrameRightMul a q) '' W

theorem isOpen_gammaTwoFrameOrbitSet
    (q : GammaTwoFrameQuotient)
    {W : Set RealModularFrame}
    (hW : IsOpen W) :
    IsOpen (gammaTwoFrameOrbitSet q W) :=
  isOpenMap_gammaTwoFrameRightMul_orbit q W hW

theorem self_mem_gammaTwoFrameOrbitSet
    (q : GammaTwoFrameQuotient)
    {W : Set RealModularFrame}
    (hW : (1 : RealModularFrame) ∈ W) :
    q ∈ gammaTwoFrameOrbitSet q W := by
  refine ⟨1, hW, ?_⟩
  change gammaTwoFrameRightMul 1 q = q
  rw [gammaTwoFrameRightMul_one]
  rfl

/-- On a compact set, fixed-size shear boxes have a uniform positive
Haar-mass lower bound. -/
theorem
    IsRightInvariantFrameProbability.exists_pos_uniform_measure_gammaTwoShearBox_on_compact
    {ν : ProbabilityMeasure GammaTwoFrameQuotient}
    (hν : IsRightInvariantFrameProbability ν)
    {K : Set GammaTwoFrameQuotient}
    (hKcompact : IsCompact K)
    (hKnonempty : K.Nonempty)
    {R A H : ℝ}
    (hR : 0 < R) (hA : 0 < A) (hH : 0 < H) :
    ∃ η : ENNReal, 0 < η ∧
      ∀ q ∈ K,
        η ≤
          (ν : Measure GammaTwoFrameQuotient)
            (gammaTwoShearBox q R A H) := by
  let O : Set RealModularFrame :=
    lowerGeodesicUpperBox R A H
  have hOopen : IsOpen O :=
    isOpen_lowerGeodesicUpperBox R A H
  have hOne : (1 : RealModularFrame) ∈ O :=
    one_mem_lowerGeodesicUpperBox hR hA hH
  obtain ⟨V, hVopen, hVone, hVV⟩ :=
    exists_open_nhds_one_mul_subset
      (hOopen.mem_nhds hOne)
  let W : Set RealModularFrame := V ∩ V⁻¹
  have hWopen : IsOpen W :=
    hVopen.inter hVopen.inv
  have hWone : (1 : RealModularFrame) ∈ W := by
    exact ⟨hVone, by simpa using hVone⟩
  have hWinv : W⁻¹ = W := by
    ext a
    simp only [W, Set.mem_inv, mem_inter_iff, inv_inv]
    tauto
  have hWW : W * W ⊆ O := by
    exact
      (mul_subset_mul inter_subset_left
        inter_subset_left).trans hVV
  let N : GammaTwoFrameQuotient →
      Set GammaTwoFrameQuotient :=
    fun q ↦ gammaTwoFrameOrbitSet q W
  have hNopen (q : GammaTwoFrameQuotient) :
      IsOpen (N q) :=
    isOpen_gammaTwoFrameOrbitSet q hWopen
  have hqN (q : GammaTwoFrameQuotient) :
      q ∈ N q :=
    self_mem_gammaTwoFrameOrbitSet q hWone
  have hNpos (q : GammaTwoFrameQuotient) :
      0 <
        (ν : Measure GammaTwoFrameQuotient) (N q) :=
    hν.measure_pos_of_isOpen_nonempty
      (hNopen q) ⟨q, hqN q⟩
  have hlocalContain
      (q z : GammaTwoFrameQuotient)
      (hz : z ∈ N q) :
      N q ⊆ gammaTwoShearBox z R A H := by
    obtain ⟨a, haW, rfl⟩ := hz
    intro x hx
    obtain ⟨b, hbW, rfl⟩ := hx
    refine
      ⟨a⁻¹ * b, ?_, ?_⟩
    · change a⁻¹ * b ∈ O
      apply hWW
      exact
        Set.mul_mem_mul
          (by
            rw [← hWinv]
            exact Set.inv_mem_inv.mpr haW)
          hbW
    · have hcomp :=
        congrFun
          (gammaTwoFrameRightMul_mul a (a⁻¹ * b)) q
      calc
        gammaTwoFrameRightMul (a⁻¹ * b)
            (gammaTwoFrameRightMul a q) =
            gammaTwoFrameRightMul
              (a * (a⁻¹ * b)) q := by
                simpa only [Function.comp_apply] using hcomp.symm
        _ = gammaTwoFrameRightMul b q := by
              congr 1
              group
  have hKcover : K ⊆ ⋃ q : GammaTwoFrameQuotient, N q := by
    intro q hq
    exact mem_iUnion.mpr ⟨q, hqN q⟩
  obtain ⟨S, hScover⟩ :=
    hKcompact.elim_finite_subcover N hNopen hKcover
  have hSnonempty : S.Nonempty := by
    obtain ⟨q, hqK⟩ := hKnonempty
    have hqUnion := hScover hqK
    by_contra hSempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hSempty] at hqUnion
    simp at hqUnion
  let E : Finset ENNReal :=
    S.image
      (fun q ↦
        (ν : Measure GammaTwoFrameQuotient) (N q))
  have hEnonempty : E.Nonempty :=
    hSnonempty.image _
  let η : ENNReal := E.min' hEnonempty
  have hηpos : 0 < η := by
    have hηmem : η ∈ E :=
      Finset.min'_mem E hEnonempty
    obtain ⟨q, hqS, hqη⟩ :=
      Finset.mem_image.mp hηmem
    rw [← hqη]
    exact hNpos q
  refine ⟨η, hηpos, ?_⟩
  intro z hzK
  obtain ⟨q, hqS, hzN⟩ :=
    mem_iUnion₂.mp (hScover hzK)
  have hηN :
      η ≤
        (ν : Measure GammaTwoFrameQuotient) (N q) :=
    Finset.min'_le E
      ((ν : Measure GammaTwoFrameQuotient) (N q))
      (Finset.mem_image.mpr ⟨q, hqS, rfl⟩)
  exact hηN.trans
    (measure_mono (hlocalContain q z hzN))

end

end HGAS.Modular
