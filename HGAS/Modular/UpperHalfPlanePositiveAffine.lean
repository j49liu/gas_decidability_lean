import HGAS.Modular.FrameBaseHaarProjection
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic

/-!
# The upper half-plane as the positive affine group

The upper-triangular subgroup of `SL(2, ℝ)` with positive upper-left
entry acts simply transitively on the upper half-plane.  This realizes
`ℍ` as an ordinary locally compact group, allowing ordinary Haar
uniqueness to be used in place of a general homogeneous-space theorem.
-/

namespace HGAS.Modular

open MeasureTheory MeasureTheory.Measure Set
open scoped MatrixGroups ENNReal NNReal

noncomputable section

/-- The connected upper-triangular subgroup of `SL(2, ℝ)`. -/
def PositiveAffineSubgroup : Subgroup RealModularFrame where
  carrier := {g | g 1 0 = 0 ∧ 0 < g 0 0}
  one_mem' := by
    simp
  mul_mem' := by
    intro g h hg hh
    constructor
    · rw [Matrix.SpecialLinearGroup.coe_mul,
        Matrix.mul_apply]
      simp [Fin.sum_univ_two, hg.1, hh.1]
    · rw [Matrix.SpecialLinearGroup.coe_mul,
        Matrix.mul_apply]
      simp only [Fin.sum_univ_two, Fin.isValue, hh.1,
        mul_zero, add_zero]
      exact mul_pos hg.2 hh.2
  inv_mem' := by
    intro g hg
    constructor
    · rw [Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_fin_two]
      simp [hg.1]
    · rw [Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_fin_two]
      have hdet : g 0 0 * g 1 1 = 1 := by
        simpa only [Matrix.det_fin_two, hg.1,
          mul_zero, sub_zero] using g.2
      have : 0 < g 1 1 := by
        exact
          pos_of_mul_pos_right
            (show 0 < g 0 0 * g 1 1 by rw [hdet]; norm_num)
            hg.2.le
      simpa using this

/-- The canonical positive-affine element carrying `I` to `z`. -/
def upperHalfPlaneToPositiveAffine
    (z : UpperHalfPlane) : PositiveAffineSubgroup :=
  ⟨z.toSL2R, by
    constructor
    · simp [UpperHalfPlane.toSL2R_apply]
    · simp only [UpperHalfPlane.coe_toSL2R]
      exact Real.sqrt_pos.2 z.im_pos⟩

/-- Orbit map from the positive affine subgroup to `ℍ`. -/
def positiveAffineOrbit
    (g : PositiveAffineSubgroup) : UpperHalfPlane :=
  g.1 • UpperHalfPlane.I

@[simp]
theorem positiveAffineOrbit_upperHalfPlaneToPositiveAffine
    (z : UpperHalfPlane) :
    positiveAffineOrbit
      (upperHalfPlaneToPositiveAffine z) = z := by
  exact UpperHalfPlane.toSL2R_smul_I z

private theorem coe_upperTriangular_smul_I
    (a b : ℝ) (ha : a ≠ 0) :
    let g : RealModularFrame :=
      ⟨!![a, b; 0, a⁻¹], by simp [ha]⟩
    (↑(g • UpperHalfPlane.I) : ℂ) =
      (a * b : ℝ) + (a ^ 2 : ℝ) * Complex.I := by
  dsimp only
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [div_eq_mul_inv]
  field_simp
  ring

private theorem upperHalfPlaneToPositiveAffine_positiveAffineOrbit
    (g : PositiveAffineSubgroup) :
    upperHalfPlaneToPositiveAffine
      (positiveAffineOrbit g) = g := by
  apply Subtype.ext
  obtain ⟨a, b, ha, hg⟩ :=
    g.1.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero g.property.1
  have ha_pos : 0 < a := by
    have h := g.property.2
    change 0 < g.1 0 0 at h
    rw [hg] at h
    simpa using h
  have hcoe :
      (↑(g.1 • UpperHalfPlane.I) : ℂ) =
        (a * b : ℝ) + (a ^ 2 : ℝ) * Complex.I := by
    rw [hg]
    exact coe_upperTriangular_smul_I a b ha
  have him :
      (g.1 • UpperHalfPlane.I).im = a ^ 2 := by
    rw [← UpperHalfPlane.coe_im, hcoe]
    simp only [Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_im, Complex.I_re,
      mul_one, mul_zero, add_zero, zero_add,
      Complex.ofReal_re]
  have hre :
      (g.1 • UpperHalfPlane.I).re = a * b := by
    rw [← UpperHalfPlane.coe_re, hcoe]
    simp only [Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero,
      Complex.ofReal_im, add_zero]
  have hsqrt :
      Real.sqrt ((g.1 • UpperHalfPlane.I).im) = a := by
    rw [him, Real.sqrt_sq_eq_abs, abs_of_pos ha_pos]
  apply Subtype.ext
  conv_rhs => rw [hg]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperHalfPlaneToPositiveAffine, positiveAffineOrbit,
      UpperHalfPlane.toSL2R_apply,
      hsqrt, hre, ha_pos.ne']

/-- The orbit map is a homeomorphism: the positive affine subgroup
acts simply transitively on `ℍ`. -/
def positiveAffineOrbitHomeomorph :
    PositiveAffineSubgroup ≃ₜ UpperHalfPlane where
  toFun := positiveAffineOrbit
  invFun := upperHalfPlaneToPositiveAffine
  left_inv := upperHalfPlaneToPositiveAffine_positiveAffineOrbit
  right_inv := positiveAffineOrbit_upperHalfPlaneToPositiveAffine
  continuous_toFun := by
    unfold positiveAffineOrbit
    fun_prop
  continuous_invFun := by
    unfold upperHalfPlaneToPositiveAffine
    exact UpperHalfPlane.continuous_toSL2R.subtype_mk _

@[simp]
theorem positiveAffineOrbitHomeomorph_apply
    (g : PositiveAffineSubgroup) :
    positiveAffineOrbitHomeomorph g =
      g.1 • UpperHalfPlane.I :=
  rfl

@[simp]
theorem positiveAffineOrbitHomeomorph_symm_apply
    (z : UpperHalfPlane) :
    positiveAffineOrbitHomeomorph.symm z =
      upperHalfPlaneToPositiveAffine z :=
  rfl

/-- The orbit homeomorphism intertwines multiplication on the positive
affine subgroup with its restricted Möbius action. -/
theorem positiveAffineOrbit_mul
    (a g : PositiveAffineSubgroup) :
    positiveAffineOrbit (a * g) =
      a.1 • positiveAffineOrbit g := by
  simp only [positiveAffineOrbit, Subgroup.coe_mul, mul_smul]

/-- Local compactness transported from the upper half-plane along the
orbit homeomorphism. -/
noncomputable instance positiveAffineLocallyCompactSpace :
    LocallyCompactSpace PositiveAffineSubgroup :=
  positiveAffineOrbitHomeomorph.isClosedEmbedding.locallyCompactSpace

/-- Second countability is likewise transported along the orbit
homeomorphism. -/
instance positiveAffineSecondCountableTopology :
    SecondCountableTopology PositiveAffineSubgroup :=
  positiveAffineOrbitHomeomorph.isEmbedding.secondCountableTopology

/-- Pull a measure on `ℍ` back to the positive affine group. -/
def positiveAffinePullbackMeasure
    (μ : Measure UpperHalfPlane) :
    Measure PositiveAffineSubgroup :=
  μ.map positiveAffineOrbitHomeomorph.symm

/-- Pushing a pulled-back measure forward along the orbit map recovers
the original measure. -/
@[simp]
theorem positiveAffinePullbackMeasure_map_orbit
    (μ : Measure UpperHalfPlane) :
    (positiveAffinePullbackMeasure μ).map
        positiveAffineOrbitHomeomorph = μ := by
  rw [positiveAffinePullbackMeasure, Measure.map_map
    positiveAffineOrbitHomeomorph.measurable
    positiveAffineOrbitHomeomorph.symm.measurable]
  have hcomp :
      (positiveAffineOrbitHomeomorph ∘
        positiveAffineOrbitHomeomorph.symm) = id := by
    funext z
    exact positiveAffineOrbitHomeomorph.apply_symm_apply z
  rw [hcomp, Measure.map_id]

/-- Local finiteness on compact sets is preserved by the pullback. -/
theorem positiveAffinePullbackMeasure_isFiniteMeasureOnCompacts
    (μ : Measure UpperHalfPlane)
    [IsFiniteMeasureOnCompacts μ] :
    IsFiniteMeasureOnCompacts
      (positiveAffinePullbackMeasure μ) := by
  exact
    Measure.IsFiniteMeasureOnCompacts.map μ
      positiveAffineOrbitHomeomorph.symm

/-- Pullback by the orbit homeomorphism detects whether a measure is
zero. -/
theorem positiveAffinePullbackMeasure_ne_zero
    (μ : Measure UpperHalfPlane) (hμ : μ ≠ 0) :
    positiveAffinePullbackMeasure μ ≠ 0 := by
  exact
    (Measure.map_ne_zero_iff
      positiveAffineOrbitHomeomorph.symm.measurable.aemeasurable).2 hμ

/-- Invariance under `SL(2, ℝ)` becomes ordinary left invariance after
pulling a measure back along the simply transitive positive-affine
orbit map. -/
theorem positiveAffinePullbackMeasure_isMulLeftInvariant
    (μ : Measure UpperHalfPlane)
    [SMulInvariantMeasure RealModularFrame UpperHalfPlane μ] :
    IsMulLeftInvariant
      (positiveAffinePullbackMeasure μ) := by
  letI :
      SMulInvariantMeasure PositiveAffineSubgroup
        UpperHalfPlane μ :=
    Subgroup.smulInvariantMeasure PositiveAffineSubgroup
  letI :
      SMulInvariantMeasure PositiveAffineSubgroup
        PositiveAffineSubgroup
        (positiveAffinePullbackMeasure μ) := by
    unfold positiveAffinePullbackMeasure
    apply smulInvariantMeasure_map μ
    · intro a z
      change
        positiveAffineOrbitHomeomorph.symm
            ((a : RealModularFrame) • z) =
          a * positiveAffineOrbitHomeomorph.symm z
      apply positiveAffineOrbitHomeomorph.injective
      rw [positiveAffineOrbitHomeomorph.apply_symm_apply]
      change
        (a : RealModularFrame) • z =
          positiveAffineOrbit
            (a * positiveAffineOrbitHomeomorph.symm z)
      rw [positiveAffineOrbit_mul]
      change
        (a : RealModularFrame) • z =
          (a : RealModularFrame) •
            positiveAffineOrbitHomeomorph
              (positiveAffineOrbitHomeomorph.symm z)
      rw [positiveAffineOrbitHomeomorph.apply_symm_apply]
    · exact positiveAffineOrbitHomeomorph.symm.measurable
  constructor
  intro a
  simpa only [smul_eq_mul] using
    (MeasureTheory.map_smul a
      (positiveAffinePullbackMeasure μ))

/-- Hyperbolic area is invariant under the special-linear action.  The
library states invariance for the larger general-linear action; this
lemma records the restriction explicitly. -/
theorem upperHalfPlaneVolume_smulInvariant :
    SMulInvariantMeasure RealModularFrame UpperHalfPlane
      (volume : Measure UpperHalfPlane) := by
  constructor
  intro g A hA
  simpa only [MulAction.compHom_smul_def] using
    (SMulInvariantMeasure.measure_preimage_smul
      (μ := (volume : Measure UpperHalfPlane))
      (Matrix.SpecialLinearGroup.mapGL ℝ g) hA)

/-- Hyperbolic area on the upper half-plane is nonzero. -/
theorem upperHalfPlaneVolume_ne_zero :
    (volume : Measure UpperHalfPlane) ≠ 0 := by
  let μ₀ : Measure UpperHalfPlane :=
    (volume : Measure ℂ).comap UpperHalfPlane.coe
  let f : UpperHalfPlane → ℝ≥0∞ :=
    fun z ↦
      ↑((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2)
  letI : IsOpenPosMeasure μ₀ :=
    Measure.IsOpenPosMeasure.comap volume
      UpperHalfPlane.isOpenEmbedding_coe
  have hfNN :
      Continuous
        (fun z : UpperHalfPlane ↦
          (1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2) := by
    refine (.pow (.div₀ continuous_const ?_ ?_) 2)
    · exact UpperHalfPlane.continuous_im.subtype_mk _
    · exact fun z ↦ NNReal.ne_iff.mp z.im_ne_zero
  have hf : Continuous f := by
    exact ENNReal.continuous_coe.comp hfNN
  rw [UpperHalfPlane.volume_def, Ne,
    withDensity_eq_zero_iff
      hf.measurable.aemeasurable]
  intro hzero
  have hall : f = 0 :=
    (hf.ae_eq_iff_eq μ₀ continuous_const).mp hzero
  have hI := congrFun hall UpperHalfPlane.I
  norm_num [f] at hI

/-- Hyperbolic area, pulled back along the positive-affine orbit map,
is a Haar measure on the positive affine group. -/
theorem positiveAffinePullbackVolume_isHaarMeasure :
    IsHaarMeasure
      (positiveAffinePullbackMeasure
        (volume : Measure UpperHalfPlane)) := by
  letI :
      IsFiniteMeasureOnCompacts
        (positiveAffinePullbackMeasure
          (volume : Measure UpperHalfPlane)) :=
    positiveAffinePullbackMeasure_isFiniteMeasureOnCompacts volume
  letI :
      IsMulLeftInvariant
        (positiveAffinePullbackMeasure
          (volume : Measure UpperHalfPlane)) :=
    letI := upperHalfPlaneVolume_smulInvariant
    positiveAffinePullbackMeasure_isMulLeftInvariant volume
  letI :
      NeZero
        (positiveAffinePullbackMeasure
          (volume : Measure UpperHalfPlane)) :=
    ⟨positiveAffinePullbackMeasure_ne_zero volume
      upperHalfPlaneVolume_ne_zero⟩
  letI :
      Regular
        (positiveAffinePullbackMeasure
          (volume : Measure UpperHalfPlane)) :=
    inferInstance
  exact
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := inferInstance }

/-- Uniqueness of locally finite `SL(2, ℝ)`-invariant measures on the
upper half-plane.  This is obtained by transferring both measures to
the simply transitive positive affine group and applying ordinary Haar
uniqueness there. -/
theorem locallyFinite_invariant_eq_smul_upperHalfPlaneVolume
    (μ : Measure UpperHalfPlane)
    [IsFiniteMeasureOnCompacts μ]
    [SMulInvariantMeasure RealModularFrame UpperHalfPlane μ] :
    ∃ c : ℝ≥0,
      μ = c • (volume : Measure UpperHalfPlane) := by
  let ν : Measure PositiveAffineSubgroup :=
    positiveAffinePullbackMeasure μ
  let ν₀ : Measure PositiveAffineSubgroup :=
    positiveAffinePullbackMeasure
      (volume : Measure UpperHalfPlane)
  letI : IsFiniteMeasureOnCompacts ν :=
    positiveAffinePullbackMeasure_isFiniteMeasureOnCompacts μ
  letI : IsMulLeftInvariant ν :=
    positiveAffinePullbackMeasure_isMulLeftInvariant μ
  letI : IsHaarMeasure ν₀ := by
    simpa only [ν₀] using
      positiveAffinePullbackVolume_isHaarMeasure
  let c : ℝ≥0 := haarScalarFactor ν ν₀
  have hpull : ν = c • ν₀ := by
    exact isMulLeftInvariant_eq_smul ν ν₀
  refine ⟨c, ?_⟩
  have hpush :=
    congrArg
      (fun m : Measure PositiveAffineSubgroup ↦
        m.map positiveAffineOrbitHomeomorph)
      hpull
  change
    (positiveAffinePullbackMeasure μ).map
        positiveAffineOrbitHomeomorph =
      (c • positiveAffinePullbackMeasure
        (volume : Measure UpperHalfPlane)).map
          positiveAffineOrbitHomeomorph at hpush
  rw [Measure.map_smul,
    positiveAffinePullbackMeasure_map_orbit,
    positiveAffinePullbackMeasure_map_orbit] at hpush
  exact hpush

end

end HGAS.Modular
