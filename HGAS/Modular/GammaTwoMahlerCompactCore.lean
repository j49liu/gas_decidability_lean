import HGAS.Modular.SL2ZFrameFundamentalDomain
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import Mathlib.Tactic

/-!
# Explicit Mahler compact cores for the level-two frame quotient

This file packages the compactness part of the elementary nonescape
argument for the horocycle flow.

For a real modular frame `g` and a primitive integral row `v`, let
`v * g` be the corresponding vector in the unimodular lattice generated
by the rows of `g`.  If every such vector has Euclidean norm at least
`δ > 0`, reduction to the standard modular fundamental domain bounds the
height by `1 / δ²`.  A finite left transversal from `SL(2,ℤ)` to `Γ(2)`
then places the original level-two quotient point in a fixed compact set.

This is the two-dimensional, explicit form of the compact-core direction
of Mahler's criterion.  No measure classification or horocycle
equidistribution is used.
-/

namespace HGAS.Modular

open Complex Function Matrix Set Topology
open scoped MatrixGroups Pointwise

noncomputable section

/-- Primitive integral row vectors, represented by the level-one
Eisenstein `gammaSet`. -/
abbrev PrimitiveIntegralRow :=
  EisensteinSeries.gammaSet 1 1 (0 : Fin 2 → ZMod 1)

/-- The real row vector obtained by multiplying a primitive integral row
by a real modular frame. -/
def primitiveIntegralRowMul
    (v : PrimitiveIntegralRow) (g : RealModularFrame) :
    Fin 2 → ℝ :=
  fun j ↦ ∑ i : Fin 2, (v.1 i : ℝ) * g i j

/-- Squared Euclidean length of a primitive integral lattice row. -/
def primitiveIntegralRowNormSq
    (v : PrimitiveIntegralRow) (g : RealModularFrame) : ℝ :=
  primitiveIntegralRowMul v g 0 ^ 2 +
    primitiveIntegralRowMul v g 1 ^ 2

/-- Every primitive integral lattice row of `g` has length at least
`δ`. -/
def HasPrimitiveRowLowerBound
    (δ : ℝ) (g : RealModularFrame) : Prop :=
  ∀ v : PrimitiveIntegralRow,
    δ ^ 2 ≤ primitiveIntegralRowNormSq v g

/-- Frames whose base lies in the standard modular domain truncated at
height `Y`. -/
def integralFrameTruncatedCore (Y : ℝ) :
    Set RealModularFrame :=
  realModularFrameBasePoint ⁻¹'
    ModularGroup.truncatedFundamentalDomain Y

/-- The orbit map `g ↦ g • i` is proper, so a compact truncated base
domain has compact full frame preimage. -/
theorem isCompact_integralFrameTruncatedCore
    (Y : ℝ) :
    IsCompact (integralFrameTruncatedCore Y) := by
  exact
    UpperHalfPlane.isProperMap_smul_I.isCompact_preimage
      (ModularGroup.isCompact_truncatedFundamentalDomain Y)

/-- The finite-index enlargement of the truncated integral frame core. -/
def gammaTwoTruncatedFrameCore (Y : ℝ) :
    Set RealModularFrame :=
  HGAS.MeasureTheory.finiteIndexSubgroupDomain
    GammaTwo (integralFrameTruncatedCore Y)

/-- The finite-index frame core is compact. -/
theorem isCompact_gammaTwoTruncatedFrameCore
    (Y : ℝ) :
    IsCompact (gammaTwoTruncatedFrameCore Y) := by
  let S : GammaTwo.LeftTransversal := default
  have hSfinite : (S : Set IntegralModularGroup).Finite :=
    S.2.finite_left
  letI : Fintype ↥(S : Set IntegralModularGroup) :=
    hSfinite.fintype
  change
    IsCompact
      (⋃ s : ↥(S : Set IntegralModularGroup),
        (s : IntegralModularGroup)⁻¹ •
          integralFrameTruncatedCore Y)
  apply isCompact_iUnion
  intro s
  exact
    (isCompact_integralFrameTruncatedCore Y).smul
      (s : IntegralModularGroup)⁻¹

/-- The compact subset of `Γ(2) \\ SL(2,ℝ)` obtained by projecting the
finite-index truncated frame core. -/
def gammaTwoMahlerCompactCore (δ : ℝ) :
    Set GammaTwoFrameQuotient :=
  gammaTwoFrameQuotientMk ''
    gammaTwoTruncatedFrameCore (1 / δ ^ 2)

theorem isCompact_gammaTwoMahlerCompactCore
    (δ : ℝ) :
    IsCompact (gammaTwoMahlerCompactCore δ) :=
  (isCompact_gammaTwoTruncatedFrameCore (1 / δ ^ 2)).image
    gammaTwoFrameQuotientMk_isCoveringMap.continuous

/-- Imaginary part of the base point in terms of the bottom row. -/
theorem realModularFrameBasePoint_im_eq
    (g : RealModularFrame) :
    (realModularFrameBasePoint g).im =
      1 / (g 1 0 ^ 2 + g 1 1 ^ 2) := by
  simp only [realModularFrameBasePoint,
    MulAction.compHom_smul_def,
    UpperHalfPlane.im_smul_eq_div_normSq,
    Matrix.SpecialLinearGroup.det_mapGL,
    Units.val_one, abs_one, UpperHalfPlane.I_im, mul_one]
  simp [UpperHalfPlane.denom, Complex.normSq, sq, add_comm]

private theorem bottomRow_primitive
    (γ : IntegralModularGroup) :
    (fun j : Fin 2 ↦ γ 1 j) ∈
      EisensteinSeries.gammaSet 1 1
        (0 : Fin 2 → ZMod 1) := by
  rw [EisensteinSeries.mem_gammaSet_one]
  exact Matrix.SpecialLinearGroup.isCoprime_row γ 1

private theorem primitiveIntegralRowNormSq_bottomRow
    (γ : IntegralModularGroup) (g : RealModularFrame) :
    primitiveIntegralRowNormSq
        ⟨fun j : Fin 2 ↦ γ 1 j, bottomRow_primitive γ⟩ g =
      (γ • g) 1 0 ^ 2 + (γ • g) 1 1 ^ 2 := by
  simp only [primitiveIntegralRowNormSq,
    primitiveIntegralRowMul,
    integralModularGroup_smul_realFrame,
    Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two,
    integralToRealFrame,
    Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply,
    Int.coe_castRingHom]

/-- **Explicit Mahler compact-core lemma.**

If every primitive integral row of `g` has length at least `δ > 0`,
then the level-two quotient class of `g` lies in the compact core with
height cutoff `1 / δ²`. -/
theorem gammaTwoFrameQuotientMk_mem_mahlerCompactCore
    {δ : ℝ} (hδ : 0 < δ)
    (g : RealModularFrame)
    (hlower : HasPrimitiveRowLowerBound δ g) :
    gammaTwoFrameQuotientMk g ∈
      gammaTwoMahlerCompactCore δ := by
  obtain ⟨γ, hγfd⟩ :=
    ModularGroup.exists_smul_mem_fd
      (realModularFrameBasePoint g)
  have hbasefd :
      realModularFrameBasePoint (γ • g) ∈
        ModularGroup.fd := by
    rw [realModularFrameBasePoint_integral_smul]
    exact hγfd
  have hrow :
      δ ^ 2 ≤
        (γ • g) 1 0 ^ 2 + (γ • g) 1 1 ^ 2 := by
    simpa only [primitiveIntegralRowNormSq_bottomRow] using
      hlower
        ⟨fun j : Fin 2 ↦ γ 1 j,
          bottomRow_primitive γ⟩
  have hheight :
      (realModularFrameBasePoint (γ • g)).im ≤
        1 / δ ^ 2 := by
    rw [realModularFrameBasePoint_im_eq]
    exact one_div_le_one_div_of_le (sq_pos_of_pos hδ) hrow
  have htruncated :
      γ • g ∈ integralFrameTruncatedCore (1 / δ ^ 2) :=
    ⟨hbasefd, hheight⟩
  let S : GammaTwo.LeftTransversal := default
  let p : ↥(S : Set IntegralModularGroup) × GammaTwo :=
    S.2.equiv γ
  have hfactor :
      (p.1 : IntegralModularGroup) *
          (p.2 : IntegralModularGroup) = γ :=
    S.2.equiv_fst_mul_equiv_snd γ
  let g' : RealModularFrame := p.2 • g
  have hg'core :
      g' ∈ gammaTwoTruncatedFrameCore (1 / δ ^ 2) := by
    change
      g' ∈
        ⋃ s : ↥(S : Set IntegralModularGroup),
          (s : IntegralModularGroup)⁻¹ •
            integralFrameTruncatedCore (1 / δ ^ 2)
    apply Set.mem_iUnion.2
    refine ⟨p.1, ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    change
      (p.1 : IntegralModularGroup) •
          ((p.2 : IntegralModularGroup) • g) ∈
        integralFrameTruncatedCore (1 / δ ^ 2)
    rw [← mul_smul, hfactor]
    exact htruncated
  refine ⟨g', hg'core, ?_⟩
  apply Quotient.sound
  exact ⟨p.2, rfl⟩

end

end HGAS.Modular
