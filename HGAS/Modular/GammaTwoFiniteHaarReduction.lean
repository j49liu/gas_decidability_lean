import HGAS.Modular.HorocycleMeasureClassification
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.MeasureTheory.Measure.Haar.Quotient
import Mathlib.Tactic

/-!
# Finite-volume reduction for the level-two frame quotient

This file isolates the part of Haar-probability existence which follows
from Mathlib's general theory of Haar measures and measurable fundamental
domains.

Let `m` be a left Haar measure on `SL(2, ℝ)`, and suppose the left action
of `Γ(2)` has a measurable fundamental domain of finite Haar mass.  The
argument below proves, without assuming unimodularity, that:

1. right translation preserves `m` (finite covolume forces
   unimodularity);
2. restricting `m` to the fundamental domain and pushing it to
   `Γ(2) \ SL(2, ℝ)` gives a finite, nonzero, right-invariant measure; and
3. normalization gives the `IsRightInvariantFrameProbability` required by
   `GammaTwoHasFiniteFrameVolume`.

Consequently, for the present quotient the entire Haar-existence input is
reduced to one concrete statement: a finite-Haar-mass fundamental domain
for the already constructed deck action.  Mathlib supplies the ambient
left Haar measure and all measure-theoretic quotient arguments.

No orbit classification is proved here.  In particular, the
Dani--Smillie periodic-or-Haar dichotomy remains a separate deep input.
-/

namespace HGAS.Modular

open Function MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal NNReal Pointwise

noncomputable section

private instance gammaTwoCountable : Countable GammaTwo :=
  Function.Injective.countable (β := Fin 2 → Fin 2 → ℤ) (by
    intro γ δ h
    apply Subtype.ext
    apply Subtype.ext
    funext i j
    exact congrFun (congrFun h i) j :
    Function.Injective
      (fun γ : GammaTwo ↦
        fun i j : Fin 2 ↦ γ.1.1 i j))

private theorem haarMeasure_ne_zero
    (m : Measure RealModularFrame) [IsHaarMeasure m] :
    m ≠ 0 := by
  rw [← measure_univ_pos]
  exact
    pos_iff_ne_zero.mpr
      (isOpen_univ.measure_ne_zero m univ_nonempty)

/-! ## Measure-preserving deck action -/

/-- Left Haar measure is invariant under the restricted left action of
`Γ(2)` on real modular frames. -/
private instance gammaTwoSMulInvariantHaar
    (m : Measure RealModularFrame) [IsMulLeftInvariant m] :
    SMulInvariantMeasure GammaTwo RealModularFrame m where
  measure_preimage_smul γ A hA := by
    simpa only [gammaTwo_smul_realFrame] using
      measure_preimage_mul m (gammaTwoToRealFrame γ) A

/-- Right multiplication commutes with the restricted left deck action. -/
private instance realFrameOpGammaTwoSMulComm :
    SMulCommClass RealModularFrameᵐᵒᵖ GammaTwo RealModularFrame where
  smul_comm a γ g := by
    change
      (gammaTwoToRealFrame γ * g) * a.unop =
        gammaTwoToRealFrame γ * (g * a.unop)
    exact mul_assoc _ _ _

/-! ## A finite lattice forces unimodularity -/

/-- A finite-mass fundamental domain for the left `Γ(2)` action forces
every ambient left Haar measure to be right invariant.

The proof is the standard lattice-implies-unimodular argument.  A right
translate `F a` is again a fundamental domain (right multiplication is
nonsingular for Haar measure), hence has the same Haar mass as `F`.
On the other hand, right translation scales left Haar measure by the
modular character.  Evaluating on `F a`, and cancelling the positive
finite mass of `F`, forces that character value to be one. -/
theorem gammaTwoHaar_rightInvariant_of_finiteFundamentalDomain
    (m : Measure RealModularFrame)
    [IsHaarMeasure m] [InnerRegular m]
    {F : Set RealModularFrame}
    (hF : IsFundamentalDomain GammaTwo F m)
    (hFfinite : m F ≠ ∞) :
    IsMulRightInvariant m := by
  have hFnonzero : m F ≠ 0 :=
    hF.measure_ne_zero (haarMeasure_ne_zero m)
  refine ⟨fun a ↦ ?_⟩
  let e : RealModularFrame ≃ RealModularFrame :=
    (Homeomorph.mulRight a).toEquiv
  let Fa : Set RealModularFrame := e '' F
  have hqmp :
      Measure.QuasiMeasurePreserving
        (fun g : RealModularFrame ↦ g * a⁻¹) m m := by
    refine ⟨measurable_mul_const a⁻¹, ?_⟩
    rw [Measure.map_right_mul_eq_modularCharacterFun_smul m a⁻¹]
    exact Measure.smul_absolutelyContinuous
  have hFa : IsFundamentalDomain GammaTwo Fa m := by
    apply hF.image_of_equiv e hqmp (Equiv.refl GammaTwo)
    intro γ g
    change
      (gammaTwoToRealFrame γ * g) * a =
        gammaTwoToRealFrame γ * (g * a)
    exact mul_assoc _ _ _
  have hmass : m F = m Fa :=
    hF.measure_eq hFa
  have hmapFa :
      (Measure.map (fun g : RealModularFrame ↦ g * a) m) Fa =
        m F := by
    have hpreimage :
        (fun g : RealModularFrame ↦ g * a) ⁻¹' Fa = F := by
      ext g
      simp [Fa, e]
    change
      (Measure.map (MeasurableEquiv.mulRight a) m)
          ((MeasurableEquiv.mulRight a) '' F) =
        m F
    rw [(MeasurableEquiv.mulRight a).map_apply]
    exact congrArg m hpreimage
  have hcharacter :
      ((Measure.modularCharacterFun a : ℝ≥0) : ℝ≥0∞) * m F =
        m F := by
    calc
      ((Measure.modularCharacterFun a : ℝ≥0) : ℝ≥0∞) * m F =
          ((Measure.modularCharacterFun a : ℝ≥0) : ℝ≥0∞) * m Fa := by
            rw [hmass]
      _ =
          (Measure.modularCharacterFun a • m) Fa := by
            simp only [Measure.coe_smul, Pi.smul_apply,
              Measure.nnreal_smul_coe_apply]
      _ =
          (Measure.map (fun g : RealModularFrame ↦ g * a) m) Fa := by
            rw [Measure.map_right_mul_eq_modularCharacterFun_smul m a]
      _ = m F := hmapFa
  have hcharacter_one :
      Measure.modularCharacterFun a = 1 := by
    apply ENNReal.coe_injective
    simpa only [ENNReal.coe_one] using
      (ENNReal.mul_eq_right hFnonzero hFfinite).mp
        hcharacter
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul m a,
    hcharacter_one, one_smul]

/-! ## The finite quotient measure -/

/-- The unnormalized quotient measure obtained by restricting an ambient
measure to a fundamental domain and pushing it through the quotient map. -/
def gammaTwoFrameFundamentalDomainMeasure
    (m : Measure RealModularFrame)
    (F : Set RealModularFrame) :
    Measure GammaTwoFrameQuotient :=
  (m.restrict F).map gammaTwoFrameQuotientMk

/-- Its total mass is exactly the mass of the fundamental domain. -/
@[simp]
theorem gammaTwoFrameFundamentalDomainMeasure_univ
    (m : Measure RealModularFrame)
    (F : Set RealModularFrame) :
    gammaTwoFrameFundamentalDomainMeasure m F Set.univ = m F := by
  rw [gammaTwoFrameFundamentalDomainMeasure,
    Measure.map_apply gammaTwoFrameQuotientMk_isCoveringMap.continuous.measurable
      MeasurableSet.univ]
  simp only [preimage_univ, Measure.restrict_apply_univ]

/-- If the ambient measure is left and right invariant, the quotient
measure is invariant under every descended right translation. -/
theorem gammaTwoFrameFundamentalDomainMeasure_rightInvariant
    (m : Measure RealModularFrame)
    [IsMulLeftInvariant m] [IsMulRightInvariant m]
    {F : Set RealModularFrame}
    (hF : IsFundamentalDomain GammaTwo F m)
    (a : RealModularFrame) :
    Measure.map (gammaTwoFrameRightMul a)
        (gammaTwoFrameFundamentalDomainMeasure m F) =
      gammaTwoFrameFundamentalDomainMeasure m F := by
  let Fa : Set RealModularFrame :=
    MulOpposite.op a • F
  have hFa : IsFundamentalDomain GammaTwo Fa m :=
    hF.smul_of_comm (MulOpposite.op a)
  have hquotient :
      (m.restrict F).map gammaTwoFrameQuotientMk =
        (m.restrict Fa).map gammaTwoFrameQuotientMk :=
    by
      ext U hU
      rw [Measure.map_apply
          gammaTwoFrameQuotientMk_isCoveringMap.continuous.measurable hU,
        Measure.map_apply
          gammaTwoFrameQuotientMk_isCoveringMap.continuous.measurable hU,
        Measure.restrict_apply
          (gammaTwoFrameQuotientMk_isCoveringMap.continuous.measurable hU),
        Measure.restrict_apply
          (gammaTwoFrameQuotientMk_isCoveringMap.continuous.measurable hU)]
      apply hF.measure_set_eq hFa
      · exact
          gammaTwoFrameQuotientMk_isCoveringMap.continuous.measurable hU
      · intro γ
        ext g
        change
          gammaTwoFrameQuotientMk (γ • g) ∈ U ↔
            gammaTwoFrameQuotientMk g ∈ U
        have hmk :
            gammaTwoFrameQuotientMk (γ • g) =
              gammaTwoFrameQuotientMk g := by
          apply Quotient.sound
          exact ⟨γ, rfl⟩
        rw [hmk]
  have hpreimage :
      (fun g : RealModularFrame ↦ g * a) ⁻¹' Fa = F := by
    have hFa_eq :
        Fa = (fun g : RealModularFrame ↦ g * a) '' F := by
      rfl
    ext g
    rw [hFa_eq]
    simp
  calc
    Measure.map (gammaTwoFrameRightMul a)
        (gammaTwoFrameFundamentalDomainMeasure m F) =
        Measure.map
          (gammaTwoFrameRightMul a ∘ gammaTwoFrameQuotientMk)
          (m.restrict F) := by
            rw [gammaTwoFrameFundamentalDomainMeasure,
              Measure.map_map
                (gammaTwoFrameRightMul_continuous a).measurable
                gammaTwoFrameQuotientMk_isCoveringMap.continuous.measurable]
    _ =
        Measure.map
          (gammaTwoFrameQuotientMk ∘
            fun g : RealModularFrame ↦ g * a)
          (m.restrict F) := by
            congr 1
    _ =
        Measure.map gammaTwoFrameQuotientMk
          (Measure.map (fun g : RealModularFrame ↦ g * a)
            (m.restrict F)) := by
            rw [Measure.map_map
              gammaTwoFrameQuotientMk_isCoveringMap.continuous.measurable
              (measurable_mul_const a)]
    _ =
        Measure.map gammaTwoFrameQuotientMk
          ((Measure.map (fun g : RealModularFrame ↦ g * a) m).restrict Fa) := by
            rw [(measurableEmbedding_mulRight a).restrict_map, hpreimage]
    _ =
        Measure.map gammaTwoFrameQuotientMk (m.restrict Fa) := by
            rw [map_mul_right_eq_self m a]
    _ =
        Measure.map gammaTwoFrameQuotientMk (m.restrict F) :=
          hquotient.symm
    _ = gammaTwoFrameFundamentalDomainMeasure m F := rfl

/-- A finite-mass fundamental domain produces the normalized
right-invariant probability on `Γ(2) \ SL(2,ℝ)`.

This theorem discharges the `GammaTwoHasFiniteFrameVolume` interface from
the sole geometric input of a finite Haar fundamental domain. -/
theorem gammaTwoHasFiniteFrameVolume_of_finiteFundamentalDomain
    (m : Measure RealModularFrame)
    [IsHaarMeasure m] [InnerRegular m]
    {F : Set RealModularFrame}
    (hF : IsFundamentalDomain GammaTwo F m)
    (hFfinite : m F ≠ ∞) :
    GammaTwoHasFiniteFrameVolume := by
  letI : IsMulRightInvariant m :=
    gammaTwoHaar_rightInvariant_of_finiteFundamentalDomain
      m hF hFfinite
  let raw : Measure GammaTwoFrameQuotient :=
    gammaTwoFrameFundamentalDomainMeasure m F
  have hrawFinite : raw Set.univ < ∞ := by
    rw [show raw Set.univ = m F by
      exact gammaTwoFrameFundamentalDomainMeasure_univ m F]
    exact lt_top_iff_ne_top.mpr hFfinite
  let finite : FiniteMeasure GammaTwoFrameQuotient :=
    ⟨raw, IsFiniteMeasure.mk hrawFinite⟩
  have hrawNonzero : raw ≠ 0 := by
    intro hzero
    have : m F = 0 := by
      rw [← gammaTwoFrameFundamentalDomainMeasure_univ m F]
      simp only [raw] at hzero
      rw [hzero]
      rfl
    exact
      (hF.measure_ne_zero (haarMeasure_ne_zero m)) this
  refine ⟨finite.normalize, fun a ↦ ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  change
    Measure.map (gammaTwoFrameRightMul a)
        (finite.normalize : Measure GammaTwoFrameQuotient) =
      (finite.normalize : Measure GammaTwoFrameQuotient)
  have hfiniteNonzero : finite ≠ 0 := by
    intro hzero
    apply hrawNonzero
    exact Subtype.ext_iff.mp hzero
  rw [finite.toMeasure_normalize_eq_of_nonzero hfiniteNonzero,
    Measure.map_smul]
  congr 1
  exact
    gammaTwoFrameFundamentalDomainMeasure_rightInvariant
      m hF a

/-! ## Canonical remaining finite-volume input -/

/-- The concrete reduction-theoretic statement still needed to construct
frame Haar probability from Mathlib's canonical ambient Haar measure.

For `Γ(2)` this follows on paper from the standard finite-area modular
fundamental domain, the finite index of `Γ(2)` in `SL(2,ℤ)`, and the
compactness of the frame-angle fibre.  Those geometric ingredients are not
yet assembled into a measure-theoretic fundamental domain for the
`GammaTwo` action in Mathlib. -/
def GammaTwoHasFiniteHaarFundamentalDomain : Prop :=
  ∃ F : Set RealModularFrame,
    IsFundamentalDomain GammaTwo F
      (Measure.haar : Measure RealModularFrame) ∧
    (Measure.haar : Measure RealModularFrame) F ≠ ∞

/-- The canonical finite-fundamental-domain statement implies the
finite-frame-volume interface, with no additional measure-theoretic or
unimodularity assumptions. -/
theorem GammaTwoHasFiniteHaarFundamentalDomain.hasFiniteFrameVolume
    (h : GammaTwoHasFiniteHaarFundamentalDomain) :
    GammaTwoHasFiniteFrameVolume := by
  obtain ⟨F, hF, hFfinite⟩ := h
  exact
    gammaTwoHasFiniteFrameVolume_of_finiteFundamentalDomain
      (Measure.haar : Measure RealModularFrame)
      hF hFfinite

/-! ## Separation of finite volume from the deep orbit classification -/

/-- The genuinely dynamical remainder of Dani--Smillie after normalized
frame Haar probability has been constructed.

The universal quantifier over `ν` avoids tying the statement to any
particular fundamental-domain normalization: whichever right-invariant
frame probability finite-volume reduction produces, it is the measure in
the nonperiodic alternative. -/
def GammaTwoErgodicHorocycleDichotomy : Prop :=
  ∀ ν : ProbabilityMeasure GammaTwoFrameQuotient,
    IsRightInvariantFrameProbability ν →
    ∀ μ : ProbabilityMeasure GammaTwoFrameQuotient,
      HGAS.Dynamics.IsErgodicInvariantProbability
          gammaTwoHorocycleFlow μ →
        IsClosedHorocycleProbability 1 μ ∨ μ = ν

/-- Finite Haar reduction plus the pure ergodic horocycle dichotomy gives
the exact `GammaTwoDaniSmillieTheorem` interface used downstream. -/
theorem GammaTwoHasFiniteHaarFundamentalDomain.daniSmillie_of_dichotomy
    (hvolume : GammaTwoHasFiniteHaarFundamentalDomain)
    (hdynamics : GammaTwoErgodicHorocycleDichotomy) :
    GammaTwoDaniSmillieTheorem := by
  obtain ⟨ν, hν⟩ := hvolume.hasFiniteFrameVolume
  exact ⟨ν, hν, hdynamics ν hν⟩

end

end HGAS.Modular
