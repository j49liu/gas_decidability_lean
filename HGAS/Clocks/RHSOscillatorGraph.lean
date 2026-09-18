import HGAS.Clocks.RadicalClock
import HGAS.Dynamics.ErgodicFactor
import HGAS.Dynamics.ErgodicIdentityFlow
import HGAS.Dynamics.MeasureSection
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.Tactic

/-!
# Ergodic graph measures for the right-hand-side oscillator

Let `ω : d → ℝ` generate translation on the finite additive torus
`UnitAddTorus d`.  Given an integer character `a : d → ℤ`, adjoin one
circle coordinate `R` with frequency

```text
                         -∑ i, a i * ω i.
```

Then

```text
                         Ξ(x,R) = R + ∑ i, a i • x i
```

is constant along the joint flow.  The triangular homeomorphism
`(x,R) ↦ (x, Ξ(x,R))` conjugates the joint flow to base translation times
the identity flow.

If `ω` has no nontrivial annihilating integer character, every ergodic
invariant probability is normalized Haar measure on exactly one graph
`Ξ = ξ`, and its base marginal is normalized Haar measure.  The proof uses
only:

* ergodicity descending through continuous factors;
* the classification of ergodic probabilities for the identity flow;
* Fourier uniqueness of Haar measure for nonresonant torus translation; and
* recovery of a measure supported on a measurable section.

For the manuscript's right-hand-side oscillator, take `a i = 4 * c i`.
This gives frequency `-4 * ∑ i, c i * ω i` and additive invariant
`R + 4 * ∑ i, c i • x i`.  A rational coefficient vector defines a
character on `ℝ / ℤ` only when its fourfold coefficients are integral; the
final section records that exact rational interface rather than pretending
that arbitrary rational scalar multiplication is well-defined on a circle.
-/

noncomputable section

open Function MeasureTheory Set
open scoped BigOperators

namespace HGAS.Clocks.RHSOscillatorGraph

variable {d : Type*} [Fintype d]

/-- State space of a finite base torus and one added oscillator circle. -/
abbrev State (d : Type*) :=
  UnitAddTorus d × UnitAddCircle

/-- The additive torus character with integer coefficient vector `a`. -/
def baseCharacter
    (a : d → ℤ) (x : UnitAddTorus d) : UnitAddCircle :=
  ∑ i : d, a i • x i

/-- Frequency paired with the base character. -/
def characterFrequency
    (a : d → ℤ) (ω : d → ℝ) : ℝ :=
  HGAS.Clocks.RadicalClock.frequencyPairing a ω

/-- The oscillator frequency which makes `R + baseCharacter a x`
invariant. -/
def oscillatorFrequency
    (a : d → ℤ) (ω : d → ℝ) : ℝ :=
  -characterFrequency a ω

/-- The joint base-translation and resonant-oscillator flow. -/
def oscillatorFlow
    (ω : d → ℝ) (a : d → ℤ) :
    Flow ℝ (State d) where
  toFun t z :=
    (HGAS.Clocks.RadicalClock.torusTranslationFlow ω t z.1,
      z.2 + (t * oscillatorFrequency a ω : UnitAddCircle))
  cont' := by
    have hbase :
        Continuous
          (fun z : ℝ × State d ↦
            HGAS.Clocks.RadicalClock.torusTranslationFlow
              ω z.1 z.2.1) :=
      (HGAS.Clocks.RadicalClock.torusTranslationFlow ω).cont'.comp
        (continuous_fst.prodMk
          (continuous_fst.comp continuous_snd))
    have hoscillator :
        Continuous
          (fun z : ℝ × State d ↦
            z.2.2 +
              (z.1 * oscillatorFrequency a ω :
                UnitAddCircle)) := by
      apply Continuous.add
      · exact continuous_snd.comp continuous_snd
      · exact QuotientAddGroup.continuous_mk.comp
          (continuous_fst.mul continuous_const)
    exact hbase.prodMk hoscillator
  map_add' := by
    intro t u z
    apply Prod.ext
    · exact
        (HGAS.Clocks.RadicalClock.torusTranslationFlow ω).map_add
          t u z.1
    · rw [show (t + u) * oscillatorFrequency a ω =
          u * oscillatorFrequency a ω +
            t * oscillatorFrequency a ω by ring]
      simp only [QuotientAddGroup.mk_add]
      abel
  map_zero' := by
    intro z
    apply Prod.ext
    · exact
        (HGAS.Clocks.RadicalClock.torusTranslationFlow ω).map_zero_apply
          z.1
    · simp

@[simp]
theorem oscillatorFlow_apply
    (ω : d → ℝ) (a : d → ℤ)
    (t : ℝ) (z : State d) :
    oscillatorFlow ω a t z =
      (HGAS.Clocks.RadicalClock.torusTranslationFlow ω t z.1,
        z.2 + (t * oscillatorFrequency a ω : UnitAddCircle)) :=
  rfl

/-- Product of base translation with a stationary circle factor. -/
def baseIdentityFlow (ω : d → ℝ) :
    Flow ℝ (State d) where
  toFun t z :=
    (HGAS.Clocks.RadicalClock.torusTranslationFlow ω t z.1, z.2)
  cont' := by
    have hbase :
        Continuous
          (fun z : ℝ × State d ↦
            HGAS.Clocks.RadicalClock.torusTranslationFlow
              ω z.1 z.2.1) :=
      (HGAS.Clocks.RadicalClock.torusTranslationFlow ω).cont'.comp
        (continuous_fst.prodMk
          (continuous_fst.comp continuous_snd))
    exact hbase.prodMk (continuous_snd.comp continuous_snd)
  map_add' := by
    intro t u z
    apply Prod.ext
    · exact
        (HGAS.Clocks.RadicalClock.torusTranslationFlow ω).map_add
          t u z.1
    · rfl
  map_zero' := by
    intro z
    apply Prod.ext
    · exact
        (HGAS.Clocks.RadicalClock.torusTranslationFlow ω).map_zero_apply
          z.1
    · rfl

omit [Fintype d] in
@[simp]
theorem baseIdentityFlow_apply
    (ω : d → ℝ) (t : ℝ) (z : State d) :
    baseIdentityFlow ω t z =
      (HGAS.Clocks.RadicalClock.torusTranslationFlow ω t z.1, z.2) :=
  rfl

/-- The conserved additive character `Ξ`. -/
def invariantCoordinate
    (a : d → ℤ) (z : State d) : UnitAddCircle :=
  z.2 + baseCharacter a z.1

/-- Graph section of the level set `Ξ = ξ`. -/
def graphSection
    (a : d → ℤ) (ξ : UnitAddCircle)
    (x : UnitAddTorus d) : State d :=
  (x, ξ - baseCharacter a x)

/-- The graph/level set selected by `ξ`. -/
def graphSet
    (a : d → ℤ) (ξ : UnitAddCircle) : Set (State d) :=
  {z | invariantCoordinate a z = ξ}

/-! ## Algebra and topology of the invariant character -/

theorem continuous_baseCharacter (a : d → ℤ) :
    Continuous (baseCharacter a) := by
  classical
  unfold baseCharacter
  fun_prop

@[simp]
theorem baseCharacter_torusDisplacement
    (a : d → ℤ) (ω : d → ℝ) (t : ℝ) :
    baseCharacter a
        (HGAS.Clocks.RadicalClock.torusDisplacement ω t) =
      (t * characterFrequency a ω : UnitAddCircle) := by
  classical
  change
    (∑ i : d,
      a i •
        (QuotientAddGroup.mk'
          (AddSubgroup.zmultiples (1 : ℝ))) (t * ω i)) =
      (QuotientAddGroup.mk'
        (AddSubgroup.zmultiples (1 : ℝ)))
          (t *
            ∑ i : d, (a i : ℝ) * ω i)
  simp_rw [← map_zsmul]
  rw [← map_sum]
  apply congrArg
    (QuotientAddGroup.mk'
      (AddSubgroup.zmultiples (1 : ℝ)))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp]
theorem baseCharacter_add
    (a : d → ℤ) (x y : UnitAddTorus d) :
    baseCharacter a (x + y) =
      baseCharacter a x + baseCharacter a y := by
  classical
  simp only [baseCharacter, Pi.add_apply, zsmul_add,
    Finset.sum_add_distrib]

theorem continuous_invariantCoordinate (a : d → ℤ) :
    Continuous (invariantCoordinate a) := by
  apply Continuous.add continuous_snd
  exact (continuous_baseCharacter a).comp continuous_fst

theorem continuous_graphSection
    (a : d → ℤ) (ξ : UnitAddCircle) :
    Continuous (graphSection a ξ) := by
  apply continuous_id.prodMk
  exact continuous_const.sub (continuous_baseCharacter a)

@[simp]
theorem graphSection_fst
    (a : d → ℤ) (ξ : UnitAddCircle)
    (x : UnitAddTorus d) :
    (graphSection a ξ x).1 = x :=
  rfl

@[simp]
theorem invariantCoordinate_graphSection
    (a : d → ℤ) (ξ : UnitAddCircle)
    (x : UnitAddTorus d) :
    invariantCoordinate a (graphSection a ξ x) = ξ := by
  simp only [invariantCoordinate, graphSection]
  abel

theorem graphSection_leftInverse
    (a : d → ℤ) (ξ : UnitAddCircle) :
    Function.LeftInverse Prod.fst (graphSection a ξ) :=
  fun _ ↦ rfl

theorem range_graphSection_eq_graphSet
    (a : d → ℤ) (ξ : UnitAddCircle) :
    Set.range (graphSection a ξ) = graphSet a ξ := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact invariantCoordinate_graphSection a ξ x
  · intro hz
    refine ⟨z.1, ?_⟩
    apply Prod.ext
    · rfl
    · change ξ - baseCharacter a z.1 = z.2
      change z.2 + baseCharacter a z.1 = ξ at hz
      rw [← hz]
      abel

theorem measurableSet_graphSet
    (a : d → ℤ) (ξ : UnitAddCircle) :
    MeasurableSet (graphSet a ξ) := by
  exact
    isClosed_eq (continuous_invariantCoordinate a)
      continuous_const |>.measurableSet

/-! ## Conservation and triangular conjugacy -/

@[simp]
theorem invariantCoordinate_oscillatorFlow
    (ω : d → ℝ) (a : d → ℤ)
    (t : ℝ) (z : State d) :
    invariantCoordinate a (oscillatorFlow ω a t z) =
      invariantCoordinate a z := by
  rw [oscillatorFlow_apply]
  simp only [invariantCoordinate]
  rw [HGAS.Clocks.RadicalClock.torusTranslationFlow_apply]
  rw [baseCharacter_add, baseCharacter_torusDisplacement]
  rw [show t * oscillatorFrequency a ω =
      -(t * characterFrequency a ω) by
        simp only [oscillatorFrequency]
        ring]
  simp only [AddCircle.coe_neg]
  abel

theorem invariantCoordinate_semiconj
    (ω : d → ℝ) (a : d → ℤ) (t : ℝ) :
    Function.Semiconj (invariantCoordinate a)
      (oscillatorFlow ω a t)
      (Flow.id ℝ UnitAddCircle t) := by
  intro z
  simpa [Flow.id_apply] using
    invariantCoordinate_oscillatorFlow ω a t z

theorem fst_semiconj
    (ω : d → ℝ) (a : d → ℤ) (t : ℝ) :
    Function.Semiconj Prod.fst
      (oscillatorFlow ω a t)
      (HGAS.Clocks.RadicalClock.torusTranslationFlow ω t) :=
  fun _ ↦ rfl

/-- Triangular change of coordinates exposing the invariant circle. -/
def straightenHomeomorph
    (a : d → ℤ) : State d ≃ₜ State d where
  toFun z := (z.1, invariantCoordinate a z)
  invFun z := graphSection a z.2 z.1
  left_inv z := by
    apply Prod.ext
    · rfl
    · simp only [graphSection, invariantCoordinate]
      abel
  right_inv z := by
    apply Prod.ext
    · rfl
    · exact invariantCoordinate_graphSection a z.2 z.1
  continuous_toFun :=
    continuous_fst.prodMk (continuous_invariantCoordinate a)
  continuous_invFun := by
    apply continuous_fst.prodMk
    exact
      continuous_snd.sub
        ((continuous_baseCharacter a).comp continuous_fst)

@[simp]
theorem straightenHomeomorph_apply
    (a : d → ℤ) (z : State d) :
    straightenHomeomorph a z =
      (z.1, invariantCoordinate a z) :=
  rfl

@[simp]
theorem straightenHomeomorph_symm_apply
    (a : d → ℤ) (z : State d) :
    (straightenHomeomorph a).symm z =
      graphSection a z.2 z.1 :=
  rfl

/-- Exact conjugacy to base translation times an identity factor. -/
theorem straightenHomeomorph_conj
    (ω : d → ℝ) (a : d → ℤ)
    (t : ℝ) (z : State d) :
    straightenHomeomorph a (oscillatorFlow ω a t z) =
      baseIdentityFlow ω t (straightenHomeomorph a z) := by
  apply Prod.ext
  · rfl
  · exact invariantCoordinate_oscillatorFlow ω a t z

/-- The inverse triangular map satisfies the reverse conjugacy equation. -/
theorem straightenHomeomorph_symm_conj
    (ω : d → ℝ) (a : d → ℤ)
    (t : ℝ) (z : State d) :
    (straightenHomeomorph a).symm
        (baseIdentityFlow ω t z) =
      oscillatorFlow ω a t
        ((straightenHomeomorph a).symm z) := by
  apply (straightenHomeomorph a).injective
  rw [straightenHomeomorph_conj]
  simp

/-- Bundled semiconjugacy supplied by the triangular homeomorphism. -/
def straighten_isSemiconjugacy
    (ω : d → ℝ) (a : d → ℤ) :
    Flow.IsSemiconjugacy (straightenHomeomorph a)
      (oscillatorFlow ω a) (baseIdentityFlow ω) where
  cont := (straightenHomeomorph a).continuous
  surj := (straightenHomeomorph a).surjective
  semiconj t := straightenHomeomorph_conj ω a t

/-- Bundled reverse semiconjugacy supplied by the inverse homeomorphism. -/
def unstraighten_isSemiconjugacy
    (ω : d → ℝ) (a : d → ℤ) :
    Flow.IsSemiconjugacy (straightenHomeomorph a).symm
      (baseIdentityFlow ω) (oscillatorFlow ω a) where
  cont := (straightenHomeomorph a).symm.continuous
  surj := (straightenHomeomorph a).symm.surjective
  semiconj t := straightenHomeomorph_symm_conj ω a t

/-! ## Invariant graph sections and their Haar measures -/

theorem graphSection_semiconj
    (ω : d → ℝ) (a : d → ℤ)
    (ξ : UnitAddCircle) (t : ℝ) :
    Function.Semiconj (graphSection a ξ)
      (HGAS.Clocks.RadicalClock.torusTranslationFlow ω t)
      (oscillatorFlow ω a t) := by
  intro x
  apply (straightenHomeomorph a).injective
  rw [straightenHomeomorph_conj]
  simp only [straightenHomeomorph_apply,
    invariantCoordinate_graphSection, graphSection_fst,
    baseIdentityFlow_apply]

theorem graphSet_isInvariant
    (ω : d → ℝ) (a : d → ℤ)
    (ξ : UnitAddCircle) :
    IsInvariant (oscillatorFlow ω a) (graphSet a ξ) := by
  intro t z hz
  change
    invariantCoordinate a (oscillatorFlow ω a t z) = ξ
  rw [invariantCoordinate_oscillatorFlow]
  exact hz

/-- Projection of one invariant graph to the base is a homeomorphism, with
inverse `graphSection`. -/
def graphHomeomorph
    (a : d → ℤ) (ξ : UnitAddCircle) :
    UnitAddTorus d ≃ₜ graphSet a ξ where
  toFun x :=
    ⟨graphSection a ξ x,
      invariantCoordinate_graphSection a ξ x⟩
  invFun z := z.1.1
  left_inv _ := rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change ξ - baseCharacter a z.1.1 = z.1.2
      have hz := z.property
      change z.1.2 + baseCharacter a z.1.1 = ξ at hz
      calc
        ξ - baseCharacter a z.1.1 =
            (z.1.2 + baseCharacter a z.1.1) -
              baseCharacter a z.1.1 := by
          exact congrArg
            (fun q ↦ q - baseCharacter a z.1.1) hz.symm
        _ = z.1.2 := by abel
  continuous_toFun :=
    (continuous_graphSection a ξ).subtype_mk _
  continuous_invFun :=
    continuous_fst.comp continuous_subtype_val

/-- Restricted flow carried by one invariant graph. -/
def graphFlow
    (ω : d → ℝ) (a : d → ℤ)
    (ξ : UnitAddCircle) :
    Flow ℝ (graphSet a ξ) :=
  (oscillatorFlow ω a).restrict
    (graphSet_isInvariant ω a ξ)

/-- The graph homeomorphism is equivariant from base translation to the
restricted oscillator flow. -/
def graphHomeomorph_isSemiconjugacy
    (ω : d → ℝ) (a : d → ℤ)
    (ξ : UnitAddCircle) :
    Flow.IsSemiconjugacy (graphHomeomorph a ξ)
      (HGAS.Clocks.RadicalClock.torusTranslationFlow ω)
      (graphFlow ω a ξ) where
  cont := (graphHomeomorph a ξ).continuous
  surj := (graphHomeomorph a ξ).surjective
  semiconj t x := by
    apply Subtype.ext
    exact graphSection_semiconj ω a ξ t x

/-- Haar probability on the base, pushed to the graph `Ξ = ξ`. -/
def graphProbability
    (a : d → ℤ) (ξ : UnitAddCircle) :
    ProbabilityMeasure (State d) :=
  HGAS.Clocks.RadicalClock.torusHaarProbability.map
    (continuous_graphSection a ξ).measurable.aemeasurable

/-- The first marginal of a graph probability is exactly base Haar. -/
@[simp]
theorem graphProbability_map_fst
    (a : d → ℤ) (ξ : UnitAddCircle) :
    (graphProbability a ξ).map
        measurable_fst.aemeasurable =
      HGAS.Clocks.RadicalClock.torusHaarProbability := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [graphProbability, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map measurable_fst
    (continuous_graphSection a ξ).measurable]
  have hcomp :
      Prod.fst ∘ graphSection a ξ =
        id := by
    funext x
    exact graphSection_fst a ξ x
  rw [hcomp, Measure.map_id]

/-- The invariant-coordinate marginal of a graph probability is Dirac at
its graph label. -/
@[simp]
theorem graphProbability_map_invariantCoordinate
    (a : d → ℤ) (ξ : UnitAddCircle) :
    (graphProbability a ξ).map
        (continuous_invariantCoordinate a).measurable.aemeasurable =
      MeasureTheory.diracProba ξ := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [graphProbability, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map
    (continuous_invariantCoordinate a).measurable
    (continuous_graphSection a ξ).measurable]
  have hcomp :
      invariantCoordinate a ∘ graphSection a ξ =
        fun _ : UnitAddTorus d ↦ ξ := by
    funext x
    exact invariantCoordinate_graphSection a ξ x
  rw [hcomp]
  rw [Measure.map_const]
  have huniv :
      ((HGAS.Clocks.RadicalClock.torusHaarProbability
          (d := d)).toMeasure) Set.univ = 1 :=
    measure_univ
  rw [huniv, one_smul]
  rfl

/-- The graph label is uniquely determined by the graph probability. -/
theorem graphProbability_injective
    (a : d → ℤ) :
    Function.Injective (graphProbability a) := by
  intro ξ η hξη
  have hmap :=
    congrArg
      (fun μ : ProbabilityMeasure (State d) ↦
        μ.map
          (continuous_invariantCoordinate a).measurable.aemeasurable)
      hξη
  apply MeasureTheory.injective_diracProba
  simpa only [graphProbability_map_invariantCoordinate] using hmap

/-- Graph Haar measure, bundled with invariance under the resonant joint
flow. -/
def graphInvariantProbability
    (ω : d → ℝ) (a : d → ℤ)
    (ξ : UnitAddCircle) :
    HGAS.Dynamics.InvariantProbabilityMeasure
      (oscillatorFlow ω a) :=
  (HGAS.Clocks.RadicalClock.torusHaarInvariantProbability ω)
    |>.mapEquivariant
      (graphSection a ξ)
      (continuous_graphSection a ξ)
      (graphSection_semiconj ω a ξ)

@[simp]
theorem graphInvariantProbability_measure
    (ω : d → ℝ) (a : d → ℤ)
    (ξ : UnitAddCircle) :
    (graphInvariantProbability ω a ξ).measure =
      graphProbability a ξ :=
  rfl

theorem graphProbability_isInvariant
    (ω : d → ℝ) (a : d → ℤ)
    (ξ : UnitAddCircle) :
    HGAS.Dynamics.IsInvariantProbability
      (oscillatorFlow ω a) (graphProbability a ξ) :=
  (graphInvariantProbability ω a ξ).invariant

/-! ## Marginals and ergodic graph classification -/

omit [Fintype d] in
/-- First-coordinate marginal of a probability on the oscillator state. -/
def baseMarginal
    (μ : ProbabilityMeasure (State d)) :
    ProbabilityMeasure (UnitAddTorus d) :=
  μ.map measurable_fst.aemeasurable

/-- Marginal of the conserved coordinate. -/
def invariantCoordinateMarginal
    (a : d → ℤ)
    (μ : ProbabilityMeasure (State d)) :
    ProbabilityMeasure UnitAddCircle :=
  μ.map
    (continuous_invariantCoordinate a).measurable.aemeasurable

/-- Every invariant joint probability has base Haar marginal.  Ergodicity is
not needed for this part. -/
theorem baseMarginal_eq_torusHaar_of_noCharacter
    (ω : d → ℝ)
    (hω :
      HGAS.Clocks.RadicalIndependence.HasNoNontrivialIntegerCharacter
        ω)
    (a : d → ℤ)
    (μ : ProbabilityMeasure (State d))
    (hμ :
      HGAS.Dynamics.IsInvariantProbability
        (oscillatorFlow ω a) μ) :
    baseMarginal μ =
      HGAS.Clocks.RadicalClock.torusHaarProbability := by
  let μInvariant :
      HGAS.Dynamics.InvariantProbabilityMeasure
        (oscillatorFlow ω a) :=
    ⟨μ, hμ⟩
  let ν :
      HGAS.Dynamics.InvariantProbabilityMeasure
        (HGAS.Clocks.RadicalClock.torusTranslationFlow ω) :=
    μInvariant.mapEquivariant Prod.fst continuous_fst
      (fst_semiconj ω a)
  have hν :=
    HGAS.Clocks.RadicalClock.invariantProbability_eq_torusHaar_of_noCharacter
      ω hω ν
  simpa only [ν, μInvariant, baseMarginal] using hν

/-- Ergodicity forces the conserved coordinate to have one almost-sure
value. -/
theorem exists_invariantCoordinateMarginal_eq_dirac
    (ω : d → ℝ) (a : d → ℤ)
    (μ : ProbabilityMeasure (State d))
    (hμ :
      HGAS.Dynamics.IsErgodicInvariantProbability
        (oscillatorFlow ω a) μ) :
    ∃ ξ : UnitAddCircle,
      invariantCoordinateMarginal a μ =
        MeasureTheory.diracProba ξ := by
  have hfactor :
      HGAS.Dynamics.IsErgodicInvariantProbability
        (Flow.id ℝ UnitAddCircle)
        (invariantCoordinateMarginal a μ) := by
    simpa only [invariantCoordinateMarginal] using
      hμ.mapEquivariant
        (invariantCoordinate a)
        (continuous_invariantCoordinate a)
        (invariantCoordinate_semiconj ω a)
  exact
    HGAS.Dynamics.exists_eq_diracProba_of_isErgodicInvariantProbability_identity
      (invariantCoordinateMarginal a μ) hfactor

/-- A Dirac invariant-coordinate marginal is equivalent to full mass on
the corresponding graph, in the direction needed by the classification. -/
theorem graphSet_measure_eq_one_of_invariantCoordinateMarginal_eq_dirac
    (a : d → ℤ)
    (μ : ProbabilityMeasure (State d))
    (ξ : UnitAddCircle)
    (hξ :
      invariantCoordinateMarginal a μ =
        MeasureTheory.diracProba ξ) :
    (μ : Measure (State d)) (graphSet a ξ) = 1 := by
  have hmap :
      Measure.map (invariantCoordinate a)
          (μ : Measure (State d)) =
        Measure.dirac ξ := by
    have hmeasure :=
      congrArg ProbabilityMeasure.toMeasure hξ
    simpa only [invariantCoordinateMarginal,
      ProbabilityMeasure.toMeasure_map,
      MeasureTheory.diracProba] using hmeasure
  change
    (μ : Measure (State d))
      ((invariantCoordinate a) ⁻¹' ({ξ} : Set UnitAddCircle)) = 1
  rw [← Measure.map_apply
    (continuous_invariantCoordinate a).measurable
    (measurableSet_singleton ξ)]
  rw [hmap]
  simp

theorem ae_mem_graphSet_of_invariantCoordinateMarginal_eq_dirac
    (a : d → ℤ)
    (μ : ProbabilityMeasure (State d))
    (ξ : UnitAddCircle)
    (hξ :
      invariantCoordinateMarginal a μ =
        MeasureTheory.diracProba ξ) :
    ∀ᵐ z ∂(μ : Measure (State d)), z ∈ graphSet a ξ := by
  apply
    (ae_mem_iff_measure_eq
      (measurableSet_graphSet a ξ).nullMeasurableSet).2
  rw [graphSet_measure_eq_one_of_invariantCoordinateMarginal_eq_dirac
    a μ ξ hξ]
  exact measure_univ.symm

theorem ae_mem_range_graphSection_of_invariantCoordinateMarginal_eq_dirac
    (a : d → ℤ)
    (μ : ProbabilityMeasure (State d))
    (ξ : UnitAddCircle)
    (hξ :
      invariantCoordinateMarginal a μ =
        MeasureTheory.diracProba ξ) :
    ∀ᵐ z ∂(μ : Measure (State d)),
      z ∈ Set.range (graphSection a ξ) := by
  simpa only [range_graphSection_eq_graphSet] using
    ae_mem_graphSet_of_invariantCoordinateMarginal_eq_dirac
      a μ ξ hξ

/-- Exact measure classification before uniqueness of the graph label is
packaged: every ergodic invariant probability is Haar pushed along one
graph section. -/
theorem exists_eq_graphProbability_of_isErgodicInvariant
    (ω : d → ℝ)
    (hω :
      HGAS.Clocks.RadicalIndependence.HasNoNontrivialIntegerCharacter
        ω)
    (a : d → ℤ)
    (μ : ProbabilityMeasure (State d))
    (hμ :
      HGAS.Dynamics.IsErgodicInvariantProbability
        (oscillatorFlow ω a) μ) :
    ∃ ξ : UnitAddCircle, μ = graphProbability a ξ := by
  obtain ⟨ξ, hξ⟩ :=
    exists_invariantCoordinateMarginal_eq_dirac
      ω a μ hμ
  have hbase :
      baseMarginal μ =
        HGAS.Clocks.RadicalClock.torusHaarProbability :=
    baseMarginal_eq_torusHaar_of_noCharacter
      ω hω a μ hμ.invariant
  have hsection :=
    HGAS.Dynamics.probabilityMeasure_eq_map_section_of_ae_mem_range
      μ Prod.fst measurable_fst
      (graphSection a ξ) (continuous_graphSection a ξ).measurable
      (graphSection_leftInverse a ξ)
      (ae_mem_range_graphSection_of_invariantCoordinateMarginal_eq_dirac
        a μ ξ hξ)
  refine ⟨ξ, ?_⟩
  rw [show μ.map measurable_fst.aemeasurable =
      HGAS.Clocks.RadicalClock.torusHaarProbability from hbase] at hsection
  simpa only [graphProbability] using hsection

/-- **Ergodic right-hand-side oscillator graph theorem.**

The base marginal is Haar, and there is exactly one graph label whose Haar
graph probability equals the given ergodic invariant probability. -/
theorem ergodicInvariantProbability_graphClassification
    (ω : d → ℝ)
    (hω :
      HGAS.Clocks.RadicalIndependence.HasNoNontrivialIntegerCharacter
        ω)
    (a : d → ℤ)
    (μ : ProbabilityMeasure (State d))
    (hμ :
      HGAS.Dynamics.IsErgodicInvariantProbability
        (oscillatorFlow ω a) μ) :
    baseMarginal μ =
        HGAS.Clocks.RadicalClock.torusHaarProbability ∧
      ∃! ξ : UnitAddCircle, μ = graphProbability a ξ := by
  refine
    ⟨baseMarginal_eq_torusHaar_of_noCharacter
      ω hω a μ hμ.invariant, ?_⟩
  obtain ⟨ξ, hξ⟩ :=
    exists_eq_graphProbability_of_isErgodicInvariant
      ω hω a μ hμ
  refine ⟨ξ, hξ, ?_⟩
  intro η hη
  apply graphProbability_injective a
  exact hη.symm.trans hξ

/-- The unique graph in the classification carries full mass. -/
theorem ergodicInvariantProbability_existsUnique_graphSupport
    (ω : d → ℝ)
    (hω :
      HGAS.Clocks.RadicalIndependence.HasNoNontrivialIntegerCharacter
        ω)
    (a : d → ℤ)
    (μ : ProbabilityMeasure (State d))
    (hμ :
      HGAS.Dynamics.IsErgodicInvariantProbability
        (oscillatorFlow ω a) μ) :
    ∃! ξ : UnitAddCircle,
      μ = graphProbability a ξ ∧
      (μ : Measure (State d)) (graphSet a ξ) = 1 := by
  obtain ⟨ξ, hξ, hunique⟩ :=
    (ergodicInvariantProbability_graphClassification
      ω hω a μ hμ).2
  refine ⟨ξ, ⟨hξ, ?_⟩, ?_⟩
  · rw [hξ]
    exact
      graphSet_measure_eq_one_of_invariantCoordinateMarginal_eq_dirac
        a (graphProbability a ξ) ξ
        (graphProbability_map_invariantCoordinate a ξ)
  · intro η hη
    exact hunique η hη.1

/-! ## Equivariant factors of arbitrary ergodic joinings -/

variable {K : Type*}
  [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]
  {ϕ : Flow ℝ K}

/-- Direct clock-pushforward statement for an arbitrary invariant joining:
the composed base projection has Haar marginal.  Ergodicity is not needed. -/
theorem equivariant_baseMarginal_eq_torusHaar_of_noCharacter
    (ω : d → ℝ)
    (hω :
      HGAS.Clocks.RadicalIndependence.HasNoNontrivialIntegerCharacter
        ω)
    (a : d → ℤ)
    (μ : ProbabilityMeasure K)
    (hμ : HGAS.Dynamics.IsInvariantProbability ϕ μ)
    (π : K → State d)
    (hπ : Continuous π)
    (hequiv :
      ∀ t : ℝ,
        Function.Semiconj π (ϕ t)
          (oscillatorFlow ω a t)) :
    μ.map
        (continuous_fst.comp hπ).measurable.aemeasurable =
      HGAS.Clocks.RadicalClock.torusHaarProbability := by
  let μInvariant :
      HGAS.Dynamics.InvariantProbabilityMeasure ϕ :=
    ⟨μ, hμ⟩
  let ν :
      HGAS.Dynamics.InvariantProbabilityMeasure
        (HGAS.Clocks.RadicalClock.torusTranslationFlow ω) :=
    μInvariant.mapEquivariant
      (Prod.fst ∘ π)
      (continuous_fst.comp hπ)
      (fun t ↦ (fst_semiconj ω a t).comp_left (hequiv t))
  have hν :=
    HGAS.Clocks.RadicalClock.invariantProbability_eq_torusHaar_of_noCharacter
      ω hω ν
  simpa only [ν, μInvariant] using hν

/-- An arbitrary ergodic joining has a graph-classified oscillator
marginal.  This is the factor form used by a larger polynomial source. -/
theorem equivariantErgodicMarginal_graphClassification
    (ω : d → ℝ)
    (hω :
      HGAS.Clocks.RadicalIndependence.HasNoNontrivialIntegerCharacter
        ω)
    (a : d → ℤ)
    (μ : ProbabilityMeasure K)
    (hμ :
      HGAS.Dynamics.IsErgodicInvariantProbability ϕ μ)
    (π : K → State d)
    (hπ : Continuous π)
    (hequiv :
      ∀ t : ℝ,
        Function.Semiconj π (ϕ t)
          (oscillatorFlow ω a t)) :
    let ν := μ.map hπ.measurable.aemeasurable
    baseMarginal ν =
        HGAS.Clocks.RadicalClock.torusHaarProbability ∧
      ∃! ξ : UnitAddCircle, ν = graphProbability a ξ := by
  dsimp only
  exact
    ergodicInvariantProbability_graphClassification
      ω hω a
      (μ.map hπ.measurable.aemeasurable)
      (hμ.mapEquivariant π hπ hequiv)

/-- Support-enhanced factor form: the unique oscillator marginal gives full
mass to its selected invariant graph. -/
theorem equivariantErgodicMarginal_existsUnique_graphSupport
    (ω : d → ℝ)
    (hω :
      HGAS.Clocks.RadicalIndependence.HasNoNontrivialIntegerCharacter
        ω)
    (a : d → ℤ)
    (μ : ProbabilityMeasure K)
    (hμ :
      HGAS.Dynamics.IsErgodicInvariantProbability ϕ μ)
    (π : K → State d)
    (hπ : Continuous π)
    (hequiv :
      ∀ t : ℝ,
        Function.Semiconj π (ϕ t)
          (oscillatorFlow ω a t)) :
    let ν := μ.map hπ.measurable.aemeasurable
    ∃! ξ : UnitAddCircle,
      ν = graphProbability a ξ ∧
      (ν : Measure (State d)) (graphSet a ξ) = 1 := by
  dsimp only
  exact
    ergodicInvariantProbability_existsUnique_graphSupport
      ω hω a
      (μ.map hπ.measurable.aemeasurable)
      (hμ.mapEquivariant π hπ hequiv)

/-! ## The manuscript's factor-four right-hand-side specialization -/

/-- Integer character multiplying every coefficient by the fourth-power
clock convention. -/
def fourMultiplier (c : d → ℤ) : d → ℤ :=
  fun i ↦ 4 * c i

/-- Literal oscillator frequency `-4 ∑ cᵢ ωᵢ`. -/
def rhsOscillatorFrequency
    (c : d → ℤ) (ω : d → ℝ) : ℝ :=
  -4 * ∑ i : d, (c i : ℝ) * ω i

theorem oscillatorFrequency_fourMultiplier
    (c : d → ℤ) (ω : d → ℝ) :
    oscillatorFrequency (fourMultiplier c) ω =
      rhsOscillatorFrequency c ω := by
  simp only [oscillatorFrequency, characterFrequency,
    HGAS.Clocks.RadicalClock.frequencyPairing,
    fourMultiplier, rhsOscillatorFrequency]
  have hsum :
      (∑ i : d, ((4 * c i : ℤ) : ℝ) * ω i) =
        4 * ∑ i : d, (c i : ℝ) * ω i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  rw [hsum]
  ring

/-- The right-hand-side oscillator flow with frequency
`-4 ∑ cᵢ ωᵢ`. -/
def rhsOscillatorFlow
    (ω : d → ℝ) (c : d → ℤ) :
    Flow ℝ (State d) :=
  oscillatorFlow ω (fourMultiplier c)

/-- Conserved coordinate
`R + 4 ∑ cᵢ • xᵢ` in additive notation. -/
def rhsInvariantCoordinate
    (c : d → ℤ) (z : State d) : UnitAddCircle :=
  invariantCoordinate (fourMultiplier c) z

@[simp]
theorem baseCharacter_fourMultiplier
    (c : d → ℤ) (x : UnitAddTorus d) :
    baseCharacter (fourMultiplier c) x =
      (4 : ℤ) • baseCharacter c x := by
  classical
  simp only [baseCharacter, fourMultiplier, mul_smul,
    Finset.smul_sum]

@[simp]
theorem rhsInvariantCoordinate_eq
    (c : d → ℤ) (z : State d) :
    rhsInvariantCoordinate c z =
      z.2 + (4 : ℤ) • baseCharacter c z.1 := by
  simp only [rhsInvariantCoordinate, invariantCoordinate,
    baseCharacter_fourMultiplier]

@[simp]
theorem rhsOscillatorFlow_apply
    (ω : d → ℝ) (c : d → ℤ)
    (t : ℝ) (z : State d) :
    rhsOscillatorFlow ω c t z =
      (HGAS.Clocks.RadicalClock.torusTranslationFlow ω t z.1,
        z.2 + (t * rhsOscillatorFrequency c ω :
          UnitAddCircle)) := by
  rw [rhsOscillatorFlow, oscillatorFlow_apply,
    oscillatorFrequency_fourMultiplier]

@[simp]
theorem rhsInvariantCoordinate_rhsOscillatorFlow
    (ω : d → ℝ) (c : d → ℤ)
    (t : ℝ) (z : State d) :
    rhsInvariantCoordinate c
        (rhsOscillatorFlow ω c t z) =
      rhsInvariantCoordinate c z :=
  invariantCoordinate_oscillatorFlow
    ω (fourMultiplier c) t z

/-- Manuscript-facing specialization of the graph classification. -/
theorem rhsErgodicInvariantProbability_graphClassification
    (ω : d → ℝ)
    (hω :
      HGAS.Clocks.RadicalIndependence.HasNoNontrivialIntegerCharacter
        ω)
    (c : d → ℤ)
    (μ : ProbabilityMeasure (State d))
    (hμ :
      HGAS.Dynamics.IsErgodicInvariantProbability
        (rhsOscillatorFlow ω c) μ) :
    baseMarginal μ =
        HGAS.Clocks.RadicalClock.torusHaarProbability ∧
      ∃! ξ : UnitAddCircle,
        μ = graphProbability (fourMultiplier c) ξ :=
  ergodicInvariantProbability_graphClassification
    ω hω (fourMultiplier c) μ hμ

/-! ## Rational coefficients with an integral fourfold character -/

/-- Rational coefficients together with the integer character represented
by their fourfold multiples.

The witness is necessary: multiplication by an arbitrary rational number
is not a well-defined endomorphism of `ℝ / ℤ`. -/
structure FourIntegralRationalCoefficients (d : Type*) where
  /-- Rational coefficient vector. -/
  value : d → ℚ
  /-- Integer lift of four times the coefficient vector. -/
  fourValue : d → ℤ
  /-- The lift really represents `4 * value`. -/
  fourValue_spec :
    ∀ i, (fourValue i : ℚ) = 4 * value i

/-- Every integer vector gives rational coefficients with the expected
fourfold character. -/
def FourIntegralRationalCoefficients.ofInteger
    (c : d → ℤ) :
    FourIntegralRationalCoefficients d where
  value i := c i
  fourValue := fourMultiplier c
  fourValue_spec := by
    intro i
    simp only [fourMultiplier]
    push_cast
    ring

/-- Literal real frequency attached to a four-integral rational vector. -/
def rationalRhsOscillatorFrequency
    (c : FourIntegralRationalCoefficients d)
    (ω : d → ℝ) : ℝ :=
  -4 * ∑ i : d, (c.value i : ℝ) * ω i

theorem oscillatorFrequency_fourIntegralRational
    (c : FourIntegralRationalCoefficients d)
    (ω : d → ℝ) :
    oscillatorFrequency c.fourValue ω =
      rationalRhsOscillatorFrequency c ω := by
  simp only [oscillatorFrequency, characterFrequency,
    HGAS.Clocks.RadicalClock.frequencyPairing,
    rationalRhsOscillatorFrequency]
  have hsum :
      (∑ i : d, (c.fourValue i : ℝ) * ω i) =
        4 * ∑ i : d, (c.value i : ℝ) * ω i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hi :
        (c.fourValue i : ℝ) =
          4 * (c.value i : ℝ) := by
      exact_mod_cast c.fourValue_spec i
    rw [hi]
    ring
  rw [hsum]
  ring

/-- Joint flow for a rational coefficient vector whose fourfold character
is integral. -/
def rationalRhsOscillatorFlow
    (ω : d → ℝ)
    (c : FourIntegralRationalCoefficients d) :
    Flow ℝ (State d) :=
  oscillatorFlow ω c.fourValue

@[simp]
theorem rationalRhsOscillatorFlow_apply
    (ω : d → ℝ)
    (c : FourIntegralRationalCoefficients d)
    (t : ℝ) (z : State d) :
    rationalRhsOscillatorFlow ω c t z =
      (HGAS.Clocks.RadicalClock.torusTranslationFlow ω t z.1,
        z.2 + (t * rationalRhsOscillatorFrequency c ω :
          UnitAddCircle)) := by
  rw [rationalRhsOscillatorFlow, oscillatorFlow_apply,
    oscillatorFrequency_fourIntegralRational]

/-- Rational-coefficient specialization of the graph classification. -/
theorem rationalRhsErgodicInvariantProbability_graphClassification
    (ω : d → ℝ)
    (hω :
      HGAS.Clocks.RadicalIndependence.HasNoNontrivialIntegerCharacter
        ω)
    (c : FourIntegralRationalCoefficients d)
    (μ : ProbabilityMeasure (State d))
    (hμ :
      HGAS.Dynamics.IsErgodicInvariantProbability
        (rationalRhsOscillatorFlow ω c) μ) :
    baseMarginal μ =
        HGAS.Clocks.RadicalClock.torusHaarProbability ∧
      ∃! ξ : UnitAddCircle,
        μ = graphProbability c.fourValue ξ :=
  ergodicInvariantProbability_graphClassification
    ω hω c.fourValue μ hμ

end HGAS.Clocks.RHSOscillatorGraph
