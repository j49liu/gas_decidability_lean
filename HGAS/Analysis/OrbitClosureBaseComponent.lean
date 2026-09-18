import HGAS.Compiler.CompactAccumulatorPipelineComponentGraph
import HGAS.Dynamics.KrylovBogolyubov
import Mathlib.Tactic

/-!
# Canonical invariant components from orbit closures

The finite-graph construction only needs one compact invariant component.
Given a seed point of the compact base flow, the closure of its complete
orbit is a canonical such component.  This module packages that elementary
construction and supplies an invariant probability by the
Krylov--Bogolyubov theorem.

It also records two closure principles used repeatedly in the detector
application:

* a continuous identity holding on the seed orbit holds on its closure;
* a closed continuous inequality holding on the seed orbit holds on its
  closure.

Consequently a concrete no-instance proof may work first on the explicit
canonical trajectory and only then pass to the component required by the
compiler.
-/

noncomputable section

open Function Set

namespace HGAS.Analysis

open HGAS.CompactAccumulatorPipelineCode

universe u

variable {n k l : ℕ}
variable {layout : Fin n → Fin k ⊕ Fin l}
variable {E M : ℕ} {P : PolynomialFieldCode n}

/-- The closure of the complete base-flow orbit through `seed`, bundled as
a measurable invariant component. -/
def orbitClosureBaseComponent
    (seed : BaseSpace layout) :
    BaseInvariantComponent layout E M P where
  carrier :=
    closure
      ((baseFlow layout E M P).orbit seed)
  measurableSet_carrier :=
    isClosed_closure.measurableSet
  invariant := by
    intro t b hb
    exact
      ((baseFlow layout E M P).isInvariant_orbit seed t).closure
        ((baseFlow layout E M P).continuous
          continuous_const continuous_id) hb

namespace orbitClosureBaseComponent

variable (seed : BaseSpace layout)

/-- The seed itself belongs to its orbit-closure component. -/
def seedPoint :
    (orbitClosureBaseComponent
      (layout := layout) (E := E) (M := M) (P := P)
      seed).Space :=
  ⟨seed,
    subset_closure
      ((baseFlow layout E M P).mem_orbit_self seed)⟩

/-- Every point on the complete seed orbit belongs to the orbit-closure
component. -/
def orbitPoint (t : ℝ) :
    (orbitClosureBaseComponent
      (layout := layout) (E := E) (M := M) (P := P)
      seed).Space :=
  ⟨baseFlow layout E M P t seed,
    subset_closure
      ((baseFlow layout E M P).mem_orbit seed t)⟩

@[simp]
theorem coe_seedPoint :
    ((seedPoint
      (layout := layout) (E := E) (M := M) (P := P)
      seed :
        (orbitClosureBaseComponent
          (layout := layout) (E := E) (M := M) (P := P)
          seed).Space) :
      BaseSpace layout) = seed :=
  rfl

@[simp]
theorem coe_orbitPoint (t : ℝ) :
    ((orbitPoint
      (layout := layout) (E := E) (M := M) (P := P)
      seed t :
        (orbitClosureBaseComponent
          (layout := layout) (E := E) (M := M) (P := P)
          seed).Space) :
      BaseSpace layout) =
        baseFlow layout E M P t seed :=
  rfl

/-- The restricted component flow sends its seed to the corresponding
ambient orbit point. -/
theorem flow_seedPoint (t : ℝ) :
    (orbitClosureBaseComponent
        (layout := layout) (E := E) (M := M) (P := P)
        seed).flow t
      (seedPoint
        (layout := layout) (E := E) (M := M) (P := P)
        seed) =
      orbitPoint
        (layout := layout) (E := E) (M := M) (P := P)
        seed t := by
  apply Subtype.ext
  rfl

/-- The orbit-closure component carries an invariant probability. -/
def probability :
    HGAS.Dynamics.InvariantProbabilityMeasure
      (orbitClosureBaseComponent
        (layout := layout) (E := E) (M := M) (P := P)
        seed).flow :=
  let C :=
    orbitClosureBaseComponent
      (layout := layout) (E := E) (M := M) (P := P)
      seed
  letI : CompactSpace C.Space :=
    isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  letI : Nonempty C.Space :=
    ⟨seedPoint
      (layout := layout) (E := E) (M := M) (P := P)
      seed⟩
  Classical.choice
    (HGAS.Dynamics.nonempty_invariantProbabilityMeasure C.flow)

end orbitClosureBaseComponent

/-! ## Closure transfer lemmas -/

/-- Two continuous maps which agree on the seed orbit agree on the whole
orbit closure. -/
theorem eqOn_orbitClosure_of_continuous
    {Y : Type u} [TopologicalSpace Y] [T2Space Y]
    (seed : BaseSpace layout)
    (f g : BaseSpace layout → Y)
    (hf : Continuous f) (hg : Continuous g)
    (horbit :
      ∀ t : ℝ,
        f (baseFlow layout E M P t seed) =
          g (baseFlow layout E M P t seed)) :
    Set.EqOn f g
      (orbitClosureBaseComponent
        (layout := layout) (E := E) (M := M) (P := P)
        seed).carrier := by
  have hEq :
      Set.EqOn f g
        ((baseFlow layout E M P).orbit seed) := by
    intro b hb
    rcases hb with ⟨t, rfl⟩
    exact horbit t
  exact hEq.closure hf hg

/-- A lower bound for a continuous real observable transfers from the
seed orbit to its closure. -/
theorem lowerBound_on_orbitClosure_of_continuous
    (seed : BaseSpace layout)
    (f : BaseSpace layout → ℝ)
    (hf : Continuous f)
    (c : ℝ)
    (horbit :
      ∀ t : ℝ,
        c ≤ f (baseFlow layout E M P t seed)) :
    ∀ b :
      (orbitClosureBaseComponent
        (layout := layout) (E := E) (M := M) (P := P)
        seed).Space,
      c ≤ f b := by
  have hclosed : IsClosed {b : BaseSpace layout | c ≤ f b} :=
    isClosed_Ici.preimage hf
  have hsubset :
      (baseFlow layout E M P).orbit seed ⊆
        {b : BaseSpace layout | c ≤ f b} := by
    rintro b ⟨t, rfl⟩
    exact horbit t
  have hclosure :
      closure ((baseFlow layout E M P).orbit seed) ⊆
        {b : BaseSpace layout | c ≤ f b} :=
    closure_minimal hsubset hclosed
  intro b
  exact hclosure b.2

/-- An upper absolute bound for a continuous real observable likewise
transfers from the seed orbit to its closure. -/
theorem absBound_on_orbitClosure_of_continuous
    (seed : BaseSpace layout)
    (f : BaseSpace layout → ℝ)
    (hf : Continuous f)
    (C : ℝ)
    (horbit :
      ∀ t : ℝ,
        |f (baseFlow layout E M P t seed)| ≤ C) :
    ∀ b :
      (orbitClosureBaseComponent
        (layout := layout) (E := E) (M := M) (P := P)
        seed).Space,
      |f b| ≤ C := by
  have h :=
    lowerBound_on_orbitClosure_of_continuous
      (layout := layout) (E := E) (M := M) (P := P)
      seed (fun b ↦ -|f b|) (by fun_prop) (-C)
      (fun t ↦ by
        simpa only [neg_le_neg_iff] using horbit t)
  intro b
  have hb := h b
  linarith

end HGAS.Analysis
