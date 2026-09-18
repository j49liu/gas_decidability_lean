import HGAS.Analysis.OrbitClosureBaseComponent
import Mathlib.Tactic

/-!
# The defining orbit is dense in its orbit-closure component

`orbitClosureBaseComponent seed` is, by definition, the closure of the
complete orbit through `seed`.  The ambient closure-transfer lemmas are
convenient when both sides of an identity are defined on the whole compact
base.  In applications one often constructs an observable only on the
component itself (for example, a quotient by a coordinate which is known
to be nonzero only on that component).  The elementary dense-range result
below is the corresponding intrinsic interface.
-/

noncomputable section

open Function Set

namespace HGAS.Analysis

open HGAS.CompactAccumulatorPipelineCode

universe u

variable {n k l : ℕ}
variable {layout : Fin n → Fin k ⊕ Fin l}
variable {E M : ℕ} {P : PolynomialFieldCode n}

namespace orbitClosureBaseComponent

variable (seed : BaseSpace layout)

/-- The named complete seed orbit has dense range in its orbit-closure
component. -/
theorem denseRange_orbitPoint :
    DenseRange
      (orbitPoint
        (layout := layout) (E := E) (M := M) (P := P)
        seed) := by
  rw [DenseRange, Subtype.dense_iff]
  intro b hb
  change
    b ∈
      closure
        (((↑) :
            (orbitClosureBaseComponent
              (layout := layout) (E := E) (M := M) (P := P)
              seed).Space →
              BaseSpace layout) ''
          Set.range
            (orbitPoint
              (layout := layout) (E := E) (M := M) (P := P)
              seed))
  have himage :
      (((↑) :
          (orbitClosureBaseComponent
            (layout := layout) (E := E) (M := M) (P := P)
            seed).Space →
            BaseSpace layout) ''
        Set.range
          (orbitPoint
            (layout := layout) (E := E) (M := M) (P := P)
            seed)) =
        (baseFlow layout E M P).orbit seed := by
    ext x
    constructor
    · rintro ⟨b, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact
        ⟨orbitPoint
            (layout := layout) (E := E) (M := M) (P := P)
            seed t,
          ⟨t, rfl⟩, rfl⟩
  rw [himage]
  exact hb

/-- Two continuous component observables which agree on the named seed
orbit agree everywhere on the orbit closure. -/
theorem eq_of_continuous_on_orbit
    {Y : Type u} [TopologicalSpace Y] [T2Space Y]
    (f g :
      (orbitClosureBaseComponent
        (layout := layout) (E := E) (M := M) (P := P)
        seed).Space → Y)
    (hf : Continuous f) (hg : Continuous g)
    (horbit :
      ∀ t : ℝ,
        f (orbitPoint
            (layout := layout) (E := E) (M := M) (P := P)
            seed t) =
          g (orbitPoint
            (layout := layout) (E := E) (M := M) (P := P)
            seed t)) :
    f = g := by
  exact
    (denseRange_orbitPoint
      (layout := layout) (E := E) (M := M) (P := P)
      seed).equalizer hf hg (funext horbit)

end orbitClosureBaseComponent

end HGAS.Analysis
