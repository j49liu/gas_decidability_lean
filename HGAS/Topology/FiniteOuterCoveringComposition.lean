import Mathlib.Topology.Covering.Basic

/-!
# Composition with a finite-sheeted outer covering

This file proves that the composite of two covering maps is a covering map
when every fiber of the outer covering is finite.

The finiteness hypothesis is the source of the only non-formal topological
idea.  Fix a point `x` in the final base and trivialize the outer covering
over a neighborhood of `x`.  For each point `i` in the outer fiber, choose
an inner evenly covered neighborhood around `i`.  The inverse of the
`i`-th outer sheet pulls that neighborhood back to a neighborhood of `x`.
There are only finitely many `i`, so the intersection of all these pulled
back neighborhoods is still open.  Over this common neighborhood, every
composite sheet is obtained by composing one inner sheet with one outer
sheet.

The proof also treats all empty-fiber cases.  Thus the final theorem does
not assume either covering is surjective, and the inner covering may have
infinite fibers.  The sheet index in the nonempty case is the dependent
sum

`Σ i : f ⁻¹' {x}, p ⁻¹' {i}`,

which records first an outer sheet and then an inner sheet above it.
-/

open Bundle Function Set Topology

namespace HGAS.Covering

noncomputable section

variable {Z B : Type*} [TopologicalSpace Z] [TopologicalSpace B]
  {F : Type*} [TopologicalSpace F] [DiscreteTopology F] {q : Z → B}

/-- A single sheet of a bundle trivialization, viewed as an open partial
homeomorphism to the base. -/
private def trivializationSlice (e : Trivialization F q) (v : F) :
    OpenPartialHomeomorph Z B :=
  e.toOpenPartialHomeomorph.trans
    { toFun := Prod.fst
      invFun := fun b ↦ (b, v)
      source := e.baseSet ×ˢ ({v} : Set F)
      target := e.baseSet
      map_source' := fun _ h ↦ h.1
      map_target' := fun _ h ↦ ⟨h, rfl⟩
      left_inv' := fun _ h ↦ Prod.ext rfl h.2.symm
      right_inv' := fun _ _ ↦ rfl
      open_source := e.open_baseSet.prod (isOpen_discrete _)
      open_target := e.open_baseSet
      continuousOn_toFun := continuousOn_fst
      continuousOn_invFun := by fun_prop }

private theorem trivializationSlice_target (e : Trivialization F q) (v : F) :
    (trivializationSlice e v).target = e.baseSet := by
  ext b
  simp [trivializationSlice, e.target_eq]

private theorem trivializationSlice_apply (e : Trivialization F q) (v : F)
    {z : Z} (hz : z ∈ (trivializationSlice e v).source) :
    trivializationSlice e v z = q z := by
  exact e.proj_toFun z (by
    simp only [trivializationSlice, OpenPartialHomeomorph.trans_source] at hz
    exact hz.1)

private theorem mem_trivializationSlice_source_iff
    (e : Trivialization F q) (v : F) (z : Z) :
    z ∈ (trivializationSlice e v).source ↔
      z ∈ e.source ∧ (e z).2 = v := by
  rw [trivializationSlice, OpenPartialHomeomorph.trans_source]
  constructor
  · rintro ⟨hz, hcoord⟩
    exact ⟨hz, hcoord.2⟩
  · rintro ⟨hz, hcoord⟩
    have htarget := e.map_source hz
    rw [e.target_eq] at htarget
    exact ⟨hz, htarget.1, hcoord⟩

private theorem trivializationSlice_symm_apply (e : Trivialization F q) (v : F)
    (b : B) :
    (trivializationSlice e v).symm b =
      e.toOpenPartialHomeomorph.symm (b, v) := by
  simp only [trivializationSlice, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_apply]
  rfl

private theorem toTrivialization_baseSet {X : Type*}
    [TopologicalSpace X] {g : Z → X} {x : X} {I : Type*}
    [TopologicalSpace I] [Nonempty I] (h : IsEvenlyCovered g x I) :
    h.toTrivialization.baseSet = h.2.choose := by
  rfl

private theorem preimage_choose_eq_empty
    {X : Type*} [TopologicalSpace X] {g : Z → X} {x : X}
    {I : Type*} [TopologicalSpace I] [IsEmpty I]
    (h : IsEvenlyCovered g x I) :
    g ⁻¹' h.2.choose = ∅ := by
  apply eq_empty_of_forall_notMem
  intro z hz
  exact isEmptyElim
    (h.2.choose_spec.2.2.2.choose ⟨z, hz⟩).2

private theorem toTrivialization_apply_fiber
    {g : Z → B} {x : B} (h : IsEvenlyCovered g x (g ⁻¹' {x}))
    [Nonempty (g ⁻¹' {x})] (i : g ⁻¹' {x}) :
    (h.toTrivialization (i : Z)).2 = i := by
  rcases i with ⟨i, hi⟩
  simp only [mem_preimage, mem_singleton_iff] at hi
  subst x
  exact h.toTrivialization_apply

private theorem toTrivialization_symm_fiber
    {g : Z → B} {x : B} (h : IsEvenlyCovered g x (g ⁻¹' {x}))
    [Nonempty (g ⁻¹' {x})] (i : g ⁻¹' {x}) :
    h.toTrivialization.toOpenPartialHomeomorph.symm (x, i) = i := by
  have hi : g (i : Z) = x := by
    simpa only [mem_preimage, mem_singleton_iff] using i.property
  have hi_base : g (i : Z) ∈ h.toTrivialization.baseSet := by
    rw [hi]
    exact h.mem_toTrivialization_baseSet
  have htarget :
      (x, i) ∈ h.toTrivialization.target :=
    h.toTrivialization.mem_target.mpr h.mem_toTrivialization_baseSet
  have hleft :=
    h.toTrivialization.apply_symm_apply htarget
  apply h.toTrivialization.toOpenPartialHomeomorph.injOn
  · exact h.toTrivialization.map_target htarget
  · exact h.toTrivialization.mem_source.mpr hi_base
  · change h.toTrivialization
        (h.toTrivialization.toOpenPartialHomeomorph.symm (x, i)) =
      h.toTrivialization (i : Z)
    rw [hleft]
    symm
    apply Prod.ext
    · exact (h.toTrivialization.coe_fst' hi_base).trans hi
    · exact toTrivialization_apply_fiber h i

private theorem exists_common_outer_neighborhood
    {X : Type*} [TopologicalSpace X] {g : B → X} {x : X}
    (h : IsEvenlyCovered g x (g ⁻¹' {x}))
    [DiscreteTopology (g ⁻¹' {x})] [Nonempty (g ⁻¹' {x})]
    [Finite (g ⁻¹' {x})]
    (V : (g ⁻¹' {x}) → Set B)
    (hV_open : ∀ i, IsOpen (V i))
    (hV_mem : ∀ i, (i : B) ∈ V i) :
    ∃ U : Set X, x ∈ U ∧ IsOpen U ∧
      U ⊆ h.toTrivialization.baseSet ∧
      ∀ (i : g ⁻¹' {x}) (y : X), y ∈ U →
        (trivializationSlice h.toTrivialization i).symm y ∈ V i := by
  let sheet (i : g ⁻¹' {x}) :=
    trivializationSlice h.toTrivialization i
  let A (i : g ⁻¹' {x}) :=
    (sheet i).target ∩ (sheet i).symm ⁻¹' V i
  let U := ⋂ i, A i
  have hA_open (i : g ⁻¹' {x}) : IsOpen (A i) := by
    exact (sheet i).symm.isOpen_inter_preimage (hV_open i)
  have hU_open : IsOpen U :=
    isOpen_iInter_of_finite hA_open
  have hxU : x ∈ U := by
    apply mem_iInter.mpr
    intro i
    constructor
    · change x ∈ (trivializationSlice h.toTrivialization i).target
      rw [trivializationSlice_target]
      exact h.mem_toTrivialization_baseSet
    · change (trivializationSlice h.toTrivialization i).symm x ∈ V i
      rw [trivializationSlice_symm_apply,
        toTrivialization_symm_fiber h i]
      exact hV_mem i
  refine ⟨U, hxU, hU_open, ?_, ?_⟩
  · intro y hy
    have hyA := mem_iInter.mp hy (Classical.arbitrary (g ⁻¹' {x}))
    have hyTarget := hyA.1
    change y ∈ (trivializationSlice h.toTrivialization
      (Classical.arbitrary (g ⁻¹' {x}))).target at hyTarget
    rw [trivializationSlice_target] at hyTarget
    exact hyTarget
  · intro i y hy
    exact (mem_iInter.mp hy i).2

end

section

variable {E B X : Type*} [TopologicalSpace E] [TopologicalSpace B]
  [TopologicalSpace X] {p : E → B} {f : B → X}

/-- Covering maps are closed under composition when the outer covering has
finite fibers.  The inner covering is allowed to have empty or infinite
fibers. -/
theorem IsCoveringMap.comp_of_finite_fibers
    (hf : IsCoveringMap f) (hp : IsCoveringMap p)
    (hfinite : ∀ x : X, (f ⁻¹' {x}).Finite) :
    IsCoveringMap (f ∘ p) := by
  intro x
  have houter := hf x
  letI : Finite (f ⁻¹' {x}) := hfinite x
  cases isEmpty_or_nonempty (f ⁻¹' {x}) with
  -- If the outer fiber is empty, its trivializing neighborhood has empty
  -- outer preimage and hence empty composite preimage.
  | inl hempty =>
      letI : IsEmpty (f ⁻¹' {x}) := hempty
      refine (IsEvenlyCovered.of_preimage_eq_empty Empty
        (houter.2.choose_spec.2.1.mem_nhds houter.2.choose_spec.1) ?_
        ).to_isEvenlyCovered_preimage
      rw [preimage_comp, preimage_choose_eq_empty houter, preimage_empty]
  | inr hnonempty =>
      letI : Nonempty (f ⁻¹' {x}) := hnonempty
      letI : DiscreteTopology (f ⁻¹' {x}) := houter.1
      let V (i : f ⁻¹' {x}) : Set B :=
        (hp (i : B)).2.choose
      have hV_open (i : f ⁻¹' {x}) : IsOpen (V i) :=
        (hp (i : B)).2.choose_spec.2.1
      have hV_mem (i : f ⁻¹' {x}) : (i : B) ∈ V i :=
        (hp (i : B)).2.choose_spec.1
      obtain ⟨U, hxU, hU_open, hU_outer, hU_inner⟩ :=
        exists_common_outer_neighborhood houter V hV_open hV_mem
      -- A composite sheet is labeled by an outer-fiber point together with
      -- an inner-fiber point above it.
      let L := Σ i : f ⁻¹' {x}, p ⁻¹' {(i : B)}
      letI : ∀ i : f ⁻¹' {x}, DiscreteTopology (p ⁻¹' {(i : B)}) :=
        fun i ↦ (hp (i : B)).1
      cases isEmpty_or_nonempty L with
      -- The common neighborhood has empty composite preimage if no such
      -- pair of sheet labels exists.
      | inl hLempty =>
          letI : IsEmpty L := hLempty
          refine (IsEvenlyCovered.of_preimage_eq_empty Empty
            (hU_open.mem_nhds hxU) ?_).to_isEvenlyCovered_preimage
          apply eq_empty_of_forall_notMem
          intro z hz
          have hpz_source :
              p z ∈ houter.toTrivialization.source :=
            houter.toTrivialization.mem_source.mpr (hU_outer hz)
          let i : f ⁻¹' {x} :=
            (houter.toTrivialization (p z)).2
          have hpz_sheet :
              p z ∈ (trivializationSlice houter.toTrivialization i).source :=
            (mem_trivializationSlice_source_iff
              houter.toTrivialization i (p z)).mpr
              ⟨hpz_source, rfl⟩
          have hinv :
              (trivializationSlice houter.toTrivialization i).symm
                  ((f ∘ p) z) = p z := by
            change (trivializationSlice houter.toTrivialization i).symm
              (f (p z)) = p z
            rw [← trivializationSlice_apply
              houter.toTrivialization i hpz_sheet]
            exact (trivializationSlice houter.toTrivialization i).left_inv hpz_sheet
          have hpzV : p z ∈ V i := by
            rw [← hinv]
            exact hU_inner i ((f ∘ p) z) hz
          letI : IsEmpty (p ⁻¹' {(i : B)}) :=
            ⟨fun j ↦ isEmptyElim (α := L) ⟨i, j⟩⟩
          have hpz_empty : z ∈ p ⁻¹' V i := hpzV
          rw [preimage_choose_eq_empty (hp (i : B))] at hpz_empty
          exact hpz_empty
      | inr hLnonempty =>
          letI : Nonempty L := hLnonempty
          letI : Nonempty E := ⟨(Classical.arbitrary L).2⟩
          let innerTriv (l : L) :
              Trivialization (p ⁻¹' {(l.1 : B)}) p :=
            letI : Nonempty (p ⁻¹' {(l.1 : B)}) := ⟨l.2⟩
            (hp (l.1 : B)).toTrivialization
          let innerSheet (l : L) :=
            trivializationSlice (innerTriv l) l.2
          let outerSheet (l : L) :=
            (trivializationSlice houter.toTrivialization l.1).trans
              (OpenPartialHomeomorph.ofSet U hU_open)
          let phi (l : L) :=
            (innerSheet l).trans (outerSheet l)
          -- Every `phi l` has the same target `U`.  This is precisely where
          -- the finite intersection constructed above is used.
          have houter_target (l : L) :
              (outerSheet l).target = U := by
            rw [show outerSheet l =
              (trivializationSlice houter.toTrivialization l.1).trans
                (OpenPartialHomeomorph.ofSet U hU_open) by rfl,
              OpenPartialHomeomorph.trans_target]
            ext y
            change (y ∈ U ∧
              y ∈ (trivializationSlice
                houter.toTrivialization l.1).target) ↔ y ∈ U
            constructor
            · exact fun hy ↦ hy.1
            · intro hy
              refine ⟨hy, ?_⟩
              rw [trivializationSlice_target]
              exact hU_outer hy
          have hinner_target (l : L) :
              (innerSheet l).target = V l.1 := by
            letI : Nonempty (p ⁻¹' {(l.1 : B)}) := ⟨l.2⟩
            rw [show innerSheet l =
              trivializationSlice (innerTriv l) l.2 by rfl,
              trivializationSlice_target]
            exact toTrivialization_baseSet (hp (l.1 : B))
          have houter_symm (l : L) (y : X) :
              (outerSheet l).symm y =
                (trivializationSlice houter.toTrivialization l.1).symm y := by
            rfl
          have hphi_target (l : L) :
              (phi l).target = U := by
            rw [show phi l = (innerSheet l).trans (outerSheet l) by rfl,
              OpenPartialHomeomorph.trans_target, houter_target,
              hinner_target]
            ext y
            constructor
            · exact fun hy ↦ hy.1
            · intro hy
              exact ⟨hy, by
                change (outerSheet l).symm y ∈ V l.1
                rw [houter_symm]
                exact hU_inner l.1 y hy⟩
          have hphi_apply (l : L) (z : E) (hz : z ∈ (phi l).source) :
              phi l z = (f ∘ p) z := by
            have hz' := hz
            rw [show phi l = (innerSheet l).trans (outerSheet l) by rfl,
              OpenPartialHomeomorph.trans_source] at hz'
            have hinner_apply :
                innerSheet l z = p z :=
              trivializationSlice_apply (innerTriv l) l.2 hz'.1
            have hpz_outer : p z ∈ (outerSheet l).source := by
              rw [← hinner_apply]
              exact hz'.2
            have hpz_outer_slice :
                p z ∈ (trivializationSlice
                  houter.toTrivialization l.1).source := by
              have hpz_outer' := hpz_outer
              rw [show outerSheet l =
                (trivializationSlice houter.toTrivialization l.1).trans
                  (OpenPartialHomeomorph.ofSet U hU_open) by rfl,
                OpenPartialHomeomorph.trans_source] at hpz_outer'
              exact hpz_outer'.1
            calc
              phi l z = outerSheet l (innerSheet l z) := rfl
              _ = outerSheet l (p z) := by rw [hinner_apply]
              _ = trivializationSlice houter.toTrivialization l.1 (p z) := rfl
              _ = f (p z) :=
                trivializationSlice_apply houter.toTrivialization l.1
                  hpz_outer_slice
              _ = (f ∘ p) z := rfl
          have houter_coord (l : L) (z : E)
              (hz : z ∈ (phi l).source) :
              (houter.toTrivialization (p z)).2 = l.1 := by
            have hz' := hz
            rw [show phi l = (innerSheet l).trans (outerSheet l) by rfl,
              OpenPartialHomeomorph.trans_source] at hz'
            have hinner_apply :
                innerSheet l z = p z :=
              trivializationSlice_apply (innerTriv l) l.2 hz'.1
            have hpz_outer : p z ∈ (outerSheet l).source := by
              rw [← hinner_apply]
              exact hz'.2
            have hpz_outer' := hpz_outer
            rw [show outerSheet l =
              (trivializationSlice houter.toTrivialization l.1).trans
                (OpenPartialHomeomorph.ofSet U hU_open) by rfl,
              OpenPartialHomeomorph.trans_source] at hpz_outer'
            exact (mem_trivializationSlice_source_iff
              houter.toTrivialization l.1 (p z)).mp hpz_outer'.1 |>.2
          have hinner_coord (l : L) (z : E)
              (hz : z ∈ (phi l).source) :
              (innerTriv l z).2 = l.2 := by
            have hz' := hz
            rw [show phi l = (innerSheet l).trans (outerSheet l) by rfl,
              OpenPartialHomeomorph.trans_source] at hz'
            exact (mem_trivializationSlice_source_iff
              (innerTriv l) l.2 z).mp hz'.1 |>.2
          have hexhaustive :
              (f ∘ p) ⁻¹' U ⊆ ⋃ l : L, (phi l).source := by
            intro z hz
            have hpz_source :
                p z ∈ houter.toTrivialization.source :=
              houter.toTrivialization.mem_source.mpr (hU_outer hz)
            let i : f ⁻¹' {x} :=
              (houter.toTrivialization (p z)).2
            have hpz_sheet :
                p z ∈ (trivializationSlice
                  houter.toTrivialization i).source :=
              (mem_trivializationSlice_source_iff
                houter.toTrivialization i (p z)).mpr
                ⟨hpz_source, rfl⟩
            have hinv :
                (trivializationSlice houter.toTrivialization i).symm
                    ((f ∘ p) z) = p z := by
              change (trivializationSlice houter.toTrivialization i).symm
                (f (p z)) = p z
              rw [← trivializationSlice_apply
                houter.toTrivialization i hpz_sheet]
              exact (trivializationSlice
                houter.toTrivialization i).left_inv hpz_sheet
            have hpzV : p z ∈ V i := by
              rw [← hinv]
              exact hU_inner i ((f ∘ p) z) hz
            let H :=
              (hp (i : B)).2.choose_spec.2.2.2.choose
            let j₀ : p ⁻¹' {(i : B)} :=
              (H ⟨z, hpzV⟩).2
            letI : Nonempty (p ⁻¹' {(i : B)}) := ⟨j₀⟩
            let ti := (hp (i : B)).toTrivialization
            have hpz_ti : p z ∈ ti.baseSet := by
              rw [toTrivialization_baseSet]
              exact hpzV
            let j : p ⁻¹' {(i : B)} := (ti z).2
            let l : L := ⟨i, j⟩
            apply mem_iUnion_of_mem l
            rw [show phi l = (innerSheet l).trans (outerSheet l) by rfl,
              OpenPartialHomeomorph.trans_source]
            constructor
            · apply (mem_trivializationSlice_source_iff
                (innerTriv l) l.2 z).mpr
              constructor
              · exact (innerTriv l).mem_source.mpr (by
                  change p z ∈ ti.baseSet
                  exact hpz_ti)
              · rfl
            · have hinner_apply :
                  innerSheet l z = p z :=
                trivializationSlice_apply (innerTriv l) l.2
                  ((mem_trivializationSlice_source_iff
                    (innerTriv l) l.2 z).mpr
                    ⟨(innerTriv l).mem_source.mpr (by
                        change p z ∈ ti.baseSet
                        exact hpz_ti), rfl⟩)
              change innerSheet l z ∈ (outerSheet l).source
              rw [hinner_apply]
              rw [show outerSheet l =
                (trivializationSlice houter.toTrivialization l.1).trans
                  (OpenPartialHomeomorph.ofSet U hU_open) by rfl,
                OpenPartialHomeomorph.trans_source]
              refine ⟨hpz_sheet, ?_⟩
              change trivializationSlice houter.toTrivialization l.1 (p z) ∈ U
              rw [trivializationSlice_apply
                houter.toTrivialization l.1 hpz_sheet]
              exact hz
          -- Assemble the pairwise-disjoint sheets into the required bundle
          -- trivialization.  `to_isEvenlyCovered_preimage` replaces the
          -- convenient sigma-type index `L` by the literal composite fiber.
          refine (IsEvenlyCovered.of_trivialization
            (t := hU_open.trivializationDiscrete
              (fun l : L ↦ (phi l).source) U
              (fun l s hs ↦ ?_)
              (fun l ↦ ?_)
              (fun l ↦ ?_)
              (fun l m hne ↦ ?_)
              hexhaustive) hxU).to_isEvenlyCovered_preimage
          · have hs_target : s ⊆ (phi l).target := by
              rw [hphi_target]
              exact hs
            rw [← (phi l).isOpen_symm_image_iff_of_subset_target hs_target,
              (phi l).symm_image_eq_source_inter_preimage hs_target]
            have hsets :
                (phi l).source ∩ (phi l) ⁻¹' s =
                  (f ∘ p) ⁻¹' s ∩ (phi l).source := by
              ext z
              constructor
              · rintro ⟨hzphi, hzs⟩
                exact ⟨by
                  change (f ∘ p) z ∈ s
                  change phi l z ∈ s at hzs
                  rw [← hphi_apply l z hzphi]
                  exact hzs, hzphi⟩
              · rintro ⟨hzs, hzphi⟩
                exact ⟨hzphi, by
                  change phi l z ∈ s
                  change (f ∘ p) z ∈ s at hzs
                  rw [hphi_apply l z hzphi]
                  exact hzs⟩
            rw [hsets]
          · intro z hz z' hz' heq
            apply (phi l).injOn hz hz'
            rw [hphi_apply l z hz, hphi_apply l z' hz', heq]
          · intro y hy
            have hy_target : y ∈ (phi l).target := by
              rw [hphi_target]
              exact hy
            refine ⟨(phi l).symm y, (phi l).map_target hy_target, ?_⟩
            rw [← hphi_apply l _ ((phi l).map_target hy_target)]
            exact (phi l).right_inv hy_target
          · apply Set.disjoint_left.mpr
            intro z hzl hzm
            apply hne
            have hi : l.1 = m.1 :=
              (houter_coord l z hzl).symm.trans (houter_coord m z hzm)
            rcases l with ⟨i, j⟩
            rcases m with ⟨i', j'⟩
            dsimp at hi
            subst i'
            have hj : j = j' := by
              calc
                j = (innerTriv ⟨i, j⟩ z).2 :=
                  (hinner_coord ⟨i, j⟩ z hzl).symm
                _ = (innerTriv ⟨i, j'⟩ z).2 := rfl
                _ = j' := hinner_coord ⟨i, j'⟩ z hzm
            subst j'
            rfl

end

end HGAS.Covering
