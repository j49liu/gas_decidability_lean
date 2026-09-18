import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Tactic

/-!
# The complex projective line as the one-point compactification

This file supplies a small, reusable topological model of `ℂP¹`.  We use
`OnePoint ℂ`; a finite point is the affine coordinate `[1:z]`, and the
point at infinity is `[0:1]`.

The extended reciprocal

```
  z ↦ z⁻¹,   0 ↦ ∞,   ∞ ↦ 0
```

is constructed explicitly and proved to be a homeomorphism.  This gives
the second affine chart without importing scheme-theoretic projective
space.
-/

namespace HGAS

open Bornology Filter Topology
open scoped OnePoint Topology

noncomputable section

/-- Reciprocal on the one-point compactification, with zero and infinity
interchanged. -/
def complexProjectiveInv : OnePoint ℂ → OnePoint ℂ
  | ∞ => (0 : ℂ)
  | (z : ℂ) => if z = 0 then ∞ else (z⁻¹ : ℂ)

@[simp] theorem complexProjectiveInv_infty :
    complexProjectiveInv ∞ = (0 : ℂ) := rfl

@[simp] theorem complexProjectiveInv_zero :
    complexProjectiveInv (0 : ℂ) = ∞ := by
  simp [complexProjectiveInv]

@[simp] theorem complexProjectiveInv_coe_of_ne
    {z : ℂ} (hz : z ≠ 0) :
    complexProjectiveInv (z : OnePoint ℂ) =
      (z⁻¹ : ℂ) := by
  simp [complexProjectiveInv, hz]

@[simp] theorem complexProjectiveInv_involutive
    (x : OnePoint ℂ) :
    complexProjectiveInv (complexProjectiveInv x) = x := by
  induction x using OnePoint.rec with
  | infty => simp
  | coe z =>
      by_cases hz : z = 0
      · subst z
        simp
      · simp [complexProjectiveInv, hz]

/-- The extended reciprocal is continuous. -/
theorem continuous_complexProjectiveInv :
    Continuous complexProjectiveInv := by
  rw [OnePoint.continuous_iff]
  constructor
  · change Tendsto
      (fun z : ℂ =>
        if z = 0 then ∞
        else ((z⁻¹ : ℂ) : OnePoint ℂ))
      (coclosedCompact ℂ)
      (𝓝 ((0 : ℂ) : OnePoint ℂ))
    have hco :
        Tendsto
          (fun z : ℂ => ((z⁻¹ : ℂ) : OnePoint ℂ))
          (coclosedCompact ℂ)
          (𝓝 ((0 : ℂ) : OnePoint ℂ)) := by
      have hcocompact :
          coclosedCompact ℂ = cobounded ℂ := by
        rw [Filter.coclosedCompact_eq_cocompact,
          ← Metric.cobounded_eq_cocompact (α := ℂ)]
      rw [hcocompact]
      exact
        OnePoint.continuous_coe.continuousAt.tendsto.comp
          Filter.tendsto_inv₀_cobounded
    have hne :
        ∀ᶠ z : ℂ in coclosedCompact ℂ, z ≠ 0 := by
      exact
        isCompact_singleton.compl_mem_coclosedCompact_of_isClosed
          isClosed_singleton
    apply hco.congr'
    filter_upwards [hne] with z hzero
    simp [hzero]
  · rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z = 0
    · subst z
      change Tendsto
        (fun w : ℂ =>
          complexProjectiveInv
            (w : OnePoint ℂ))
        (𝓝 0)
        (𝓝 (complexProjectiveInv
          ((0 : ℂ) : OnePoint ℂ)))
      rw [complexProjectiveInv_zero]
      rw [← nhdsNE_sup_pure]
      rw [tendsto_sup]
      constructor
      · have hinv :
            Tendsto (fun w : ℂ => w⁻¹)
              (𝓝[≠] 0) (cobounded ℂ) :=
          Filter.tendsto_inv₀_nhdsNE_zero
        have hcoe :
            Tendsto
              (fun w : ℂ =>
                ((w⁻¹ : ℂ) : OnePoint ℂ))
              (𝓝[≠] 0) (𝓝 ∞) := by
          exact
            OnePoint.tendsto_coe_infty.comp
              (hinv.mono_right
                (by
                  rw [Metric.cobounded_eq_cocompact]
                  exact cocompact_le_coclosedCompact))
        apply hcoe.congr'
        filter_upwards
          [self_mem_nhdsWithin] with w hw
        simp only [Set.mem_compl_iff,
          Set.mem_singleton_iff] at hw
        simp [complexProjectiveInv, hw]
      · rw [tendsto_pure_left]
        intro s hs
        rw [complexProjectiveInv_zero]
        exact mem_of_mem_nhds hs
    · change Tendsto
        (fun w : ℂ =>
          complexProjectiveInv
            (w : OnePoint ℂ))
        (𝓝 z)
        (𝓝 (complexProjectiveInv
          (z : OnePoint ℂ)))
      rw [complexProjectiveInv_coe_of_ne hz]
      have hne : ∀ᶠ w in 𝓝 z, w ≠ 0 :=
        eventually_ne_nhds hz
      have hinv :
          Tendsto (fun w : ℂ => w⁻¹)
            (𝓝 z) (𝓝 z⁻¹) :=
        tendsto_inv₀ hz
      have hcoe :
          Tendsto
            (fun w : ℂ =>
              ((w⁻¹ : ℂ) : OnePoint ℂ))
            (𝓝 z)
            (𝓝 ((z⁻¹ : ℂ) : OnePoint ℂ)) :=
        OnePoint.continuous_coe.continuousAt.tendsto.comp
          hinv
      apply hcoe.congr'
      filter_upwards [hne] with w hw
      simp [complexProjectiveInv, hw]

/-- Reciprocal is a homeomorphism of the complex projective line. -/
def complexProjectiveInvHomeomorph :
    OnePoint ℂ ≃ₜ OnePoint ℂ where
  toFun := complexProjectiveInv
  invFun := complexProjectiveInv
  left_inv := complexProjectiveInv_involutive
  right_inv := complexProjectiveInv_involutive
  continuous_toFun := continuous_complexProjectiveInv
  continuous_invFun := continuous_complexProjectiveInv

/-! ## Homogeneous coordinates -/

/-- A nonzero pair of complex homogeneous coordinates. -/
abbrev ComplexProjectivePair :=
  {p : ℂ × ℂ // p ≠ 0}

/-- The affine coordinate `[a:b] ↦ b/a`, with `[0:b]` sent to infinity. -/
def complexProjectiveRatio
    (p : ComplexProjectivePair) : OnePoint ℂ :=
  if p.1.1 = 0 then ∞
  else ((p.1.2 / p.1.1 : ℂ) : OnePoint ℂ)

@[simp] theorem complexProjectiveRatio_of_fst_ne
    (p : ComplexProjectivePair)
    (hp : p.1.1 ≠ 0) :
    complexProjectiveRatio p =
      ((p.1.2 / p.1.1 : ℂ) : OnePoint ℂ) := by
  simp [complexProjectiveRatio, hp]

@[simp] theorem complexProjectiveRatio_of_fst_eq
    (p : ComplexProjectivePair)
    (hp : p.1.1 = 0) :
    complexProjectiveRatio p = ∞ := by
  simp [complexProjectiveRatio, hp]

/-- The reciprocal chart formula. -/
theorem complexProjectiveRatio_eq_inv_second
    (p : ComplexProjectivePair)
    (hp : p.1.2 ≠ 0) :
    complexProjectiveRatio p =
      complexProjectiveInv
        (((p.1.1 / p.1.2 : ℂ) : OnePoint ℂ)) := by
  by_cases hfirst : p.1.1 = 0
  · simp [complexProjectiveRatio, hfirst]
  · rw [complexProjectiveRatio_of_fst_ne p hfirst,
      complexProjectiveInv_coe_of_ne
        (div_ne_zero hfirst hp)]
    congr 1
    field_simp

/-- The affine-ratio model of `ℂP¹` is continuous on nonzero homogeneous
pairs. -/
theorem continuous_complexProjectiveRatio :
    Continuous complexProjectiveRatio := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hfirst : p.1.1 = 0
  · have hsecond : p.1.2 ≠ 0 := by
      intro hzero
      apply p.2
      apply Prod.ext
      · exact hfirst
      · exact hzero
    change Tendsto complexProjectiveRatio
      (𝓝 p) (𝓝 (complexProjectiveRatio p))
    rw [complexProjectiveRatio_eq_inv_second p hsecond]
    have hfirstContinuous :
        ContinuousAt
          (fun q : ComplexProjectivePair => q.1.1) p := by
      fun_prop
    have hsecondContinuous :
        ContinuousAt
          (fun q : ComplexProjectivePair => q.1.2) p := by
      fun_prop
    have hquotient :
        ContinuousAt
          (fun q : ComplexProjectivePair =>
            q.1.1 / q.1.2) p :=
      hfirstContinuous.div hsecondContinuous hsecond
    have hfinite :
        ContinuousAt
          (fun q : ComplexProjectivePair =>
            (((q.1.1 / q.1.2 : ℂ) :
              OnePoint ℂ))) p :=
      OnePoint.continuous_coe.continuousAt.comp
        hquotient
    have hinv :
        ContinuousAt
          (fun q : ComplexProjectivePair =>
            complexProjectiveInv
              (((q.1.1 / q.1.2 : ℂ) :
                OnePoint ℂ))) p :=
      continuous_complexProjectiveInv.continuousAt.comp
        hfinite
    have hne :
        ∀ᶠ q in 𝓝 p, q.1.2 ≠ 0 :=
      hsecondContinuous.eventually_ne hsecond
    apply hinv.congr'
    filter_upwards [hne] with q hq
    exact (complexProjectiveRatio_eq_inv_second q hq).symm
  · change Tendsto complexProjectiveRatio
      (𝓝 p) (𝓝 (complexProjectiveRatio p))
    rw [complexProjectiveRatio_of_fst_ne p hfirst]
    have hfirstContinuous :
        ContinuousAt
          (fun q : ComplexProjectivePair => q.1.1) p := by
      fun_prop
    have hsecondContinuous :
        ContinuousAt
          (fun q : ComplexProjectivePair => q.1.2) p := by
      fun_prop
    have hquotient :
        ContinuousAt
          (fun q : ComplexProjectivePair =>
            q.1.2 / q.1.1) p :=
      hsecondContinuous.div hfirstContinuous hfirst
    have hfinite :
        ContinuousAt
          (fun q : ComplexProjectivePair =>
            (((q.1.2 / q.1.1 : ℂ) :
              OnePoint ℂ))) p :=
      OnePoint.continuous_coe.continuousAt.comp
        hquotient
    have hne :
        ∀ᶠ q in 𝓝 p, q.1.1 ≠ 0 :=
      hfirstContinuous.eventually_ne hfirst
    apply hfinite.congr'
    filter_upwards [hne] with q hq
    exact (complexProjectiveRatio_of_fst_ne q hq).symm

/-- Equality of affine projective ratios yields one common nonzero scale
between the two homogeneous pairs. -/
theorem exists_common_scale_of_complexProjectiveRatio_eq
    (p q : ComplexProjectivePair)
    (h :
      complexProjectiveRatio p =
        complexProjectiveRatio q) :
    ∃ c : ℂ, c ≠ 0 ∧
      c * p.1.1 = q.1.1 ∧
      c * p.1.2 = q.1.2 := by
  by_cases hp0 : p.1.1 = 0
  · have hp1 : p.1.2 ≠ 0 := by
      intro hp1
      apply p.2
      exact Prod.ext hp0 hp1
    have hq0 : q.1.1 = 0 := by
      by_contra hq0
      rw [complexProjectiveRatio_of_fst_eq p hp0,
        complexProjectiveRatio_of_fst_ne q hq0] at h
      exact OnePoint.infty_ne_coe _ h
    have hq1 : q.1.2 ≠ 0 := by
      intro hq1
      apply q.2
      exact Prod.ext hq0 hq1
    refine
      ⟨q.1.2 / p.1.2,
        div_ne_zero hq1 hp1, ?_, ?_⟩
    · rw [hp0, hq0, mul_zero]
    · exact div_mul_cancel₀ q.1.2 hp1
  · have hq0 : q.1.1 ≠ 0 := by
      intro hq0
      rw [complexProjectiveRatio_of_fst_ne p hp0,
        complexProjectiveRatio_of_fst_eq q hq0] at h
      exact OnePoint.coe_ne_infty _ h
    have hratio :
        p.1.2 / p.1.1 =
          q.1.2 / q.1.1 := by
      rw [complexProjectiveRatio_of_fst_ne p hp0,
        complexProjectiveRatio_of_fst_ne q hq0] at h
      exact OnePoint.coe_injective h
    refine
      ⟨q.1.1 / p.1.1,
        div_ne_zero hq0 hp0, ?_, ?_⟩
    · exact div_mul_cancel₀ q.1.1 hp0
    · have hcross :
          p.1.2 * q.1.1 =
            q.1.2 * p.1.1 :=
        (div_eq_div_iff hp0 hq0).mp hratio
      field_simp
      linear_combination hcross

/-- A pair of functions with no common zero, viewed as a map to
homogeneous pairs. -/
def complexProjectivePairMap
    {X : Type*} (f g : X → ℂ)
    (hfg : ∀ x, (f x, g x) ≠ 0)
    (x : X) : ComplexProjectivePair :=
  ⟨(f x, g x), hfg x⟩

/-- The projective ratio associated with two functions with no common
zero. -/
def complexProjectiveRatioMap
    {X : Type*} (f g : X → ℂ)
    (hfg : ∀ x, (f x, g x) ≠ 0) :
    X → OnePoint ℂ :=
  complexProjectiveRatio ∘
    complexProjectivePairMap f g hfg

@[simp] theorem complexProjectiveRatioMap_apply
    {X : Type*} (f g : X → ℂ)
    (hfg : ∀ x, (f x, g x) ≠ 0)
    (x : X) :
    complexProjectiveRatioMap f g hfg x =
      if f x = 0 then ∞
      else ((g x / f x : ℂ) : OnePoint ℂ) := rfl

theorem complexProjectiveRatioMap_of_fst_ne
    {X : Type*} (f g : X → ℂ)
    (hfg : ∀ x, (f x, g x) ≠ 0)
    {x : X} (hx : f x ≠ 0) :
    complexProjectiveRatioMap f g hfg x =
      ((g x / f x : ℂ) : OnePoint ℂ) := by
  simp [complexProjectiveRatioMap_apply, hx]

theorem complexProjectiveRatioMap_eq_inv_second
    {X : Type*} (f g : X → ℂ)
    (hfg : ∀ x, (f x, g x) ≠ 0)
    {x : X} (hx : g x ≠ 0) :
    complexProjectiveRatioMap f g hfg x =
      complexProjectiveInv
        (((f x / g x : ℂ) : OnePoint ℂ)) := by
  exact
    complexProjectiveRatio_eq_inv_second
      (complexProjectivePairMap f g hfg x) hx

/-- Continuous homogeneous coordinates give a continuous projective-line
map. -/
theorem continuous_complexProjectiveRatioMap
    {X : Type*} [TopologicalSpace X]
    {f g : X → ℂ}
    (hfg : ∀ x, (f x, g x) ≠ 0)
    (hf : Continuous f)
    (hg : Continuous g) :
    Continuous
      (complexProjectiveRatioMap f g hfg) := by
  apply continuous_complexProjectiveRatio.comp
  apply Continuous.subtype_mk
  exact hf.prodMk hg

/-- **Open mapping theorem for a homogeneous analytic pair.**

If two entire functions have no common zero and neither is a global
constant multiple of the other, their map to `ℂP¹` is open.  Critical
points cause no problem: this uses the complex open mapping theorem,
not a nonvanishing-derivative shortcut. -/
theorem isOpenMap_complexProjectiveRatioMap
    {f g : ℂ → ℂ}
    (hfg : ∀ z, (f z, g z) ≠ 0)
    (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ)
    (hgf :
      ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c * f z)
    (hfg' :
      ¬ ∃ c : ℂ, ∀ z : ℂ, f z = c * g z) :
    IsOpenMap
      (complexProjectiveRatioMap f g hfg) := by
  rw [isOpenMap_iff_nhds_le]
  intro z
  by_cases hfirst : f z = 0
  · have hsecond : g z ≠ 0 := by
      intro hzero
      apply hfg z
      apply Prod.ext
      · exact hfirst
      · exact hzero
    let s : ℂ → ℂ := fun w => f w / g w
    have hsAnalytic : AnalyticAt ℂ s z := by
      exact
        (hf z (Set.mem_univ z)).div
          (hg z (Set.mem_univ z)) hsecond
    have hsNotConstant :
        ¬ ∀ᶠ w in 𝓝 z, s w = s z := by
      intro hlocal
      apply hfg'
      let c : ℂ := s z
      refine ⟨c, ?_⟩
      have hg_ne :
          ∀ᶠ w in 𝓝 z, g w ≠ 0 :=
        (hg z (Set.mem_univ z)).continuousAt.eventually_ne
          hsecond
      have hevent :
          f =ᶠ[𝓝 z] fun w => c * g w := by
        filter_upwards [hlocal, hg_ne] with w hw hgw
        change f w / g w = c at hw
        exact (div_eq_iff hgw).mp hw
      have hright :
          AnalyticOnNhd ℂ
            (fun w => c * g w) Set.univ :=
        analyticOnNhd_const.mul hg
      have hglobal :=
        hf.eqOn_of_preconnected_of_eventuallyEq
          hright
          PreconnectedSpace.isPreconnected_univ
          (Set.mem_univ z) hevent
      intro w
      exact hglobal (Set.mem_univ w)
    have hsOpen :
        𝓝 (s z) ≤ map s (𝓝 z) :=
      hsAnalytic
        |>.eventually_constant_or_nhds_le_map_nhds
        |>.resolve_left hsNotConstant
    have hfinite :
        𝓝 ((s z : ℂ) : OnePoint ℂ) ≤
          map
            (fun w : ℂ =>
              ((s w : ℂ) : OnePoint ℂ))
            (𝓝 z) := by
      rw [OnePoint.nhds_coe_eq]
      calc
        map ((↑) : ℂ → OnePoint ℂ) (𝓝 (s z)) ≤
            map ((↑) : ℂ → OnePoint ℂ)
              (map s (𝓝 z)) :=
          map_mono hsOpen
        _ =
            map
              (fun w : ℂ =>
                ((s w : ℂ) : OnePoint ℂ))
              (𝓝 z) := by
          rw [map_map]
          rfl
    rw [complexProjectiveRatioMap_eq_inv_second
      f g hfg hsecond]
    calc
      𝓝
          (complexProjectiveInv
            (((f z / g z : ℂ) :
              OnePoint ℂ))) =
          map complexProjectiveInv
            (𝓝 (((s z : ℂ) :
              OnePoint ℂ))) := by
        simpa only [s] using
          (complexProjectiveInvHomeomorph.map_nhds_eq
            (((s z : ℂ) :
              OnePoint ℂ))).symm
      _ ≤
          map complexProjectiveInv
            (map
              (fun w : ℂ =>
                ((s w : ℂ) : OnePoint ℂ))
              (𝓝 z)) :=
        map_mono hfinite
      _ =
          map
            (complexProjectiveRatioMap f g hfg)
            (𝓝 z) := by
        rw [map_map]
        apply Filter.map_congr
        have hg_ne :
            ∀ᶠ w in 𝓝 z, g w ≠ 0 :=
          (hg z (Set.mem_univ z)).continuousAt.eventually_ne
            hsecond
        filter_upwards [hg_ne] with w hw
        exact
          (complexProjectiveRatioMap_eq_inv_second
            f g hfg hw).symm
  · let r : ℂ → ℂ := fun w => g w / f w
    have hrAnalytic : AnalyticAt ℂ r z := by
      exact
        (hg z (Set.mem_univ z)).div
          (hf z (Set.mem_univ z)) hfirst
    have hrNotConstant :
        ¬ ∀ᶠ w in 𝓝 z, r w = r z := by
      intro hlocal
      apply hgf
      let c : ℂ := r z
      refine ⟨c, ?_⟩
      have hf_ne :
          ∀ᶠ w in 𝓝 z, f w ≠ 0 :=
        (hf z (Set.mem_univ z)).continuousAt.eventually_ne
          hfirst
      have hevent :
          g =ᶠ[𝓝 z] fun w => c * f w := by
        filter_upwards [hlocal, hf_ne] with w hw hfw
        change g w / f w = c at hw
        exact (div_eq_iff hfw).mp hw
      have hright :
          AnalyticOnNhd ℂ
            (fun w => c * f w) Set.univ :=
        analyticOnNhd_const.mul hf
      have hglobal :=
        hg.eqOn_of_preconnected_of_eventuallyEq
          hright
          PreconnectedSpace.isPreconnected_univ
          (Set.mem_univ z) hevent
      intro w
      exact hglobal (Set.mem_univ w)
    have hrOpen :
        𝓝 (r z) ≤ map r (𝓝 z) :=
      hrAnalytic
        |>.eventually_constant_or_nhds_le_map_nhds
        |>.resolve_left hrNotConstant
    rw [complexProjectiveRatioMap_of_fst_ne
      f g hfg hfirst, OnePoint.nhds_coe_eq]
    calc
      map ((↑) : ℂ → OnePoint ℂ)
          (𝓝 (g z / f z)) ≤
          map ((↑) : ℂ → OnePoint ℂ)
            (map r (𝓝 z)) := by
        simpa only [r] using map_mono hrOpen
      _ =
          map
            (complexProjectiveRatioMap f g hfg)
            (𝓝 z) := by
        rw [map_map]
        apply Filter.map_congr
        have hf_ne :
            ∀ᶠ w in 𝓝 z, f w ≠ 0 :=
          (hf z (Set.mem_univ z)).continuousAt.eventually_ne
            hfirst
        filter_upwards [hf_ne] with w hw
        exact
          (complexProjectiveRatioMap_of_fst_ne
            f g hfg hw).symm

/-- A compact reduction plus openness forces a projective-line map to be
surjective.

This is the elementary open-and-closed argument behind compact
uniformization.  It is stated for a map on `ℂ` so that an application may
use a fundamental parallelogram without first constructing a quotient
topology. -/
theorem surjective_to_complexProjectiveLine_of_compact_reduction
    {F : ℂ → OnePoint ℂ}
    {K : Set ℂ}
    (hFContinuous : Continuous F)
    (hFOpen : IsOpenMap F)
    (hKCompact : IsCompact K)
    (hreduce :
      ∀ z : ℂ, ∃ w ∈ K, F w = F z) :
    Function.Surjective F := by
  have hrange :
      Set.range F = F '' K := by
    apply Set.Subset.antisymm
    · rintro y ⟨z, rfl⟩
      obtain ⟨w, hwK, hw⟩ := hreduce z
      exact ⟨w, hwK, hw⟩
    · exact Set.image_subset_range F K
  have hcompact :
      IsCompact (Set.range F) := by
    rw [hrange]
    exact hKCompact.image hFContinuous
  have hopen :
      IsOpen (Set.range F) := by
    rw [← Set.image_univ]
    exact hFOpen Set.univ isOpen_univ
  have hnonempty :
      (Set.range F).Nonempty :=
    ⟨F 0, ⟨0, rfl⟩⟩
  have hall :
      Set.range F = Set.univ :=
    IsClopen.eq_univ
      ⟨hcompact.isClosed, hopen⟩ hnonempty
  intro y
  have hy : y ∈ Set.range F := by
    rw [hall]
    exact Set.mem_univ y
  exact hy

end

end HGAS
