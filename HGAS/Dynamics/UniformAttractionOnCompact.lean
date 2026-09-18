import HGAS.Dynamics.Stability
import Mathlib.Analysis.ODE.Transform
import Mathlib.Dynamics.Flow
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

/-!
# Uniform attraction on compact sets

Pointwise global attraction becomes uniform on compact sets once Lyapunov
stability and continuous dependence on initial data are available.

The proof is elementary and useful well beyond homogeneous systems.  Given
a target radius `ε`, stability supplies a smaller radius `δ` such that every
trajectory starting in the `δ`-ball remains in the `ε`-ball.  Every point
of the compact initial set enters the `δ`-ball at some time.  Continuity of
the flow makes the same entry time work on a neighborhood of that point.
A finite subcover gives finitely many entry times; their sum is a common
upper bound.  Stability then keeps every later state in the target ball.

This is the compactness step needed in the direct proof that homogeneous
GAS forces a uniform negative angular cocycle block.
-/

namespace HGAS

open Function Set
open scoped Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonnegative time shift of a forward orbit of a genuine flow is again
a forward trajectory.  The flow law identifies the shifted orbit with the
translated original curve. -/
theorem IsForwardTrajectory.flow_timeShift
    {F : E → E} (ϕ : Flow ℝ E) {x : E}
    (hϕ :
      IsForwardTrajectory F (fun t : ℝ ↦ ϕ t x) x)
    {T : ℝ} (hT : 0 ≤ T) :
    IsForwardTrajectory F
      (fun t : ℝ ↦ ϕ t (ϕ T x)) (ϕ T x) := by
  refine ⟨by simp, ?_⟩
  have htranslated :=
    hϕ.2.comp_add T
  have hmono :
      IsIntegralCurveOn
        ((fun t : ℝ ↦ ϕ t x) ∘ (· + T))
        ((fun _ : ℝ ↦ F) ∘ (· + T))
        (Ici (0 : ℝ)) :=
    htranslated.mono (by
      intro t ht
      rw [mem_vadd_set_iff_neg_vadd_mem]
      simp only [neg_neg, vadd_eq_add, mem_Ici]
      change 0 ≤ t at ht
      linarith)
  convert hmono using 1
  · funext t
    exact (ϕ.map_add t T x).symm

/-- A continuous global ODE flow for a GAS equilibrium attracts every
compact set uniformly. -/
theorem GloballyAsymptoticallyStable.uniformAttractionOnCompact
    {F : E → E} {xEq : E}
    (hgas : GloballyAsymptoticallyStable F xEq)
    (ϕ : Flow ℝ E)
    (hflow :
      ∀ x : E,
        IsForwardTrajectory F (fun t : ℝ ↦ ϕ t x) x)
    {K : Set E} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 0 ≤ T ∧
      ∀ x ∈ K, ∀ t : ℝ, T ≤ t →
        dist (ϕ t x) xEq < ε := by
  obtain ⟨δ, hδ, hstable⟩ :=
    hgas.stable ε hε
  let hitTime : K → ℝ :=
    fun x ↦ Classical.choose
      (hgas.attractive x.1
        (fun t : ℝ ↦ ϕ t x.1) (hflow x.1) δ hδ)
  have hhitTime_nonneg (x : K) :
      0 ≤ hitTime x :=
    (Classical.choose_spec
      (hgas.attractive x.1
        (fun t : ℝ ↦ ϕ t x.1) (hflow x.1) δ hδ)).1
  have hhitTime_enters (x : K) :
      dist (ϕ (hitTime x) x.1) xEq < δ :=
    by
      have hspec :=
        Classical.choose_spec
          (hgas.attractive x.1
            (fun t : ℝ ↦ ϕ t x.1) (hflow x.1) δ hδ)
      apply hspec.2 (hitTime x)
      exact le_rfl
  let U : K → Set E :=
    fun x ↦ {y | dist (ϕ (hitTime x) y) xEq < δ}
  have hUopen (x : K) : IsOpen (U x) := by
    have hcont :
        Continuous (fun y : E ↦ dist (ϕ (hitTime x) y) xEq) :=
      (ϕ.continuous continuous_const continuous_id).dist continuous_const
    exact isOpen_lt hcont continuous_const
  have hUself (x : K) : x.1 ∈ U x :=
    hhitTime_enters x
  have hcover : K ⊆ ⋃ x : K, U x := by
    intro y hy
    exact mem_iUnion.2 ⟨⟨y, hy⟩, hUself ⟨y, hy⟩⟩
  obtain ⟨S, hScover⟩ :=
    hK.elim_finite_subcover U hUopen hcover
  let T : ℝ := ∑ x ∈ S, hitTime x
  have hT_nonneg : 0 ≤ T := by
    dsimp only [T]
    exact Finset.sum_nonneg (fun x _hx ↦ hhitTime_nonneg x)
  refine ⟨T, hT_nonneg, ?_⟩
  intro y hy t ht
  have hycover : y ∈ ⋃ x ∈ S, U x :=
    hScover hy
  obtain ⟨x, hxS, hyU⟩ := mem_iUnion₂.1 hycover
  have hxTime_le : hitTime x ≤ T := by
    dsimp only [T]
    exact Finset.single_le_sum
      (fun z hz ↦ hhitTime_nonneg z) hxS
  let s : ℝ := t - hitTime x
  have hs : 0 ≤ s := by
    dsimp only [s]
    linarith
  have hshift :
      IsForwardTrajectory F
        (fun r : ℝ ↦ ϕ r (ϕ (hitTime x) y))
        (ϕ (hitTime x) y) :=
    hflow (ϕ (hitTime x) y)
  have hremain :=
    hstable (ϕ (hitTime x) y) hyU
      (fun r : ℝ ↦ ϕ r (ϕ (hitTime x) y))
      hshift s hs
  have hadd : s + hitTime x = t := by
    dsimp only [s]
    ring
  rw [← hadd, ϕ.map_add]
  exact hremain

/-- Variant of `uniformAttractionOnCompact` in which the supplied global
auxiliary flow is required to solve the original ODE only for initial
points in the compact set.

This is the form needed for homogeneous polynomial fields: a smooth
cutoff gives a two-sided global ambient flow, and its nonnegative orbits
agree with the original (possibly backward-incomplete) field for all
unit-sphere initial conditions. -/
theorem GloballyAsymptoticallyStable.uniformAttractionOnCompact_of_orbits
    {F : E → E} {xEq : E}
    (hgas : GloballyAsymptoticallyStable F xEq)
    (ϕ : Flow ℝ E)
    {K : Set E} (hK : IsCompact K)
    (hflow :
      ∀ x ∈ K,
        IsForwardTrajectory F (fun t : ℝ ↦ ϕ t x) x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 0 ≤ T ∧
      ∀ x ∈ K, ∀ t : ℝ, T ≤ t →
        dist (ϕ t x) xEq < ε := by
  obtain ⟨δ, hδ, hstable⟩ :=
    hgas.stable ε hε
  let hitTime : K → ℝ :=
    fun x ↦ Classical.choose
      (hgas.attractive x.1
        (fun t : ℝ ↦ ϕ t x.1) (hflow x.1 x.2) δ hδ)
  have hhitTime_nonneg (x : K) :
      0 ≤ hitTime x :=
    (Classical.choose_spec
      (hgas.attractive x.1
        (fun t : ℝ ↦ ϕ t x.1) (hflow x.1 x.2) δ hδ)).1
  have hhitTime_enters (x : K) :
      dist (ϕ (hitTime x) x.1) xEq < δ := by
    have hspec :=
      Classical.choose_spec
        (hgas.attractive x.1
          (fun t : ℝ ↦ ϕ t x.1) (hflow x.1 x.2) δ hδ)
    exact hspec.2 (hitTime x) le_rfl
  let U : K → Set E :=
    fun x ↦ {y | dist (ϕ (hitTime x) y) xEq < δ}
  have hUopen (x : K) : IsOpen (U x) := by
    have hcont :
        Continuous (fun y : E ↦ dist (ϕ (hitTime x) y) xEq) :=
      (ϕ.continuous continuous_const continuous_id).dist continuous_const
    exact isOpen_lt hcont continuous_const
  have hUself (x : K) : x.1 ∈ U x :=
    hhitTime_enters x
  have hcover : K ⊆ ⋃ x : K, U x := by
    intro y hy
    exact mem_iUnion.2 ⟨⟨y, hy⟩, hUself ⟨y, hy⟩⟩
  obtain ⟨S, hScover⟩ :=
    hK.elim_finite_subcover U hUopen hcover
  let T : ℝ := ∑ x ∈ S, hitTime x
  have hT_nonneg : 0 ≤ T := by
    dsimp only [T]
    exact Finset.sum_nonneg (fun x _hx ↦ hhitTime_nonneg x)
  refine ⟨T, hT_nonneg, ?_⟩
  intro y hy t ht
  have hycover : y ∈ ⋃ x ∈ S, U x :=
    hScover hy
  obtain ⟨x, hxS, hyU⟩ := mem_iUnion₂.1 hycover
  have hxTime_le : hitTime x ≤ T := by
    dsimp only [T]
    exact Finset.single_le_sum
      (fun z hz ↦ hhitTime_nonneg z) hxS
  let s : ℝ := t - hitTime x
  have hs : 0 ≤ s := by
    dsimp only [s]
    linarith
  have hshift :
      IsForwardTrajectory F
        (fun r : ℝ ↦ ϕ r (ϕ (hitTime x) y))
        (ϕ (hitTime x) y) :=
    (hflow y hy).flow_timeShift ϕ
      (hhitTime_nonneg x)
  have hremain :=
    hstable (ϕ (hitTime x) y) hyU
      (fun r : ℝ ↦ ϕ r (ϕ (hitTime x) y))
      hshift s hs
  have hadd : s + hitTime x = t := by
    dsimp only [s]
    ring
  rw [← hadd, ϕ.map_add]
  exact hremain

end

end HGAS
