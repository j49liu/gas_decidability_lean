import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Scratch development for the finite maximal ergodic lemma.
-/

open Filter Function MeasureTheory Set Topology

noncomputable section

namespace HGAS.Dynamics

variable {X : Type*} [MeasurableSpace X]

/-- The positive maximum of the first `n` partial sums, defined recursively.
The recursion is the dynamic-programming identity
`M_{n+1} f x = max 0 (f x + M_n f (T x))`. -/
def positiveMaxPartialSum (T : X → X) (f : X → ℝ) :
    ℕ → X → ℝ
  | 0 => 0
  | n + 1 => fun x => max 0 (f x + positiveMaxPartialSum T f n (T x))

omit [MeasurableSpace X] in
@[simp]
theorem positiveMaxPartialSum_zero
    (T : X → X) (f : X → ℝ) :
    positiveMaxPartialSum T f 0 = 0 :=
  rfl

omit [MeasurableSpace X] in
@[simp]
theorem positiveMaxPartialSum_succ_apply
    (T : X → X) (f : X → ℝ) (n : ℕ) (x : X) :
    positiveMaxPartialSum T f (n + 1) x =
      max 0 (f x + positiveMaxPartialSum T f n (T x)) :=
  rfl

omit [MeasurableSpace X] in
theorem positiveMaxPartialSum_nonneg
    (T : X → X) (f : X → ℝ) (n : ℕ) (x : X) :
    0 ≤ positiveMaxPartialSum T f n x := by
  cases n with
  | zero => simp
  | succ n => simp [positiveMaxPartialSum]

omit [MeasurableSpace X] in
theorem positiveMaxPartialSum_mono_nat
    (T : X → X) (f : X → ℝ) :
    Monotone (fun n ↦ positiveMaxPartialSum T f n) := by
  refine monotone_nat_of_le_succ ?_
  intro n x
  induction n generalizing x with
  | zero =>
      exact positiveMaxPartialSum_nonneg T f 1 x
  | succ n ih =>
      simp only [positiveMaxPartialSum_succ_apply]
      exact max_le_max_left 0 (by
        have h := ih (T x)
        exact add_le_add_right h (f x))

omit [MeasurableSpace X] in
/-- The recursion is exactly the maximum of zero and the first `n`
Birkhoff partial sums. -/
theorem positiveMaxPartialSum_eq_sup'
    (T : X → X) (f : X → ℝ) (n : ℕ) (x : X) :
    positiveMaxPartialSum T f n x =
      (Finset.range (n + 1)).sup'
        ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩
        (fun k ↦ birkhoffSum T f k x) := by
  induction n generalizing x with
  | zero =>
      simp [positiveMaxPartialSum, birkhoffSum]
  | succ n ih =>
      let hne : (Finset.range (n + 1)).Nonempty :=
        ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩
      let hne' : (Finset.range (n + 2)).Nonempty :=
        ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ (n + 1))⟩
      apply le_antisymm
      · rw [positiveMaxPartialSum_succ_apply]
        apply max_le
        · exact Finset.le_sup'_of_le
            (f := fun k ↦ birkhoffSum T f k x)
            (Finset.mem_range.mpr (Nat.zero_lt_succ (n + 1)))
            (by simp only [birkhoffSum_zero]; exact le_rfl)
        · rw [ih]
          obtain ⟨j, hj, hjmax⟩ :=
            Finset.exists_mem_eq_sup' hne
              (fun k ↦ birkhoffSum T f k (T x))
          rw [hjmax]
          have hjsucc : j + 1 ∈ Finset.range (n + 2) := by
            simp only [Finset.mem_range] at hj ⊢
            omega
          refine Finset.le_sup'_of_le
            (f := fun k ↦ birkhoffSum T f k x) hjsucc ?_
          exact (birkhoffSum_succ' T f j x).symm.le
      · refine Finset.sup'_le hne'
          (fun k ↦ birkhoffSum T f k x) ?_
        intro k hk
        simp only [Finset.mem_range] at hk
        cases k with
        | zero =>
            exact positiveMaxPartialSum_nonneg T f (n + 1) x
        | succ j =>
            have hj : j ∈ Finset.range (n + 1) := by
              simp only [Finset.mem_range]
              omega
            change birkhoffSum T f (j + 1) x ≤
              positiveMaxPartialSum T f (n + 1) x
            rw [birkhoffSum_succ',
              positiveMaxPartialSum_succ_apply, ih]
            exact le_max_of_le_right
              (add_le_add_right
                (Finset.le_sup'
                  (fun k ↦ birkhoffSum T f k (T x)) hj)
                (f x))

theorem measurable_positiveMaxPartialSum
    {T : X → X} {f : X → ℝ}
    (hT : Measurable T) (hf : Measurable f) :
    ∀ n, Measurable (positiveMaxPartialSum T f n)
  | 0 => measurable_const
  | n + 1 =>
      measurable_const.max
        (hf.add ((measurable_positiveMaxPartialSum hT hf n).comp hT))

theorem integrable_positiveMaxPartialSum
    {T : X → X} {f : X → ℝ} {μ : Measure X}
    (hT : MeasurePreserving T μ μ)
    (hf : Integrable f μ) :
    ∀ n, Integrable (positiveMaxPartialSum T f n) μ
  | 0 => integrable_zero _ _ _
  | n + 1 => by
      simpa only [max_comm] using
        (hf.add (hT.integrable_comp_of_integrable
          (integrable_positiveMaxPartialSum hT hf n))).pos_part

/-- The points where at least one of the first `n` partial sums is
positive. -/
def positiveMaxPartialSumSet
    (T : X → X) (f : X → ℝ) (n : ℕ) : Set X :=
  {x | 0 < positiveMaxPartialSum T f n x}

omit [MeasurableSpace X] in
/-- Membership in the positivity set means exactly that one of the
first `n` nonempty Birkhoff sums is positive. -/
theorem mem_positiveMaxPartialSumSet_iff
    (T : X → X) (f : X → ℝ) (n : ℕ) (x : X) :
    x ∈ positiveMaxPartialSumSet T f n ↔
      ∃ k < n + 1, 0 < birkhoffSum T f k x := by
  rw [positiveMaxPartialSumSet, mem_setOf_eq,
    positiveMaxPartialSum_eq_sup']
  simpa only [Finset.mem_range] using
    (Finset.lt_sup'_iff
      (H := ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩)
      (f := fun k ↦ birkhoffSum T f k x) (a := (0 : ℝ)))

theorem measurableSet_positiveMaxPartialSumSet
    {T : X → X} {f : X → ℝ}
    (hT : Measurable T) (hf : Measurable f) (n : ℕ) :
    MeasurableSet (positiveMaxPartialSumSet T f n) := by
  exact measurableSet_Ioi.preimage
    (measurable_positiveMaxPartialSum hT hf n)

omit [MeasurableSpace X] in
/-- The recursive maximum vanishes off its positivity set. -/
theorem positiveMaxPartialSum_eq_zero_of_not_mem
    (T : X → X) (f : X → ℝ) (n : ℕ) {x : X}
    (hx : x ∉ positiveMaxPartialSumSet T f n) :
    positiveMaxPartialSum T f n x = 0 := by
  have hnonneg := positiveMaxPartialSum_nonneg T f n x
  simp only [positiveMaxPartialSumSet, mem_setOf_eq, not_lt] at hx
  exact le_antisymm hx hnonneg

omit [MeasurableSpace X] in
/-- On its positivity set, the recursive maximum satisfies the
untruncated recursion. -/
theorem positiveMaxPartialSum_succ_eq_on_positiveSet
    (T : X → X) (f : X → ℝ) (n : ℕ) {x : X}
    (hx : x ∈ positiveMaxPartialSumSet T f (n + 1)) :
    positiveMaxPartialSum T f (n + 1) x =
      f x + positiveMaxPartialSum T f n (T x) := by
  rw [positiveMaxPartialSum_succ_apply]
  have h :
      0 < f x + positiveMaxPartialSum T f n (T x) := by
    simpa only [positiveMaxPartialSumSet, mem_setOf_eq,
      positiveMaxPartialSum_succ_apply, lt_max_iff,
      lt_self_iff_false, false_or] using hx
  exact max_eq_right h.le

/-- The finite maximal ergodic lemma.

For a measure-preserving map `T` and an integrable real observable `f`,
the integral of `f` over the set where one of its first `n` partial sums
is positive is nonnegative.  This is the finite combinatorial core of
the pointwise ergodic theorem. -/
theorem finite_maximal_ergodic
    {T : X → X} {f : X → ℝ} {μ : Measure X}
    (hT : MeasurePreserving T μ μ)
    (hf_meas : Measurable f) (hf_int : Integrable f μ)
    (n : ℕ) :
    0 ≤ ∫ x in positiveMaxPartialSumSet T f (n + 1), f x ∂μ := by
  let M : ℕ → X → ℝ := positiveMaxPartialSum T f
  let E : Set X := positiveMaxPartialSumSet T f (n + 1)
  have hM_meas (k : ℕ) : Measurable (M k) :=
    measurable_positiveMaxPartialSum hT.measurable hf_meas k
  have hM_int (k : ℕ) : Integrable (M k) μ :=
    integrable_positiveMaxPartialSum hT hf_int k
  have hE_meas : MeasurableSet E :=
    measurableSet_positiveMaxPartialSumSet hT.measurable hf_meas (n + 1)
  have hcomp_int : Integrable (fun x ↦ M n (T x)) μ :=
    hT.integrable_comp_of_integrable (hM_int n)
  have hpoint :
      ∀ x ∈ E, f x = M (n + 1) x - M n (T x) := by
    intro x hx
    have hrec :=
      positiveMaxPartialSum_succ_eq_on_positiveSet T f n hx
    dsimp only [M] at hrec ⊢
    linarith
  have hset_eq :
      (∫ x in E, f x ∂μ) =
        ∫ x in E, (M (n + 1) x - M n (T x)) ∂μ := by
    exact setIntegral_congr_fun hE_meas hpoint
  have hnext_set :
      (∫ x in E, M (n + 1) x ∂μ) =
        ∫ x, M (n + 1) x ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    exact positiveMaxPartialSum_eq_zero_of_not_mem T f (n + 1) hx
  have hcomp_full :
      (∫ x, M n (T x) ∂μ) = ∫ x, M n x ∂μ := by
    calc
      (∫ x, M n (T x) ∂μ) =
          ∫ x, M n x ∂Measure.map T μ := by
            symm
            exact integral_map hT.measurable.aemeasurable
              (hM_meas n).aestronglyMeasurable
      _ = ∫ x, M n x ∂μ := by rw [hT.map_eq]
  have hcomp_set_le :
      (∫ x in E, M n (T x) ∂μ) ≤ ∫ x, M n x ∂μ := by
    calc
      (∫ x in E, M n (T x) ∂μ) ≤
          ∫ x, M n (T x) ∂μ :=
        setIntegral_le_integral hcomp_int
          (Eventually.of_forall fun x ↦
            positiveMaxPartialSum_nonneg T f n (T x))
      _ = ∫ x, M n x ∂μ := hcomp_full
  have hmono_full :
      (∫ x, M n x ∂μ) ≤ ∫ x, M (n + 1) x ∂μ := by
    exact integral_mono (hM_int n) (hM_int (n + 1))
      (positiveMaxPartialSum_mono_nat T f (Nat.le_succ n))
  rw [hset_eq, integral_sub (hM_int (n + 1)).integrableOn
    hcomp_int.integrableOn, hnext_set]
  linarith

omit [MeasurableSpace X] in
/-- Subtracting a constant from an observable subtracts `n` copies of
that constant from its `n`th Birkhoff sum. -/
theorem birkhoffSum_sub_const
    (T : X → X) (f : X → ℝ) (c : ℝ) (n : ℕ) (x : X) :
    birkhoffSum T (fun y ↦ f y - c) n x =
      birkhoffSum T f n x - (n : ℝ) * c := by
  simp only [birkhoffSum, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]

omit [MeasurableSpace X] in
/-- Positivity of the shifted partial-sum maximum is the same as a
finite Birkhoff average exceeding the shift. -/
theorem mem_positiveMaxPartialSumSet_sub_const_iff
    (T : X → X) (f : X → ℝ) {c : ℝ} (hc : 0 < c)
    (n : ℕ) (x : X) :
    x ∈ positiveMaxPartialSumSet T (fun y ↦ f y - c) n ↔
      ∃ k < n + 1, c < birkhoffAverage ℝ T f k x := by
  rw [mem_positiveMaxPartialSumSet_iff]
  constructor
  · rintro ⟨k, hk, hsum⟩
    have hkpos : 0 < k := by
      cases k with
      | zero =>
          simp only [birkhoffSum_zero] at hsum
          exact (lt_irrefl 0 hsum).elim
      | succ k => exact Nat.zero_lt_succ k
    refine ⟨k, hk, ?_⟩
    rw [birkhoffSum_sub_const] at hsum
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hkpos
    rw [birkhoffAverage]
    change c < (k : ℝ)⁻¹ * birkhoffSum T f k x
    rw [inv_mul_eq_div]
    exact (lt_div_iff₀ hkR).2 (by nlinarith)
  · rintro ⟨k, hk, havg⟩
    have hkpos : 0 < k := by
      by_contra hkzero
      have : k = 0 := Nat.eq_zero_of_not_pos hkzero
      subst k
      simp only [birkhoffAverage_zero] at havg
      linarith
    refine ⟨k, hk, ?_⟩
    rw [birkhoffSum_sub_const]
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hkpos
    rw [birkhoffAverage] at havg
    change c < (k : ℝ)⁻¹ * birkhoffSum T f k x at havg
    rw [inv_mul_eq_div] at havg
    have := (lt_div_iff₀ hkR).1 havg
    nlinarith

/-- The finite weak `(1,1)` maximal inequality for Birkhoff averages.
The right side is localized to the finite exceedance set, which is
slightly sharper than the usual global `L¹` bound. -/
theorem finite_birkhoff_maximal_inequality
    {T : X → X} {f : X → ℝ} {μ : Measure X}
    [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ)
    (hf_meas : Measurable f) (hf_int : Integrable f μ)
    {c : ℝ} (hc : 0 < c) (n : ℕ) :
    c * μ.real
        {x | ∃ k < n + 2, c < birkhoffAverage ℝ T f k x} ≤
      ∫ x in {x | ∃ k < n + 2,
        c < birkhoffAverage ℝ T f k x}, |f x| ∂μ := by
  let g : X → ℝ := fun x ↦ f x - c
  let E : Set X := positiveMaxPartialSumSet T g (n + 1)
  have hg_meas : Measurable g := hf_meas.sub measurable_const
  have hg_int : Integrable g μ := hf_int.sub (integrable_const c)
  have hE_meas : MeasurableSet E :=
    measurableSet_positiveMaxPartialSumSet hT.measurable hg_meas (n + 1)
  have hmax : 0 ≤ ∫ x in E, g x ∂μ :=
    finite_maximal_ergodic hT hg_meas hg_int n
  have hE_desc :
      E = {x | ∃ k < n + 2,
        c < birkhoffAverage ℝ T f k x} := by
    ext x
    exact mem_positiveMaxPartialSumSet_sub_const_iff T f hc (n + 1) x
  have hshift :
      (∫ x in E, g x ∂μ) =
        (∫ x in E, f x ∂μ) - c * μ.real E := by
    rw [show g = fun x ↦ f x - c by rfl,
      integral_sub hf_int.integrableOn
        (integrable_const c).integrableOn]
    simp only [setIntegral_const, smul_eq_mul]
    ring
  have hf_le_abs :
      (∫ x in E, f x ∂μ) ≤ ∫ x in E, |f x| ∂μ := by
    exact setIntegral_mono_on hf_int.integrableOn hf_int.abs.integrableOn
      hE_meas (fun x _ ↦ le_abs_self (f x))
  rw [hE_desc] at hmax hshift hf_le_abs
  linarith

/-- The weak `(1,1)` maximal inequality over all positive averaging
lengths. -/
theorem birkhoff_maximal_inequality
    {T : X → X} {f : X → ℝ} {μ : Measure X}
    [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ)
    (hf_meas : Measurable f) (hf_int : Integrable f μ)
    {c : ℝ} (hc : 0 < c) :
    c * μ.real
        {x | ∃ k, c < birkhoffAverage ℝ T f k x} ≤
      ∫ x, |f x| ∂μ := by
  let E : ℕ → Set X := fun n ↦
    {x | ∃ k < n + 2, c < birkhoffAverage ℝ T f k x}
  let Eall : Set X :=
    {x | ∃ k, c < birkhoffAverage ℝ T f k x}
  have hmono : Monotone E := by
    intro m n hmn x
    rintro ⟨k, hk, havg⟩
    exact ⟨k, by omega, havg⟩
  have hunion : (⋃ n, E n) = Eall := by
    ext x
    simp only [mem_iUnion, E, Eall, mem_setOf_eq]
    constructor
    · rintro ⟨n, k, _, hk⟩
      exact ⟨k, hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, k, by omega, hk⟩
  have hfinite (n : ℕ) :
      c * μ.real (E n) ≤ ∫ x, |f x| ∂μ := by
    exact (finite_birkhoff_maximal_inequality hT hf_meas hf_int hc n).trans
      (setIntegral_le_integral hf_int.abs
        (Eventually.of_forall fun x ↦ abs_nonneg (f x)))
  have hmeasure :
      Tendsto (fun n ↦ μ.real (E n)) atTop
        (𝓝 (μ.real Eall)) := by
    have hμ :
        Tendsto (fun n ↦ μ (E n)) atTop
          (𝓝 (μ (⋃ n, E n))) :=
      tendsto_measure_iUnion_atTop hmono
    rw [hunion] at hμ
    simpa only [measureReal_def] using
      (ENNReal.tendsto_toReal (by finiteness)).comp hμ
  exact le_of_tendsto'
    (tendsto_const_nhds.mul hmeasure) hfinite

/-- The two-sided weak maximal inequality. -/
theorem birkhoff_absolute_maximal_inequality
    {T : X → X} {f : X → ℝ} {μ : Measure X}
    [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ)
    (hf_meas : Measurable f) (hf_int : Integrable f μ)
    {c : ℝ} (hc : 0 < c) :
    c * μ.real
        {x | ∃ k, c < |birkhoffAverage ℝ T f k x|} ≤
      2 * ∫ x, |f x| ∂μ := by
  let Eabs : Set X :=
    {x | ∃ k, c < |birkhoffAverage ℝ T f k x|}
  let Epos : Set X :=
    {x | ∃ k, c < birkhoffAverage ℝ T f k x}
  let Eneg : Set X :=
    {x | ∃ k, c <
      birkhoffAverage ℝ T (fun y ↦ -f y) k x}
  have hsubset : Eabs ⊆ Epos ∪ Eneg := by
    intro x
    rintro ⟨k, hk⟩
    rcases (lt_abs.mp hk) with hkpos | hkneg
    · exact Or.inl ⟨k, hkpos⟩
    · right
      refine ⟨k, ?_⟩
      change c < birkhoffAverage ℝ T (-f) k x
      rw [birkhoffAverage_neg]
      simp only [Pi.neg_apply]
      linarith
  have hmeasure :
      μ.real Eabs ≤ μ.real Epos + μ.real Eneg :=
    (measureReal_mono hsubset).trans (measureReal_union_le Epos Eneg)
  have hpos :
      c * μ.real Epos ≤ ∫ x, |f x| ∂μ :=
    birkhoff_maximal_inequality hT hf_meas hf_int hc
  have hneg :
      c * μ.real Eneg ≤ ∫ x, |f x| ∂μ := by
    simpa only [abs_neg] using
      (birkhoff_maximal_inequality hT hf_meas.neg hf_int.neg hc)
  dsimp only [Eabs, Epos, Eneg] at hmeasure hpos hneg ⊢
  have hc0 : 0 ≤ c := hc.le
  nlinarith [mul_le_mul_of_nonneg_left hmeasure hc0]

omit [MeasurableSpace X] in
/-- A bounded coboundary has pointwise Birkhoff average zero. -/
theorem tendsto_birkhoffAverage_coboundary
    (T : X → X) (g : X → ℝ)
    (hg : Bornology.IsBounded (range g)) (x : X) :
    Tendsto
      (fun n ↦ birkhoffAverage ℝ T (fun y ↦ g (T y) - g y) n x)
      atTop (𝓝 0) := by
  have horbit :
      Bornology.IsBounded (range (g <| T^[·] x)) := by
    apply hg.subset
    rintro _ ⟨n, rfl⟩
    exact mem_range_self (T^[n] x)
  have hbase :=
    tendsto_birkhoffAverage_apply_sub_birkhoffAverage
      (𝕜 := ℝ) (f := T) (g := g) (x := x) horbit
  convert hbase using 1
  funext n
  change birkhoffAverage ℝ T ((g ∘ T) - g) n x =
    birkhoffAverage ℝ T g n (T x) - birkhoffAverage ℝ T g n x
  rw [birkhoffAverage_sub]
  simp only [Pi.sub_apply]
  congr 1
  unfold birkhoffAverage
  apply congrArg
  unfold birkhoffSum
  apply Finset.sum_congr rfl
  intro k _
  simp only [Function.comp_apply]
  rw [← iterate_succ_apply, iterate_succ_apply']

/-- Points where the Birkhoff averages make deviations larger than
`c` arbitrarily far out in time. -/
def birkhoffPersistentDeviationSet
    (T : X → X) (f : X → ℝ) (c : ℝ) : Set X :=
  {x | ∀ N, ∃ n ≥ N, c < |birkhoffAverage ℝ T f n x|}

omit [MeasurableSpace X] in
/-- If a bounded coboundary is subtracted from `f`, then every
persistent `2c` deviation of `f` produces some `c` deviation of the
residual. -/
theorem birkhoffPersistentDeviationSet_subset_residualMax
    (T : X → X) (f g : X → ℝ)
    (hg : Bornology.IsBounded (range g))
    {c : ℝ} (hc : 0 < c) :
    birkhoffPersistentDeviationSet T f (2 * c) ⊆
      {x | ∃ n, c <
        |birkhoffAverage ℝ T
          (fun y ↦ f y - (g (T y) - g y)) n x|} := by
  intro x hx
  have hcob :=
    tendsto_birkhoffAverage_coboundary T g hg x
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.1 hcob) c hc
  obtain ⟨n, hn, hdev⟩ := hx N
  refine ⟨n, ?_⟩
  have hcob_small :
      |birkhoffAverage ℝ T
        (fun y ↦ g (T y) - g y) n x| < c := by
    simpa only [Real.dist_eq, sub_zero] using hN n hn
  have hres :
      birkhoffAverage ℝ T
          (fun y ↦ f y - (g (T y) - g y)) n x =
        birkhoffAverage ℝ T f n x -
          birkhoffAverage ℝ T
            (fun y ↦ g (T y) - g y) n x := by
    change birkhoffAverage ℝ T
      (f - fun y ↦ g (T y) - g y) n x = _
    rw [birkhoffAverage_sub]
    rfl
  have htriangle :
      |birkhoffAverage ℝ T f n x| ≤
        |birkhoffAverage ℝ T
          (fun y ↦ f y - (g (T y) - g y)) n x| +
        |birkhoffAverage ℝ T
          (fun y ↦ g (T y) - g y) n x| := by
    let F := birkhoffAverage ℝ T f n x
    let C := birkhoffAverage ℝ T
      (fun y ↦ g (T y) - g y) n x
    let R := birkhoffAverage ℝ T
      (fun y ↦ f y - (g (T y) - g y)) n x
    have hRF : R = F - C := hres
    calc
      |F| = |(F - C) + C| := by rw [sub_add_cancel]
      _ ≤ |F - C| + |C| := abs_add_le _ _
      _ = |R| + |C| := by rw [hRF]
  linarith

/-- An observable is in the `L¹` closure of bounded coboundaries if it
can be approximated in integral absolute value by functions
`g ∘ T - g` with bounded measurable transfer function `g`. -/
def IsL1LimitOfBoundedCoboundaries
    (T : X → X) (f : X → ℝ) (μ : Measure X) : Prop :=
  ∀ ε, 0 < ε → ∃ g : X → ℝ,
    Measurable g ∧ Integrable g μ ∧
      Bornology.IsBounded (range g) ∧
        (∫ x, |f x - (g (T x) - g x)| ∂μ) < ε

/-- The Banach-principle step: for an `L¹` limit of bounded
coboundaries, every fixed positive persistent-deviation set is null. -/
theorem measureReal_birkhoffPersistentDeviationSet_eq_zero
    {T : X → X} {f : X → ℝ} {μ : Measure X}
    [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ)
    (hf_meas : Measurable f) (hf_int : Integrable f μ)
    (hclosure : IsL1LimitOfBoundedCoboundaries T f μ)
    {c : ℝ} (hc : 0 < c) :
    μ.real (birkhoffPersistentDeviationSet T f (2 * c)) = 0 := by
  apply le_antisymm
  · by_contra hne
    have hmass :
        0 < μ.real (birkhoffPersistentDeviationSet T f (2 * c)) :=
      lt_of_not_ge hne
    let ε : ℝ :=
      c * μ.real (birkhoffPersistentDeviationSet T f (2 * c)) / 4
    have hε : 0 < ε := by
      dsimp only [ε]
      positivity
    obtain ⟨g, hg_meas, hg_int, hg_bdd, hg_approx⟩ :=
      hclosure ε hε
    let r : X → ℝ := fun x ↦ f x - (g (T x) - g x)
    have hr_meas : Measurable r :=
      hf_meas.sub ((hg_meas.comp hT.measurable).sub hg_meas)
    have hr_int : Integrable r μ :=
      hf_int.sub
        ((hT.integrable_comp_of_integrable hg_int).sub hg_int)
    have hsubset :
        birkhoffPersistentDeviationSet T f (2 * c) ⊆
          {x | ∃ n, c < |birkhoffAverage ℝ T r n x|} := by
      exact birkhoffPersistentDeviationSet_subset_residualMax
        T f g hg_bdd hc
    have hmass_le :
        μ.real (birkhoffPersistentDeviationSet T f (2 * c)) ≤
          μ.real {x | ∃ n, c <
            |birkhoffAverage ℝ T r n x|} :=
      measureReal_mono hsubset
    have hmax :
        c * μ.real {x | ∃ n, c <
            |birkhoffAverage ℝ T r n x|} ≤
          2 * ∫ x, |r x| ∂μ :=
      birkhoff_absolute_maximal_inequality
        hT hr_meas hr_int hc
    have hscaled :
        c * μ.real (birkhoffPersistentDeviationSet T f (2 * c)) ≤
          c * μ.real {x | ∃ n, c <
            |birkhoffAverage ℝ T r n x|} :=
      mul_le_mul_of_nonneg_left hmass_le hc.le
    have happ :
        (∫ x, |r x| ∂μ) < ε := hg_approx
    dsimp only [ε] at hε
    dsimp only [r] at happ
    have : c * μ.real
          (birkhoffPersistentDeviationSet T f (2 * c)) <
        c * μ.real
          (birkhoffPersistentDeviationSet T f (2 * c)) := by
      calc
        c * μ.real
              (birkhoffPersistentDeviationSet T f (2 * c)) ≤
            c * μ.real {x | ∃ n, c <
              |birkhoffAverage ℝ T r n x|} := hscaled
        _ ≤ 2 * ∫ x, |r x| ∂μ := hmax
        _ < 2 * ε := by nlinarith
        _ < c * μ.real
              (birkhoffPersistentDeviationSet T f (2 * c)) := by
            dsimp only [ε]
            nlinarith
    exact (lt_irrefl _ this)
  · exact measureReal_nonneg

/-- The full Banach principle: every integrable observable in the
`L¹` closure of bounded coboundaries has Birkhoff averages converging
to zero almost everywhere. -/
theorem ae_tendsto_birkhoffAverage_zero_of_L1Limit_boundedCoboundaries
    {T : X → X} {f : X → ℝ} {μ : Measure X}
    [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ)
    (hf_meas : Measurable f) (hf_int : Integrable f μ)
    (hclosure : IsL1LimitOfBoundedCoboundaries T f μ) :
    ∀ᵐ x ∂μ,
      Tendsto (fun n ↦ birkhoffAverage ℝ T f n x)
        atTop (𝓝 0) := by
  let D : ℕ → Set X := fun m ↦
    birkhoffPersistentDeviationSet T f
      (2 * ((m + 1 : ℕ) : ℝ)⁻¹)
  let B : Set X := {x |
    ¬ Tendsto (fun n ↦ birkhoffAverage ℝ T f n x)
      atTop (𝓝 0)}
  have hB_subset : B ⊆ ⋃ m, D m := by
    intro x hx
    change ¬ Tendsto
      (fun n ↦ birkhoffAverage ℝ T f n x)
      atTop (𝓝 0) at hx
    rw [Metric.tendsto_atTop] at hx
    push Not at hx
    obtain ⟨ε, hε, hx⟩ := hx
    have hseq :
        Tendsto (fun m : ℕ ↦ (2 : ℝ) / (m + 1))
          atTop (𝓝 0) :=
      by
        convert
          (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp
            (tendsto_add_atTop_nat 1) using 1
        funext m
        simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    have hevent :
        ∀ᶠ m : ℕ in atTop, (2 : ℝ) / (m + 1) < ε :=
      (tendsto_order.1 hseq).2 ε hε
    obtain ⟨m, hm⟩ := eventually_atTop.1 hevent
    apply mem_iUnion.2
    refine ⟨m, ?_⟩
    dsimp only [D, birkhoffPersistentDeviationSet]
    intro N
    obtain ⟨n, hn, hdev⟩ := hx N
    refine ⟨n, hn, ?_⟩
    have hsmall := hm m (le_refl m)
    have hrewrite :
        2 * ((m + 1 : ℕ) : ℝ)⁻¹ =
          (2 : ℝ) / (m + 1) := by
      rw [div_eq_mul_inv]
      norm_num
    rw [hrewrite]
    have hdev' :
        ε ≤ |birkhoffAverage ℝ T f n x| := by
      simpa only [Real.dist_eq, sub_zero] using hdev
    exact hsmall.trans_le hdev'
  have hD_zero (m : ℕ) : μ (D m) = 0 := by
    have hc : 0 < (((m + 1 : ℕ) : ℝ)⁻¹) := by positivity
    have hreal :=
      measureReal_birkhoffPersistentDeviationSet_eq_zero
        hT hf_meas hf_int hclosure hc
    exact (measureReal_eq_zero_iff).1 (by
      simpa only [D] using hreal)
  have hB_zero : μ B = 0 :=
    measure_mono_null hB_subset (measure_iUnion_null hD_zero)
  rw [ae_iff]
  simpa only [B, compl_setOf, not_not] using hB_zero

/-- A finite transfer function whose coboundary is the difference
between `f` and its `n`th Birkhoff average. -/
def birkhoffCoboundaryTransfer
    (T : X → X) (f : X → ℝ) (n : ℕ) (x : X) : ℝ :=
  -(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, birkhoffSum T f k x

omit [MeasurableSpace X] in
/-- The finite transfer function satisfies the exact coboundary
identity `g ∘ T - g = f - Aₙ f`. -/
theorem birkhoffCoboundaryTransfer_comp_sub
    (T : X → X) (f : X → ℝ) {n : ℕ} (hn : 0 < n) (x : X) :
    birkhoffCoboundaryTransfer T f n (T x) -
        birkhoffCoboundaryTransfer T f n x =
      f x - birkhoffAverage ℝ T f n x := by
  unfold birkhoffCoboundaryTransfer birkhoffAverage
  simp only [smul_eq_mul]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  simp_rw [birkhoffSum_apply_sub_birkhoffSum]
  rw [Finset.sum_sub_distrib]
  simp only [birkhoffSum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  field_simp
  ring

theorem measurable_birkhoffSum
    {T : X → X} {f : X → ℝ}
    (hT : Measurable T) (hf : Measurable f) (n : ℕ) :
    Measurable (birkhoffSum T f n) := by
  unfold birkhoffSum
  fun_prop

theorem integrable_birkhoffSum
    {T : X → X} {f : X → ℝ} {μ : Measure X}
    (hT : MeasurePreserving T μ μ)
    (hf : Integrable f μ) (n : ℕ) :
    Integrable (birkhoffSum T f n) μ := by
  unfold birkhoffSum
  apply integrable_finsetSum
  intro k _
  exact (hT.iterate k).integrable_comp_of_integrable hf

theorem measurable_birkhoffCoboundaryTransfer
    {T : X → X} {f : X → ℝ}
    (hT : Measurable T) (hf : Measurable f) (n : ℕ) :
    Measurable (birkhoffCoboundaryTransfer T f n) := by
  unfold birkhoffCoboundaryTransfer
  have hsum :
      Measurable (fun x ↦
        ∑ k ∈ Finset.range n, birkhoffSum T f k x) := by
    apply Finset.measurable_fun_sum
    intro k _
    exact measurable_birkhoffSum hT hf k
  exact measurable_const.mul hsum

theorem integrable_birkhoffCoboundaryTransfer
    {T : X → X} {f : X → ℝ} {μ : Measure X}
    (hT : MeasurePreserving T μ μ)
    (hf : Integrable f μ) (n : ℕ) :
    Integrable (birkhoffCoboundaryTransfer T f n) μ := by
  unfold birkhoffCoboundaryTransfer
  exact (integrable_finsetSum (Finset.range n)
    (fun k _ ↦ integrable_birkhoffSum hT hf k)).const_mul _

omit [MeasurableSpace X] in
theorem abs_birkhoffSum_le
    (T : X → X) {f : X → ℝ} {C : ℝ}
    (hf : ∀ x, |f x| ≤ C) (n : ℕ) (x : X) :
    |birkhoffSum T f n x| ≤ (n : ℝ) * C := by
  unfold birkhoffSum
  calc
    |∑ k ∈ Finset.range n, f (T^[k] x)| ≤
        ∑ k ∈ Finset.range n, |f (T^[k] x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, C := by
      gcongr with k hk
      exact hf (T^[k] x)
    _ = (n : ℝ) * C := by simp

omit [MeasurableSpace X] in
theorem isBounded_range_birkhoffCoboundaryTransfer
    (T : X → X) {f : X → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x, |f x| ≤ C) (n : ℕ) :
    Bornology.IsBounded
      (range (birkhoffCoboundaryTransfer T f n)) := by
  let B : ℝ :=
    |(n : ℝ)⁻¹| *
      ∑ k ∈ Finset.range n, (k : ℝ) * C
  have hB_nonneg : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (abs_nonneg _)
      (Finset.sum_nonneg fun k _ ↦ mul_nonneg (Nat.cast_nonneg k) hC)
  have htransfer (x : X) :
      |birkhoffCoboundaryTransfer T f n x| ≤ B := by
    unfold birkhoffCoboundaryTransfer
    rw [abs_mul, abs_neg]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc
        |∑ k ∈ Finset.range n, birkhoffSum T f k x| ≤
            ∑ k ∈ Finset.range n,
              |birkhoffSum T f k x| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range n, (k : ℝ) * C := by
          gcongr with k hk
          exact abs_birkhoffSum_le T hf k x
  rw [Metric.isBounded_range_iff]
  refine ⟨2 * B, fun x y ↦ ?_⟩
  rw [Real.dist_eq]
  calc
    |birkhoffCoboundaryTransfer T f n x -
        birkhoffCoboundaryTransfer T f n y| ≤
        |birkhoffCoboundaryTransfer T f n x| +
          |birkhoffCoboundaryTransfer T f n y| :=
      abs_sub _ _
    _ ≤ B + B := add_le_add (htransfer x) (htransfer y)
    _ = 2 * B := by ring

/-- `L¹` convergence of Birkhoff averages to zero supplies the bounded
coboundary approximations needed by the Banach principle. -/
theorem isL1LimitOfBoundedCoboundaries_of_tendsto_integral_abs
    {T : X → X} {f : X → ℝ} {μ : Measure X}
    (hT : MeasurePreserving T μ μ)
    (hf_meas : Measurable f) (hf_int : Integrable f μ)
    {C : ℝ} (hC : 0 ≤ C) (hf_bound : ∀ x, |f x| ≤ C)
    (hL1 :
      Tendsto
        (fun n : ℕ ↦
          ∫ x, |birkhoffAverage ℝ T f (n + 1) x| ∂μ)
        atTop (𝓝 0)) :
    IsL1LimitOfBoundedCoboundaries T f μ := by
  intro ε hε
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        (∫ x, |birkhoffAverage ℝ T f (n + 1) x| ∂μ) < ε :=
    (tendsto_order.1 hL1).2 ε hε
  obtain ⟨m, hm⟩ := eventually_atTop.1 hevent
  let n : ℕ := m + 1
  let g : X → ℝ := birkhoffCoboundaryTransfer T f n
  refine ⟨g,
    measurable_birkhoffCoboundaryTransfer hT.measurable hf_meas n,
    integrable_birkhoffCoboundaryTransfer hT hf_int n,
    isBounded_range_birkhoffCoboundaryTransfer T hC hf_bound n, ?_⟩
  have hn : 0 < n := Nat.succ_pos m
  have havg := hm m (le_refl m)
  have hpoint (x : X) :
      f x - (g (T x) - g x) =
        birkhoffAverage ℝ T f n x := by
    dsimp only [g]
    rw [birkhoffCoboundaryTransfer_comp_sub T f hn x]
    ring
  simpa only [hpoint, n] using havg

/-- A bounded integrable observable whose Birkhoff averages converge
to zero in `L¹` converges to zero almost everywhere. -/
theorem ae_tendsto_birkhoffAverage_zero_of_tendsto_integral_abs
    {T : X → X} {f : X → ℝ} {μ : Measure X}
    [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ)
    (hf_meas : Measurable f) (hf_int : Integrable f μ)
    {C : ℝ} (hC : 0 ≤ C) (hf_bound : ∀ x, |f x| ≤ C)
    (hL1 :
      Tendsto
        (fun n : ℕ ↦
          ∫ x, |birkhoffAverage ℝ T f (n + 1) x| ∂μ)
        atTop (𝓝 0)) :
    ∀ᵐ x ∂μ,
      Tendsto (fun n ↦ birkhoffAverage ℝ T f n x)
        atTop (𝓝 0) := by
  exact
    ae_tendsto_birkhoffAverage_zero_of_L1Limit_boundedCoboundaries
      hT hf_meas hf_int
        (isL1LimitOfBoundedCoboundaries_of_tendsto_integral_abs
          hT hf_meas hf_int hC hf_bound hL1)

end HGAS.Dynamics
