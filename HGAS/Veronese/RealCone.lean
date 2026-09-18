import HGAS.Veronese.ToricRelations
import Mathlib.Tactic

/-!
# Real points of the complete Veronese quadratic zero set

This module proves the converse deliberately left open in
`ToricRelations`: a nonzero real point satisfying every balanced
quadratic relation is a scalar multiple of a Veronese point.

The proof is elementary and constructive.  After finding a nonzero pure
coordinate `y_(k e_i)`, use the adjacent coordinates
`y_((k-1)e_i+e_j)` as affine ratios.  The balanced quadrics then move one
unit of exponent at a time toward the base vertex and force every
coordinate to be the corresponding monomial in those ratios.

The normalized statement follows from
`Q (νₖ x) = (∑ xᵢ²)^k`: after normalizing the reconstructed source
vector, the remaining scalar on `Q=1` is exactly `+1` or `-1`.
-/

namespace HGAS.Veronese

open scoped BigOperators

noncomputable section

variable {n k : ℕ}

/-! ## Elementary moves in the degree-`k` simplex -/

/-- The pure degree-`k` multiindex `k e_i`. -/
def pureMultiIndex (i : Fin n) : MultiIndex n k :=
  ⟨Pi.single i k, by
    simp [multiIndexFinset, Finset.mem_piAntidiag]⟩

@[simp]
theorem pureMultiIndex_apply_same (i : Fin n) :
    (pureMultiIndex (k := k) i).1 i = k := by
  simp [pureMultiIndex]

@[simp]
theorem pureMultiIndex_apply_of_ne
    {i j : Fin n} (hji : j ≠ i) :
    (pureMultiIndex (k := k) i).1 j = 0 := by
  simp [pureMultiIndex, hji]

/-- Move one unit of exponent from coordinate `j` to coordinate `i`. -/
def transferFunction
    (a : Fin n → ℕ) (i j : Fin n) : Fin n → ℕ :=
  Function.update (Function.update a j (a j - 1)) i (a i + 1)

theorem sum_transferFunction
    (a : Fin n → ℕ) (i j : Fin n)
    (hij : i ≠ j) (hj : 0 < a j) :
    ∑ l, transferFunction a i j l = ∑ l, a l := by
  classical
  unfold transferFunction
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have hji : j ∈ (Finset.univ : Finset (Fin n)) \ {i} := by
    simp [hij.symm]
  rw [Finset.sum_update_of_mem hji]
  have hiDecomp :=
    Finset.sum_eq_add_sum_diff_singleton
      (s := (Finset.univ : Finset (Fin n))) i a (by simp)
  have hjDecomp :=
    Finset.sum_eq_add_sum_diff_singleton
      (s := (Finset.univ : Finset (Fin n)) \ {i}) j a
      (by simp [hij.symm])
  rw [hiDecomp, hjDecomp]
  omega

/-- Bundled degree-`k` multiindex obtained by transferring one unit from
`j` to `i`. -/
def transferMultiIndex
    (a : MultiIndex n k) (i j : Fin n)
    (hij : i ≠ j) (hj : 0 < a.1 j) :
    MultiIndex n k :=
  ⟨transferFunction a.1 i j, by
    simp only [multiIndexFinset, Finset.mem_piAntidiag]
    constructor
    · rw [sum_transferFunction a.1 i j hij hj,
        multiIndex_degree a]
    · simp⟩

@[simp]
theorem transferMultiIndex_apply_same
    (a : MultiIndex n k) (i j : Fin n)
    (hij : i ≠ j) (hj : 0 < a.1 j) :
    (transferMultiIndex a i j hij hj).1 i = a.1 i + 1 := by
  simp [transferMultiIndex, transferFunction]

@[simp]
theorem transferMultiIndex_apply_source
    (a : MultiIndex n k) (i j : Fin n)
    (hij : i ≠ j) (hj : 0 < a.1 j) :
    (transferMultiIndex a i j hij hj).1 j = a.1 j - 1 := by
  simp [transferMultiIndex, transferFunction, hij.symm]

@[simp]
theorem transferMultiIndex_apply_of_ne
    (a : MultiIndex n k) (i j l : Fin n)
    (hij : i ≠ j) (hj : 0 < a.1 j)
    (hli : l ≠ i) (hlj : l ≠ j) :
    (transferMultiIndex a i j hij hj).1 l = a.1 l := by
  simp [transferMultiIndex, transferFunction, hli, hlj]

/-! ## A nonzero toric point has a nonzero pure coordinate -/

/-- The balanced relation centered at `a`, obtained by moving one unit
from `j` to `i` in one factor and one unit back in the other. -/
def midpointTransferRelation
    (a : MultiIndex n k) (i j : Fin n)
    (hij : i ≠ j) (hi : 0 < a.1 i) (hj : 0 < a.1 j) :
    ToricRelationIndex n k where
  alpha := a
  beta := a
  gamma := transferMultiIndex a i j hij hj
  delta := transferMultiIndex a j i hij.symm hi
  balanced := by
    intro l
    by_cases hli : l = i
    · subst l
      simp
      omega
    by_cases hlj : l = j
    · subst l
      simp
      omega
    simp [transferMultiIndex_apply_of_ne, hli, hlj]

/-- Every coordinate of a degree-`k` multiindex is at most `k`. -/
theorem multiIndex_apply_le_degree
    (a : MultiIndex n k) (i : Fin n) :
    a.1 i ≤ k := by
  calc
    a.1 i ≤ ∑ j, a.1 j :=
      Finset.single_le_sum
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    _ = k := multiIndex_degree a

/-- If the `i`-th entry already equals the full degree, the multiindex is
the pure vertex `k e_i`. -/
theorem multiIndex_eq_pure_of_apply_eq_degree
    (a : MultiIndex n k) (i : Fin n)
    (hi : a.1 i = k) :
    a = pureMultiIndex i := by
  apply Subtype.ext
  funext j
  by_cases hji : j = i
  · subst j
    simp [hi]
  · have hdecomp :=
      Finset.sum_erase_add
        (Finset.univ : Finset (Fin n)) a.1 (Finset.mem_univ i)
    rw [multiIndex_degree a, hi] at hdecomp
    have hsum :
        ∑ l ∈ (Finset.univ : Finset (Fin n)).erase i, a.1 l = 0 := by
      omega
    have hjmem :
        j ∈ (Finset.univ : Finset (Fin n)).erase i := by
      simp [hji]
    have hjzero :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun l _ ↦ Nat.zero_le (a.1 l))).mp hsum j hjmem
    rw [hjzero]
    simp [pureMultiIndex, hji]

/-- A nonzero real point satisfying all balanced quadrics has a nonzero
pure coordinate.  The proof maximizes one exponent among all nonzero
coordinates; a midpoint quadric would otherwise produce a nonzero
coordinate with a larger exponent. -/
theorem exists_pureMultiIndex_ne_zero
    {y : MultiIndex n k → ℝ}
    (hk : 1 ≤ k)
    (hy : y ∈ toricZeroSet (R := ℝ) n k)
    (hy0 : y ≠ 0) :
    ∃ i : Fin n, y (pureMultiIndex i) ≠ 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hy0
  have ha0 : y a ≠ 0 := by
    simpa using ha
  have hsumne : (∑ i, a.1 i) ≠ 0 := by
    rw [multiIndex_degree a]
    omega
  obtain ⟨i, _, hi0⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hsumne
  have hi : 0 < a.1 i := Nat.pos_of_ne_zero hi0
  let S : Finset (MultiIndex n k) :=
    Finset.univ.filter (fun b ↦ y b ≠ 0)
  have haS : a ∈ S := by
    simp [S, ha0]
  obtain ⟨b, hbS, hmax⟩ :=
    Finset.exists_max_image S (fun b ↦ b.1 i) ⟨a, haS⟩
  have hb0 : y b ≠ 0 := by
    simpa [S] using hbS
  have hbi : 0 < b.1 i :=
    lt_of_lt_of_le hi (hmax a haS)
  have hbik : b.1 i = k := by
    apply le_antisymm (multiIndex_apply_le_degree b i)
    by_contra hnot
    have hbilt : b.1 i < k := lt_of_not_ge hnot
    have hdecomp :=
      Finset.sum_erase_add
        (Finset.univ : Finset (Fin n)) b.1 (Finset.mem_univ i)
    rw [multiIndex_degree b] at hdecomp
    have herase :
        (∑ l ∈ (Finset.univ : Finset (Fin n)).erase i,
          b.1 l) ≠ 0 := by
      omega
    obtain ⟨j, hjmem, hj0⟩ :=
      Finset.exists_ne_zero_of_sum_ne_zero herase
    have hji : j ≠ i := Finset.ne_of_mem_erase hjmem
    have hj : 0 < b.1 j := Nat.pos_of_ne_zero hj0
    let bp := transferMultiIndex b i j hji.symm hj
    let bm := transferMultiIndex b j i hji hbi
    have hrelation :=
      hy (midpointTransferRelation b i j hji.symm hbi hj)
    have heq :
        y b * y b = y bp * y bm := by
      simpa only [toricRelation, midpointTransferRelation] using
        sub_eq_zero.mp hrelation
    have hprod : y bp * y bm ≠ 0 := by
      rw [← heq]
      exact mul_ne_zero hb0 hb0
    have hbp0 : y bp ≠ 0 := (mul_ne_zero_iff.mp hprod).1
    have hbpS : bp ∈ S := by
      simp [S, hbp0]
    have hle := hmax bp hbpS
    have hbpi : bp.1 i = b.1 i + 1 := by
      exact transferMultiIndex_apply_same b i j hji.symm hj
    rw [hbpi] at hle
    omega
  refine ⟨i, ?_⟩
  rw [← multiIndex_eq_pure_of_apply_eq_degree b i hbik]
  exact hb0

/-! ## Affine reconstruction from a pure coordinate -/

/-- The adjacent multiindex `(k-1)e_i + e_j`.  When `j=i` this is the
pure vertex itself. -/
def edgeMultiIndex
    (hk : 1 ≤ k) (i j : Fin n) : MultiIndex n k :=
  if hji : j = i then pureMultiIndex i
  else
    transferMultiIndex (pureMultiIndex i) j i hji
      (by simpa using hk)

@[simp]
theorem edgeMultiIndex_same
    (hk : 1 ≤ k) (i : Fin n) :
    edgeMultiIndex hk i i = pureMultiIndex i := by
  simp [edgeMultiIndex]

theorem edgeMultiIndex_of_ne
    (hk : 1 ≤ k) (i j : Fin n) (hji : j ≠ i) :
    edgeMultiIndex hk i j =
      transferMultiIndex (pureMultiIndex i) j i hji
        (by simpa using hk) := by
  simp [edgeMultiIndex, hji]

/-- The affine source coordinates read from a toric point after choosing
a nonzero pure coordinate. -/
def affineSource
    (y : MultiIndex n k → ℝ) (hk : 1 ≤ k)
    (i : Fin n) : Fin n → ℝ :=
  fun j ↦ y (edgeMultiIndex hk i j) / y (pureMultiIndex i)

@[simp]
theorem affineSource_apply_base
    (y : MultiIndex n k → ℝ) (hk : 1 ≤ k)
    (i : Fin n) (hpure : y (pureMultiIndex i) ≠ 0) :
    affineSource y hk i i = 1 := by
  simp [affineSource, hpure]

/-- Moving one unit from `j` toward the base `i` gives the balanced
identity

`a + k e_i = transfer(a,j→i) + ((k-1)e_i+e_j)`.
-/
def baseTransferRelation
    (a : MultiIndex n k) (hk : 1 ≤ k)
    (i j : Fin n) (hji : j ≠ i) (hj : 0 < a.1 j) :
    ToricRelationIndex n k where
  alpha := a
  beta := pureMultiIndex i
  gamma := transferMultiIndex a i j hji.symm hj
  delta := edgeMultiIndex hk i j
  balanced := by
    intro l
    rw [edgeMultiIndex_of_ne hk i j hji]
    by_cases hli : l = i
    · subst l
      simp
      omega
    by_cases hlj : l = j
    · subst l
      simp [hji]
      omega
    simp [transferMultiIndex_apply_of_ne, hli, hlj]

/-- Pointwise exponent bookkeeping for a one-unit transfer. -/
theorem transferMultiIndex_add_single
    (a : MultiIndex n k) (i j : Fin n)
    (hij : i ≠ j) (hj : 0 < a.1 j) (l : Fin n) :
    (transferMultiIndex a i j hij hj).1 l +
        (if l = j then 1 else 0) =
      a.1 l + (if l = i then 1 else 0) := by
  by_cases hli : l = i
  · subst l
    simp [hij]
  by_cases hlj : l = j
  · subst l
    simp [hij.symm]
    omega
  simp [transferMultiIndex_apply_of_ne, hli, hlj]

/-- A monomial changes predictably under a one-unit exponent transfer:

`x^(transfer(a,j→i)) x_j = x^a x_i`.
-/
theorem monomial_transfer_mul
    (x : Fin n → ℝ) (a : MultiIndex n k)
    (i j : Fin n) (hij : i ≠ j) (hj : 0 < a.1 j) :
    monomial x (transferMultiIndex a i j hij hj) * x j =
      monomial x a * x i := by
  classical
  have hjprod :
      (∏ l : Fin n, x l ^ (if l = j then 1 else 0)) = x j := by
    simp
  have hiprod :
      (∏ l : Fin n, x l ^ (if l = i then 1 else 0)) = x i := by
    simp
  rw [← hjprod, ← hiprod]
  simp only [monomial, ← Finset.prod_mul_distrib, ← pow_add]
  apply Finset.prod_congr rfl
  intro l _
  rw [transferMultiIndex_add_single a i j hij hj l]

/-- If the base exponent is not yet `k`, some non-base exponent is
positive and can be transferred toward the base. -/
theorem exists_ne_base_apply_pos
    (a : MultiIndex n k) (i : Fin n)
    (hi : a.1 i < k) :
    ∃ j : Fin n, j ≠ i ∧ 0 < a.1 j := by
  have hdecomp :=
    Finset.sum_erase_add
      (Finset.univ : Finset (Fin n)) a.1 (Finset.mem_univ i)
  rw [multiIndex_degree a] at hdecomp
  have herase :
      (∑ l ∈ (Finset.univ : Finset (Fin n)).erase i,
        a.1 l) ≠ 0 := by
    omega
  obtain ⟨j, hjmem, hj0⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero herase
  exact
    ⟨j, Finset.ne_of_mem_erase hjmem,
      Nat.pos_of_ne_zero hj0⟩

/-- Monomial of a pure multiindex. -/
@[simp]
theorem monomial_pureMultiIndex
    (x : Fin n → ℝ) (i : Fin n) :
    monomial x (pureMultiIndex (k := k) i) = x i ^ k := by
  classical
  simp [monomial, pureMultiIndex, Pi.single_apply]

/-! ## Reconstruction theorem -/

/-- Once a nonzero pure coordinate has been chosen, every toric
coordinate is forced to be the corresponding affine monomial. -/
theorem coordinate_eq_pure_mul_monomial_affineSource
    {y : MultiIndex n k → ℝ}
    (hk : 1 ≤ k)
    (hy : y ∈ toricZeroSet (R := ℝ) n k)
    (i : Fin n) (hpure : y (pureMultiIndex i) ≠ 0)
    (a : MultiIndex n k) :
    y a =
      y (pureMultiIndex i) *
        monomial (affineSource y hk i) a := by
  generalize hm : k - a.1 i = m
  induction m using Nat.strong_induction_on generalizing a with
  | h m ih =>
      by_cases hai : a.1 i = k
      · have ha : a = pureMultiIndex i :=
          multiIndex_eq_pure_of_apply_eq_degree a i hai
        subst a
        rw [monomial_pureMultiIndex,
          affineSource_apply_base y hk i hpure,
          one_pow, mul_one]
      · have hailt : a.1 i < k :=
          lt_of_le_of_ne (multiIndex_apply_le_degree a i) hai
        obtain ⟨j, hji, hj⟩ :=
          exists_ne_base_apply_pos a i hailt
        let ap :=
          transferMultiIndex a i j hji.symm hj
        have hapi : ap.1 i = a.1 i + 1 := by
          exact transferMultiIndex_apply_same
            a i j hji.symm hj
        have hmeasure : k - ap.1 i < m := by
          rw [hapi, ← hm]
          omega
        have hIH :
            y ap =
              y (pureMultiIndex i) *
                monomial (affineSource y hk i) ap :=
          ih (k - ap.1 i) hmeasure ap rfl
        have hrelation :=
          hy (baseTransferRelation a hk i j hji hj)
        have heq :
            y a * y (pureMultiIndex i) =
              y ap * y (edgeMultiIndex hk i j) := by
          simpa only [toricRelation, baseTransferRelation] using
            sub_eq_zero.mp hrelation
        have hedge :
            y (edgeMultiIndex hk i j) =
              y (pureMultiIndex i) *
                affineSource y hk i j := by
          exact
            (mul_div_cancel₀
              (y (edgeMultiIndex hk i j)) hpure).symm
        have hmon :
            monomial (affineSource y hk i) ap *
                affineSource y hk i j =
              monomial (affineSource y hk i) a := by
          have hmoving :=
            monomial_transfer_mul
              (affineSource y hk i) a i j hji.symm hj
          rw [affineSource_apply_base y hk i hpure,
            mul_one] at hmoving
          exact hmoving
        apply mul_right_cancel₀ hpure
        calc
          y a * y (pureMultiIndex i) =
              y ap * y (edgeMultiIndex hk i j) := heq
          _ =
              (y (pureMultiIndex i) *
                  monomial (affineSource y hk i) ap) *
                (y (pureMultiIndex i) *
                  affineSource y hk i j) := by
                    rw [hIH, hedge]
          _ =
              (y (pureMultiIndex i) *
                  monomial (affineSource y hk i) a) *
                y (pureMultiIndex i) := by
                    rw [← hmon]
                    ring

/-! ## The real cone and its normalized sheets -/

/-- Constructive affine-cone parametrization.  The scalar is the chosen
pure coordinate and the corresponding source coordinate is `1`. -/
theorem exists_smul_veronese_of_mem_toricZeroSet
    {y : MultiIndex n k → ℝ}
    (hk : 1 ≤ k)
    (hy : y ∈ toricZeroSet (R := ℝ) n k)
    (hy0 : y ≠ 0) :
    ∃ (t : ℝ) (x : Fin n → ℝ),
      t ≠ 0 ∧ x ≠ 0 ∧
        y = t • veroneseMap (k := k) x := by
  obtain ⟨i, hpure⟩ :=
    exists_pureMultiIndex_ne_zero hk hy hy0
  refine
    ⟨y (pureMultiIndex i), affineSource y hk i,
      hpure, ?_, ?_⟩
  · apply Function.ne_iff.mpr
    refine ⟨i, ?_⟩
    simp [affineSource_apply_base y hk i hpure]
  · funext a
    change y a =
      y (pureMultiIndex i) *
        monomial (affineSource y hk i) a
    exact coordinate_eq_pure_mul_monomial_affineSource
      hk hy i hpure a

/-- Euclidean squared radius of a source vector. -/
def sourceRadiusSq (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i ^ 2

/-- Euclidean radius of a source vector. -/
noncomputable def sourceRadius (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (sourceRadiusSq x)

/-- Normalize a nonzero source vector to the Euclidean unit sphere. -/
noncomputable def normalizeSource (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ x i / sourceRadius x

theorem sourceRadiusSq_nonneg (x : Fin n → ℝ) :
    0 ≤ sourceRadiusSq x := by
  exact Finset.sum_nonneg fun i _ ↦ sq_nonneg (x i)

theorem sourceRadiusSq_pos_of_ne_zero
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    0 < sourceRadiusSq x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hi0 : x i ≠ 0 := by
    simpa using hi
  exact Finset.sum_pos'
    (fun j _ ↦ sq_nonneg (x j))
    ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi0⟩

theorem sourceRadius_pos_of_ne_zero
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    0 < sourceRadius x := by
  exact Real.sqrt_pos.2 (sourceRadiusSq_pos_of_ne_zero hx)

theorem sourceRadius_sq
    (x : Fin n → ℝ) :
    sourceRadius x ^ 2 = sourceRadiusSq x := by
  exact Real.sq_sqrt (sourceRadiusSq_nonneg x)

/-- The normalized source vector has Euclidean squared norm one. -/
theorem sourceRadiusSq_normalizeSource
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    sourceRadiusSq (normalizeSource x) = 1 := by
  have hr : sourceRadius x ≠ 0 :=
    ne_of_gt (sourceRadius_pos_of_ne_zero hx)
  simp only [sourceRadiusSq, normalizeSource, div_pow]
  rw [← Finset.sum_div]
  rw [sourceRadius_sq]
  exact div_self (ne_of_gt (sourceRadiusSq_pos_of_ne_zero hx))

/-- Recover a nonzero vector from its radius and normalization. -/
theorem sourceRadius_smul_normalizeSource
    {x : Fin n → ℝ} (hx : x ≠ 0) :
    sourceRadius x • normalizeSource x = x := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, normalizeSource]
  exact mul_div_cancel₀ (x i)
    (ne_of_gt (sourceRadius_pos_of_ne_zero hx))

/-- Real-cone parametrization with a unit source vector.  This is the
set-theoretic content of equation (15.7). -/
theorem exists_unit_smul_veronese_of_mem_toricZeroSet
    {y : MultiIndex n k → ℝ}
    (hk : 1 ≤ k)
    (hy : y ∈ toricZeroSet (R := ℝ) n k)
    (hy0 : y ≠ 0) :
    ∃ (t : ℝ) (u : Fin n → ℝ),
      t ≠ 0 ∧ sourceRadiusSq u = 1 ∧
        y = t • veroneseMap (k := k) u := by
  obtain ⟨s, x, hs, hx, hyx⟩ :=
    exists_smul_veronese_of_mem_toricZeroSet hk hy hy0
  let r := sourceRadius x
  let u := normalizeSource x
  have hr : r ≠ 0 :=
    ne_of_gt (sourceRadius_pos_of_ne_zero hx)
  have hxu : r • u = x := by
    exact sourceRadius_smul_normalizeSource hx
  refine
    ⟨s * r ^ k, u, mul_ne_zero hs (pow_ne_zero k hr),
      sourceRadiusSq_normalizeSource hx, ?_⟩
  calc
    y = s • veroneseMap (k := k) x := hyx
    _ = s • veroneseMap (k := k) (r • u) := by rw [hxu]
    _ = s • (r ^ k • veroneseMap (k := k) u) := by
      rw [veroneseMap_smul]
    _ = (s * r ^ k) • veroneseMap (k := k) u := by
      rw [smul_smul]

/-- Complete normalized sheet characterization.  Every real common zero
on `Q=1` is a positive or negative unit Veronese point, and conversely.

This theorem is valid uniformly in the parity of `k`; parity is needed
only to identify or separate the two parametrized sheets. -/
theorem mem_toricSphereZeroSet_iff_exists_signed_veronese
    (hk : 1 ≤ k) (y : MultiIndex n k → ℝ) :
    y ∈ toricSphereZeroSet n k ↔
      ∃ u : Fin n → ℝ,
        sourceRadiusSq u = 1 ∧
          (y = veroneseMap (k := k) u ∨
            y = -veroneseMap (k := k) u) := by
  constructor
  · rintro ⟨hy, hQ⟩
    have hy0 : y ≠ 0 := by
      intro hyzero
      subst y
      simp [Q] at hQ
    obtain ⟨t, u, ht, hu, hyu⟩ :=
      exists_unit_smul_veronese_of_mem_toricZeroSet
        hk hy hy0
    have htSq : t ^ 2 = 1 := by
      calc
        t ^ 2 =
            Q (t • veroneseMap (k := k) u) := by
              rw [Q_smul, Q_veroneseMap,
                show (∑ i, u i ^ 2) = 1 by
                  simpa [sourceRadiusSq] using hu]
              simp
        _ = Q y := by rw [hyu]
        _ = 1 := hQ
    refine ⟨u, hu, ?_⟩
    rcases sq_eq_one_iff.mp htSq with htOne | htNeg
    · left
      simpa [htOne] using hyu
    · right
      simpa [htNeg] using hyu
  · rintro ⟨u, hu, hyu | hyu⟩
    · subst y
      exact veronese_mem_toricSphereZeroSet_of_unit u hu
    · subst y
      exact neg_veronese_mem_toricSphereZeroSet_of_unit u hu

end

end HGAS.Veronese
