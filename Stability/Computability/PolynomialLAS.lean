import Stability.Computability.PolynomialGAS
import Stability.Dynamics.LocalAsymptoticStability
import HGAS.Algebra.HomogeneousEvaluation

/-!
# LAS for general rational polynomial vector fields

`PLASQ n d` is local asymptotic stability of the origin for rational
polynomial vector fields of decoded total degree at most `d`. Its local
semantics include existence of forward trajectories, so finite-time
blow-up cannot make the attraction condition vacuous.

Local and global asymptotic stability coincide for positive-degree
homogeneous fields. The total cubic compiler from `PolynomialGAS` therefore
also reduces homogeneous cubic GAS to general polynomial LAS. This gives
many-one hardness, undecidability, and a non-r.e. complement at every
cofinal fixed dimension and every degree bound at least three. We do not
assert that general polynomial LAS is recursively enumerable.
-/

namespace Stability

open HGAS

/-- The exact bounded-degree rational polynomial LAS language on raw sparse
codes. Degree is measured after decoding and cancellation. -/
def PLASQ (n d : ℕ) (F : PolynomialFieldCode n) : Prop :=
  (∀ i : Fin n, (PolynomialCode.decode (F i)).totalDegree ≤ d) ∧
    PolynomialFieldCode.realize F 0 = 0 ∧
    LocallyAsymptoticallyStable (PolynomialFieldCode.realize F) 0

/-- LAS membership depends on decoded coordinate polynomials, not their
possibly redundant sparse representations. -/
theorem plasQ_iff_of_decode_eq
    {n d : ℕ} {F G : PolynomialFieldCode n}
    (hdecode : ∀ i, PolynomialCode.decode (F i) = PolynomialCode.decode (G i)) :
    PLASQ n d F ↔ PLASQ n d G := by
  have hrealize : PolynomialFieldCode.realize F = PolynomialFieldCode.realize G := by
    funext x i
    simp only [PolynomialFieldCode.realize_apply, hdecode]
  simp only [PLASQ, hdecode, hrealize]

/-- Increasing the degree bound preserves membership. -/
theorem plasQ_mono_degree
    {n d e : ℕ} {F : PolynomialFieldCode n}
    (hde : d ≤ e) (hF : PLASQ n d F) : PLASQ n e F :=
  ⟨fun i ↦ (hF.1 i).trans hde, hF.2⟩

/-- General polynomial GAS implies general polynomial LAS at the same
degree bound. -/
theorem plasQ_of_pgasQ
    {n d : ℕ} {F : PolynomialFieldCode n}
    (hF : PGASQ n d F) : PLASQ n d F :=
  ⟨hF.1, hF.2.1,
    locallyAsymptoticallyStable_of_globallyAsymptoticallyStable hF.2.2⟩

/-- Positive-degree homogeneity upgrades local asymptotic stability of a
coded polynomial field to global asymptotic stability, and conversely. -/
theorem polynomialFieldCode_las_iff_gas
    {n k : ℕ} (F : PolynomialFieldCode n)
    (hF : PolynomialFieldCode.homogeneous (k + 1) F = true) :
    LocallyAsymptoticallyStable (PolynomialFieldCode.realize F) 0 ↔
      GloballyAsymptoticallyStable (PolynomialFieldCode.realize F) 0 := by
  apply locallyAsymptoticallyStable_iff_globallyAsymptoticallyStable
    (PolynomialFieldCode.realize F) k
  intro c x
  exact evalPolynomialField_smul (PolynomialFieldCode.decode F)
    ((PolynomialFieldCode.homogeneous_eq_true_iff (k + 1) F).mp hF) c x

/-- The bounded-degree LAS and GAS languages agree on every positive-degree
homogeneous field, without changing the target degree bound. -/
theorem plasQ_iff_pgasQ_of_homogeneous
    {n k d : ℕ} {F : PolynomialFieldCode n}
    (hF : PolynomialFieldCode.homogeneous (k + 1) F = true) :
    PLASQ n d F ↔ PGASQ n d F := by
  simp only [PLASQ, PGASQ, polynomialFieldCode_las_iff_gas F hF]

/-- In positive dimension, the zero fallback is not locally asymptotically
stable. Its homogeneity converts hypothetical LAS to the excluded GAS case. -/
theorem zeroPolynomialFieldCode_not_plasQ
    {n : ℕ} (hn : 0 < n) (d : ℕ) :
    ¬ PLASQ n d (Veronese.zeroPolynomialFieldCode n) := by
  rw [plasQ_iff_pgasQ_of_homogeneous (k := 2)
    (Veronese.zeroPolynomialFieldCode_homogeneous n 3)]
  exact zeroPolynomialFieldCode_not_pgasQ hn d

/-- The existing total cubic compiler is also a correct reduction to LAS,
including its invalid-code branch. -/
theorem cubicToPolynomialCode_correct_las
    {n d : ℕ} (hn : 0 < n) (hd : 3 ≤ d)
    (F : PolynomialFieldCode n) :
    HGASQ n 3 F ↔ PLASQ n d (cubicToPolynomialCode n F) := by
  by_cases hvalid : PolynomialFieldCode.homogeneous 3 F = true
  · rw [cubicToPolynomialCode_of_homogeneous hvalid,
      plasQ_iff_pgasQ_of_homogeneous (k := 2) hvalid]
    exact ⟨pgasQ_of_hgasQ hd, fun hF ↦ ⟨hvalid, hF.2.2⟩⟩
  · rw [cubicToPolynomialCode_of_not_homogeneous hvalid]
    exact ⟨fun hF ↦ (hvalid hF.1).elim,
      fun hF ↦ (zeroPolynomialFieldCode_not_plasQ hn d hF).elim⟩

/-- Homogeneous cubic GAS many-one reduces to polynomial LAS in the same
positive dimension, for every degree bound at least three. -/
theorem hgasQ_manyOneReducible_plasQ
    {n d : ℕ} (hn : 0 < n) (hd : 3 ≤ d) :
    HGASQ n 3 ≤₀ PLASQ n d :=
  ⟨cubicToPolynomialCode n, (cubicToPolynomialCode_primrec n).to_comp,
    cubicToPolynomialCode_correct_las hn hd⟩

/-- General polynomial LAS is many-one hard for every cofinal fixed
dimension and every fixed degree bound at least three. -/
theorem plasQ_manyOneHard
    (n d : ℕ)
    (hn : NormalizedCorrectedAugmentedEffectiveFamily.cofinalDimensionThreshold ≤ n)
    (hd : 3 ≤ d) :
    ManyOneHard (PLASQ n d) := by
  exact ManyOneHard.of_manyOneReducible
    (NormalizedCorrectedAugmentedEffectiveFamily.cubic_sigmaOneComplete n hn).2
    (hgasQ_manyOneReducible_plasQ (cofinalDimensionThreshold_pos.trans_le hn) hd)

/-- General polynomial LAS is undecidable at these fixed dimensions and
degree bounds. -/
theorem plasQ_not_computable
    (n d : ℕ)
    (hn : NormalizedCorrectedAugmentedEffectiveFamily.cofinalDimensionThreshold ≤ n)
    (hd : 3 ≤ d) :
    ¬ ComputablePred (PLASQ n d) :=
  (plasQ_manyOneHard n d hn hd).not_computable

/-- The complement of general polynomial LAS is not recursively enumerable
at these same fixed dimensions and degree bounds. -/
theorem plasQ_complement_not_re
    (n d : ℕ)
    (hn : NormalizedCorrectedAugmentedEffectiveFamily.cofinalDimensionThreshold ≤ n)
    (hd : 3 ≤ d) :
    ¬ REPred (fun F ↦ ¬ PLASQ n d F) :=
  (plasQ_manyOneHard n d hn hd).complement_not_re

end Stability
