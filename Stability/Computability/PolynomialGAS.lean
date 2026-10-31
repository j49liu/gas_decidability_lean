import HGAS.Arithmetic.NormalizedCorrectedAugmentedEffectiveFamily
import HGAS.Computability.ManyOneHard

/-!
# GAS for general rational polynomial vector fields

`PGASQ n d` asks whether a rational polynomial vector field of total degree
at most `d`, with the origin as an equilibrium, is globally asymptotically
stable. Degree bounds apply to the decoded coordinate polynomials: repeated
monomials may cancel, and zero coefficients do not contribute to degree.

The primitive-recursive reduction below retains homogeneous cubic inputs
and sends invalid inputs to the zero field. Consequently, general polynomial
GAS is many-one hard, undecidable, and has a non-r.e. complement in every
fixed dimension above the existing cubic threshold, for every degree bound
at least three. These conclusions do not assert recursive enumerability of
the general polynomial language.
-/

namespace Stability

open HGAS

/-- The exact bounded-degree rational polynomial GAS language on raw sparse
codes. The bound concerns decoded total degree, not the largest exponent
appearing in the input list. -/
def PGASQ (n d : ℕ) (F : PolynomialFieldCode n) : Prop :=
  (∀ i : Fin n, (PolynomialCode.decode (F i)).totalDegree ≤ d) ∧
    PolynomialFieldCode.realize F 0 = 0 ∧
    GloballyAsymptoticallyStable (PolynomialFieldCode.realize F) 0

/-- The polynomial language is unchanged by any recoding that preserves
the decoded coordinate polynomials, including cancellation and normalization. -/
theorem pgasQ_iff_of_decode_eq
    {n d : ℕ} {F G : PolynomialFieldCode n}
    (hdecode : ∀ i, PolynomialCode.decode (F i) = PolynomialCode.decode (G i)) :
    PGASQ n d F ↔ PGASQ n d G := by
  have hrealize : PolynomialFieldCode.realize F = PolynomialFieldCode.realize G := by
    funext x i
    simp only [PolynomialFieldCode.realize_apply, hdecode]
  simp only [PGASQ, hdecode, hrealize]

/-- Increasing a degree bound preserves membership. -/
theorem pgasQ_mono_degree
    {n d e : ℕ} {F : PolynomialFieldCode n}
    (hde : d ≤ e) (hF : PGASQ n d F) : PGASQ n e F :=
  ⟨fun i ↦ (hF.1 i).trans hde, hF.2⟩

/-- Every homogeneous GAS instance satisfies the general-polynomial
language at every larger degree bound. -/
theorem pgasQ_of_hgasQ
    {n k d : ℕ} {F : PolynomialFieldCode n}
    (hkd : k ≤ d) (hF : HGASQ n k F) : PGASQ n d F := by
  refine ⟨?_, hF.2.equilibrium, hF.2⟩
  intro i
  exact
    ((PolynomialFieldCode.homogeneous_eq_true_iff k F).mp hF.1 i).totalDegree_le.trans
      hkd

/-- Retain valid cubic inputs; send invalid inputs to the zero field.
The latter is a negative GAS instance in every positive dimension. -/
def cubicToPolynomialCode (n : ℕ) (F : PolynomialFieldCode n) :
    PolynomialFieldCode n :=
  bif PolynomialFieldCode.homogeneous 3 F then F
  else Veronese.zeroPolynomialFieldCode n

/-- The total reduction on raw codes is primitive recursive. -/
theorem cubicToPolynomialCode_primrec (n : ℕ) :
    Primrec (cubicToPolynomialCode n) := by
  apply Primrec.cond
  · exact (PolynomialFieldCode.homogeneous_primrec n).comp
      (Primrec.pair (Primrec.const 3) Primrec.id)
  · exact Primrec.id
  · exact Primrec.const (Veronese.zeroPolynomialFieldCode n)

@[simp]
theorem cubicToPolynomialCode_of_homogeneous
    {n : ℕ} {F : PolynomialFieldCode n}
    (hF : PolynomialFieldCode.homogeneous 3 F = true) :
    cubicToPolynomialCode n F = F := by
  simp [cubicToPolynomialCode, hF]

@[simp]
theorem cubicToPolynomialCode_of_not_homogeneous
    {n : ℕ} {F : PolynomialFieldCode n}
    (hF : PolynomialFieldCode.homogeneous 3 F ≠ true) :
    cubicToPolynomialCode n F = Veronese.zeroPolynomialFieldCode n := by
  simp [cubicToPolynomialCode, Bool.eq_false_of_not_eq_true hF]

/-- The fallback remains outside the general polynomial GAS language even
though it has degree zero and the origin is an equilibrium. -/
theorem zeroPolynomialFieldCode_not_pgasQ
    {n : ℕ} (hn : 0 < n) (d : ℕ) :
    ¬ PGASQ n d (Veronese.zeroPolynomialFieldCode n) := by
  intro hF
  have hGAS := hF.2.2
  rw [Veronese.realize_zeroPolynomialFieldCode] at hGAS
  exact Veronese.zeroVectorField_not_globallyAsymptoticallyStable
    (Veronese.sourceBasisVector ⟨0, hn⟩)
    (Veronese.sourceBasisVector_ne_zero ⟨0, hn⟩) hGAS

/-- Exact correctness of the reduction, including invalid source codes. -/
theorem cubicToPolynomialCode_correct
    {n d : ℕ} (hn : 0 < n) (hd : 3 ≤ d)
    (F : PolynomialFieldCode n) :
    HGASQ n 3 F ↔ PGASQ n d (cubicToPolynomialCode n F) := by
  by_cases hvalid : PolynomialFieldCode.homogeneous 3 F = true
  · rw [cubicToPolynomialCode_of_homogeneous hvalid]
    exact ⟨pgasQ_of_hgasQ hd, fun hF ↦ ⟨hvalid, hF.2.2⟩⟩
  · rw [cubicToPolynomialCode_of_not_homogeneous hvalid]
    exact ⟨fun hF ↦ (hvalid hF.1).elim,
      fun hF ↦ (zeroPolynomialFieldCode_not_pgasQ hn d hF).elim⟩

/-- Homogeneous cubic GAS many-one reduces to general polynomial GAS in
the same positive dimension, for every degree bound at least three. -/
theorem hgasQ_manyOneReducible_pgasQ
    {n d : ℕ} (hn : 0 < n) (hd : 3 ≤ d) :
    HGASQ n 3 ≤₀ PGASQ n d :=
  ⟨cubicToPolynomialCode n, (cubicToPolynomialCode_primrec n).to_comp,
    cubicToPolynomialCode_correct hn hd⟩

/-- The existing cubic threshold is positive because its multi-index set
contains a pure power of a coordinate of the positive-dimensional source. -/
theorem cofinalDimensionThreshold_pos :
    0 < NormalizedCorrectedAugmentedEffectiveFamily.cofinalDimensionThreshold := by
  let i : Fin NormalizedCorrectedAugmentedEffectiveFamily.fixedDimension :=
    ⟨0, NormalizedCorrectedAugmentedEffectiveFamily.fixedDimension_pos⟩
  let j : Fin NormalizedCorrectedAugmentedEffectiveFamily.cofinalDimensionThreshold :=
    Veronese.cubicLiftIndexEquiv _ _ (Veronese.pureMultiIndex i)
  exact Nat.zero_lt_of_lt j.isLt

/-- Every recursively enumerable predicate many-one reduces to general
polynomial GAS at every cofinal fixed dimension and degree bound `d ≥ 3`.
No parity condition is required for a degree bound. -/
theorem pgasQ_manyOneHard
    (n d : ℕ)
    (hn : NormalizedCorrectedAugmentedEffectiveFamily.cofinalDimensionThreshold ≤ n)
    (hd : 3 ≤ d) :
    ManyOneHard (PGASQ n d) := by
  exact ManyOneHard.of_manyOneReducible
    (NormalizedCorrectedAugmentedEffectiveFamily.cubic_sigmaOneComplete n hn).2
    (hgasQ_manyOneReducible_pgasQ (cofinalDimensionThreshold_pos.trans_le hn) hd)

/-- General polynomial GAS is undecidable at every cofinal fixed dimension
and every fixed degree bound at least three. -/
theorem pgasQ_not_computable
    (n d : ℕ)
    (hn : NormalizedCorrectedAugmentedEffectiveFamily.cofinalDimensionThreshold ≤ n)
    (hd : 3 ≤ d) :
    ¬ ComputablePred (PGASQ n d) :=
  (pgasQ_manyOneHard n d hn hd).not_computable

/-- The complement of general polynomial GAS is not recursively enumerable
at these same fixed dimensions and degree bounds. -/
theorem pgasQ_complement_not_re
    (n d : ℕ)
    (hn : NormalizedCorrectedAugmentedEffectiveFamily.cofinalDimensionThreshold ≤ n)
    (hd : 3 ≤ d) :
    ¬ REPred (fun F ↦ ¬ PGASQ n d F) :=
  (pgasQ_manyOneHard n d hn hd).complement_not_re

end Stability
