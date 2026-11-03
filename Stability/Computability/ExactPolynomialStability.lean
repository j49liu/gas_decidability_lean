import Stability.Computability.ExactDegreePolynomialCode
import Stability.Dynamics.DegreeCarrier
import Stability.Dynamics.ProductStability

/-!
# Undecidability at each prescribed polynomial degree

Appending the independent planar system
`w' = -w^3`, `z' = -z^3 + w^d` gives a field of exact decoded degree `d`
whenever the source has degree at most three and `d ≥ 3`. This planar system
is globally asymptotically stable, so the product preserves and reflects
both global and local asymptotic stability.

The total reduction first applies the existing cubic-input check and then
appends these two coordinates. As in the earlier bounded-degree reduction,
invalid source codes are replaced by the zero field. The manuscript uses
the identity field on this branch instead; both are negative instances of
GAS and LAS in positive dimension. The appended planar coordinates ensure
exact target degree even on this branch.

Consequently, `PGASExactQ n d` and `PLASExactQ n d` are many-one hard,
undecidable, and have non-r.e. complements for every sufficiently large
fixed dimension and every fixed degree `d ≥ 3`, without a parity restriction.
These conclusions do not assert recursive enumerability of either language.
The earlier bounded-degree languages and their theorems remain unchanged.
-/

namespace Stability

open HGAS

namespace ExactDegreeCode

/-- Appending the stable planar factor preserves and reflects GAS. -/
theorem appendDegreeCarrierCode_gas_iff
    (n d : ℕ) (F : PolynomialFieldCode n) (hd : 3 ≤ d) :
    GloballyAsymptoticallyStable
        (PolynomialFieldCode.realize (appendDegreeCarrierCode n d F)) 0 ↔
      GloballyAsymptoticallyStable (PolynomialFieldCode.realize F) 0 := by
  rw [realize_appendDegreeCarrierCode,
    globallyAsymptoticallyStable_conjugateField_iff]
  change GloballyAsymptoticallyStable
      (productField (PolynomialFieldCode.realize F) (degreeCarrier d)) (0, 0) ↔ _
  have hcarrier := degreeCarrier_gas d hd
  exact ⟨fun h ↦ h.fst_of_product hcarrier.equilibrium, fun h ↦ h.prod hcarrier⟩

/-- Appending the stable planar factor preserves and reflects LAS. -/
theorem appendDegreeCarrierCode_las_iff
    (n d : ℕ) (F : PolynomialFieldCode n) (hd : 3 ≤ d) :
    LocallyAsymptoticallyStable
        (PolynomialFieldCode.realize (appendDegreeCarrierCode n d F)) 0 ↔
      LocallyAsymptoticallyStable (PolynomialFieldCode.realize F) 0 := by
  rw [realize_appendDegreeCarrierCode,
    locallyAsymptoticallyStable_conjugateField_iff]
  change LocallyAsymptoticallyStable
      (productField (PolynomialFieldCode.realize F) (degreeCarrier d)) (0, 0) ↔ _
  rw [locallyAsymptoticallyStable_productField_iff]
  exact and_iff_left
    (locallyAsymptoticallyStable_of_globallyAsymptoticallyStable (degreeCarrier_gas d hd))

/-- On source fields of degree at most three, the appended code belongs to
the exact-degree GAS language exactly when the source belongs to the
bounded-degree cubic GAS language. -/
theorem appendDegreeCarrierCode_pgasExactQ_iff
    (n d : ℕ) (F : PolynomialFieldCode n) (hd : 3 ≤ d)
    (hF : ∀ i, (PolynomialCode.decode (F i)).totalDegree ≤ 3) :
    PGASExactQ (n + 2) d (appendDegreeCarrierCode n d F) ↔ PGASQ n 3 F := by
  constructor
  · intro h
    have hgas := (appendDegreeCarrierCode_gas_iff n d F hd).mp h.2.2
    exact ⟨hF, hgas.equilibrium, hgas⟩
  · intro h
    have hgas := (appendDegreeCarrierCode_gas_iff n d F hd).mpr h.2.2
    exact ⟨appendDegreeCarrierCode_exactDegree n d F hd hF, hgas.equilibrium, hgas⟩

/-- The same exact-degree construction preserves the bounded-degree cubic
LAS language. No homogeneity assumption is needed for this product step. -/
theorem appendDegreeCarrierCode_plasExactQ_iff
    (n d : ℕ) (F : PolynomialFieldCode n) (hd : 3 ≤ d)
    (hF : ∀ i, (PolynomialCode.decode (F i)).totalDegree ≤ 3) :
    PLASExactQ (n + 2) d (appendDegreeCarrierCode n d F) ↔ PLASQ n 3 F := by
  constructor
  · intro h
    have hlas := (appendDegreeCarrierCode_las_iff n d F hd).mp h.2.2
    exact ⟨hF, hlas.equilibrium, hlas⟩
  · intro h
    have hlas := (appendDegreeCarrierCode_las_iff n d F hd).mpr h.2.2
    exact ⟨appendDegreeCarrierCode_exactDegree n d F hd hF, hlas.equilibrium, hlas⟩

end ExactDegreeCode

/-- The existing input check always returns a homogeneous cubic code,
including its zero-field branch. -/
theorem cubicToPolynomialCode_homogeneous (n : ℕ) (F : PolynomialFieldCode n) :
    PolynomialFieldCode.homogeneous 3 (cubicToPolynomialCode n F) = true := by
  by_cases hF : PolynomialFieldCode.homogeneous 3 F = true
  · simpa only [cubicToPolynomialCode_of_homogeneous hF] using hF
  · simpa only [cubicToPolynomialCode_of_not_homogeneous hF] using
      Veronese.zeroPolynomialFieldCode_homogeneous n 3

private theorem cubicToPolynomialCode_degree_le (n : ℕ) (F : PolynomialFieldCode n) :
    ∀ i, (PolynomialCode.decode (cubicToPolynomialCode n F i)).totalDegree ≤ 3 :=
  fun i ↦ ((PolynomialFieldCode.homogeneous_eq_true_iff 3
    (cubicToPolynomialCode n F)).mp (cubicToPolynomialCode_homogeneous n F) i).totalDegree_le

/-- Check the cubic source code and append the two planar coordinates.
The result has exact degree `d` even when the source check fails. -/
def cubicToExactPolynomialCode (n d : ℕ) (F : PolynomialFieldCode n) :
    PolynomialFieldCode (n + 2) :=
  ExactDegreeCode.appendDegreeCarrierCode n d (cubicToPolynomialCode n F)

/-- The complete transformation of raw sparse codes is primitive recursive. -/
theorem cubicToExactPolynomialCode_primrec (n d : ℕ) :
    Primrec (cubicToExactPolynomialCode n d) :=
  (ExactDegreeCode.appendDegreeCarrierCode_primrec n d).comp
    (cubicToPolynomialCode_primrec n)

/-- Every output of the reduction has the prescribed decoded degree. -/
theorem cubicToExactPolynomialCode_exactDegree
    (n d : ℕ) (F : PolynomialFieldCode n) (hd : 3 ≤ d) :
    PolynomialFieldExactDegree (n + 2) d (cubicToExactPolynomialCode n d F) :=
  ExactDegreeCode.appendDegreeCarrierCode_exactDegree n d (cubicToPolynomialCode n F)
    hd (cubicToPolynomialCode_degree_le n F)

/-- Correctness on every raw source code, including the zero fallback. -/
theorem cubicToExactPolynomialCode_correct
    {n d : ℕ} (hn : 0 < n) (hd : 3 ≤ d) (F : PolynomialFieldCode n) :
    HGASQ n 3 F ↔ PGASExactQ (n + 2) d (cubicToExactPolynomialCode n d F) :=
  (cubicToPolynomialCode_correct hn (le_refl 3) F).trans
    (ExactDegreeCode.appendDegreeCarrierCode_pgasExactQ_iff n d (cubicToPolynomialCode n F)
      hd (cubicToPolynomialCode_degree_le n F)).symm

/-- The same total transformation reduces homogeneous cubic GAS to LAS
at the prescribed polynomial degree. -/
theorem cubicToExactPolynomialCode_correct_las
    {n d : ℕ} (hn : 0 < n) (hd : 3 ≤ d) (F : PolynomialFieldCode n) :
    HGASQ n 3 F ↔ PLASExactQ (n + 2) d (cubicToExactPolynomialCode n d F) :=
  (cubicToPolynomialCode_correct_las hn (le_refl 3) F).trans
    (ExactDegreeCode.appendDegreeCarrierCode_plasExactQ_iff n d (cubicToPolynomialCode n F)
      hd (cubicToPolynomialCode_degree_le n F)).symm

/-- Cubic homogeneous GAS reduces to exact-degree polynomial GAS with two
additional variables. -/
theorem hgasQ_manyOneReducible_pgasExactQ
    {n d : ℕ} (hn : 0 < n) (hd : 3 ≤ d) :
    HGASQ n 3 ≤₀ PGASExactQ (n + 2) d :=
  ⟨cubicToExactPolynomialCode n d, (cubicToExactPolynomialCode_primrec n d).to_comp,
    cubicToExactPolynomialCode_correct hn hd⟩

/-- Cubic homogeneous GAS reduces to exact-degree polynomial LAS with two
additional variables. -/
theorem hgasQ_manyOneReducible_plasExactQ
    {n d : ℕ} (hn : 0 < n) (hd : 3 ≤ d) :
    HGASQ n 3 ≤₀ PLASExactQ (n + 2) d :=
  ⟨cubicToExactPolynomialCode n d, (cubicToExactPolynomialCode_primrec n d).to_comp,
    cubicToExactPolynomialCode_correct_las hn hd⟩

/-- Two auxiliary coordinates above the existing cofinal cubic threshold
suffice for every exact polynomial degree at least three. -/
noncomputable abbrev exactPolynomialDimensionThreshold : ℕ :=
  NormalizedCorrectedAugmentedEffectiveFamily.cofinalDimensionThreshold + 2

/-- GAS is many-one hard in every sufficiently large fixed dimension and
every fixed exact degree at least three, including even degrees. -/
theorem pgasExactQ_manyOneHard
    (n d : ℕ) (hn : exactPolynomialDimensionThreshold ≤ n) (hd : 3 ≤ d) :
    ManyOneHard (PGASExactQ n d) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := by
    refine ⟨n - 2, ?_⟩
    change NormalizedCorrectedAugmentedEffectiveFamily.cofinalDimensionThreshold + 2 ≤ n at hn
    omega
  have hsource :
      NormalizedCorrectedAugmentedEffectiveFamily.cofinalDimensionThreshold ≤ m := by
    change NormalizedCorrectedAugmentedEffectiveFamily.cofinalDimensionThreshold + 2 ≤ m + 2 at hn
    omega
  exact ManyOneHard.of_manyOneReducible
    (NormalizedCorrectedAugmentedEffectiveFamily.cubic_sigmaOneComplete m hsource).2
    (hgasQ_manyOneReducible_pgasExactQ (cofinalDimensionThreshold_pos.trans_le hsource) hd)

/-- LAS has the same exact-degree many-one hardness. -/
theorem plasExactQ_manyOneHard
    (n d : ℕ) (hn : exactPolynomialDimensionThreshold ≤ n) (hd : 3 ≤ d) :
    ManyOneHard (PLASExactQ n d) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := by
    refine ⟨n - 2, ?_⟩
    change NormalizedCorrectedAugmentedEffectiveFamily.cofinalDimensionThreshold + 2 ≤ n at hn
    omega
  have hsource :
      NormalizedCorrectedAugmentedEffectiveFamily.cofinalDimensionThreshold ≤ m := by
    change NormalizedCorrectedAugmentedEffectiveFamily.cofinalDimensionThreshold + 2 ≤ m + 2 at hn
    omega
  exact ManyOneHard.of_manyOneReducible
    (NormalizedCorrectedAugmentedEffectiveFamily.cubic_sigmaOneComplete m hsource).2
    (hgasQ_manyOneReducible_plasExactQ (cofinalDimensionThreshold_pos.trans_le hsource) hd)

/-- GAS is undecidable at these fixed dimensions and exact degrees. -/
theorem pgasExactQ_not_computable
    (n d : ℕ) (hn : exactPolynomialDimensionThreshold ≤ n) (hd : 3 ≤ d) :
    ¬ ComputablePred (PGASExactQ n d) :=
  (pgasExactQ_manyOneHard n d hn hd).not_computable

/-- LAS is undecidable at these fixed dimensions and exact degrees. -/
theorem plasExactQ_not_computable
    (n d : ℕ) (hn : exactPolynomialDimensionThreshold ≤ n) (hd : 3 ≤ d) :
    ¬ ComputablePred (PLASExactQ n d) :=
  (plasExactQ_manyOneHard n d hn hd).not_computable

/-- The exact-degree GAS complement is not recursively enumerable. -/
theorem pgasExactQ_complement_not_re
    (n d : ℕ) (hn : exactPolynomialDimensionThreshold ≤ n) (hd : 3 ≤ d) :
    ¬ REPred (fun F ↦ ¬ PGASExactQ n d F) :=
  (pgasExactQ_manyOneHard n d hn hd).complement_not_re

/-- The exact-degree LAS complement is not recursively enumerable. -/
theorem plasExactQ_complement_not_re
    (n d : ℕ) (hn : exactPolynomialDimensionThreshold ≤ n) (hd : 3 ≤ d) :
    ¬ REPred (fun F ↦ ¬ PLASExactQ n d F) :=
  (plasExactQ_manyOneHard n d hn hd).complement_not_re

end Stability
