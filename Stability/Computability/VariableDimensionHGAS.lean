import Stability.Computability.RawGridComputability
import Stability.Computability.VariableHGASDegree

/-!
# Homogeneous GAS with dimension and degree as raw input

An input is `(n,d,F)`, with the field and all exponent vectors encoded
by ordinary lists. Shape validation requires exactly `n` coordinates.
Membership then means odd `d` and the existing semantic `HGASQ n d`
for the decoded field. Homogeneity is tested after exact cancellation
of duplicate monomials, not by restricting the displayed terms.

One primitive-recursive witness checker handles every `n` and `d`.
Its correctness follows from exact commutation with the existing
finite-grid checker. A fixed cubic slice gives completeness.
-/

namespace Stability

open HGAS RawCodePrimrec

abbrev RawHGASInput := ℕ × (ℕ × RawPolynomialFieldCode)
abbrev RawGridCandidate := (ℕ × RawPolynomialCode) × (ℕ × ℕ)

/-- The dimension and degree are both input data. Malformed shapes and
even degrees are negative instances. The last conjunct is semantic GAS. -/
def DimensionDegreeHGASQ (input : RawHGASInput) : Prop :=
  RawPolynomialFieldCode.wellFormed input.1 input.2.2 = true ∧
    Odd input.2.1 ∧
      HGASQ input.1 input.2.1 (RawPolynomialFieldCode.toFixed input.1 input.2.2)

namespace RawHGASChecker

def fieldHomogeneous (d : ℕ) (F : RawPolynomialFieldCode) : Bool :=
  F.all (RawPolynomialCode.homogeneous d)

def candidateOfFixed {n : ℕ} (c : GridRationalLyapunovCandidate.Candidate n) :
    RawGridCandidate := ((c.1.1, RawPolynomialCode.ofFixed c.1.2), c.2)

def candidateToFixed (n : ℕ) (c : RawGridCandidate) :
    GridRationalLyapunovCandidate.Candidate n :=
  ((c.1.1, RawPolynomialCode.toFixed n c.1.2), c.2)

def core (n d : ℕ) (F : RawPolynomialFieldCode) (c : RawGridCandidate) : Bool :=
  fieldHomogeneous d F && RawPolynomialCode.homogeneous (2 * (c.1.1 + 1)) c.1.2 &&
    RawGridCertificate.checkStrictPositiveOnSupSphere n c.1.2 c.2.1 &&
    RawGridCertificate.checkStrictPositiveOnSupSphere n
      (RawPolynomialCode.rationalLyapunovNumerator n F c.1.2 c.1.1) c.2.2

/-- Shape checks are explicit and independent of the polynomial's
coefficients. The remaining operations use exact rational arithmetic. -/
def checkCandidate (input : RawHGASInput) (c : RawGridCandidate) : Bool :=
  RawPolynomialFieldCode.wellFormed input.1 input.2.2 &&
    (input.2.1 % 2 == 1) && RawPolynomialCode.wellFormed input.1 c.1.2 &&
    core input.1 input.2.1 input.2.2 c

/-- Total natural-number decoding; unsuccessful decodes have zero grid
resolutions and therefore cannot create accepted witnesses. -/
def decodeCandidate (code : ℕ) : RawGridCandidate :=
  (Encodable.decode (α := RawGridCandidate) code).getD ((0, []), (0, 0))

def check (input : RawHGASInput) (code : ℕ) : Bool :=
  checkCandidate input (decodeCandidate code)

@[simp]
theorem decodeCandidate_encode (c : RawGridCandidate) :
    decodeCandidate (Encodable.encode c) = c := by simp [decodeCandidate]

/-- Failed witness decoding cannot accept an input, even in dimension
zero, because its fallback has resolution zero. -/
theorem check_eq_false_of_decode_none (input : RawHGASInput) (code : ℕ)
    (hcode : Encodable.decode (α := RawGridCandidate) code = none) :
    check input code = false := by
  simp [check, decodeCandidate, hcode, checkCandidate, core,
    RawGridCertificate.checkStrictPositiveOnSupSphere]

@[simp]
theorem fieldHomogeneous_ofFixed {n : ℕ} (d : ℕ) (F : PolynomialFieldCode n) :
    fieldHomogeneous d (RawPolynomialFieldCode.ofFixed F) =
      PolynomialFieldCode.homogeneous d F := by
  apply Bool.eq_iff_iff.mpr
  simp [fieldHomogeneous, RawPolynomialFieldCode.ofFixed,
    PolynomialFieldCode.homogeneous, List.all_eq_true, List.mem_ofFn]

@[simp]
theorem core_ofFixed {n : ℕ} (d : ℕ) (F : PolynomialFieldCode n)
    (c : GridRationalLyapunovCandidate.Candidate n) :
    core n d (RawPolynomialFieldCode.ofFixed F) (candidateOfFixed c) =
      checkGridRationalLyapunov d F c := by
  simp only [core, candidateOfFixed, fieldHomogeneous_ofFixed,
    RawPolynomialCode.homogeneous_ofFixed,
    RawGridCertificate.checkStrictPositiveOnSupSphere_ofFixed,
    RawPolynomialCode.rationalLyapunovNumerator_ofFixed]
  rfl

theorem core_eq_fixed {n : ℕ} (d : ℕ) (F : RawPolynomialFieldCode)
    (c : RawGridCandidate) (hF : RawPolynomialFieldCode.wellFormed n F = true)
    (hc : RawPolynomialCode.wellFormed n c.1.2 = true) :
    core n d F c = checkGridRationalLyapunov d (RawPolynomialFieldCode.toFixed n F)
      (candidateToFixed n c) := by
  have hc' : candidateOfFixed (candidateToFixed n c) = c := by
    simp only [candidateOfFixed, candidateToFixed,
      RawPolynomialCode.ofFixed_toFixed _ hc, Prod.mk.eta]
  rw [← core_ofFixed, RawPolynomialFieldCode.ofFixed_toFixed _ hF, hc']

theorem checkCandidate_eq_true_iff (input : RawHGASInput) (c : RawGridCandidate) :
    checkCandidate input c = true ↔
      RawPolynomialFieldCode.wellFormed input.1 input.2.2 = true ∧
      Odd input.2.1 ∧ RawPolynomialCode.wellFormed input.1 c.1.2 = true ∧
      core input.1 input.2.1 input.2.2 c = true := by
  simp only [checkCandidate, Bool.and_eq_true, beq_iff_eq, ← Nat.odd_iff]
  tauto

attribute [local fun_prop] Primrec Primrec.id Primrec.const Primrec.fst Primrec.snd
attribute [local fun_prop] Primrec.comp Primrec.pair natAdd natMul natMod boolAnd beq
attribute [local fun_prop] RawPolynomialCode.homogeneous_primrec
attribute [local fun_prop] RawPolynomialCode.wellFormed_primrec
attribute [local fun_prop] RawPolynomialFieldCode.wellFormed_primrec
attribute [local fun_prop] RawPolynomialCode.rationalLyapunovNumerator_primrec
attribute [local fun_prop] RawGridCertificate.checkStrictPositiveOnSupSphere_primrec

@[local fun_prop] theorem fieldHomogeneous_primrec :
    Primrec (fun q : ℕ × RawPolynomialFieldCode ↦ fieldHomogeneous q.1 q.2) := by
  unfold fieldHomogeneous
  apply listAll <;> fun_prop

@[local fun_prop] theorem core_primrec :
    Primrec (fun q : ℕ × (ℕ × (RawPolynomialFieldCode × RawGridCandidate)) ↦
      core q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold core
  fun_prop

/-- A single primitive-recursive program, not a separate family indexed
by a fixed dimension. -/
theorem checkCandidate_primrec :
    Primrec (fun q : RawHGASInput × RawGridCandidate ↦ checkCandidate q.1 q.2) := by
  unfold checkCandidate
  fun_prop

theorem decodeCandidate_primrec : Primrec decodeCandidate :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const ((0, []), (0, 0)))

theorem check_primrec : Primrec (fun q : RawHGASInput × ℕ ↦ check q.1 q.2) :=
  checkCandidate_primrec.comp
    (Primrec.pair Primrec.fst (decodeCandidate_primrec.comp Primrec.snd))

end RawHGASChecker

open RawHGASChecker

/-- Exact semantic soundness and completeness for the raw-input checker. -/
theorem dimensionDegreeHGASQ_iff_exists_check (input : RawHGASInput) :
    DimensionDegreeHGASQ input ↔ ∃ code, check input code = true := by
  constructor
  · rintro ⟨hF, hodd, hgas⟩
    obtain ⟨c, hc⟩ := (hgasQ_iff_hasGridRationalLyapunov hodd.pos
      (hasRealRationalHomogeneousConverse_of_odd hodd) _).mp hgas
    refine ⟨Encodable.encode (candidateOfFixed c), ?_⟩
    rw [check, decodeCandidate_encode, checkCandidate_eq_true_iff]
    refine ⟨hF, hodd, RawPolynomialCode.wellFormed_ofFixed _, ?_⟩
    rw [← RawPolynomialFieldCode.ofFixed_toFixed _ hF, core_ofFixed]
    exact hc
  · rintro ⟨code, hcode⟩
    obtain ⟨hF, hodd, hp, hc⟩ := (checkCandidate_eq_true_iff _ _).mp hcode
    rw [core_eq_fixed _ _ _ hF hp] at hc
    exact ⟨hF, hodd, hgasQ_of_checkGridRationalLyapunov hodd.pos _ _ hc⟩

/-- Recursive enumerability is uniform in every raw input component. -/
theorem dimensionDegreeHGASQ_re : REPred DimensionDegreeHGASQ := by
  have hrelation : ComputablePred (fun q : RawHGASInput × ℕ ↦ check q.1 q.2 = true) :=
    ComputablePred.computable_iff.mpr ⟨_, check_primrec.to_comp, rfl⟩
  apply REPred.of_eq (rePred_exists_nat_of_computableRel
    (fun input code ↦ check input code = true) hrelation)
  intro input
  exact (dimensionDegreeHGASQ_iff_exists_check input).symm

/-- The finite-list encoding of one fixed-dimensional sparse polynomial
is primitive recursive. This is used only for the hardness embedding. -/
theorem rawPolynomial_ofFixed_primrec (n : ℕ) :
    Primrec (RawPolynomialCode.ofFixed : PolynomialCode n → RawPolynomialCode) := by
  apply Primrec.list_map Primrec.id
  apply Primrec.pair
  · apply Primrec.list_ofFn
    intro i
    exact Primrec.fin_app.comp (Primrec.fst.comp Primrec.snd) (Primrec.const i)
  · exact Primrec.snd.comp Primrec.snd

theorem rawField_ofFixed_primrec (n : ℕ) :
    Primrec (RawPolynomialFieldCode.ofFixed : PolynomialFieldCode n → RawPolynomialFieldCode) :=
  Primrec.list_ofFn fun i ↦ (rawPolynomial_ofFixed_primrec n).comp
    (Primrec.fin_app.comp Primrec.id (Primrec.const i))

/-- A fixed odd-degree slice embeds every field code without a semantic
test or a validity-dependent fallback. Shape is guaranteed by encoding. -/
theorem hgasQ_manyOneReducible_dimensionDegreeHGASQ
    (n d : ℕ) (hd : Odd d) : HGASQ n d ≤₀ DimensionDegreeHGASQ := by
  refine ⟨fun F ↦ (n, d, RawPolynomialFieldCode.ofFixed F),
    Computable.pair (Computable.const n)
      (Computable.pair (Computable.const d) (rawField_ofFixed_primrec n).to_comp), ?_⟩
  intro F
  simp [DimensionDegreeHGASQ, hd]

/-- The single raw language with both dimension and degree as input is
`Σ⁰₁`-complete. One fixed cubic slice already supplies hardness. -/
theorem dimensionDegreeHGASQ_sigmaOneComplete : SigmaOneComplete DimensionDegreeHGASQ := by
  refine ⟨dimensionDegreeHGASQ_re, ?_⟩
  intro q hq
  exact ((NormalizedCorrectedAugmentedEffectiveFamily.cubic_sigmaOneComplete
    NormalizedCorrectedAugmentedEffectiveFamily.cofinalDimensionThreshold le_rfl).2 q hq).trans
      (hgasQ_manyOneReducible_dimensionDegreeHGASQ
        NormalizedCorrectedAugmentedEffectiveFamily.cofinalDimensionThreshold 3 (by norm_num))

theorem dimensionDegreeHGASQ_not_computable : ¬ ComputablePred DimensionDegreeHGASQ :=
  dimensionDegreeHGASQ_sigmaOneComplete.not_computable

theorem dimensionDegreeHGASQ_complement_not_re :
    ¬ REPred (fun input ↦ ¬ DimensionDegreeHGASQ input) :=
  dimensionDegreeHGASQ_sigmaOneComplete.complement_not_re

end Stability
