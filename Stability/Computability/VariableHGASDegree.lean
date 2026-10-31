import HGAS.Arithmetic.NormalizedCorrectedAugmentedEffectiveFamily

/-!
# A uniform degree-input homogeneous GAS language

For fixed dimension `n`, the input is a raw pair `(d, F)` of a natural
degree and a finite rational polynomial-field code.  Membership requires
that `d` be odd, that every decoded coordinate be homogeneous of degree
`d`, and that the realized field be GAS.  Even-degree inputs and invalid
homogeneity codes are negative instances.

The proof of recursive enumerability constructs one primitive-recursive
checker with `d` as data.  It does not infer uniformity from the separate
fixed-degree r.e. theorems.  The candidate syntax and decoder do not depend
on `d`.  A fixed cubic slice supplies hardness in every sufficiently large
fixed dimension.

Dimension remains fixed throughout this file.  A language with dimension
as input still requires uniform raw encodings and a uniform grid checker;
the results here make no variable-dimension computability claim.
-/

namespace Stability

open HGAS HGAS.GridRationalLyapunovCandidate HGAS.ExactGridPositivity

/-- Odd-degree homogeneous GAS with the degree included in the raw input.
The dimension is a fixed parameter, not part of the machine input. -/
def VariableOddHGASQ (n : ℕ) (input : ℕ × PolynomialFieldCode n) : Prop :=
  Odd input.1 ∧ HGASQ n input.1 input.2

set_option maxHeartbeats 800000 in
-- Composing the nested product programs in the grid checker requires
-- extra elaboration steps, as in the existing fixed-degree checker proof.
/-- The exact-grid checker is primitive recursive jointly in the degree,
the field code, and its finite candidate, for each fixed dimension. -/
theorem checkGridRationalLyapunov_degree_primrec (n : ℕ) :
    Primrec (fun q : ℕ × (PolynomialFieldCode n × Candidate n) ↦
      checkGridRationalLyapunov q.1 q.2.1 q.2.2) := by
  have hF : Primrec (fun q : ℕ × (PolynomialFieldCode n × Candidate n) ↦ q.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun q : ℕ × (PolynomialFieldCode n × Candidate n) ↦ q.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hr : Primrec (fun q : ℕ × (PolynomialFieldCode n × Candidate n) ↦ q.2.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp hc)
  have hp : Primrec (fun q : ℕ × (PolynomialFieldCode n × Candidate n) ↦ q.2.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp hc)
  have hmp : Primrec (fun q : ℕ × (PolynomialFieldCode n × Candidate n) ↦ q.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp hc)
  have hmq : Primrec (fun q : ℕ × (PolynomialFieldCode n × Candidate n) ↦ q.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp hc)
  have hvalid : Primrec (fun q : ℕ × (PolynomialFieldCode n × Candidate n) ↦
      PolynomialFieldCode.homogeneous q.1 q.2.1) :=
    (PolynomialFieldCode.homogeneous_primrec n).comp (Primrec.pair Primrec.fst hF)
  have hpDegree : Primrec (fun q : ℕ × (PolynomialFieldCode n × Candidate n) ↦
      2 * (q.2.2.1.1 + 1)) :=
    Primrec.nat_mul.comp (Primrec.const 2) (Primrec.succ.comp hr)
  have hpHomogeneous : Primrec (fun q : ℕ × (PolynomialFieldCode n × Candidate n) ↦
      PolynomialCode.homogeneous (2 * (q.2.2.1.1 + 1)) q.2.2.1.2) :=
    PolynomialCode.homogeneous_primrec.comp hpDegree hp
  have hpGrid : Primrec (fun q : ℕ × (PolynomialFieldCode n × Candidate n) ↦
      checkStrictPositiveOnSupSphere q.2.2.1.2 q.2.2.2.1) :=
    checkStrictPositiveOnSupSphere_primrec.comp hp hmp
  have hqInput : Primrec (fun q : ℕ × (PolynomialFieldCode n × Candidate n) ↦
      ((q.2.1, q.2.2.1.2), q.2.2.1.1)) :=
    Primrec.pair (Primrec.pair hF hp) hr
  have hq : Primrec (fun q : ℕ × (PolynomialFieldCode n × Candidate n) ↦
      PolynomialCode.rationalLyapunovNumerator q.2.1 q.2.2.1.2 q.2.2.1.1) :=
    PolynomialCode.rationalLyapunovNumerator_primrec.comp hqInput
  have hqGrid : Primrec (fun q : ℕ × (PolynomialFieldCode n × Candidate n) ↦
      checkStrictPositiveOnSupSphere
        (PolynomialCode.rationalLyapunovNumerator q.2.1 q.2.2.1.2 q.2.2.1.1)
        q.2.2.2.2) :=
    checkStrictPositiveOnSupSphere_primrec.comp hq hmq
  exact (Primrec.and.comp
    (Primrec.and.comp (Primrec.and.comp hvalid hpHomogeneous) hpGrid) hqGrid).of_eq
      fun _ ↦ rfl

/-- A total Boolean witness test, including the input degree's parity and
homogeneity validation.  Every witness is decoded by the same fixed-`n`
decoder, independently of the input degree. -/
def checkVariableOddHGAS {n : ℕ}
    (input : ℕ × PolynomialFieldCode n) (code : ℕ) : Bool :=
  (input.1 % 2 == 1) &&
    checkGridRationalLyapunov input.1 input.2
      (decodeGridRationalLyapunovCandidateTotal n code)

@[simp]
theorem checkVariableOddHGAS_eq_true_iff {n : ℕ}
    (input : ℕ × PolynomialFieldCode n) (code : ℕ) :
    checkVariableOddHGAS input code = true ↔
      Odd input.1 ∧ checkGridRationalLyapunov input.1 input.2
        (decodeGridRationalLyapunovCandidateTotal n code) = true := by
  simp [checkVariableOddHGAS, Nat.odd_iff]

/-- One primitive-recursive program checks every degree input. -/
theorem checkVariableOddHGAS_primrec (n : ℕ) :
    Primrec (fun q : (ℕ × PolynomialFieldCode n) × ℕ ↦
      checkVariableOddHGAS q.1 q.2) := by
  have hd : Primrec (fun q : (ℕ × PolynomialFieldCode n) × ℕ ↦ q.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hF : Primrec (fun q : (ℕ × PolynomialFieldCode n) × ℕ ↦ q.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hodd : Primrec (fun q : (ℕ × PolynomialFieldCode n) × ℕ ↦ q.1.1 % 2 == 1) :=
    Primrec.beq.comp (Primrec.nat_mod.comp hd (Primrec.const 2)) (Primrec.const 1)
  have hc : Primrec (fun q : (ℕ × PolynomialFieldCode n) × ℕ ↦
      decodeGridRationalLyapunovCandidateTotal n q.2) :=
    (decodeGridRationalLyapunovCandidateTotal_primrec n).comp Primrec.snd
  have hcheck := (checkGridRationalLyapunov_degree_primrec n).comp
    (Primrec.pair hd (Primrec.pair hF hc))
  exact (Primrec.and.comp hodd hcheck).of_eq fun _ ↦ rfl

/-- The uniform checker accepts some witness exactly for the intended
semantic language.  Oddness supplies the positive degree needed for
soundness and the homogeneous converse needed for completeness. -/
theorem variableOddHGASQ_iff_exists_check {n : ℕ}
    (input : ℕ × PolynomialFieldCode n) :
    VariableOddHGASQ n input ↔ ∃ code, checkVariableOddHGAS input code = true := by
  constructor
  · rintro ⟨hodd, hgas⟩
    have hgrid := (hgasQ_iff_hasGridRationalLyapunov hodd.pos
      (hasRealRationalHomogeneousConverse_of_odd hodd) input.2).mp hgas
    obtain ⟨code, hcode⟩ :=
      (hasGridRationalLyapunov_iff_exists_nat input.1 input.2).mp hgrid
    exact ⟨code, (checkVariableOddHGAS_eq_true_iff input code).mpr ⟨hodd, hcode⟩⟩
  · rintro ⟨code, hcode⟩
    obtain ⟨hodd, hcheck⟩ := (checkVariableOddHGAS_eq_true_iff input code).mp hcode
    exact ⟨hodd, hgasQ_of_checkGridRationalLyapunov hodd.pos input.2 _ hcheck⟩

/-- Recursive enumerability is uniform in the degree supplied as input,
not merely a family of fixed-degree r.e. assertions. -/
theorem variableOddHGASQ_re (n : ℕ) : REPred (VariableOddHGASQ n) := by
  have hrelation : ComputablePred
      (fun q : (ℕ × PolynomialFieldCode n) × ℕ ↦
        checkVariableOddHGAS q.1 q.2 = true) := by
    apply ComputablePred.computable_iff.mpr
    exact ⟨_, (checkVariableOddHGAS_primrec n).to_comp, rfl⟩
  apply REPred.of_eq (rePred_exists_nat_of_computableRel
    (fun input code ↦ checkVariableOddHGAS input code = true) hrelation)
  intro input
  exact (variableOddHGASQ_iff_exists_check input).symm

/-- Insert a fixed odd degree into the raw input; every field code,
including invalid homogeneity codes, is preserved by this reduction. -/
theorem hgasQ_manyOneReducible_variableOddHGASQ
    (n d : ℕ) (hd : Odd d) : HGASQ n d ≤₀ VariableOddHGASQ n := by
  refine ⟨fun F ↦ (d, F), Computable.pair (Computable.const d) Computable.id, ?_⟩
  intro F
  simp [VariableOddHGASQ, hd]

/-- The degree-input language is `Σ⁰₁`-complete in every dimension above
the existing cubic threshold.  No uniformity in dimension is asserted. -/
theorem variableOddHGASQ_sigmaOneComplete
    (n : ℕ)
    (hn : NormalizedCorrectedAugmentedEffectiveFamily.cofinalDimensionThreshold ≤ n) :
    SigmaOneComplete (VariableOddHGASQ n) := by
  refine ⟨variableOddHGASQ_re n, ?_⟩
  intro q hq
  exact ((NormalizedCorrectedAugmentedEffectiveFamily.cubic_sigmaOneComplete n hn).2
    q hq).trans (hgasQ_manyOneReducible_variableOddHGASQ n 3 (by norm_num))

theorem variableOddHGASQ_not_computable
    (n : ℕ)
    (hn : NormalizedCorrectedAugmentedEffectiveFamily.cofinalDimensionThreshold ≤ n) :
    ¬ ComputablePred (VariableOddHGASQ n) :=
  (variableOddHGASQ_sigmaOneComplete n hn).not_computable

theorem variableOddHGASQ_complement_not_re
    (n : ℕ)
    (hn : NormalizedCorrectedAugmentedEffectiveFamily.cofinalDimensionThreshold ≤ n) :
    ¬ REPred (fun input ↦ ¬ VariableOddHGASQ n input) :=
  (variableOddHGASQ_sigmaOneComplete n hn).complement_not_re

end Stability
