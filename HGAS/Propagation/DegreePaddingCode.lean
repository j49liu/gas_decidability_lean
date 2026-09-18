import HGAS.Computability.HGASLanguage
import HGAS.Dynamics.LinearConjugacyGAS
import HGAS.Foundation.PolynomialDifferentiationCode
import HGAS.Propagation.DegreePaddingGAS
import Mathlib.Computability.Primrec.List
import Mathlib.Tactic

/-!
# An effective finite-code compiler for dimension and degree padding

The semantic construction in `DegreePadding` adjoins independent cubic
sinks and multiplies the resulting field by a power of the total squared
radius.  This file implements that construction on the raw sparse rational
codes used by `HGASQ`.

There are two small but reusable pieces.

* `ExponentCode.dimensionEmbed` and `PolynomialCode.dimensionEmbed` insert
  a polynomial in the first block of a larger set of variables.  Their
  decoding theorems identify the operation exactly with
  `MvPolynomial.rename`.
* `degreeDimensionPadCode` emits the common squared-radius factor and either
  an embedded source coordinate or one of the new scalar cubic sinks.

Every operation is primitive recursive for fixed dimensions and exponent.
The realization theorem identifies the emitted code with the semantic
degree-padded field, up to the canonical linear reindexing between
`Fin (m + p)` and the two coordinate blocks.  Consequently the compiler
preserves and reflects GAS on valid cubic inputs.
-/

namespace HGAS

open MvPolynomial
open scoped BigOperators

noncomputable section

namespace DegreePaddingCode

/-- Index of an original variable in the first block of `Fin (m + p)`. -/
def baseIndex (m p : ℕ) (i : Fin m) : Fin (m + p) :=
  finSumFinEquiv (Sum.inl i)

/-- Index of an auxiliary sink variable in the second block of
`Fin (m + p)`. -/
def sinkIndex (m p : ℕ) (r : Fin p) : Fin (m + p) :=
  finSumFinEquiv (Sum.inr r)

@[simp]
theorem finSumFinEquiv_symm_baseIndex
    (m p : ℕ) (i : Fin m) :
    finSumFinEquiv.symm (baseIndex m p i) = Sum.inl i := by
  simp [baseIndex]

@[simp]
theorem finSumFinEquiv_symm_sinkIndex
    (m p : ℕ) (r : Fin p) :
    finSumFinEquiv.symm (sinkIndex m p r) = Sum.inr r := by
  simp [sinkIndex]

theorem baseIndex_injective (m p : ℕ) :
    Function.Injective (baseIndex m p) :=
  finSumFinEquiv.injective.comp Sum.inl_injective

theorem sinkIndex_ne_baseIndex
    (m p : ℕ) (r : Fin p) (i : Fin m) :
    sinkIndex m p r ≠ baseIndex m p i := by
  intro h
  have := congrArg finSumFinEquiv.symm h
  simp at this

/-- The canonical linear identification of a flat target vector with its
original and auxiliary coordinate blocks. -/
def splitEquiv (m p : ℕ) :
    (Fin (m + p) → ℝ) ≃L[ℝ] SplitPoint m p ℝ :=
  (ContinuousLinearEquiv.piCongrLeft ℝ
      (fun _ : Fin (m + p) => ℝ) finSumFinEquiv).symm |>.trans
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ
      (Fin m) (Fin p) (fun _ => ℝ))

@[simp]
theorem splitEquiv_fst_apply
    (m p : ℕ) (x : Fin (m + p) → ℝ) (i : Fin m) :
    (splitEquiv m p x).1 i = x (baseIndex m p i) := by
  rfl

@[simp]
theorem splitEquiv_snd_apply
    (m p : ℕ) (x : Fin (m + p) → ℝ) (r : Fin p) :
    (splitEquiv m p x).2 r = x (sinkIndex m p r) := by
  rfl

@[simp]
theorem splitEquiv_symm_baseIndex
    (m p : ℕ) (x : SplitPoint m p ℝ) (i : Fin m) :
    (splitEquiv m p).symm x (baseIndex m p i) = x.1 i := by
  change
    Equiv.piCongrLeft (fun _ : Fin (m + p) => ℝ) finSumFinEquiv
      ((Equiv.sumPiEquivProdPi
        (fun _ : Fin m ⊕ Fin p => ℝ)).symm x)
      (finSumFinEquiv (Sum.inl i)) = x.1 i
  exact Equiv.piCongrLeft_sumInl _ _ _ _ _

@[simp]
theorem splitEquiv_symm_sinkIndex
    (m p : ℕ) (x : SplitPoint m p ℝ) (r : Fin p) :
    (splitEquiv m p).symm x (sinkIndex m p r) = x.2 r := by
  change
    Equiv.piCongrLeft (fun _ : Fin (m + p) => ℝ) finSumFinEquiv
      ((Equiv.sumPiEquivProdPi
        (fun _ : Fin m ⊕ Fin p => ℝ)).symm x)
      (finSumFinEquiv (Sum.inr r)) = x.2 r
  exact Equiv.piCongrLeft_sumInr _ _ _ _ _

end DegreePaddingCode

namespace ExponentCode

variable {m : ℕ}

/-- Insert an exponent vector in the first block of `Fin (m + p)`, putting
zero on every new variable. -/
def dimensionEmbed (p : ℕ) (e : ExponentCode m) :
    ExponentCode (m + p) :=
  fun q =>
    match finSumFinEquiv.symm q with
    | Sum.inl i => e i
    | Sum.inr _ => 0

@[simp]
theorem dimensionEmbed_base
    (p : ℕ) (e : ExponentCode m) (i : Fin m) :
    dimensionEmbed p e (DegreePaddingCode.baseIndex m p i) = e i := by
  simp [dimensionEmbed, DegreePaddingCode.baseIndex]

@[simp]
theorem dimensionEmbed_sink
    (p : ℕ) (e : ExponentCode m) (r : Fin p) :
    dimensionEmbed p e (DegreePaddingCode.sinkIndex m p r) = 0 := by
  simp [dimensionEmbed, DegreePaddingCode.sinkIndex]

theorem decode_dimensionEmbed
    (p : ℕ) (e : ExponentCode m) :
    decode (dimensionEmbed p e) =
      (decode e).mapDomain (DegreePaddingCode.baseIndex m p) := by
  ext q
  obtain ⟨i | r, rfl⟩ := finSumFinEquiv.surjective q
  · change
      dimensionEmbed p e (DegreePaddingCode.baseIndex m p i) =
        ((decode e).mapDomain
          (DegreePaddingCode.baseIndex m p))
          (DegreePaddingCode.baseIndex m p i)
    rw [Finsupp.mapDomain_apply
      (DegreePaddingCode.baseIndex_injective m p)]
    simp [ExponentCode.decode]
  · rw [Finsupp.mapDomain_notin_range]
    · change dimensionEmbed p e
        (DegreePaddingCode.sinkIndex m p r) = 0
      simp
    · intro h
      rcases h with ⟨i, hi⟩
      exact DegreePaddingCode.sinkIndex_ne_baseIndex m p r i hi.symm

/-- For fixed dimensions, inserting a zero block in an exponent vector is
primitive recursive. -/
theorem dimensionEmbed_primrec (m p : ℕ) :
    Primrec (dimensionEmbed p : ExponentCode m → ExponentCode (m + p)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro q
  obtain ⟨i | r, rfl⟩ := finSumFinEquiv.surjective q
  · exact
      (Primrec.fin_app.comp Primrec.id (Primrec.const i)).of_eq
        fun e => (dimensionEmbed_base p e i).symm
  · exact (Primrec.const 0).of_eq
      fun e => (dimensionEmbed_sink p e r).symm

end ExponentCode

namespace PolynomialCode

variable {m : ℕ}

/-- Insert one sparse term into the first variable block. -/
def dimensionEmbedTerm (p : ℕ)
    (t : ExponentCode m × RationalCode) :
    ExponentCode (m + p) × RationalCode :=
  (ExponentCode.dimensionEmbed p t.1, t.2)

/-- Insert a sparse polynomial into the first variable block. -/
def dimensionEmbed (p : ℕ) (q : PolynomialCode m) :
    PolynomialCode (m + p) :=
  q.map (dimensionEmbedTerm p)

@[simp]
theorem decodeTerm_dimensionEmbedTerm
    (p : ℕ) (t : ExponentCode m × RationalCode) :
    decodeTerm (dimensionEmbedTerm p t) =
      MvPolynomial.rename (DegreePaddingCode.baseIndex m p)
        (decodeTerm t) := by
  simp only [dimensionEmbedTerm, decodeTerm,
    ExponentCode.decode_dimensionEmbed]
  exact (MvPolynomial.rename_monomial
    (DegreePaddingCode.baseIndex m p)
    (ExponentCode.decode t.1)
    (RationalCode.decode t.2)).symm

@[simp]
theorem decode_dimensionEmbed
    (p : ℕ) (q : PolynomialCode m) :
    decode (dimensionEmbed p q) =
      MvPolynomial.rename (DegreePaddingCode.baseIndex m p) (decode q) := by
  induction q with
  | nil => simp [dimensionEmbed]
  | cons t q ih =>
      change
        decodeTerm (dimensionEmbedTerm p t) +
            decode (dimensionEmbed p q) =
          MvPolynomial.rename (DegreePaddingCode.baseIndex m p)
            (decodeTerm t + decode q)
      rw [decodeTerm_dimensionEmbedTerm, ih, map_add]

theorem dimensionEmbedTerm_primrec (m p : ℕ) :
    Primrec (dimensionEmbedTerm p :
      (ExponentCode m × RationalCode) →
        (ExponentCode (m + p) × RationalCode)) := by
  exact Primrec.pair
    ((ExponentCode.dimensionEmbed_primrec m p).comp Primrec.fst)
    Primrec.snd

/-- For fixed dimensions, sparse polynomial variable insertion is
primitive recursive. -/
theorem dimensionEmbed_primrec (m p : ℕ) :
    Primrec (dimensionEmbed p :
      PolynomialCode m → PolynomialCode (m + p)) := by
  have hterm :
      Primrec₂
        (fun (_ : PolynomialCode m)
          (t : ExponentCode m × RationalCode) =>
            dimensionEmbedTerm p t) :=
    (dimensionEmbedTerm_primrec m p).comp₂ Primrec₂.right
  exact (Primrec.list_map Primrec.id hterm).of_eq fun _ => rfl

end PolynomialCode

namespace DegreePaddingCode

/-- Sparse code of the total squared radius in all `N` variables. -/
def totalNormSqCode (N : ℕ) : PolynomialCode N :=
  PolynomialCode.sumCodes
    (List.ofFn fun q : Fin N =>
      PolynomialCode.mul
        (PolynomialCode.varCode q)
        (PolynomialCode.varCode q))

@[simp]
theorem decode_totalNormSqCode (N : ℕ) :
    PolynomialCode.decode (totalNormSqCode N) =
      ∑ q : Fin N,
        (MvPolynomial.X q : MvPolynomial (Fin N) ℚ) ^ 2 := by
  rw [totalNormSqCode, PolynomialCode.decode_sumCodes,
    List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro q _
  simp [Function.comp_apply, pow_two]

theorem totalNormSqCode_primrec (N : ℕ) :
    Primrec (fun _ : Unit => totalNormSqCode N) :=
  Primrec.const _

/-- Raw finite-code version of dimension padding followed by degree
padding.  The first `m` output coordinates contain the embedded source
field; the last `p` coordinates are independent scalar cubic sinks. -/
def degreeDimensionPadCode
    (m p j : ℕ) (H : PolynomialFieldCode m) :
    PolynomialFieldCode (m + p) :=
  fun q =>
    let factor :=
      PolynomialCode.pow (totalNormSqCode (m + p)) j
    match finSumFinEquiv.symm q with
    | Sum.inl i =>
        PolynomialCode.mul factor
          (PolynomialCode.dimensionEmbed p (H i))
    | Sum.inr _ =>
        PolynomialCode.mul factor
          (PolynomialCode.neg
            (PolynomialCode.pow (PolynomialCode.varCode q) 3))

@[simp]
theorem degreeDimensionPadCode_base
    (m p j : ℕ) (H : PolynomialFieldCode m) (i : Fin m) :
    degreeDimensionPadCode m p j H (baseIndex m p i) =
      PolynomialCode.mul
        (PolynomialCode.pow (totalNormSqCode (m + p)) j)
        (PolynomialCode.dimensionEmbed p (H i)) := by
  simp [degreeDimensionPadCode, baseIndex]

@[simp]
theorem degreeDimensionPadCode_sink
    (m p j : ℕ) (H : PolynomialFieldCode m) (r : Fin p) :
    degreeDimensionPadCode m p j H (sinkIndex m p r) =
      PolynomialCode.mul
        (PolynomialCode.pow (totalNormSqCode (m + p)) j)
        (PolynomialCode.neg
          (PolynomialCode.pow
            (PolynomialCode.varCode (sinkIndex m p r)) 3)) := by
  simp [degreeDimensionPadCode, sinkIndex]

/-- For fixed `m`, `p`, and `j`, the complete field-code compiler is
primitive recursive. -/
theorem degreeDimensionPadCode_primrec
    (m p j : ℕ) :
    Primrec (degreeDimensionPadCode m p j) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro q
  cases hq : finSumFinEquiv.symm q with
  | inl i =>
      exact
        (PolynomialCode.mul_primrec.comp
          (Primrec.const
            (PolynomialCode.pow (totalNormSqCode (m + p)) j))
          ((PolynomialCode.dimensionEmbed_primrec m p).comp
            (Primrec.fin_app.comp Primrec.id (Primrec.const i)))).of_eq
          fun H => by simp [degreeDimensionPadCode, hq]
  | inr r =>
      exact
        (Primrec.const
          (PolynomialCode.mul
            (PolynomialCode.pow (totalNormSqCode (m + p)) j)
            (PolynomialCode.neg
              (PolynomialCode.pow (PolynomialCode.varCode q) 3)))).of_eq
        fun H => by simp [degreeDimensionPadCode, hq]

/-! ## Exact decoding and realization -/

theorem totalNormSqCode_isHomogeneous (N : ℕ) :
    (PolynomialCode.decode (totalNormSqCode N)).IsHomogeneous 2 := by
  rw [decode_totalNormSqCode]
  apply MvPolynomial.IsHomogeneous.sum Finset.univ
  intro q _
  exact MvPolynomial.isHomogeneous_X_pow q 2

@[simp]
theorem eval₂Hom_totalNormSqCode
    (N : ℕ) (x : Fin N → ℝ) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (totalNormSqCode N)) =
      normSq x := by
  rw [decode_totalNormSqCode]
  simp [normSq, dot, pow_two]

@[simp]
theorem eval₂Hom_dimensionEmbed
    (m p : ℕ) (q : PolynomialCode m)
    (x : Fin (m + p) → ℝ) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode
          (PolynomialCode.dimensionEmbed p q)) =
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (splitEquiv m p x).1 (PolynomialCode.decode q) := by
  rw [PolynomialCode.decode_dimensionEmbed,
    MvPolynomial.eval₂Hom_rename]
  congr 1

/-- The flat squared norm is the sum of the squared norms of the two
blocks under `splitEquiv`. -/
theorem normSq_eq_splitNormSq_splitEquiv
    (m p : ℕ) (x : Fin (m + p) → ℝ) :
    normSq x = splitNormSq (splitEquiv m p x) := by
  change
    (∑ q : Fin (m + p), x q * x q) =
      (∑ i : Fin m,
          x (baseIndex m p i) * x (baseIndex m p i)) +
        ∑ r : Fin p,
          x (sinkIndex m p r) * x (sinkIndex m p r)
  simpa [baseIndex, sinkIndex] using
    (Fin.sum_univ_add
      (f := fun q : Fin (m + p) => x q * x q))

@[simp]
theorem eval₂Hom_totalNormSqCode_eq_splitNormSq
    (m p : ℕ) (x : Fin (m + p) → ℝ) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (totalNormSqCode (m + p))) =
      splitNormSq (splitEquiv m p x) := by
  rw [eval₂Hom_totalNormSqCode,
    normSq_eq_splitNormSq_splitEquiv]

@[simp]
theorem realize_degreeDimensionPadCode_base
    (m p j : ℕ) (H : PolynomialFieldCode m)
    (x : Fin (m + p) → ℝ) (i : Fin m) :
    PolynomialFieldCode.realize
        (degreeDimensionPadCode m p j H) x
        (baseIndex m p i) =
      (degreePaddedField
        (k := p) (PolynomialFieldCode.realize H) j
        (splitEquiv m p x)).1 i := by
  rw [PolynomialFieldCode.realize_apply,
    degreeDimensionPadCode_base]
  simp only [PolynomialCode.decode_mul_code,
    PolynomialCode.decode_pow_code, map_mul, map_pow,
    eval₂Hom_totalNormSqCode_eq_splitNormSq,
    eval₂Hom_dimensionEmbed]
  rfl

@[simp]
theorem realize_degreeDimensionPadCode_sink
    (m p j : ℕ) (H : PolynomialFieldCode m)
    (x : Fin (m + p) → ℝ) (r : Fin p) :
    PolynomialFieldCode.realize
        (degreeDimensionPadCode m p j H) x
        (sinkIndex m p r) =
      (degreePaddedField
        (k := p) (PolynomialFieldCode.realize H) j
        (splitEquiv m p x)).2 r := by
  rw [PolynomialFieldCode.realize_apply,
    degreeDimensionPadCode_sink]
  simp only [PolynomialCode.decode_mul_code,
    PolynomialCode.decode_pow_code,
    PolynomialCode.decode_neg_code,
    PolynomialCode.decode_varCode,
    map_mul, map_pow, map_neg,
    MvPolynomial.eval₂Hom_X',
    eval₂Hom_totalNormSqCode_eq_splitNormSq]
  rfl

/-- Exact semantic specification of the sparse compiler.  The only
conjugacy is the canonical reindexing between a flat `Fin (m + p)` vector
and the two coordinate blocks used by the semantic construction. -/
theorem realize_degreeDimensionPadCode
    (m p j : ℕ) (H : PolynomialFieldCode m) :
    PolynomialFieldCode.realize
        (degreeDimensionPadCode m p j H) =
      conjugateField (splitEquiv m p).symm
        (degreePaddedField
          (k := p) (PolynomialFieldCode.realize H) j) := by
  funext x q
  obtain ⟨i | r, rfl⟩ := finSumFinEquiv.surjective q
  · change
      PolynomialFieldCode.realize
          (degreeDimensionPadCode m p j H) x
          (baseIndex m p i) =
        (splitEquiv m p).symm
          (degreePaddedField
            (k := p) (PolynomialFieldCode.realize H) j
            (splitEquiv m p x))
          (baseIndex m p i)
    rw [splitEquiv_symm_baseIndex]
    exact realize_degreeDimensionPadCode_base m p j H x i
  · change
      PolynomialFieldCode.realize
          (degreeDimensionPadCode m p j H) x
          (sinkIndex m p r) =
        (splitEquiv m p).symm
          (degreePaddedField
            (k := p) (PolynomialFieldCode.realize H) j
            (splitEquiv m p x))
          (sinkIndex m p r)
    rw [splitEquiv_symm_sinkIndex]
    exact realize_degreeDimensionPadCode_sink m p j H x r

/-! ## Homogeneity and GAS correctness -/

theorem degreeDimensionPadCode_homogeneous
    (m p j : ℕ) (H : PolynomialFieldCode m)
    (hH :
      PolynomialFieldCode.homogeneous 3 H = true) :
    PolynomialFieldCode.homogeneous (3 + 2 * j)
      (degreeDimensionPadCode m p j H) = true := by
  rw [PolynomialFieldCode.homogeneous_eq_true_iff] at hH ⊢
  intro q
  obtain ⟨i | r, rfl⟩ := finSumFinEquiv.surjective q
  · change
      (PolynomialCode.decode
        (degreeDimensionPadCode m p j H
          (baseIndex m p i))).IsHomogeneous (3 + 2 * j)
    rw [degreeDimensionPadCode_base,
      PolynomialCode.decode_mul_code,
      PolynomialCode.decode_pow_code,
      PolynomialCode.decode_dimensionEmbed]
    have hfactor :
        ((PolynomialCode.decode
          (totalNormSqCode (m + p))) ^ j).IsHomogeneous
            (2 * j) :=
      (totalNormSqCode_isHomogeneous (m + p)).pow j
    have hcoordinate :
        (MvPolynomial.rename (baseIndex m p)
          (PolynomialCode.decode (H i))).IsHomogeneous 3 :=
      MvPolynomial.IsHomogeneous.rename_isHomogeneous (hH i)
    simpa [Nat.add_comm] using hfactor.mul hcoordinate
  · change
      (PolynomialCode.decode
        (degreeDimensionPadCode m p j H
          (sinkIndex m p r))).IsHomogeneous (3 + 2 * j)
    rw [degreeDimensionPadCode_sink,
      PolynomialCode.decode_mul_code,
      PolynomialCode.decode_pow_code,
      PolynomialCode.decode_neg_code,
      PolynomialCode.decode_pow_code,
      PolynomialCode.decode_varCode]
    have hfactor :
        ((PolynomialCode.decode
          (totalNormSqCode (m + p))) ^ j).IsHomogeneous
            (2 * j) :=
      (totalNormSqCode_isHomogeneous (m + p)).pow j
    have hsink :
        (-(MvPolynomial.X (sinkIndex m p r) ^
            3 : MvPolynomial (Fin (m + p)) ℚ)).IsHomogeneous 3 :=
      (MvPolynomial.isHomogeneous_X_pow
        (R := ℚ) (sinkIndex m p r) 3).neg
    simpa [Nat.add_comm] using hfactor.mul hsink

/-- GAS is invariant under the executable padding construction once the
source code is a valid cubic field. -/
theorem globallyAsymptoticallyStable_realize_degreeDimensionPadCode_iff
    (m p j : ℕ) (H : PolynomialFieldCode m)
    (hH :
      PolynomialFieldCode.homogeneous 3 H = true) :
    GloballyAsymptoticallyStable
        (PolynomialFieldCode.realize
          (degreeDimensionPadCode m p j H)) 0 ↔
      GloballyAsymptoticallyStable
        (PolynomialFieldCode.realize H) 0 := by
  have hhomogeneous :
      ∀ i : Fin m,
        (PolynomialCode.decode (H i)).IsHomogeneous 3 :=
    (PolynomialFieldCode.homogeneous_eq_true_iff 3 H).mp hH
  have hzero :
      PolynomialFieldCode.realize H 0 = 0 :=
    polynomialFieldCode_realize_zero_of_homogeneous
      H (by norm_num) hhomogeneous
  rw [realize_degreeDimensionPadCode]
  rw [globallyAsymptoticallyStable_conjugateField_iff]
  exact degreePaddedField_gas_iff
    (PolynomialFieldCode.realize H)
    (contDiff_polynomialFieldCode_realize H) hzero j

/-- Complete language-level correctness on valid cubic source codes. -/
theorem degreeDimensionPadCode_hgasQ_iff_of_homogeneous
    (m p j : ℕ) (H : PolynomialFieldCode m)
    (hH :
      PolynomialFieldCode.homogeneous 3 H = true) :
    HGASQ m 3 H ↔
      HGASQ (m + p) (3 + 2 * j)
        (degreeDimensionPadCode m p j H) := by
  have htarget :=
    degreeDimensionPadCode_homogeneous m p j H hH
  rw [hgasQ_iff_of_homogeneous H hH,
    hgasQ_iff_of_homogeneous
      (degreeDimensionPadCode m p j H) htarget]
  exact
    (globallyAsymptoticallyStable_realize_degreeDimensionPadCode_iff
      m p j H hH).symm

end DegreePaddingCode

end

end HGAS
