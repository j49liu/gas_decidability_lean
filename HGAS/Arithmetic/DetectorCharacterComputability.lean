import HGAS.Arithmetic.DetectorCharacterDegrees
import HGAS.Arithmetic.DQLEnumerability
import HGAS.Clocks.ControllerPhaseProductCharacterComputability
import Mathlib.Tactic

/-!
# Effective compilation of DQL detector characters

For fixed numbers of equations and variables, this file proves that every
finite character datum used by the detector is primitive recursive in the
integer coefficients and in the runtime lattice indices.

There are two representation points worth making explicit.

First, a detector character is naturally indexed by
`Fin vars ⊕ Fin eqs`, whereas the polynomial clock compiler expects an
exponent vector indexed by `Fin (vars + eqs)`.  We equip detector characters
with the primitive coding transported through the canonical *unscaled*
reindexing.  Reindexing and its inverse are primitive recursive.  The
actual `flattenCharacter` then multiplies every exponent by four, matching
the manuscript's convention that the arithmetic clocks are fourth powers
of the fundamental polynomial clocks; this normalization is primitive
recursive but, correctly, is not claimed to be invertible.

Second, the finite DQL code stores coefficients as canonical signed
constructor codes.  We prove directly that decoding those integers and the
signed-magnitude arithmetic used elsewhere in the compiler are primitive
recursive.  This yields reusable primitive-recursive integer negation,
addition, multiplication, and finite summation lemmas.

The resulting theorems cover:

* private, quadratic, linear, right-hand-side, and Poisson characters;
* theta summands and fully expanded detector characters;
* all corresponding sparse polynomial character codes; and
* the `omegaWeights` and `numberWeights` controller-frequency data.

For indexed families we give both a theorem at a fixed index and a theorem
which compiles the complete finite family in one call.
-/

namespace HGAS.DetectorCharacterCode

open HGAS
open HGAS.Clocks.ControllerPhaseProductCharacterCode
open scoped BigOperators

variable {eqs vars : ℕ}

/-! ## Reusable primitive-recursive integer arithmetic -/

/-- The canonical constructor code `ℕ ⊕ ℕ` decodes primitive recursively.

Both the sum encoding and Mathlib's integer encoding use the same zig-zag
layout: `inl n` and the nonnegative integer `n` have code `2n`, while
`inr n` and `Int.negSucc n` have code `2n+1`. -/
theorem signedCodeValue_primrec :
    Primrec signedCodeValue := by
  rw [← Primrec.encode_iff]
  exact
    (Primrec.encode :
      Primrec (fun c : SignedCode ↦ Encodable.encode c)).of_eq
      (by
        intro c
        cases c <;> rfl)

/-- Decoding a possibly noncanonical signed-magnitude integer is primitive
recursive.  In the negative-sign branch, magnitude zero is the second code
for zero; positive magnitude `m` has integer code `2m-1`. -/
theorem signedMagnitudeDecode_primrec :
    Primrec SignedMagnitudeCode.decode := by
  rw [← Primrec.encode_iff]
  have hdouble :
      Primrec (fun z : SignedMagnitudeCode ↦ 2 * z.2) :=
    Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd
  have hzero :
      PrimrecPred (fun z : SignedMagnitudeCode ↦ z.2 = 0) :=
    Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hnegative :
      Primrec (fun z : SignedMagnitudeCode ↦
        if z.2 = 0 then 0 else 2 * z.2 - 1) :=
    Primrec.ite hzero (Primrec.const 0)
      (Primrec.nat_sub.comp hdouble (Primrec.const 1))
  exact
    (Primrec.cond Primrec.fst hnegative hdouble).of_eq
      (by
        intro z
        rcases z with ⟨s, m⟩
        cases s <;> cases m <;> rfl)

/-- Integer negation, implemented through the already executable
signed-magnitude sign toggle. -/
theorem integerNeg_primrec :
    Primrec (fun z : ℤ ↦ -z) := by
  exact
    (signedMagnitudeDecode_primrec.comp
      (SignedMagnitudeCode.neg_primrec.comp
        signedMagnitudeEncode_primrec)).of_eq
      (by
        intro z
        simp)

/-- Integer addition, implemented by signed-magnitude addition. -/
theorem integerAdd_primrec :
    Primrec₂ ((· + ·) : ℤ → ℤ → ℤ) := by
  have hcode :
      Primrec
        (fun p : ℤ × ℤ ↦
          SignedMagnitudeCode.add
            (SignedMagnitudeCode.encode p.1)
            (SignedMagnitudeCode.encode p.2)) :=
    SignedMagnitudeCode.add_primrec.comp
      (signedMagnitudeEncode_primrec.comp Primrec.fst)
      (signedMagnitudeEncode_primrec.comp Primrec.snd)
  exact
    (signedMagnitudeDecode_primrec.comp hcode).of_eq
      (by
        intro p
        simp)

/-- Integer multiplication, implemented by signed-magnitude
multiplication. -/
theorem integerMul_primrec :
    Primrec₂ ((· * ·) : ℤ → ℤ → ℤ) := by
  have hcode :
      Primrec
        (fun p : ℤ × ℤ ↦
          SignedMagnitudeCode.mul
            (SignedMagnitudeCode.encode p.1)
            (SignedMagnitudeCode.encode p.2)) :=
    SignedMagnitudeCode.mul_primrec.comp
      (signedMagnitudeEncode_primrec.comp Primrec.fst)
      (signedMagnitudeEncode_primrec.comp Primrec.snd)
  exact
    (signedMagnitudeDecode_primrec.comp hcode).of_eq
      (by
        intro p
        simp)

/-- Sum a finite list of integers. -/
def integerListSum (l : List ℤ) : ℤ :=
  l.sum

/-- Finite integer summation is primitive recursive. -/
theorem integerListSum_primrec :
    Primrec integerListSum := by
  have hstep :
      Primrec₂
        (fun (_ : List ℤ) (p : ℤ × ℤ) ↦ p.1 + p.2) :=
    integerAdd_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right)
  exact
    (Primrec.list_foldr Primrec.id (Primrec.const 0) hstep).of_eq
      (by
        intro l
        induction l with
        | nil => rfl
        | cons z l ih =>
            have ih' :
                List.foldr (· + ·) 0 l = l.sum := by
              simpa [integerListSum] using ih
            change z + List.foldr (· + ·) 0 l = z + l.sum
            rw [ih'])

/-! ## A transparent coding of detector characters -/

/-- Reindex a detector character without applying the fourth-power clock
normalization.  This map, unlike `flattenCharacter`, is an equivalence. -/
def reindexCharacter
    (a : DetectorPhase eqs vars → ℤ) :
    Fin (clockCount eqs vars) → ℤ :=
  fun i ↦ a (finSumFinEquiv.symm i)

/-- Undo the canonical reindexing of a detector character. -/
def unreindexCharacter
    (a : Fin (clockCount eqs vars) → ℤ) :
    DetectorPhase eqs vars → ℤ :=
  fun phase ↦ a (finSumFinEquiv phase)

@[simp]
theorem unreindexCharacter_reindexCharacter
    (a : DetectorPhase eqs vars → ℤ) :
    unreindexCharacter (reindexCharacter a) = a := by
  funext phase
  simp [unreindexCharacter, reindexCharacter]

@[simp]
theorem reindexCharacter_unreindexCharacter
    (a : Fin (clockCount eqs vars) → ℤ) :
    reindexCharacter (unreindexCharacter a) = a := by
  funext i
  simp [unreindexCharacter, reindexCharacter]

/-- Detector characters and unscaled, reindexed exponent vectors are
canonically equivalent. -/
def detectorCharacterCodingEquiv (eqs vars : ℕ) :
    (DetectorPhase eqs vars → ℤ) ≃
      (Fin (clockCount eqs vars) → ℤ) where
  toFun := reindexCharacter
  invFun := unreindexCharacter
  left_inv := unreindexCharacter_reindexCharacter
  right_inv := reindexCharacter_unreindexCharacter

/-- We code a detector character by its unscaled reindexed exponent tuple.
The actual polynomial compiler subsequently applies the noninvertible
factor-four normalization. -/
instance detectorCharacterPrimcodable (eqs vars : ℕ) :
    Primcodable (DetectorPhase eqs vars → ℤ) :=
  Primcodable.ofEquiv
    (Fin (clockCount eqs vars) → ℤ)
    (detectorCharacterCodingEquiv eqs vars)

/-- Pure reindexing is primitive recursive under the explicit transported
coding above. -/
theorem reindexCharacter_primrec :
    Primrec
      (reindexCharacter :
        (DetectorPhase eqs vars → ℤ) →
          (Fin (clockCount eqs vars) → ℤ)) :=
  Primrec.of_equiv

/-- The inverse reindexing is primitive recursive as well. -/
theorem unreindexCharacter_primrec :
    Primrec
      (unreindexCharacter :
        (Fin (clockCount eqs vars) → ℤ) →
          (DetectorPhase eqs vars → ℤ)) :=
  Primrec.of_equiv_symm

/-- Multiply every entry of a fixed-length integer tuple by four. -/
theorem scaleFourExponents_primrec {q : ℕ} :
    Primrec
      (fun exponents : Fin q → ℤ ↦
        fun i ↦ 4 * exponents i) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro i
  exact
    integerMul_primrec.comp
      (Primrec.const 4)
      (Primrec.fin_app.comp Primrec.id (Primrec.const i))

/-- The manuscript's actual flattening—canonical reindexing followed by
the fourth-power normalization—is primitive recursive. -/
theorem flattenCharacter_primrec :
    Primrec
      (flattenCharacter :
        (DetectorPhase eqs vars → ℤ) →
          (Fin (clockCount eqs vars) → ℤ)) := by
  exact
    (scaleFourExponents_primrec.comp
      (reindexCharacter_primrec
        (eqs := eqs) (vars := vars))).of_eq
      (by
        intro a
        rfl)

/-! ## Primitive-recursive access to DQL coefficients -/

theorem quadraticEntry_primrec
    (row : Fin eqs) (j : Fin vars) :
    Primrec (fun I : DQLSystem eqs vars ↦
      I.quadratic row j) := by
  exact
    (signedCodeValue_primrec.comp
      ((finiteCodeQuadratic_primrec row j).comp
        (dqlSystemCodeEquiv_primrec eqs vars))).of_eq
      (by
        intro I
        simp)

theorem linearEntry_primrec
    (row : Fin eqs) (j : Fin vars) :
    Primrec (fun I : DQLSystem eqs vars ↦
      I.linear row j) := by
  exact
    (signedCodeValue_primrec.comp
      ((finiteCodeLinear_primrec row j).comp
        (dqlSystemCodeEquiv_primrec eqs vars))).of_eq
      (by
        intro I
        simp)

theorem rhsEntry_primrec
    (row : Fin eqs) :
    Primrec (fun I : DQLSystem eqs vars ↦ I.rhs row) := by
  exact
    (signedCodeValue_primrec.comp
      ((finiteCodeRhs_primrec row).comp
        (dqlSystemCodeEquiv_primrec eqs vars))).of_eq
      (by
        intro I
        simp)

/-! ## Unscaled reindexing compilers -/

/-- The complete private-character family is primitive recursive in its
finite index. -/
theorem reindexPrivateCharacter_primrec :
    Primrec
      (fun j : Fin vars ↦
        reindexCharacter
          (privateCharacter (eqs := eqs) j)) :=
  Primrec.dom_finite _

/-- Compile one quadratic-column character. -/
theorem reindexQuadraticCharacter_primrec
    (j : Fin vars) :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        reindexCharacter (quadraticCharacter I j)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro i
  obtain ⟨k | row, rfl⟩ :=
    finSumFinEquiv.surjective i
  · exact
      (Primrec.const 0).of_eq
        (by
          intro I
          simp [reindexCharacter, quadraticCharacter])
  · exact
      (quadraticEntry_primrec row j).of_eq
        (by
          intro I
          simp [reindexCharacter, quadraticCharacter])

/-- Compile one linear-column character. -/
theorem reindexLinearCharacter_primrec
    (j : Fin vars) :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        reindexCharacter (linearCharacter I j)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro i
  obtain ⟨k | row, rfl⟩ :=
    finSumFinEquiv.surjective i
  · exact
      (Primrec.const 0).of_eq
        (by
          intro I
          simp [reindexCharacter, linearCharacter])
  · exact
      (linearEntry_primrec row j).of_eq
        (by
          intro I
          simp [reindexCharacter, linearCharacter])

/-- Compile the global right-hand-side character. -/
theorem reindexRhsCharacter_primrec :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        reindexCharacter (rhsCharacter I)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro i
  obtain ⟨k | row, rfl⟩ :=
    finSumFinEquiv.surjective i
  · exact
      (Primrec.const 0).of_eq
        (by
          intro I
          simp [reindexCharacter, rhsCharacter])
  · exact
      (integerNeg_primrec.comp
        (rhsEntry_primrec row)).of_eq
        (by
          intro I
          simp [reindexCharacter, rhsCharacter])

/-- Compile the Poisson argument `Q_j⁻¹ S_j`. -/
theorem reindexPoissonArgumentCharacter_primrec
    (j : Fin vars) :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        reindexCharacter
          (poissonArgumentCharacter I j)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro i
  obtain ⟨k | row, rfl⟩ :=
    finSumFinEquiv.surjective i
  · exact
      (Primrec.const
        (-(if k = j then (1 : ℤ) else 0))).of_eq
        (by
          intro I
          simp [reindexCharacter, poissonArgumentCharacter,
            privateCharacter, quadraticCharacter])
  · exact
      (quadraticEntry_primrec row j).of_eq
        (by
          intro I
          simp [reindexCharacter, poissonArgumentCharacter,
            privateCharacter, quadraticCharacter])

/-- Runtime input for one theta-character compiler. -/
abbrev ThetaCharacterInput (eqs vars : ℕ) :=
  DQLSystem eqs vars × (Fin vars → ℤ)

/-- Compile the character of one theta summand at a fixed variable index. -/
theorem reindexThetaTermCharacter_primrec
    (j : Fin vars) :
    Primrec
      (fun input : ThetaCharacterInput eqs vars ↦
        reindexCharacter
          (thetaTermCharacter input.1 input.2 j)) := by
  have hx :
      Primrec
        (fun input : ThetaCharacterInput eqs vars ↦ input.2 j) :=
    Primrec.fin_app.comp Primrec.snd (Primrec.const j)
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro i
  obtain ⟨k | row, rfl⟩ :=
    finSumFinEquiv.surjective i
  · by_cases hkj : k = j
    · subst k
      exact
        (integerMul_primrec.comp hx hx).of_eq
          (by
            intro input
            simp [reindexCharacter, thetaTermCharacter,
              privateCharacter, linearCharacter, pow_two])
    · exact
        (Primrec.const 0).of_eq
          (by
            intro input
            simp [reindexCharacter, thetaTermCharacter,
              privateCharacter, linearCharacter, hkj])
  · have hlinear :
        Primrec
          (fun input : ThetaCharacterInput eqs vars ↦
            input.1.linear row j) :=
      (linearEntry_primrec row j).comp Primrec.fst
    exact
      (integerMul_primrec.comp hx hlinear).of_eq
        (by
          intro input
          simp [reindexCharacter, thetaTermCharacter,
            privateCharacter, linearCharacter])

/-- Runtime input for a fully expanded detector character. -/
abbrev ExpandedCharacterInput (eqs vars : ℕ) :=
  DQLSystem eqs vars ×
    ((Fin vars → ℤ) × (Fin vars → ℤ))

/-- Compile the character of one fully expanded detector term, uniformly
in the system and both integer index vectors. -/
theorem reindexExpandedTermCharacter_primrec :
    Primrec
      (fun input : ExpandedCharacterInput eqs vars ↦
        reindexCharacter
          (expandedTermCharacter
            input.1 input.2.1 input.2.2)) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro i
  obtain ⟨k | row, rfl⟩ :=
    finSumFinEquiv.surjective i
  · have hx :
        Primrec
          (fun input : ExpandedCharacterInput eqs vars ↦
            input.2.1 k) :=
      Primrec.fin_app.comp
        (Primrec.fst.comp Primrec.snd)
        (Primrec.const k)
    have hs :
        Primrec
          (fun input : ExpandedCharacterInput eqs vars ↦
            input.2.2 k) :=
      Primrec.fin_app.comp
        (Primrec.snd.comp Primrec.snd)
        (Primrec.const k)
    exact
      (integerAdd_primrec.comp
        (integerMul_primrec.comp hx hx)
        (integerNeg_primrec.comp hs)).of_eq
        (by
          intro input
          simp [reindexCharacter,
            expandedTermCharacter_eq_detectorExponent,
            detectorExponent, privatePhaseExponent, pow_two,
            sub_eq_add_neg])
  · have hterms :
        Primrec
          (fun input : ExpandedCharacterInput eqs vars ↦
            List.ofFn fun j : Fin vars ↦
              input.1.quadratic row j * input.2.2 j +
                input.1.linear row j * input.2.1 j) := by
      apply Primrec.list_ofFn
      intro j
      have hq :
          Primrec
            (fun input : ExpandedCharacterInput eqs vars ↦
              input.1.quadratic row j) :=
        (quadraticEntry_primrec row j).comp Primrec.fst
      have hl :
          Primrec
            (fun input : ExpandedCharacterInput eqs vars ↦
              input.1.linear row j) :=
        (linearEntry_primrec row j).comp Primrec.fst
      have hx :
          Primrec
            (fun input : ExpandedCharacterInput eqs vars ↦
              input.2.1 j) :=
        Primrec.fin_app.comp
          (Primrec.fst.comp Primrec.snd)
          (Primrec.const j)
      have hs :
          Primrec
            (fun input : ExpandedCharacterInput eqs vars ↦
              input.2.2 j) :=
        Primrec.fin_app.comp
          (Primrec.snd.comp Primrec.snd)
          (Primrec.const j)
      exact
        integerAdd_primrec.comp
          (integerMul_primrec.comp hq hs)
          (integerMul_primrec.comp hl hx)
    have hrhs :
        Primrec
          (fun input : ExpandedCharacterInput eqs vars ↦
            input.1.rhs row) :=
      (rhsEntry_primrec row).comp Primrec.fst
    exact
      (integerAdd_primrec.comp
        (integerListSum_primrec.comp hterms)
        (integerNeg_primrec.comp hrhs)).of_eq
        (by
          intro input
          simp [integerListSum, reindexCharacter,
            expandedTermCharacter_eq_detectorExponent,
            detectorExponent, equationPhaseExponent,
            List.sum_ofFn, sub_eq_add_neg])

/-! ## Direct sum-indexed character compilers -/

theorem privateCharacter_primrec :
    Primrec
      (privateCharacter (eqs := eqs) :
        Fin vars → DetectorPhase eqs vars → ℤ) :=
  Primrec.dom_finite _

theorem quadraticCharacter_primrec
    (j : Fin vars) :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        quadraticCharacter I j) := by
  exact
    (unreindexCharacter_primrec.comp
      (reindexQuadraticCharacter_primrec j)).of_eq
      (by
        intro I
        simp)

theorem linearCharacter_primrec
    (j : Fin vars) :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        linearCharacter I j) := by
  exact
    (unreindexCharacter_primrec.comp
      (reindexLinearCharacter_primrec j)).of_eq
      (by
        intro I
        simp)

theorem rhsCharacter_primrec :
    Primrec
      (rhsCharacter :
        DQLSystem eqs vars →
          DetectorPhase eqs vars → ℤ) := by
  exact
    (unreindexCharacter_primrec.comp
      reindexRhsCharacter_primrec).of_eq
      (by
        intro I
        simp)

theorem poissonArgumentCharacter_primrec
    (j : Fin vars) :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        poissonArgumentCharacter I j) := by
  exact
    (unreindexCharacter_primrec.comp
      (reindexPoissonArgumentCharacter_primrec j)).of_eq
      (by
        intro I
        simp)

theorem thetaTermCharacter_primrec
    (j : Fin vars) :
    Primrec
      (fun input : ThetaCharacterInput eqs vars ↦
        thetaTermCharacter input.1 input.2 j) := by
  exact
    (unreindexCharacter_primrec.comp
      (reindexThetaTermCharacter_primrec j)).of_eq
      (by
        intro input
        simp)

theorem expandedTermCharacter_primrec :
    Primrec
      (fun input : ExpandedCharacterInput eqs vars ↦
        expandedTermCharacter
          input.1 input.2.1 input.2.2) := by
  exact
    (unreindexCharacter_primrec.comp
      reindexExpandedTermCharacter_primrec).of_eq
      (by
        intro input
        simp)

/-! ## Normalized flattened character compilers -/

/-- Compile the full private-character family in fundamental-clock
coordinates, including the required factor four. -/
theorem flattenPrivateCharacter_primrec :
    Primrec
      (fun j : Fin vars ↦
        flattenCharacter
          (privateCharacter (eqs := eqs) j)) :=
  flattenCharacter_primrec.comp privateCharacter_primrec

theorem flattenQuadraticCharacter_primrec
    (j : Fin vars) :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        flattenCharacter (quadraticCharacter I j)) :=
  flattenCharacter_primrec.comp
    (quadraticCharacter_primrec j)

theorem flattenLinearCharacter_primrec
    (j : Fin vars) :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        flattenCharacter (linearCharacter I j)) :=
  flattenCharacter_primrec.comp
    (linearCharacter_primrec j)

theorem flattenRhsCharacter_primrec :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        flattenCharacter (rhsCharacter I)) :=
  flattenCharacter_primrec.comp rhsCharacter_primrec

theorem flattenPoissonArgumentCharacter_primrec
    (j : Fin vars) :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        flattenCharacter
          (poissonArgumentCharacter I j)) :=
  flattenCharacter_primrec.comp
    (poissonArgumentCharacter_primrec j)

theorem flattenThetaTermCharacter_primrec
    (j : Fin vars) :
    Primrec
      (fun input : ThetaCharacterInput eqs vars ↦
        flattenCharacter
          (thetaTermCharacter input.1 input.2 j)) :=
  flattenCharacter_primrec.comp
    (thetaTermCharacter_primrec j)

theorem flattenExpandedTermCharacter_primrec :
    Primrec
      (fun input : ExpandedCharacterInput eqs vars ↦
        flattenCharacter
          (expandedTermCharacter
            input.1 input.2.1 input.2.2)) :=
  flattenCharacter_primrec.comp
    expandedTermCharacter_primrec

/-! ## Complete finite character families -/

theorem quadraticCharacters_primrec :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        fun j ↦ quadraticCharacter I j) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro j
  exact quadraticCharacter_primrec j

theorem linearCharacters_primrec :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        fun j ↦ linearCharacter I j) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro j
  exact linearCharacter_primrec j

theorem poissonArgumentCharacters_primrec :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        fun j ↦ poissonArgumentCharacter I j) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro j
  exact poissonArgumentCharacter_primrec j

theorem thetaTermCharacters_primrec :
    Primrec
      (fun input : ThetaCharacterInput eqs vars ↦
        fun j ↦ thetaTermCharacter input.1 input.2 j) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro j
  exact thetaTermCharacter_primrec j

/-! ## Sparse polynomial-code compilers -/

theorem privateCode_primrec :
    Primrec
      (privateCode (eqs := eqs) :
        Fin vars →
          ComplexPairCode
            (HGAS.Clocks.ControllerPhaseProductPolynomialCode.dimension
              (clockCount eqs vars))) :=
  characterCode_primrec.comp flattenPrivateCharacter_primrec

theorem quadraticCode_primrec
    (j : Fin vars) :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        quadraticCode I j) :=
  characterCode_primrec.comp
    (flattenQuadraticCharacter_primrec j)

theorem linearCode_primrec
    (j : Fin vars) :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        linearCode I j) :=
  characterCode_primrec.comp
    (flattenLinearCharacter_primrec j)

theorem rhsCode_primrec :
    Primrec
      (rhsCode :
        DQLSystem eqs vars →
          ComplexPairCode
            (HGAS.Clocks.ControllerPhaseProductPolynomialCode.dimension
              (clockCount eqs vars))) :=
  characterCode_primrec.comp flattenRhsCharacter_primrec

theorem poissonArgumentCode_primrec
    (j : Fin vars) :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        poissonArgumentCode I j) :=
  characterCode_primrec.comp
    (flattenPoissonArgumentCharacter_primrec j)

theorem thetaTermCode_primrec
    (j : Fin vars) :
    Primrec
      (fun input : ThetaCharacterInput eqs vars ↦
        thetaTermCode input.1 input.2 j) :=
  characterCode_primrec.comp
    (flattenThetaTermCharacter_primrec j)

theorem expandedTermCode_primrec :
    Primrec
      (fun input : ExpandedCharacterInput eqs vars ↦
        expandedTermCode
          input.1 input.2.1 input.2.2) :=
  characterCode_primrec.comp
    flattenExpandedTermCharacter_primrec

theorem quadraticCodes_primrec :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        fun j ↦ quadraticCode I j) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro j
  exact quadraticCode_primrec j

theorem linearCodes_primrec :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        fun j ↦ linearCode I j) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro j
  exact linearCode_primrec j

theorem poissonArgumentCodes_primrec :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        fun j ↦ poissonArgumentCode I j) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro j
  exact poissonArgumentCode_primrec j

theorem thetaTermCodes_primrec :
    Primrec
      (fun input : ThetaCharacterInput eqs vars ↦
        fun j ↦ thetaTermCode input.1 input.2 j) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro j
  exact thetaTermCode_primrec j

/-! ## Controller-frequency weights -/

/-- The complete private-clock weight tuple is primitive recursive in
`j`. -/
theorem omegaWeights_primrec :
    Primrec
      (omegaWeights (eqs := eqs) :
        Fin vars →
          Fin (clockCount eqs vars) → RationalCode) :=
  exponentWeights_primrec.comp flattenPrivateCharacter_primrec

/-- The number-observable weights at a fixed variable index are primitive
recursive in the DQL system. -/
theorem numberWeights_primrec
    (j : Fin vars) :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        numberWeights I j) :=
  exponentWeights_primrec.comp
    (flattenLinearCharacter_primrec j)

/-- Compile the complete family of number-observable weight tuples. -/
theorem numberWeightFamily_primrec :
    Primrec
      (fun I : DQLSystem eqs vars ↦
        fun j ↦ numberWeights I j) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro j
  exact numberWeights_primrec j

/-! ## Linear frequency-readout compilers -/

set_option maxHeartbeats 800000 in
-- The linear-code compiler has nested finite-function encodings.
/-- At a fixed private index, the controller polynomial obtained from
`omegaWeights` is primitive recursive in the rational parameter tuple. -/
theorem omegaFrequencyCode_primrec
    (j : Fin vars) :
    Primrec
      (fun parameters :
          Fin (clockCount eqs vars) → RationalCode ↦
        HGAS.Clocks.ControllerPhaseProductLinearFrequencyCode.code
          (omegaWeights (eqs := eqs) j) parameters) := by
  exact
    HGAS.Clocks.ControllerPhaseProductLinearFrequencyCode.code_primrec.comp
      (Primrec.pair
        (Primrec.const (omegaWeights (eqs := eqs) j))
        Primrec.id)

/-- Compile all private-frequency readout polynomials simultaneously. -/
theorem omegaFrequencyCodeFamily_primrec :
    Primrec
      (fun parameters :
          Fin (clockCount eqs vars) → RationalCode ↦
        fun j ↦
          HGAS.Clocks.ControllerPhaseProductLinearFrequencyCode.code
            (omegaWeights (eqs := eqs) j) parameters) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro j
  exact omegaFrequencyCode_primrec j

/-- Runtime input for the number-observable frequency compiler. -/
abbrev NumberFrequencyInput (eqs vars : ℕ) :=
  DQLSystem eqs vars ×
    (Fin (clockCount eqs vars) → RationalCode)

set_option maxHeartbeats 800000 in
-- Composition through two nested finite tuples is costly to elaborate.
/-- At a fixed variable index, the `numberWeights` frequency polynomial is
primitive recursive jointly in the DQL system and controller parameters. -/
theorem numberFrequencyCode_primrec
    (j : Fin vars) :
    Primrec
      (fun input : NumberFrequencyInput eqs vars ↦
        HGAS.Clocks.ControllerPhaseProductLinearFrequencyCode.code
          (numberWeights input.1 j) input.2) := by
  exact
    HGAS.Clocks.ControllerPhaseProductLinearFrequencyCode.code_primrec.comp
      (Primrec.pair
        ((numberWeights_primrec j).comp Primrec.fst)
        Primrec.snd)

/-- Compile all number-observable frequency readouts simultaneously. -/
theorem numberFrequencyCodeFamily_primrec :
    Primrec
      (fun input : NumberFrequencyInput eqs vars ↦
        fun j ↦
          HGAS.Clocks.ControllerPhaseProductLinearFrequencyCode.code
            (numberWeights input.1 j) input.2) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro j
  exact numberFrequencyCode_primrec j

/-! ## Computable corollaries -/

theorem expandedTermCharacter_computable :
    Computable
      (fun input : ExpandedCharacterInput eqs vars ↦
        expandedTermCharacter
          input.1 input.2.1 input.2.2) :=
  expandedTermCharacter_primrec.to_comp

theorem expandedTermCode_computable :
    Computable
      (fun input : ExpandedCharacterInput eqs vars ↦
        expandedTermCode input.1 input.2.1 input.2.2) :=
  expandedTermCode_primrec.to_comp

theorem numberFrequencyCodeFamily_computable :
    Computable
      (fun input : NumberFrequencyInput eqs vars ↦
        fun j ↦
          HGAS.Clocks.ControllerPhaseProductLinearFrequencyCode.code
            (numberWeights input.1 j) input.2) :=
  numberFrequencyCodeFamily_primrec.to_comp

theorem quadraticLinearPoissonCodeFamilies_computable :
    Computable
      (fun I : DQLSystem eqs vars ↦
        (fun j ↦ quadraticCode I j,
          fun j ↦ linearCode I j,
          fun j ↦ poissonArgumentCode I j)) := by
  exact Computable.pair
    quadraticCodes_primrec.to_comp
    (Computable.pair
      linearCodes_primrec.to_comp
      poissonArgumentCodes_primrec.to_comp)

end HGAS.DetectorCharacterCode
