import HGAS.Arithmetic.SparseCipherCircuit
import HGAS.Arithmetic.ExpressionCircuitSemantics
import HGAS.Arithmetic.FiniteDiophantineExtraction
import Mathlib.Tactic

/-!
# Bounded universal quantification by sparse ciphers

This module assembles the reusable pieces of Matiyasevich's sparse-cipher
argument into the closure theorem needed at the DPRM boundary.

Let `set` be a Diophantine relation in `m` outer parameters and one
additional index.  The relation constructed here has the same `m`
parameters together with a bound `length`, and asserts

```
  ∀ index < length, (parameters, index) ∈ set.
```

For a fixed finite Diophantine representation of `set`, its polynomial
equation is compiled to a finite arithmetic circuit.  Every circuit
register is then transposed across all `index < length` and stored as one
sparse cipher.  Constant ciphers hold the outer parameters, `CodeNat`
holds `0,1,...,length-1`, and the parallel circuit relation verifies all
polynomial witnesses simultaneously.

The proof remains finite and explicit throughout.  In particular, the
Diophantine certificate below uses only:

* `Code`, `ConstCode`, and `CodeNat`;
* coordinatewise cipher addition and multiplication;
* a fixed finite conjunction, one for each gate/register.

No DPRM closure theorem is assumed.
-/

namespace HGAS

namespace SparseBoundedForall

open SparseCipherCode
open SparseCipherIndex
open SparseCipherCircuit
open SparseOnesCipher
open PolynomialGateCompiler

variable {m : ℕ}

/-! ## The semantic bounded-universal relation -/

/-- The first `m` visible coordinates are the outer parameters. -/
def outerParameters
    (visible : Fin (m + 1) → ℕ) : Fin m → ℕ :=
  fun i => visible (Fin.castAdd 1 i)

/-- The final visible coordinate is the exclusive upper bound. -/
def visibleBound
    (visible : Fin (m + 1) → ℕ) : ℕ :=
  visible (Fin.natAdd m (0 : Fin 1))

/-- Insert a concrete index after the `m` outer parameters. -/
def indexedParameters
    (visible : Fin (m + 1) → ℕ) (index : ℕ) :
    Fin (m + 1) → ℕ :=
  Fin.append (outerParameters visible) (fun _ : Fin 1 => index)

/-- Bounded universal quantification of a relation with one distinguished
last argument. -/
def BoundedForall
    (set : Set (Fin (m + 1) → ℕ)) :
    Set (Fin (m + 1) → ℕ) :=
  {visible |
    ∀ index, index < visibleBound visible →
      indexedParameters visible index ∈ set}

/-! ## The fixed polynomial circuit -/

/-- Positive natural expression associated with the representing integer
polynomial. -/
def positiveExpression
    {set : Set (Fin (m + 1) → ℕ)}
    (representation :
      FiniteDiophantineRepresentation (m + 1) set) :
    NaturalArithmeticExpression
      ((m + 1) + representation.witnessCount) :=
  NaturalArithmeticExpression.ofPolynomialForward
    (IntegerPolynomialCode.positivePart representation.polynomial)

/-- Negative natural expression associated with the representing integer
polynomial. -/
def negativeExpression
    {set : Set (Fin (m + 1) → ℕ)}
    (representation :
      FiniteDiophantineRepresentation (m + 1) set) :
    NaturalArithmeticExpression
      ((m + 1) + representation.witnessCount) :=
  NaturalArithmeticExpression.ofPolynomialForward
    (IntegerPolynomialCode.negativePart representation.polynomial)

/-- Number of registers in the compiled equation circuit. -/
def circuitVariableCount
    {set : Set (Fin (m + 1) → ℕ)}
    (representation :
      FiniteDiophantineRepresentation (m + 1) set) : ℕ :=
  expressionEquationVariableCount
    (positiveExpression representation)
    (negativeExpression representation)

/-- The fixed arithmetic circuit for the representing polynomial. -/
def polynomialCircuit
    {set : Set (Fin (m + 1) → ℕ)}
    (representation :
      FiniteDiophantineRepresentation (m + 1) set) :
    List (ArithmeticGate (circuitVariableCount representation)) :=
  expressionEquationCircuit
    (positiveExpression representation)
    (negativeExpression representation)

/-- Circuit register containing one input of the representing
polynomial. -/
def polynomialInputRegister
    {set : Set (Fin (m + 1) → ℕ)}
    (representation :
      FiniteDiophantineRepresentation (m + 1) set)
    (input :
      Fin ((m + 1) + representation.witnessCount)) :
    Fin (circuitVariableCount representation) :=
  expressionEquationInput
    (positiveExpression representation)
    (negativeExpression representation) input

/-- Polynomial input occupied by outer parameter `i`. -/
def outerPolynomialInput
    {set : Set (Fin (m + 1) → ℕ)}
    (representation :
      FiniteDiophantineRepresentation (m + 1) set)
    (i : Fin m) :
    Fin ((m + 1) + representation.witnessCount) :=
  Fin.castAdd representation.witnessCount
    (Fin.castAdd 1 i)

/-- Polynomial input occupied by the distinguished index. -/
def indexPolynomialInput
    {set : Set (Fin (m + 1) → ℕ)}
    (representation :
      FiniteDiophantineRepresentation (m + 1) set) :
    Fin ((m + 1) + representation.witnessCount) :=
  Fin.castAdd representation.witnessCount
    (Fin.natAdd m (0 : Fin 1))

/-- Circuit register occupied by outer parameter `i`. -/
def outerRegister
    {set : Set (Fin (m + 1) → ℕ)}
    (representation :
      FiniteDiophantineRepresentation (m + 1) set)
    (i : Fin m) :
    Fin (circuitVariableCount representation) :=
  polynomialInputRegister representation
    (outerPolynomialInput representation i)

/-- Circuit register occupied by the distinguished index. -/
def indexRegister
    {set : Set (Fin (m + 1) → ℕ)}
    (representation :
      FiniteDiophantineRepresentation (m + 1) set) :
    Fin (circuitVariableCount representation) :=
  polynomialInputRegister representation
    (indexPolynomialInput representation)

/-! ## The finite numeric certificate -/

/-- The semantic sparse-cipher certificate.  Its witnesses are one common
radix parameter `q` and one numeric cipher for every circuit register. -/
def CipherCertificate
    {set : Set (Fin (m + 1) → ℕ)}
    (representation :
      FiniteDiophantineRepresentation (m + 1) set)
    (visible : Fin (m + 1) → ℕ) : Prop :=
  ∃ q : ℕ,
    ∃ code : Fin (circuitVariableCount representation) → ℕ,
      CipherCircuitHolds
        (polynomialCircuit representation)
        (visibleBound visible) q code ∧
      CodeNat (visibleBound visible) q
        (code (indexRegister representation)) ∧
      ∀ i : Fin m,
        ConstCode (visibleBound visible) q
          (outerParameters visible i)
          (code (outerRegister representation i))

/-- Hidden coordinate block: the common radix followed by the register
ciphers. -/
abbrev CipherWitness
    {set : Set (Fin (m + 1) → ℕ)}
    (representation :
      FiniteDiophantineRepresentation (m + 1) set) :=
  Fin 1 ⊕ Fin (circuitVariableCount representation)

/-- The same certificate with all witnesses exposed as coordinates. -/
def CipherCore
    {set : Set (Fin (m + 1) → ℕ)}
    (representation :
      FiniteDiophantineRepresentation (m + 1) set)
    (value :
      (Fin (m + 1) ⊕ CipherWitness representation) → ℕ) : Prop :=
  CipherCircuitHolds
      (polynomialCircuit representation)
      (value (Sum.inl (Fin.natAdd m (0 : Fin 1))))
      (value (Sum.inr (Sum.inl 0)))
      (fun register =>
        value (Sum.inr (Sum.inr register))) ∧
    CodeNat
      (value (Sum.inl (Fin.natAdd m (0 : Fin 1))))
      (value (Sum.inr (Sum.inl 0)))
      (value
        (Sum.inr
          (Sum.inr (indexRegister representation)))) ∧
    ∀ i : Fin m,
      ConstCode
        (value (Sum.inl (Fin.natAdd m (0 : Fin 1))))
        (value (Sum.inr (Sum.inl 0)))
        (value (Sum.inl (Fin.castAdd 1 i)))
        (value
          (Sum.inr
            (Sum.inr (outerRegister representation i))))

/-- The exposed finite certificate is Diophantine. -/
theorem cipherCore_dioph
    {set : Set (Fin (m + 1) → ℕ)}
    (representation :
      FiniteDiophantineRepresentation (m + 1) set) :
    Dioph {value :
      (Fin (m + 1) ⊕ CipherWitness representation) → ℕ |
        CipherCore representation value} := by
  let combined :=
    Fin (m + 1) ⊕ CipherWitness representation
  let lengthCoordinate : combined :=
    Sum.inl (Fin.natAdd m (0 : Fin 1))
  let qCoordinate : combined :=
    Sum.inr (Sum.inl 0)
  let registerCoordinate
      (register : Fin (circuitVariableCount representation)) :
      combined :=
    Sum.inr (Sum.inr register)
  have hCircuit :
      Dioph {value : combined → ℕ |
        CipherCircuitHolds
          (polynomialCircuit representation)
          (value lengthCoordinate)
          (value qCoordinate)
          (fun register =>
            value (registerCoordinate register))} := by
    exact
      Dioph.reindex_dioph combined
        (Sum.elim
          ![lengthCoordinate, qCoordinate]
          registerCoordinate)
        (cipherCircuit_dioph
          (polynomialCircuit representation))
  have hIndex :
      Dioph {value : combined → ℕ |
        CodeNat
          (value lengthCoordinate)
          (value qCoordinate)
          (value
            (registerCoordinate
              (indexRegister representation)))} := by
    exact
      Dioph.reindex_dioph combined
        ![lengthCoordinate, qCoordinate,
          registerCoordinate (indexRegister representation)]
        codeNat_dioph
  have hConstants :
      Dioph {value : combined → ℕ |
        ∀ i : Fin m,
          ConstCode
            (value lengthCoordinate)
            (value qCoordinate)
            (value (Sum.inl (Fin.castAdd 1 i)))
            (value
              (registerCoordinate
                (outerRegister representation i)))} := by
    apply dioph_forall_fin
    intro i
    exact
      Dioph.reindex_dioph combined
        ![lengthCoordinate, qCoordinate,
          Sum.inl (Fin.castAdd 1 i),
          registerCoordinate (outerRegister representation i)]
        constCode_dioph
  exact
    Dioph.ext
      (hCircuit.inter (hIndex.inter hConstants))
      fun value => by
        rfl

/-- Hiding the finite witness block proves that the semantic certificate
is Diophantine in its visible parameters. -/
theorem cipherCertificate_dioph
    {set : Set (Fin (m + 1) → ℕ)}
    (representation :
      FiniteDiophantineRepresentation (m + 1) set) :
    Dioph {visible : Fin (m + 1) → ℕ |
      CipherCertificate representation visible} := by
  have hhidden :=
    Dioph.ex_dioph (cipherCore_dioph representation)
  refine
    Dioph.ext hhidden fun visible => ?_
  constructor
  · rintro ⟨witness, hcore⟩
    refine
      ⟨witness (Sum.inl 0),
        fun register => witness (Sum.inr register), ?_⟩
    simpa [CipherCore, visibleBound, outerParameters] using hcore
  · rintro ⟨q, code, hcertificate⟩
    let witness : CipherWitness representation → ℕ :=
      Sum.elim (fun _ : Fin 1 => q) code
    refine ⟨witness, ?_⟩
    simpa [CipherCore, visibleBound, outerParameters, witness] using
      hcertificate

/-! ## Semantic correctness of the certificate -/

/-- Equality of the two compiled natural expressions is exactly
vanishing of the representing integer polynomial. -/
theorem expressions_equal_iff_polynomial_zero
    {set : Set (Fin (m + 1) → ℕ)}
    (representation :
      FiniteDiophantineRepresentation (m + 1) set)
    (input :
      Fin ((m + 1) + representation.witnessCount) → ℕ) :
    (positiveExpression representation).eval input =
        (negativeExpression representation).eval input ↔
      IntegerPolynomialCode.eval representation.polynomial input = 0 := by
  simp only [positiveExpression, negativeExpression,
    NaturalArithmeticExpression.eval_ofPolynomialForward]
  exact
    IntegerPolynomialCode.positivePart_eq_negativePart_iff
      representation.polynomial input

/-- Decode a sparse-cipher certificate at a concrete position.  The
distinguished cipher supplies the position itself, constant ciphers
supply the outer parameters, and the parallel circuit supplies a
polynomial witness. -/
theorem boundedForall_of_cipherCertificate
    {set : Set (Fin (m + 1) → ℕ)}
    (representation :
      FiniteDiophantineRepresentation (m + 1) set)
    {visible : Fin (m + 1) → ℕ}
    (hcertificate :
      CipherCertificate representation visible) :
    visible ∈ BoundedForall set := by
  rintro index hindex
  rcases hcertificate with
    ⟨q, code, hcircuit, hindexCode, hconstants⟩
  obtain ⟨entry, hentry, hgates⟩ :=
    (cipherCircuit_spec
      (polynomialCircuit representation) code).mp hcircuit
  let position : Fin (visibleBound visible) :=
    ⟨index, hindex⟩
  have hindexEntry :
      entry (indexRegister representation) =
        fun i : Fin (visibleBound visible) => (i : ℕ) := by
    exact
      (hentry (indexRegister representation)).entry_eq
        hindexCode
  have hconstantEntry :
      ∀ i : Fin m,
        ∀ position : Fin (visibleBound visible),
          entry (outerRegister representation i) position =
            outerParameters visible i := by
    intro i
    exact
      (constCode_spec
        (hentry (outerRegister representation i))).mp
        (hconstants i)
  have hnaturalCircuit :
      GateDQLCompiler.NaturalCircuitHolds
        (polynomialCircuit representation)
        (fun register => entry register position) := by
    apply
      (natGatesHold_iff_naturalCircuitHolds
        (polynomialCircuit representation)
        (fun register => entry register position)).mp
    intro gateIndex
    exact hgates gateIndex position
  have hequation :=
    expressionEquationCircuit_holds_implies_eval_eq
      (positiveExpression representation)
      (negativeExpression representation)
      (fun register => entry register position)
      hnaturalCircuit
  let input :
      Fin ((m + 1) + representation.witnessCount) → ℕ :=
    fun coordinate =>
      entry (polynomialInputRegister representation coordinate)
        position
  let witnesses : Fin representation.witnessCount → ℕ :=
    fun witness =>
      input (Fin.natAdd (m + 1) witness)
  have hsourceInputs :
      ∀ source : Fin (m + 1),
        input
            (Fin.castAdd representation.witnessCount source) =
          indexedParameters visible index source := by
    intro source
    induction source using Fin.addCases with
    | left i =>
        simpa [input, outerRegister, outerPolynomialInput,
          polynomialInputRegister, indexedParameters] using
            hconstantEntry i position
    | right i =>
        fin_cases i
        have hposition :=
          congrFun hindexEntry position
        simpa [input, indexRegister, indexPolynomialInput,
          polynomialInputRegister, indexedParameters, position] using
            hposition
  have hinputSplit :
      input =
        Fin.append
          (indexedParameters visible index) witnesses := by
    funext coordinate
    induction coordinate using Fin.addCases with
    | left source =>
        simpa [Fin.append] using hsourceInputs source
    | right witness =>
        simp [witnesses, Fin.append]
  have hzero :
      IntegerPolynomialCode.eval
        representation.polynomial input = 0 := by
    apply
      (expressions_equal_iff_polynomial_zero
        representation input).mp
    simpa [input] using hequation
  apply
    (representation.represents
      (indexedParameters visible index)).2
  refine ⟨witnesses, ?_⟩
  change
    IntegerPolynomialCode.eval representation.polynomial
      (Fin.append
        (indexedParameters visible index) witnesses) = 0
  rw [← hinputSplit]
  exact hzero

/-- Conversely, pointwise polynomial witnesses for every index below the
bound can be transposed into register sequences and encoded with one
common sufficiently large sparse radix. -/
theorem cipherCertificate_of_boundedForall
    {set : Set (Fin (m + 1) → ℕ)}
    (representation :
      FiniteDiophantineRepresentation (m + 1) set)
    {visible : Fin (m + 1) → ℕ}
    (hbounded : visible ∈ BoundedForall set) :
    CipherCertificate representation visible := by
  classical
  have hwitnessExists :
      ∀ position : Fin (visibleBound visible),
        ∃ witnesses : Fin representation.witnessCount → ℕ,
          IntegerPolynomialCode.eval representation.polynomial
            (Fin.append
              (indexedParameters visible (position : ℕ))
              witnesses) = 0 := by
    intro position
    have hmember :
        indexedParameters visible (position : ℕ) ∈ set :=
      hbounded position position.isLt
    have hrepresented :=
      (representation.represents
        (indexedParameters visible (position : ℕ))).mp hmember
    simpa only [Fin.append] using hrepresented
  choose polynomialWitness hpolynomial using hwitnessExists
  let input
      (position : Fin (visibleBound visible)) :
      Fin ((m + 1) + representation.witnessCount) → ℕ :=
    Fin.append
      (indexedParameters visible (position : ℕ))
      (polynomialWitness position)
  have hequation :
      ∀ position : Fin (visibleBound visible),
        (positiveExpression representation).eval
            (input position) =
          (negativeExpression representation).eval
            (input position) := by
    intro position
    apply
      (expressions_equal_iff_polynomial_zero
        representation (input position)).mpr
    simpa [input] using hpolynomial position
  have hcircuitExists :
      ∀ position : Fin (visibleBound visible),
        ∃ value : Fin (circuitVariableCount representation) → ℕ,
          GateDQLCompiler.NaturalCircuitHolds
            (polynomialCircuit representation) value ∧
          ∀ coordinate :
              Fin ((m + 1) + representation.witnessCount),
            value
                (polynomialInputRegister representation coordinate) =
              input position coordinate := by
    intro position
    exact
      exists_expressionEquationCircuit_holds_agrees
        (positiveExpression representation)
        (negativeExpression representation)
        (input position) (hequation position)
  choose circuitValue hcircuit hinputs using hcircuitExists
  let entry
      (register : Fin (circuitVariableCount representation))
      (position : Fin (visibleBound visible)) : ℕ :=
    circuitValue position register
  let total : ℕ :=
    ∑ position : Fin (visibleBound visible),
      ∑ register : Fin (circuitVariableCount representation),
        entry register position
  let q : ℕ :=
    visibleBound visible + total + 2
  have hlengthQ :
      visibleBound visible + 1 < q := by
    simp [q]
  have hentryLeTotal :
      ∀ register : Fin (circuitVariableCount representation),
        ∀ position : Fin (visibleBound visible),
          entry register position ≤ total := by
    intro register position
    have hregister :
        entry register position ≤
          ∑ other : Fin (circuitVariableCount representation),
            entry other position := by
      exact
        Finset.single_le_sum
          (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ register)
    have hposition :
        (∑ other : Fin (circuitVariableCount representation),
            entry other position) ≤ total := by
      simpa only [total] using
        Finset.single_le_sum
          (f := fun
            otherPosition : Fin (visibleBound visible) =>
              ∑ other :
                  Fin (circuitVariableCount representation),
                entry other otherPosition)
          (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ position)
    exact hregister.trans hposition
  have hentryBound :
      ∀ register : Fin (circuitVariableCount representation),
        ∀ position : Fin (visibleBound visible),
          entry register position < entryBase q := by
    intro register position
    have hltq : entry register position < q := by
      have hle := hentryLeTotal register position
      simp only [q]
      omega
    have hqpow : q < 2 ^ q :=
      Nat.lt_two_pow_self
    exact hltq.trans (by
      simpa only [entryBase] using hqpow)
  let code
      (register : Fin (circuitVariableCount representation)) : ℕ :=
    SparseRadixCipher.encode (cipherBase q) (entry register)
  have hentryCipher :
      ∀ register : Fin (circuitVariableCount representation),
        CipherOf (visibleBound visible) q
          (entry register) (code register) := by
    intro register
    refine
      ⟨hlengthQ, hentryBound register, ?_⟩
    simp only [code]
  have hcipherCircuit :
      CipherCircuitHolds
        (polynomialCircuit representation)
        (visibleBound visible) q code := by
    apply
      (cipherCircuit_spec
        (polynomialCircuit representation) code).mpr
    refine ⟨entry, hentryCipher, ?_⟩
    intro gateIndex position
    have hgate :
        NatGateHolds
          ((polynomialCircuit representation).get gateIndex)
          (circuitValue position) :=
      (natGatesHold_iff_naturalCircuitHolds
        (polynomialCircuit representation)
        (circuitValue position)).mpr
          (hcircuit position) gateIndex
    simpa [entry] using hgate
  have hindexEntry :
      entry (indexRegister representation) =
        fun position : Fin (visibleBound visible) =>
          (position : ℕ) := by
    funext position
    have hinput :=
      hinputs position (indexPolynomialInput representation)
    simpa [entry, input, indexRegister, indexPolynomialInput,
      polynomialInputRegister, indexedParameters] using hinput
  have hindexCipher :
      CodeNat (visibleBound visible) q
        (code (indexRegister representation)) := by
    change
      CipherOf (visibleBound visible) q
        (fun position : Fin (visibleBound visible) =>
          (position : ℕ))
        (code (indexRegister representation))
    rw [← hindexEntry]
    exact hentryCipher (indexRegister representation)
  refine ⟨q, code, hcipherCircuit, hindexCipher, ?_⟩
  intro i
  apply
    (constCode_spec
      (hentryCipher (outerRegister representation i))).mpr
  intro position
  have hinput :=
    hinputs position (outerPolynomialInput representation i)
  simpa [entry, input, outerRegister, outerPolynomialInput,
    polynomialInputRegister, indexedParameters] using hinput

/-- Exact correctness of the complete sparse-cipher construction. -/
theorem cipherCertificate_iff_boundedForall
    {set : Set (Fin (m + 1) → ℕ)}
    (representation :
      FiniteDiophantineRepresentation (m + 1) set)
    (visible : Fin (m + 1) → ℕ) :
    CipherCertificate representation visible ↔
      visible ∈ BoundedForall set :=
  ⟨boundedForall_of_cipherCertificate representation,
    cipherCertificate_of_boundedForall representation⟩

/-- A fixed finite Diophantine representation of the source relation
therefore proves Diophantineness of its bounded universal closure. -/
theorem boundedForall_dioph_of_representation
    {set : Set (Fin (m + 1) → ℕ)}
    (representation :
      FiniteDiophantineRepresentation (m + 1) set) :
    Dioph (BoundedForall set) := by
  exact
    Dioph.ext (cipherCertificate_dioph representation) fun visible =>
      cipherCertificate_iff_boundedForall representation visible

/-- **Bounded universal closure for Mathlib-Diophantine relations.**

If a relation in `m` parameters and one final index is Diophantine, then
asserting it for every index below a visible bound is again
Diophantine.  The finite representation is extracted noncomputably from
the proof in `Prop`; the sparse-cipher certificate itself is completely
explicit and unconditional. -/
theorem boundedForall_dioph
    {set : Set (Fin (m + 1) → ℕ)}
    (hset : Dioph set) :
    Dioph (BoundedForall set) := by
  let representation :=
    finiteDiophantineRepresentationOfDioph hset
  exact
    boundedForall_dioph_of_representation representation

end SparseBoundedForall

end HGAS
