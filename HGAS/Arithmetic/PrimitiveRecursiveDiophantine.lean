import HGAS.Arithmetic.SparseBoundedForall
import HGAS.Arithmetic.RadixSequenceCode
import Mathlib.Computability.Primrec.List
import Mathlib.Tactic

/-!
# Primitive-recursive graphs are Diophantine

This module closes the structural layer above sparse bounded universal
quantification.  We work first with unary primitive-recursive functions
in Mathlib's native `Nat.Primrec` presentation, where multiple arguments
are encoded by `Nat.pair`.

The main semantic predicate is the two-coordinate graph

```
  f(input) = output.
```

Zero, successor, projections, pairing, and composition are elementary
Diophantine constructions.  Primitive recursion is handled by a radix
trace:

```
  a(0)   = f(z),
  a(i+1) = g(pair z (pair i (a(i)))).
```

The entire variable-length block of transition equations is discharged by
`SparseBoundedForall.boundedForall_dioph`, whose proof is the explicit
sparse-cipher construction.
-/

namespace HGAS

namespace PrimitiveRecursiveDiophantine

open Vector3
open scoped Vector3
open SparseBoundedForall

/-! ## Generic substitution and the natural pairing function -/

/-- Substitute two Diophantine functions into a two-coordinate
Diophantine relation. -/
theorem binaryRelation_comp_dioph
    {α : Type} {relation : ℕ → ℕ → Prop}
    (hrelation :
      Dioph {value : Fin 2 → ℕ |
        relation (value 0) (value 1)})
    {left right : (α → ℕ) → ℕ}
    (hleft : Dioph.DiophFn left)
    (hright : Dioph.DiophFn right) :
    Dioph {value : α → ℕ |
      relation (left value) (right value)} := by
  have hvector :
      Dioph {value : Vector3 ℕ 2 |
        relation
          (value (Fin2.ofFin 0))
          (value (Fin2.ofFin 1))} :=
    Dioph.reindex_dioph
      (Fin2 2) Fin2.ofFin hrelation
  exact
    Dioph.dioph_comp hvector [left, right]
      ⟨hleft, hright⟩

/-- The graph of a unary natural-number function. -/
def UnaryGraph (function : ℕ → ℕ) :
    Set (Fin 2 → ℕ) :=
  {value | function (value 0) = value 1}

/-- Substitute Diophantine functions into a unary graph. -/
theorem unaryGraph_substitute_dioph
    {α : Type} {function : ℕ → ℕ}
    (hgraph : Dioph (UnaryGraph function))
    {input output : (α → ℕ) → ℕ}
    (hinput : Dioph.DiophFn input)
    (houtput : Dioph.DiophFn output) :
    Dioph {value : α → ℕ |
      function (input value) = output value} := by
  apply binaryRelation_comp_dioph
    (relation := fun x y => function x = y)
    (left := input) (right := output)
  · simpa only [UnaryGraph] using hgraph
  · exact hinput
  · exact houtput

/-- Pair two Diophantine natural-valued functions.  The proof unfolds
Mathlib's pairing formula into its two polynomial branches. -/
theorem natPair_comp_diophFn
    {α : Type}
    {left right : (α → ℕ) → ℕ}
    (hleft : Dioph.DiophFn left)
    (hright : Dioph.DiophFn right) :
    Dioph.DiophFn fun value =>
      Nat.pair (left value) (right value) := by
  let liftedLeft :
      ((Option α → ℕ) → ℕ) :=
    fun value => left (value ∘ some)
  let liftedRight :
      ((Option α → ℕ) → ℕ) :=
    fun value => right (value ∘ some)
  let output :
      ((Option α → ℕ) → ℕ) :=
    fun value => value none
  have hLiftedLeft : Dioph.DiophFn liftedLeft :=
    Dioph.reindex_diophFn some hleft
  have hLiftedRight : Dioph.DiophFn liftedRight :=
    Dioph.reindex_diophFn some hright
  have hOutput : Dioph.DiophFn output :=
    Dioph.proj_dioph none
  have hLeftBranch :
      Dioph {value : Option α → ℕ |
        liftedLeft value < liftedRight value ∧
        output value =
          liftedRight value * liftedRight value +
            liftedLeft value} := by
    exact
      (Dioph.lt_dioph hLiftedLeft hLiftedRight).inter
        (Dioph.eq_dioph hOutput
          (Dioph.add_dioph
            (Dioph.mul_dioph
              hLiftedRight hLiftedRight)
            hLiftedLeft))
  have hRightBranch :
      Dioph {value : Option α → ℕ |
        liftedRight value ≤ liftedLeft value ∧
        output value =
          liftedLeft value * liftedLeft value +
            liftedLeft value + liftedRight value} := by
    exact
      (Dioph.le_dioph hLiftedRight hLiftedLeft).inter
        (Dioph.eq_dioph hOutput
          (Dioph.add_dioph
            (Dioph.add_dioph
              (Dioph.mul_dioph
                hLiftedLeft hLiftedLeft)
              hLiftedLeft)
            hLiftedRight))
  unfold Dioph.DiophFn
  refine
    Dioph.ext (hLeftBranch.union hRightBranch)
      fun value => ?_
  simp only [Set.mem_union, Set.mem_setOf_eq,
    liftedLeft, liftedRight, output]
  rw [Nat.pair]
  by_cases hlt :
      left (value ∘ some) < right (value ∘ some)
  · simp [hlt, Nat.not_le_of_lt hlt, eq_comm]
  · have hle :
        right (value ∘ some) ≤ left (value ∘ some) :=
      Nat.le_of_not_gt hlt
    simp [hlt, hle, eq_comm]

/-- The ordinary binary pairing function is a Diophantine function. -/
theorem natPair_diophFn :
    Dioph.DiophFn fun value : Fin 2 → ℕ =>
      Nat.pair (value 0) (value 1) :=
  natPair_comp_diophFn
    (Dioph.proj_dioph (0 : Fin 2))
    (Dioph.proj_dioph (1 : Fin 2))

/-! ## Elementary unary graphs -/

theorem unaryGraph_zero_dioph :
    Dioph (UnaryGraph fun _ => 0) := by
  exact
    Dioph.eq_dioph
      (Dioph.const_dioph 0)
      (Dioph.proj_dioph (1 : Fin 2))

theorem unaryGraph_succ_dioph :
    Dioph (UnaryGraph Nat.succ) := by
  exact
    Dioph.eq_dioph
      (Dioph.add_dioph
        (Dioph.proj_dioph (0 : Fin 2))
        (Dioph.const_dioph 1))
      (Dioph.proj_dioph (1 : Fin 2))

/-- The graph of the first unpairing projection, characterized by an
existential partner and injectivity of `Nat.pair`. -/
theorem unaryGraph_unpairLeft_dioph :
    Dioph (UnaryGraph fun input => input.unpair.1) := by
  let combined := Fin 2 ⊕ Fin 1
  have hcore :
      Dioph {value : combined → ℕ |
        Nat.pair
            (value (Sum.inl 1))
            (value (Sum.inr 0)) =
          value (Sum.inl 0)} := by
    exact
      Dioph.eq_dioph
        (natPair_comp_diophFn
          (Dioph.proj_dioph (Sum.inl 1))
          (Dioph.proj_dioph (Sum.inr 0)))
        (Dioph.proj_dioph (Sum.inl 0))
  have hhidden := Dioph.ex_dioph hcore
  refine
    Dioph.ext hhidden fun value => ?_
  change
    (∃ witness : Fin 1 → ℕ,
      Nat.pair (value 1) (witness 0) = value 0) ↔
      (value 0).unpair.1 = value 1
  constructor
  · rintro ⟨witness, hwitness⟩
    have hunpair := congrArg Nat.unpair hwitness
    simpa using (congrArg Prod.fst hunpair).symm
  · intro hleft
    refine ⟨fun _ => (value 0).unpair.2, ?_⟩
    rw [← hleft]
    exact Nat.pair_unpair (value 0)

/-- The graph of the second unpairing projection. -/
theorem unaryGraph_unpairRight_dioph :
    Dioph (UnaryGraph fun input => input.unpair.2) := by
  let combined := Fin 2 ⊕ Fin 1
  have hcore :
      Dioph {value : combined → ℕ |
        Nat.pair
            (value (Sum.inr 0))
            (value (Sum.inl 1)) =
          value (Sum.inl 0)} := by
    exact
      Dioph.eq_dioph
        (natPair_comp_diophFn
          (Dioph.proj_dioph (Sum.inr 0))
          (Dioph.proj_dioph (Sum.inl 1)))
        (Dioph.proj_dioph (Sum.inl 0))
  have hhidden := Dioph.ex_dioph hcore
  refine
    Dioph.ext hhidden fun value => ?_
  change
    (∃ witness : Fin 1 → ℕ,
      Nat.pair (witness 0) (value 1) = value 0) ↔
      (value 0).unpair.2 = value 1
  constructor
  · rintro ⟨witness, hwitness⟩
    have hunpair := congrArg Nat.unpair hwitness
    simpa using (congrArg Prod.snd hunpair).symm
  · intro hright
    refine ⟨fun _ => (value 0).unpair.1, ?_⟩
    rw [← hright]
    exact Nat.pair_unpair (value 0)

/-! ## Pairing and composition of unary graphs -/

/-- If `f` and `g` have Diophantine graphs, so does
`input ↦ pair (f input) (g input)`. -/
theorem unaryGraph_pair_dioph
    {left right : ℕ → ℕ}
    (hleft : Dioph (UnaryGraph left))
    (hright : Dioph (UnaryGraph right)) :
    Dioph
      (UnaryGraph fun input =>
        Nat.pair (left input) (right input)) := by
  let combined := Fin 2 ⊕ Fin 2
  have hLeftGraph :
      Dioph {value : combined → ℕ |
        left (value (Sum.inl 0)) =
          value (Sum.inr 0)} :=
    Dioph.reindex_dioph combined
      ![Sum.inl 0, Sum.inr 0] hleft
  have hRightGraph :
      Dioph {value : combined → ℕ |
        right (value (Sum.inl 0)) =
          value (Sum.inr 1)} :=
    Dioph.reindex_dioph combined
      ![Sum.inl 0, Sum.inr 1] hright
  have hPair :
      Dioph {value : combined → ℕ |
        Nat.pair
            (value (Sum.inr 0))
            (value (Sum.inr 1)) =
          value (Sum.inl 1)} :=
    Dioph.eq_dioph
      (natPair_comp_diophFn
        (Dioph.proj_dioph (Sum.inr 0))
        (Dioph.proj_dioph (Sum.inr 1)))
      (Dioph.proj_dioph (Sum.inl 1))
  have hhidden :=
    Dioph.ex_dioph
      (hLeftGraph.inter (hRightGraph.inter hPair))
  refine
    Dioph.ext hhidden fun value => ?_
  change
    (∃ witness : Fin 2 → ℕ,
      left (value 0) = witness 0 ∧
      right (value 0) = witness 1 ∧
      Nat.pair (witness 0) (witness 1) = value 1) ↔
      Nat.pair (left (value 0)) (right (value 0)) = value 1
  constructor
  · rintro ⟨witness, hleftValue, hrightValue, hpair⟩
    rwa [hleftValue, hrightValue]
  · intro hpair
    exact
      ⟨![left (value 0), right (value 0)],
        rfl, rfl, hpair⟩

/-- Diophantine unary graphs are closed under composition. -/
theorem unaryGraph_comp_dioph
    {outer inner : ℕ → ℕ}
    (houter : Dioph (UnaryGraph outer))
    (hinner : Dioph (UnaryGraph inner)) :
    Dioph (UnaryGraph fun input => outer (inner input)) := by
  let combined := Fin 2 ⊕ Fin 1
  have hInnerGraph :
      Dioph {value : combined → ℕ |
        inner (value (Sum.inl 0)) =
          value (Sum.inr 0)} :=
    Dioph.reindex_dioph combined
      ![Sum.inl 0, Sum.inr 0] hinner
  have hOuterGraph :
      Dioph {value : combined → ℕ |
        outer (value (Sum.inr 0)) =
          value (Sum.inl 1)} :=
    Dioph.reindex_dioph combined
      ![Sum.inr 0, Sum.inl 1] houter
  have hhidden :=
    Dioph.ex_dioph (hInnerGraph.inter hOuterGraph)
  refine
    Dioph.ext hhidden fun value => ?_
  change
    (∃ witness : Fin 1 → ℕ,
      inner (value 0) = witness 0 ∧
      outer (witness 0) = value 1) ↔
      outer (inner (value 0)) = value 1
  constructor
  · rintro ⟨witness, hwitness, houterValue⟩
    rwa [hwitness]
  · intro hvalue
    exact ⟨fun _ => inner (value 0), rfl, hvalue⟩

/-! ## Primitive-recursion traces -/

/-- The successive accumulator values of one primitive recursion with
fixed external parameter `z`. -/
def recursionTrace
    (initial step : ℕ → ℕ) (z : ℕ) : ℕ → ℕ
  | 0 => initial z
  | index + 1 =>
      step
        (Nat.pair z
          (Nat.pair index
            (recursionTrace initial step z index)))

@[simp]
theorem recursionTrace_zero
    (initial step : ℕ → ℕ) (z : ℕ) :
    recursionTrace initial step z 0 = initial z :=
  rfl

@[simp]
theorem recursionTrace_succ
    (initial step : ℕ → ℕ) (z index : ℕ) :
    recursionTrace initial step z (index + 1) =
      step
        (Nat.pair z
          (Nat.pair index
            (recursionTrace initial step z index))) :=
  rfl

/-- Unary paired-input form of primitive recursion. -/
def primitiveRecursionFunction
    (initial step : ℕ → ℕ) (input : ℕ) : ℕ :=
  recursionTrace initial step input.unpair.1 input.unpair.2

/-- The transition relation has outer coordinates
`(z, base, code)` and final coordinate `index`. -/
def RecursionTransitionSet (step : ℕ → ℕ) :
    Set (Fin 4 → ℕ) :=
  {value |
    step
        (Nat.pair (value 0)
          (Nat.pair (value 3)
            (RadixSequence.digit
              (value 1) (value 2) (value 3)))) =
      RadixSequence.digit
        (value 1) (value 2) (value 3 + 1)}

/-- A Diophantine step graph gives a Diophantine radix-transition
relation. -/
theorem recursionTransitionSet_dioph
    {step : ℕ → ℕ}
    (hstep : Dioph (UnaryGraph step)) :
    Dioph (RecursionTransitionSet step) := by
  let base : ((Fin 4 → ℕ) → ℕ) :=
    fun value => value 1
  let code : ((Fin 4 → ℕ) → ℕ) :=
    fun value => value 2
  let index : ((Fin 4 → ℕ) → ℕ) :=
    fun value => value 3
  let current : ((Fin 4 → ℕ) → ℕ) :=
    fun value =>
      RadixSequence.digit
        (base value) (code value) (index value)
  let nextIndex : ((Fin 4 → ℕ) → ℕ) :=
    fun value => index value + 1
  let next : ((Fin 4 → ℕ) → ℕ) :=
    fun value =>
      RadixSequence.digit
        (base value) (code value) (nextIndex value)
  let indexedCurrent : ((Fin 4 → ℕ) → ℕ) :=
    fun value => Nat.pair (index value) (current value)
  let stepInput : ((Fin 4 → ℕ) → ℕ) :=
    fun value => Nat.pair (value 0) (indexedCurrent value)
  have hbase : Dioph.DiophFn base :=
    Dioph.proj_dioph (1 : Fin 4)
  have hcode : Dioph.DiophFn code :=
    Dioph.proj_dioph (2 : Fin 4)
  have hindex : Dioph.DiophFn index :=
    Dioph.proj_dioph (3 : Fin 4)
  have hcurrent : Dioph.DiophFn current :=
    RadixSequence.digit_diophFn hbase hcode hindex
  have hnextIndex : Dioph.DiophFn nextIndex :=
    Dioph.add_dioph hindex (Dioph.const_dioph 1)
  have hnext : Dioph.DiophFn next :=
    RadixSequence.digit_diophFn hbase hcode hnextIndex
  have hindexedCurrent : Dioph.DiophFn indexedCurrent :=
    natPair_comp_diophFn hindex hcurrent
  have hstepInput : Dioph.DiophFn stepInput :=
    natPair_comp_diophFn
      (Dioph.proj_dioph (0 : Fin 4))
      hindexedCurrent
  simpa [RecursionTransitionSet, base, code, index,
    current, nextIndex, next, indexedCurrent, stepInput] using
      unaryGraph_substitute_dioph
        hstep hstepInput hnext

/-- Visible tuple supplied to bounded universal quantification of the
transition relation. -/
def recursionTransitionParameters
    (z base code length : ℕ) : Fin 4 → ℕ :=
  ![z, base, code, length]

@[simp]
theorem visibleBound_recursionTransitionParameters
    (z base code length : ℕ) :
    visibleBound
      (recursionTransitionParameters z base code length) =
        length :=
  rfl

@[simp]
theorem indexedParameters_recursionTransitionParameters
    (z base code length index : ℕ) :
    indexedParameters
        (recursionTransitionParameters z base code length) index =
      recursionTransitionParameters z base code index := by
  funext coordinate
  fin_cases coordinate <;> rfl

/-- The concrete trace certificate for primitive recursion. -/
def RecursionCertificate
    (initial step : ℕ → ℕ)
    (input output : ℕ) : Prop :=
  ∃ z n base code : ℕ,
    Nat.pair z n = input ∧
    0 < base ∧
    initial z = RadixSequence.digit base code 0 ∧
    output = RadixSequence.digit base code n ∧
    recursionTransitionParameters z base code n ∈
      BoundedForall (RecursionTransitionSet step)

/-! ## Diophantineness of the trace certificate -/

/-- The primitive-recursion trace certificate is Diophantine whenever
the initial and step functions have Diophantine graphs. -/
theorem recursionCertificate_dioph
    {initial step : ℕ → ℕ}
    (hinitial : Dioph (UnaryGraph initial))
    (hstep : Dioph (UnaryGraph step)) :
    Dioph {value : Fin 2 → ℕ |
      RecursionCertificate initial step
        (value 0) (value 1)} := by
  let combined := Fin 2 ⊕ Fin 4
  let inputCoordinate : combined := Sum.inl 0
  let outputCoordinate : combined := Sum.inl 1
  let zCoordinate : combined := Sum.inr 0
  let nCoordinate : combined := Sum.inr 1
  let baseCoordinate : combined := Sum.inr 2
  let codeCoordinate : combined := Sum.inr 3
  have hPair :
      Dioph {value : combined → ℕ |
        Nat.pair
            (value zCoordinate) (value nCoordinate) =
          value inputCoordinate} :=
    Dioph.eq_dioph
      (natPair_comp_diophFn
        (Dioph.proj_dioph zCoordinate)
        (Dioph.proj_dioph nCoordinate))
      (Dioph.proj_dioph inputCoordinate)
  have hBase :
      Dioph {value : combined → ℕ |
        0 < value baseCoordinate} :=
    Dioph.lt_dioph
      (Dioph.const_dioph 0)
      (Dioph.proj_dioph baseCoordinate)
  let initialDigit : ((combined → ℕ) → ℕ) :=
    fun value =>
      RadixSequence.digit
        (value baseCoordinate) (value codeCoordinate) 0
  have hInitialDigit : Dioph.DiophFn initialDigit :=
    RadixSequence.digit_diophFn
      (Dioph.proj_dioph baseCoordinate)
      (Dioph.proj_dioph codeCoordinate)
      (Dioph.const_dioph 0)
  have hInitial :
      Dioph {value : combined → ℕ |
        initial (value zCoordinate) =
          initialDigit value} :=
    unaryGraph_substitute_dioph hinitial
      (Dioph.proj_dioph zCoordinate)
      hInitialDigit
  let finalDigit : ((combined → ℕ) → ℕ) :=
    fun value =>
      RadixSequence.digit
        (value baseCoordinate) (value codeCoordinate)
        (value nCoordinate)
  have hFinalDigit : Dioph.DiophFn finalDigit :=
    RadixSequence.digit_diophFn
      (Dioph.proj_dioph baseCoordinate)
      (Dioph.proj_dioph codeCoordinate)
      (Dioph.proj_dioph nCoordinate)
  have hFinal :
      Dioph {value : combined → ℕ |
        value outputCoordinate = finalDigit value} :=
    Dioph.eq_dioph
      (Dioph.proj_dioph outputCoordinate)
      hFinalDigit
  have hTransitionBase :
      Dioph
        (BoundedForall
          (RecursionTransitionSet step)) :=
    boundedForall_dioph
      (recursionTransitionSet_dioph hstep)
  have hTransitions :
      Dioph {value : combined → ℕ |
        recursionTransitionParameters
            (value zCoordinate)
            (value baseCoordinate)
            (value codeCoordinate)
            (value nCoordinate) ∈
          BoundedForall
            (RecursionTransitionSet step)} := by
    exact
      Dioph.reindex_dioph combined
        ![zCoordinate, baseCoordinate,
          codeCoordinate, nCoordinate]
        hTransitionBase
  have hcore :=
    hPair.inter
      (hBase.inter
        (hInitial.inter
          (hFinal.inter hTransitions)))
  have hhidden := Dioph.ex_dioph hcore
  refine
    Dioph.ext hhidden fun value => ?_
  change
    (∃ witness : Fin 4 → ℕ,
      Nat.pair (witness 0) (witness 1) = value 0 ∧
      0 < witness 2 ∧
      initial (witness 0) =
        RadixSequence.digit (witness 2) (witness 3) 0 ∧
      value 1 =
        RadixSequence.digit
          (witness 2) (witness 3) (witness 1) ∧
      recursionTransitionParameters
          (witness 0) (witness 2) (witness 3) (witness 1) ∈
        BoundedForall (RecursionTransitionSet step)) ↔
      RecursionCertificate initial step (value 0) (value 1)
  constructor
  · rintro
      ⟨witness, hpair, hbase, hinitialValue,
        hfinal, htransitions⟩
    exact
      ⟨witness 0, witness 1, witness 2, witness 3,
        hpair, hbase, hinitialValue, hfinal, htransitions⟩
  · rintro
      ⟨z, n, base, code, hpair, hbase,
        hinitialValue, hfinal, htransitions⟩
    exact
      ⟨![z, n, base, code],
        hpair, hbase, hinitialValue, hfinal, htransitions⟩

/-! ## Exact semantics of primitive-recursion traces -/

/-- Every genuine primitive-recursion computation has a finite radix
trace certificate. -/
theorem recursionCertificate_of_primitiveRecursionFunction
    (initial step : ℕ → ℕ)
    (input output : ℕ)
    (houtput :
      primitiveRecursionFunction initial step input = output) :
    RecursionCertificate initial step input output := by
  let z := input.unpair.1
  let n := input.unpair.2
  let sequence : Fin (n + 1) → ℕ :=
    fun index =>
      recursionTrace initial step z index
  obtain ⟨base, code, hbase, hdigit⟩ :=
    RadixSequence.exists_code_for_fin_family sequence
  have hpair : Nat.pair z n = input := by
    exact Nat.pair_unpair input
  have hinitial :
      initial z = RadixSequence.digit base code 0 := by
    have hzero :=
      hdigit (0 : Fin (n + 1))
    simpa [sequence] using hzero.symm
  have hfinal :
      output = RadixSequence.digit base code n := by
    let finalIndex : Fin (n + 1) :=
      ⟨n, Nat.lt_succ_self n⟩
    have hlast := hdigit finalIndex
    have houtputTrace :
        output = recursionTrace initial step z n := by
      simpa [primitiveRecursionFunction, z, n] using
        houtput.symm
    calc
      output = recursionTrace initial step z n :=
        houtputTrace
      _ = sequence finalIndex := by
        rfl
      _ = RadixSequence.digit base code n :=
        hlast.symm
  have htransitions :
      recursionTransitionParameters z base code n ∈
        BoundedForall (RecursionTransitionSet step) := by
    intro index hindex
    have hindexN : index < n := by
      simpa using hindex
    rw [
      indexedParameters_recursionTransitionParameters]
    change
      step
          (Nat.pair z
            (Nat.pair index
              (RadixSequence.digit base code index))) =
        RadixSequence.digit base code (index + 1)
    let currentIndex : Fin (n + 1) :=
      ⟨index, by omega⟩
    let nextIndex : Fin (n + 1) :=
      ⟨index + 1, by omega⟩
    have hcurrent := hdigit currentIndex
    have hnext := hdigit nextIndex
    rw [show
      RadixSequence.digit base code index =
        recursionTrace initial step z index by
          simpa [sequence, currentIndex] using hcurrent]
    rw [show
      RadixSequence.digit base code (index + 1) =
        recursionTrace initial step z (index + 1) by
          simpa [sequence, nextIndex] using hnext]
    rfl
  exact
    ⟨z, n, base, code, hpair, hbase,
      hinitial, hfinal, htransitions⟩

/-- Every radix trace certificate reconstructs the primitive recursion
value by induction on the encoded position. -/
theorem primitiveRecursionFunction_eq_of_recursionCertificate
    (initial step : ℕ → ℕ)
    (input output : ℕ)
    (hcertificate :
      RecursionCertificate initial step input output) :
    primitiveRecursionFunction initial step input = output := by
  rcases hcertificate with
    ⟨z, n, base, code, hpair, _hbase,
      hinitial, hfinal, htransitions⟩
  have htransition :
      ∀ index, index < n →
        step
            (Nat.pair z
              (Nat.pair index
                (RadixSequence.digit base code index))) =
          RadixSequence.digit base code (index + 1) := by
    intro index hindex
    have hstep := htransitions index (by
      simpa using hindex)
    rw [
      indexedParameters_recursionTransitionParameters]
      at hstep
    exact hstep
  have hdigitTrace :
      ∀ index, index ≤ n →
        RadixSequence.digit base code index =
          recursionTrace initial step z index := by
    intro index
    induction index with
    | zero =>
        intro _hle
        exact hinitial.symm
    | succ index ih =>
        intro hle
        have hindexLt : index < n := by
          omega
        have hprevious := ih (by omega)
        have hstep := htransition index hindexLt
        calc
          RadixSequence.digit base code (index + 1) =
              step
                (Nat.pair z
                  (Nat.pair index
                    (RadixSequence.digit base code index))) :=
            hstep.symm
          _ =
              step
                (Nat.pair z
                  (Nat.pair index
                    (recursionTrace initial step z index))) := by
            rw [hprevious]
          _ = recursionTrace initial step z (index + 1) := by
            rfl
  have hinput : input = Nat.pair z n :=
    hpair.symm
  calc
    primitiveRecursionFunction initial step input =
        recursionTrace initial step z n := by
      rw [hinput]
      simp [primitiveRecursionFunction]
    _ = RadixSequence.digit base code n :=
      (hdigitTrace n le_rfl).symm
    _ = output :=
      hfinal.symm

/-- Exact certificate specification. -/
theorem recursionCertificate_iff
    (initial step : ℕ → ℕ)
    (input output : ℕ) :
    RecursionCertificate initial step input output ↔
      primitiveRecursionFunction initial step input = output :=
  ⟨primitiveRecursionFunction_eq_of_recursionCertificate
      initial step input output,
    recursionCertificate_of_primitiveRecursionFunction
      initial step input output⟩

/-- Diophantine unary graphs are closed under primitive recursion. -/
theorem unaryGraph_primitiveRecursion_dioph
    {initial step : ℕ → ℕ}
    (hinitial : Dioph (UnaryGraph initial))
    (hstep : Dioph (UnaryGraph step)) :
    Dioph
      (UnaryGraph
        (primitiveRecursionFunction initial step)) := by
  exact
    Dioph.ext (recursionCertificate_dioph hinitial hstep)
      fun value =>
        recursionCertificate_iff
          initial step (value 0) (value 1)

/-! ## Structural induction on Mathlib primitive recursion -/

/-- The trace definition agrees with the literal `Nat.rec` expression
used by Mathlib's `Nat.Primrec.prec` constructor. -/
theorem recursionTrace_eq_natRec
    (initial step : ℕ → ℕ) (z n : ℕ) :
    recursionTrace initial step z n =
      n.rec (initial z)
        (fun index previous =>
          step (Nat.pair z (Nat.pair index previous))) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp only [recursionTrace_succ]
      rw [ih]

/-- Unary paired-input primitive recursion agrees extensionally with the
function emitted by `Nat.Primrec.prec`. -/
theorem primitiveRecursionFunction_eq_unpaired
    (initial step : ℕ → ℕ) :
    primitiveRecursionFunction initial step =
      Nat.unpaired fun z n =>
        n.rec (initial z)
          (fun index previous =>
            step (Nat.pair z (Nat.pair index previous))) := by
  funext input
  exact
    recursionTrace_eq_natRec initial step
      input.unpair.1 input.unpair.2

/-- Every unary primitive-recursive natural-number function has a
Diophantine graph.

The primitive-recursion constructor is precisely where the sparse
bounded-universal theorem is used; all other cases are finite elementary
closures. -/
theorem natPrimrec_unaryGraph_dioph
    {function : ℕ → ℕ}
    (hfunction : Nat.Primrec function) :
    Dioph (UnaryGraph function) := by
  induction hfunction with
  | zero =>
      exact unaryGraph_zero_dioph
  | succ =>
      exact unaryGraph_succ_dioph
  | left =>
      exact unaryGraph_unpairLeft_dioph
  | right =>
      exact unaryGraph_unpairRight_dioph
  | pair hleft hright ihLeft ihRight =>
      exact unaryGraph_pair_dioph ihLeft ihRight
  | comp houter hinner ihOuter ihInner =>
      exact unaryGraph_comp_dioph ihOuter ihInner
  | prec hinitial hstep ihInitial ihStep =>
      rw [← primitiveRecursionFunction_eq_unpaired]
      exact
        unaryGraph_primitiveRecursion_dioph
          ihInitial ihStep

/-! ## Primitive-recursive relations -/

/-- Every primitive-recursive binary relation on natural numbers is
Diophantine.

Mathlib defines such a relation by primitive recursiveness of its Boolean
characteristic function.  After encoding `true` as `1`, the preceding
graph theorem applies.  Pairing the two visible inputs and requiring
output `1` recovers the original relation exactly. -/
theorem binaryPrimrecRel_dioph
    (relation : ℕ → ℕ → Prop)
    (hrelation : PrimrecRel relation) :
    Dioph {input : Fin 2 → ℕ |
      relation (input 0) (input 1)} := by
  classical
  have hdecision :
      Primrec₂
        (fun left right : ℕ =>
          decide (relation left right)) :=
    PrimrecRel.decide hrelation
  have hencoded :
      Primrec₂
        (fun left right : ℕ =>
          Encodable.encode
            (decide (relation left right))) :=
    Primrec₂.encode_iff.mpr hdecision
  let characteristic : ℕ → ℕ :=
    Nat.unpaired fun left right =>
      Encodable.encode
        (decide (relation left right))
  have hcharacteristic :
      Nat.Primrec characteristic := by
    exact Primrec₂.unpaired'.mpr hencoded
  have hgraph :
      Dioph (UnaryGraph characteristic) :=
    natPrimrec_unaryGraph_dioph hcharacteristic
  have hone :
      Dioph {input : Fin 2 → ℕ |
        characteristic
            (Nat.pair (input 0) (input 1)) = 1} :=
    unaryGraph_substitute_dioph hgraph
      natPair_diophFn
      (Dioph.const_dioph 1)
  refine
    Dioph.ext hone fun input => ?_
  simp only [Set.mem_setOf_eq]
  rw [show
    characteristic (Nat.pair (input 0) (input 1)) =
      Encodable.encode
        (decide (relation (input 0) (input 1))) by
          simp [characteristic, Nat.unpaired]]
  by_cases h : relation (input 0) (input 1)
  · simp [h, Encodable.encode_true]
  · simp [h, Encodable.encode_false]

end PrimitiveRecursiveDiophantine

end HGAS
