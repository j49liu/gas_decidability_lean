import Stability.Computability.RegisterMachine

/-!
# Arithmetic macros built from finite register-machine instructions

The specifications in this file constrain literal instructions at finitely
many labels. Their correctness theorems derive the resulting runs; no
execution behavior is assumed. Macro exits may be active labels, allowing
the blocks to be embedded in a larger finite program.
-/

namespace Stability.RegisterMachine

open Function

variable {k s : ℕ}

/-- Encode a finite stack as a base-`b` numeral, with its top at the least
significant digit. Alphabet values `0, …, b-2` use digits `1, …, b-1`, so
the empty stack alone has code zero. In particular, four symbols use base five. -/
def stackNumeral (b : ℕ) : List (Fin (b - 1)) → ℕ
  | [] => 0
  | d :: ds => b * stackNumeral b ds + (d.val + 1)

@[simp]
theorem stackNumeral_eq_zero_iff (b : ℕ) (ds : List (Fin (b - 1))) :
    stackNumeral b ds = 0 ↔ ds = [] := by
  cases ds with
  | nil => simp [stackNumeral]
  | cons d ds => simp [stackNumeral]

/-- Division removes the top symbol from an encoded stack. -/
@[simp]
theorem stackNumeral_cons_div {b : ℕ} (d : Fin (b - 1)) (ds : List (Fin (b - 1))) :
    stackNumeral b (d :: ds) / b = stackNumeral b ds := by
  have hd : d.val + 1 < b := by have := d.isLt; omega
  rw [stackNumeral, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hd, Nat.add_zero]

/-- Remainder reads the nonzero digit of the top stack symbol. -/
@[simp]
theorem stackNumeral_cons_mod {b : ℕ} (d : Fin (b - 1)) (ds : List (Fin (b - 1))) :
    stackNumeral b (d :: ds) % b = d.val + 1 := by
  have hd : d.val + 1 < b := by have := d.isLt; omega
  rw [stackNumeral, Nat.mul_add_mod, Nat.mod_eq_of_lt hd]

/-- Distinct finite stacks have distinct numeral encodings. -/
theorem stackNumeral_injective (b : ℕ) : Function.Injective (stackNumeral b) := by
  intro ds es h
  induction ds generalizing es with
  | nil =>
      have he : stackNumeral b es = 0 := h.symm
      exact ((stackNumeral_eq_zero_iff b es).mp he).symm
  | cons d ds ih =>
      cases es with
      | nil =>
          have : d :: ds = [] := (stackNumeral_eq_zero_iff b (d :: ds)).mp h
          contradiction
      | cons e es =>
          have hmod := congrArg (fun n ↦ n % b) h
          simp only [stackNumeral_cons_mod] at hmod
          have hde : d = e := Fin.ext (by omega)
          have hdiv := congrArg (fun n ↦ n / b) h
          simp only [stackNumeral_cons_div] at hdiv
          exact congrArg₂ List.cons hde (ih hdiv)

/-- Enter the first label of a block, or its continuation if it is empty. -/
def blockEntry (labels : List (Fin s)) (exit : Option (Fin s)) : Option (Fin s) :=
  match labels with
  | [] => exit
  | q :: _ => some q

/-- Literal code equations for a finite chain of increments. -/
def IncrementChain (P : Program k s) (i : Fin k) :
    List (Fin s) → Option (Fin s) → Prop
  | [], _ => True
  | q :: qs, exit => P q = .inc i (blockEntry qs exit) ∧ IncrementChain P i qs exit

/-- A chain of `m` increments adds exactly `m`, preserving other registers. -/
theorem run_incrementChain {P : Program k s} {i : Fin k} {labels : List (Fin s)}
    {exit : Option (Fin s)} (hcode : IncrementChain P i labels exit) (r : Fin k → ℕ) :
    run P labels.length ⟨blockEntry labels exit, r⟩ =
      ⟨exit, update r i (r i + labels.length)⟩ := by
  induction labels generalizing r with
  | nil => simp [blockEntry, run, update_eq_self]
  | cons q qs ih =>
      rcases hcode with ⟨hq, hqs⟩
      rw [List.length_cons, run_succ]
      change run P qs.length (step P ⟨some q, r⟩) = _
      rw [step_inc hq, ih hqs]
      congr 1
      ext j
      by_cases hj : j = i
      · subst j
        simp only [update_self]
        omega
      · simp [hj]

/-- One test/decrement followed by `b` increments transfers each source
unit with weight `b`. The final zero test is included in the step count. -/
theorem run_weightedTransfer {P : Program k s} {test : Fin s}
    {source target : Fin k} {increments : List (Fin s)} {exit : Option (Fin s)}
    (hne : source ≠ target)
    (htest : P test = .dec source exit (blockEntry increments (some test)))
    (hinc : IncrementChain P target increments (some test)) (r : Fin k → ℕ) :
    run P ((increments.length + 1) * r source + 1) ⟨some test, r⟩ =
      ⟨exit, update (update r source 0) target
        (r target + increments.length * r source)⟩ := by
  generalize hn : r source = n
  induction n generalizing r with
  | zero =>
      rw [Nat.mul_zero, Nat.zero_add, run_succ, step_dec_zero htest r hn, run_zero]
      congr 1
      ext j
      by_cases hjt : j = target
      · subst j; simp
      · by_cases hjs : j = source
        · subst j; simp [hne, hn]
        · simp [hjt, hjs]
  | succ n ih =>
      rw [show (increments.length + 1) * (n + 1) + 1 =
          (increments.length + ((increments.length + 1) * n + 1)) + 1 by ring,
        run_succ, step_dec_positive htest r (by omega), run_add,
        run_incrementChain hinc]
      have hsource : (update (update r source (r source - 1)) target
          ((update r source (r source - 1)) target + increments.length)) source = n := by
        simp [hne, hn]
      rw [ih _ hsource]
      congr 1
      ext j
      by_cases hjt : j = target
      · subst j
        simp only [update_self, update_of_ne (Ne.symm hne)]
        ring
      · by_cases hjs : j = source
        · subst j; simp [hne]
        · simp [hjt, hjs]

/-- A base-`b` stack push is weighted transfer to a cleared scratch
register, ordinary transfer back, then `d` increments. The macro changes
`N` to `b * N + d`, clears the scratch, and preserves every other register.
For a numeral stack, the caller chooses `b ≥ 2` and `0 < d < b`; the
arithmetic identity itself needs neither restriction. -/
theorem run_stackPush {P : Program k s} {multiply copy add : Fin s}
    {value scratch : Fin k} {base digit : List (Fin s)} {exit : Option (Fin s)}
    (hne : value ≠ scratch)
    (hmultiply : P multiply = .dec value (some copy) (blockEntry base (some multiply)))
    (hbase : IncrementChain P scratch base (some multiply))
    (hcopy : P copy = .dec scratch (blockEntry digit exit) (some add))
    (hadd : P add = .inc value (some copy))
    (hdigit : IncrementChain P value digit exit)
    (r : Fin k → ℕ) (hscratch : r scratch = 0) :
    run P (((base.length + 1) * r value + 1) +
      (2 * (base.length * r value) + 1) + digit.length) ⟨some multiply, r⟩ =
      ⟨exit, update (update r scratch 0) value (base.length * r value + digit.length)⟩ := by
  rw [run_add, run_add, run_weightedTransfer hne hmultiply hbase]
  simp only [hscratch, Nat.zero_add]
  rw [show 2 * (base.length * r value) + 1 =
      2 * (update (update r value 0) scratch (base.length * r value)) scratch + 1 by
        simp, run_transfer (Ne.symm hne) hcopy hadd]
  rw [run_incrementChain hdigit]
  congr 1
  ext j
  by_cases hjv : j = value
  · subst j; simp [hne]
  · by_cases hjs : j = scratch
    · subst j; simp [Ne.symm hne]
    · simp [hjv, hjs]

/-- Enter a block of zero tests, each carrying its own zero continuation. -/
def decrementEntry (tests : List (Fin s × Option (Fin s)))
    (exit : Option (Fin s)) : Option (Fin s) :=
  blockEntry (tests.map Prod.fst) exit

/-- A finite chain of decrements. Each zero branch exits immediately;
positive branches advance to the next test. -/
def DecrementChain (P : Program k s) (i : Fin k) :
    List (Fin s × Option (Fin s)) → Option (Fin s) → Prop
  | [], _ => True
  | (q, zero) :: qs, exit =>
      P q = .dec i zero (decrementEntry qs exit) ∧ DecrementChain P i qs exit

/-- If the register contains at least the block length, every branch is
positive and the block subtracts exactly its length. -/
theorem run_decrementChain_positive {P : Program k s} {i : Fin k}
    {tests : List (Fin s × Option (Fin s))} {exit : Option (Fin s)}
    (hcode : DecrementChain P i tests exit) (r : Fin k → ℕ)
    (hsize : tests.length ≤ r i) :
    run P tests.length ⟨decrementEntry tests exit, r⟩ =
      ⟨exit, update r i (r i - tests.length)⟩ := by
  induction tests generalizing r with
  | nil => simp [decrementEntry, blockEntry, run, update_eq_self]
  | cons q qs ih =>
      rcases q with ⟨q, zero⟩
      rcases hcode with ⟨hq, hqs⟩
      rw [List.length_cons, run_succ]
      change run P qs.length (step P ⟨some q, r⟩) = _
      have hpositive : 0 < r i := by
        simp only [List.length_cons] at hsize
        omega
      rw [step_dec_positive hq r hpositive]
      rw [ih hqs _ (by simp only [update_self]; simp only [List.length_cons] at hsize; omega)]
      congr 1
      ext j
      by_cases hj : j = i
      · subst j
        simp only [update_self]
        omega
      · simp [hj]

/-- If the register is smaller than the block length, its initial value
selects the zero continuation after exactly that many decrements. -/
theorem run_decrementChain_zero {P : Program k s} {i : Fin k}
    {tests : List (Fin s × Option (Fin s))} {exit : Option (Fin s)}
    (hcode : DecrementChain P i tests exit) (r : Fin k → ℕ)
    {n : ℕ} (hn : r i = n) (hsize : n < tests.length) :
    run P (n + 1) ⟨decrementEntry tests exit, r⟩ =
      ⟨(tests[n]).2, update r i 0⟩ := by
  induction tests generalizing n r with
  | nil => simp at hsize
  | cons q qs ih =>
      rcases q with ⟨q, zero⟩
      rcases hcode with ⟨hq, hqs⟩
      cases n with
      | zero =>
          rw [run_succ]
          change run P 0 (step P ⟨some q, r⟩) = _
          rw [step_dec_zero hq r hn, run_zero]
          congr 1
          exact (update_eq_self i r).symm.trans (congrArg (update r i) hn)
      | succ n =>
          rw [run_succ]
          change run P (n + 1) (step P ⟨some q, r⟩) = _
          rw [step_dec_positive hq r (by omega)]
          simpa using ih hqs (update r i (r i - 1)) (by simp [hn])
            (by simp only [List.length_cons] at hsize; omega)

/-- Repeated blocks of `b` decrements implement division with remainder.
The remainder is stored in the chosen finite zero-branch continuation,
and the quotient is added to `scratch`. The source register ends at zero.
This theorem concerns only literal DEC tests and one INC per full block. -/
theorem run_division {P : Program k s} {add : Fin s} {value scratch : Fin k}
    {tests : List (Fin s × Option (Fin s))}
    (hne : value ≠ scratch)
    (hcode : DecrementChain P value tests (some add))
    (hadd : P add = .inc scratch (decrementEntry tests (some add)))
    (r : Fin k → ℕ) (q rem : ℕ)
    (hn : r value = tests.length * q + rem) (hrem : rem < tests.length) :
    run P ((tests.length + 1) * q + rem + 1)
      ⟨decrementEntry tests (some add), r⟩ =
      ⟨(tests[rem]).2, update (update r value 0) scratch (r scratch + q)⟩ := by
  induction q generalizing r with
  | zero =>
      simp only [Nat.mul_zero, Nat.zero_add] at hn ⊢
      rw [run_decrementChain_zero hcode r hn hrem]
      congr 1
      ext j
      by_cases hj : j = scratch
      · subst j; simp [Ne.symm hne]
      · simp [hj]
  | succ q ih =>
      have hsize : tests.length ≤ r value := by
        rw [hn, Nat.mul_add, Nat.mul_one]
        omega
      rw [show (tests.length + 1) * (q + 1) + rem + 1 =
          tests.length + (((tests.length + 1) * q + rem + 1) + 1) by ring,
        run_add, run_decrementChain_positive hcode r hsize, run_succ, step_inc hadd]
      have hvalue : (update (update r value (r value - tests.length)) scratch
          ((update r value (r value - tests.length)) scratch + 1)) value =
          tests.length * q + rem := by
        simp only [update_of_ne hne, update_self]
        rw [hn, Nat.mul_add, Nat.mul_one]
        omega
      rw [ih _ hvalue]
      congr 1
      ext j
      by_cases hjs : j = scratch
      · subst j
        simp only [update_self, update_of_ne (Ne.symm hne)]
        omega
      · by_cases hjv : j = value
        · subst j; simp [hne]
        · simp [hjs, hjv]

/-- A base-`b` numeral pop divides the value register by `b`, branches on
its remainder, and returns its quotient scratch register to zero.

Each remainder has a two-instruction transfer continuation. Thus the
remainder is carried by finite control, not by an unbounded extra state.
All code assumptions are literal INC/DEC equations at finite labels.
For a stack alphabet, use nonzero digits below `b`; a zero numeral then
selects the empty-stack continuation without changing any register.
-/
theorem run_stackPop {P : Program k s} {quotientAdd : Fin s} {value scratch : Fin k}
    {tests : List (Fin s × Option (Fin s))}
    (hb : 0 < tests.length) (hne : value ≠ scratch)
    (hcode : DecrementChain P value tests (some quotientAdd))
    (hquotient : P quotientAdd = .inc scratch (decrementEntry tests (some quotientAdd)))
    (copy add : Fin tests.length → Fin s) (exit : Fin tests.length → Option (Fin s))
    (hzero : ∀ j : Fin tests.length, (tests[j.val]).2 = some (copy j))
    (hcopy : ∀ j, P (copy j) = .dec scratch (exit j) (some (add j)))
    (hadd : ∀ j, P (add j) = .inc value (some (copy j)))
    (r : Fin k → ℕ) (hscratch : r scratch = 0) :
    run P (((tests.length + 1) * (r value / tests.length) +
      r value % tests.length + 1) + (2 * (r value / tests.length) + 1))
      ⟨decrementEntry tests (some quotientAdd), r⟩ =
      ⟨exit ⟨r value % tests.length, Nat.mod_lt _ hb⟩,
        update (update r scratch 0) value (r value / tests.length)⟩ := by
  rw [run_add, run_division hne hcode hquotient r (r value / tests.length)
    (r value % tests.length) (Nat.div_add_mod _ _).symm (Nat.mod_lt _ hb)]
  rw [hzero ⟨r value % tests.length, Nat.mod_lt _ hb⟩]
  simp only [hscratch, Nat.zero_add]
  rw [show 2 * (r value / tests.length) + 1 =
      2 * (update (update r value 0) scratch (r value / tests.length)) scratch + 1 by
        simp, run_transfer (Ne.symm hne) (hcopy _) (hadd _)]
  congr 1
  ext j
  by_cases hjv : j = value
  · subst j; simp [hne]
  · by_cases hjs : j = scratch
    · subst j; simp [Ne.symm hne]
    · simp [hjv, hjs]

end Stability.RegisterMachine
