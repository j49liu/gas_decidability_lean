import HGAS.Compiler.CompactAccumulatorPipelineCode
import HGAS.Accumulator.PolynomialComputability
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Effectivity of the compactification--accumulator pipeline

The semantic construction in `CompactAccumulatorPipelineCode` is a
literal compiler on finite sparse syntax.  This file records that fact
in a form suitable for many-one reductions.

The finite layout and denominator-clearing exponent are compile-time
parameters.  The runtime input consists of

* the rational drift scale `κ`;
* the source polynomial field `P`;
* the finite family of drift observables `h`; and
* the rational reward margin `ε`.

Every stage is primitive recursive.  In particular, the compiler never
normalizes a polynomial, tests semantic equality, solves an ODE, or
performs a real-number operation.
-/

namespace HGAS

namespace CompactAccumulatorPipelineCode

variable {n k l m : ℕ}

/-- Runtime input to the complete finite-syntax pipeline.  The
parenthesization is chosen so the field data and reward margin have
simple primitive-recursive projections. -/
abbrev CompilerInput (n m : ℕ) :=
  ((RationalCode × PolynomialFieldCode n) ×
      (Fin m → PolynomialCode n)) × RationalCode

/-- Complete compiler output: the compact polynomial field together
with its strict-sign reward polynomial. -/
abbrev CompilerOutput (n k m : ℕ) :=
  PolynomialFieldCode ((n + k) + (m + 1)) ×
    PolynomialCode ((n + k) + (m + 1))

/-- Package the field and reward compilers into one finite object. -/
def compile
    (layout : Fin n → Fin k ⊕ Fin l) (M : ℕ)
    (input : CompilerInput n m) :
    CompilerOutput n k m :=
  (fieldCode layout M input.1.1.1 input.1.1.2 input.1.2,
    rewardCode input.2)

/-- The centrally compactified base field is primitive recursive in the
raw source field code. -/
theorem baseFieldCode_primrec
    (layout : Fin n → Fin k ⊕ Fin l) (M : ℕ) :
    Primrec
      (baseFieldCode layout M :
        PolynomialFieldCode n →
          PolynomialFieldCode (n + k)) :=
  MixedCentralPolynomialCode.fieldCode_primrec layout M

/-- One slowed drift coordinate is primitive recursive jointly in its
rational scale and raw sparse drift family. -/
theorem slowedDriftCode_primrec
    (layout : Fin n → Fin k ⊕ Fin l)
    (M : ℕ) (i : Fin m) :
    Primrec
      (fun input :
          RationalCode × (Fin m → PolynomialCode n) ↦
        slowedDriftCode layout M input.1 input.2 i) := by
  exact
    (PolynomialCode.mul_primrec.comp
      (PolynomialCode.constant_primrec.comp Primrec.fst)
      ((MixedCentralPolynomialCode.homogenize_primrec
          layout M).comp
        (Primrec.fin_app.comp Primrec.snd
          (Primrec.const i)))).of_eq fun _ ↦ rfl

/-- The complete finite family of slowed drift coordinates is primitive
recursive. -/
theorem slowedDriftFamily_primrec
    (layout : Fin n → Fin k ⊕ Fin l) (M : ℕ) :
    Primrec
      (fun input :
          RationalCode × (Fin m → PolynomialCode n) ↦
        slowedDriftCode layout M input.1 input.2) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro i
  exact slowedDriftCode_primrec layout M i

set_option maxHeartbeats 800000 in
-- Finite-function encodings make this composition unusually expensive to elaborate.
/-- **Effective composed field compiler.**  The rational scale, source
field, and drift family are all runtime inputs. -/
theorem fieldCode_primrec
    (layout : Fin n → Fin k ⊕ Fin l) (M : ℕ) :
    Primrec
      (fun input :
          (RationalCode × PolynomialFieldCode n) ×
            (Fin m → PolynomialCode n) ↦
        fieldCode layout M input.1.1 input.1.2 input.2) := by
  have hbase :
      Primrec
        (fun input :
            (RationalCode × PolynomialFieldCode n) ×
              (Fin m → PolynomialCode n) ↦
          baseFieldCode layout M input.1.2) :=
    (baseFieldCode_primrec layout M).comp
      (Primrec.snd.comp Primrec.fst)
  have hdrift :
      Primrec
        (fun input :
            (RationalCode × PolynomialFieldCode n) ×
              (Fin m → PolynomialCode n) ↦
          slowedDriftCode layout M input.1.1 input.2) :=
    (slowedDriftFamily_primrec
      (m := m) layout M).comp
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          Primrec.snd)
  exact
    (AccumulatorPolynomialCode.fieldCode_primrec
      (n + k) m).comp (Primrec.pair hbase hdrift)

theorem fieldCode_computable
    (layout : Fin n → Fin k ⊕ Fin l) (M : ℕ) :
    Computable
      (fun input :
          (RationalCode × PolynomialFieldCode n) ×
            (Fin m → PolynomialCode n) ↦
        fieldCode layout M input.1.1 input.1.2 input.2) :=
  (fieldCode_primrec layout M).to_comp

/-- The central weight product is a fixed raw sparse code, hence a
primitive-recursive constant for fixed dimensions. -/
theorem centralWeightProductCode_primrec :
    Primrec
      (fun _ : Unit ↦
        centralWeightProductCode (n := n) (k := k)) :=
  Primrec.const _

/-- The lifted central weight product is also a fixed raw sparse code. -/
theorem liftedCentralWeightProductCode_primrec :
    Primrec
      (fun _ : Unit ↦
        liftedCentralWeightProductCode
          (n := n) (k := k) (m := m)) :=
  Primrec.const _

/-- The reward compiler is primitive recursive in the rational margin
`ε`. -/
theorem rewardCode_primrec :
    Primrec
      (rewardCode (n := n) (k := k) (m := m) :
        RationalCode →
          PolynomialCode ((n + k) + (m + 1))) := by
  exact
    PolynomialCode.sub_primrec.comp
      (Primrec.const
        (PolynomialCode.add
          (PolynomialCode.varCode
            (AccumulatorPolynomialCode.wIndex (n + k) m))
          (PolynomialCode.mul
            (PolynomialCode.constant (RationalCode.ofNat 2))
            (liftedCentralWeightProductCode
              (n := n) (k := k) (m := m)))))
      (PolynomialCode.add_primrec.comp
        (Primrec.const PolynomialCode.one)
        (PolynomialCode.constant_primrec.comp Primrec.id))

theorem rewardCode_computable :
    Computable
      (rewardCode (n := n) (k := k) (m := m) :
        RationalCode →
          PolynomialCode ((n + k) + (m + 1))) :=
  (rewardCode_primrec (n := n) (k := k) (m := m)).to_comp

/-- **Primitive-recursive complete pipeline.** -/
theorem compile_primrec
    (layout : Fin n → Fin k ⊕ Fin l) (M : ℕ) :
    Primrec (compile (m := m) layout M) := by
  exact
    Primrec.pair
      ((fieldCode_primrec
        (m := m) layout M).comp Primrec.fst)
      ((rewardCode_primrec
        (n := n) (k := k) (m := m)).comp Primrec.snd)

/-- The complete finite-syntax pipeline is computable. -/
theorem compile_computable
    (layout : Fin n → Fin k ⊕ Fin l) (M : ℕ) :
    Computable (compile (m := m) layout M) :=
  (compile_primrec (m := m) layout M).to_comp

end CompactAccumulatorPipelineCode

end HGAS
