import HGAS.Accumulator.PolynomialCode
import Mathlib.Computability.Partrec
import Mathlib.Tactic

/-!
# Effectivity of the compact-accumulator compiler

For fixed base and accumulator dimensions, every operation in
`Accumulator.PolynomialCode` is primitive recursive on raw finite sparse
syntax.  In particular,

```
 (base field code, drift code) ↦ combined compact-accumulator field code
```

is a computable function.  No invariant measure, solution of an ODE, or
real-number choice occurs in this compiler.
-/

namespace HGAS.AccumulatorPolynomialCode

variable {n m : ℕ}

theorem liftBase_primrec (n m : ℕ) :
    Primrec
      (liftBase (n := n) (m := m) :
        PolynomialCode n →
          PolynomialCode (n + (m + 1))) :=
  PolynomialCode.dimensionEmbed_primrec n (m + 1)

theorem driftCode_primrec
    (n m : ℕ) (i : Fin m) :
    Primrec
      (fun g : Fin m → PolynomialCode n ↦
        driftCode g i) :=
  (liftBase_primrec n m).comp
    (Primrec.fin_app.comp Primrec.id (Primrec.const i))

theorem dotCode_primrec (n m : ℕ) :
    Primrec
      (dotCode (n := n) (m := m) :
        (Fin m → PolynomialCode n) →
          PolynomialCode (n + (m + 1))) := by
  apply PolynomialCode.sumCodes_primrec.comp
  apply Primrec.list_ofFn
  intro i
  exact
    PolynomialCode.mul_primrec.comp
      (Primrec.const
        (PolynomialCode.varCode (uIndex (n := n) i)))
      (driftCode_primrec n m i)

theorem uFieldCode_primrec
    (n m : ℕ) (i : Fin m) :
    Primrec
      (fun g : Fin m → PolynomialCode n ↦
        uFieldCode g i) := by
  have hfirst :
      Primrec
        (fun g : Fin m → PolynomialCode n ↦
          PolynomialCode.mul
            (onePlusWCode (n := n) (m := m))
            (driftCode g i)) :=
    PolynomialCode.mul_primrec.comp
      (Primrec.const onePlusWCode)
      (driftCode_primrec n m i)
  have hsecond :
      Primrec
        (fun g : Fin m → PolynomialCode n ↦
          PolynomialCode.mul
            (dotCode g)
            (PolynomialCode.varCode (uIndex (n := n) i))) :=
    PolynomialCode.mul_primrec.comp
      (dotCode_primrec n m)
      (Primrec.const
        (PolynomialCode.varCode (uIndex (n := n) i)))
  exact
    (PolynomialCode.sub_primrec.comp
      hfirst hsecond).of_eq fun _ ↦ rfl

theorem wFieldCode_primrec (n m : ℕ) :
    Primrec
      (wFieldCode (n := n) (m := m) :
        (Fin m → PolynomialCode n) →
          PolynomialCode (n + (m + 1))) := by
  exact
    PolynomialCode.neg_primrec.comp
      (PolynomialCode.mul_primrec.comp
        (Primrec.const
          (onePlusWCode (n := n) (m := m)))
        (dotCode_primrec n m))

/-- Primitive-recursive complete field compiler. -/
theorem fieldCode_primrec (n m : ℕ) :
    Primrec
      (fun input :
          PolynomialFieldCode n ×
            (Fin m → PolynomialCode n) ↦
        fieldCode input.1 input.2) := by
  rw [Primrec.fin_curry]
  apply Primrec₂.swap
  rw [Primrec.fin_curry₁]
  intro q
  cases houter : finSumFinEquiv.symm q with
  | inl j =>
      exact
        ((liftBase_primrec n m).comp
          (Primrec.fin_app.comp Primrec.fst
            (Primrec.const j))).of_eq fun input ↦ by
              simp only [fieldCode, houter]
              rfl
  | inr r =>
      cases hinner : finSumFinEquiv.symm r with
      | inl i =>
          exact
            ((uFieldCode_primrec n m i).comp
              Primrec.snd).of_eq fun input ↦ by
                simp only [fieldCode, houter, hinner]
      | inr j =>
          exact
            ((wFieldCode_primrec n m).comp
              Primrec.snd).of_eq fun input ↦ by
                simp only [fieldCode, houter, hinner]

theorem fieldCode_computable (n m : ℕ) :
    Computable
      (fun input :
          PolynomialFieldCode n ×
            (Fin m → PolynomialCode n) ↦
        fieldCode input.1 input.2) :=
  (fieldCode_primrec n m).to_comp

end HGAS.AccumulatorPolynomialCode
