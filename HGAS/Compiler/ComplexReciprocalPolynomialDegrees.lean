import HGAS.Compiler.ComplexReciprocalPolynomialCode
import Mathlib.Tactic

/-!
# Parametric degree bounds for the complex reciprocal compiler

The reciprocal compiler adjoins a complex coordinate `g` to a real
polynomial source.  Its two new differential equations encode

```
                         g' = η wdot g²,
```

where `η` is rational and therefore has degree zero.  Consequently, if
the two real components of `wdot` have raw degree at most `E`, the two
new field coordinates have raw degree at most `E + 2`.  Combining them
with a base field of degree at most `D` gives the sharp uniform compiler
bound

```
                         max D (E + 2).
```

Likewise, each coordinate of the graph residual

```
                         (1 - η w) g - 1
```

has raw degree at most `W + 1` when the two components of `w` have raw
degree at most `W`.

All bounds concern the literal sparse syntax emitted by the compiler,
before normalization or cancellation.  They therefore remain valid as
robust syntactic certificates for later compiler stages.
-/

namespace HGAS.ComplexReciprocalPolynomialCode

variable {n D E W : ℕ}

/-- Componentwise raw degree bound for a coded complex observable. -/
def ComplexObservableTermsDegreeLE
    (D : ℕ) (p : ComplexObservableCode n) : Prop :=
  PolynomialCode.TermsDegreeLE D p.1 ∧
    PolynomialCode.TermsDegreeLE D p.2

instance complexObservableTermsDegreeLEDecidable
    (D : ℕ) (p : ComplexObservableCode n) :
    Decidable (ComplexObservableTermsDegreeLE D p) := by
  unfold ComplexObservableTermsDegreeLE
  infer_instance

/-- Inserting a base polynomial into the extended state preserves every
raw monomial-degree bound. -/
theorem liftBase_termsDegreeLE
    {p : PolynomialCode n}
    (hp : PolynomialCode.TermsDegreeLE D p) :
    PolynomialCode.TermsDegreeLE D (liftBase p) :=
  PolynomialCode.termsDegreeLE_injectVariables _ hp

/-- A coded rational parameter has raw degree zero. -/
theorem etaCode_termsDegreeLE (η : RationalCode) :
    PolynomialCode.TermsDegreeLE 0
      (etaCode η : PolynomialCode (dimension n)) := by
  intro t ht
  exact
    (PolynomialCode.termsParityEligible_constant η t
      (by simpa [etaCode] using ht)).1

/-- The literal code for one has raw degree zero. -/
theorem oneCode_termsDegreeLE :
    PolynomialCode.TermsDegreeLE 0
      (oneCode : PolynomialCode (dimension n)) := by
  simpa [oneCode] using
    (PolynomialCode.termsDegreeLE_one :
      PolynomialCode.TermsDegreeLE 0
        (PolynomialCode.one : PolynomialCode (dimension n)))

/-- The literal code for two has raw degree zero. -/
theorem twoCode_termsDegreeLE :
    PolynomialCode.TermsDegreeLE 0
      (twoCode : PolynomialCode (dimension n)) := by
  intro t ht
  exact
    (PolynomialCode.termsParityEligible_constant
      (RationalCode.encode 2) t
      (by simpa [twoCode] using ht)).1

/-- Each reciprocal coordinate is linear. -/
theorem reciprocalReCode_termsDegreeLE :
    PolynomialCode.TermsDegreeLE 1
      (reciprocalReCode : PolynomialCode (dimension n)) := by
  simpa [reciprocalReCode] using
    PolynomialCode.termsDegreeLE_varCode (reciprocalReIndex n)

/-- Each reciprocal coordinate is linear. -/
theorem reciprocalImCode_termsDegreeLE :
    PolynomialCode.TermsDegreeLE 1
      (reciprocalImCode : PolynomialCode (dimension n)) := by
  simpa [reciprocalImCode] using
    PolynomialCode.termsDegreeLE_varCode (reciprocalImIndex n)

/-- The real coordinate of `g²` is quadratic in the extended state. -/
theorem reciprocalSquareReCode_termsDegreeLE :
    PolynomialCode.TermsDegreeLE 2
      (reciprocalSquareReCode :
        PolynomialCode (dimension n)) := by
  exact
    PolynomialCode.termsDegreeLE_sub
      (by
        simpa using
          PolynomialCode.termsDegreeLE_mul
            (reciprocalReCode_termsDegreeLE (n := n))
            (reciprocalReCode_termsDegreeLE (n := n)))
      (by
        simpa using
          PolynomialCode.termsDegreeLE_mul
            (reciprocalImCode_termsDegreeLE (n := n))
            (reciprocalImCode_termsDegreeLE (n := n)))

/-- The imaginary coordinate of `g²` is quadratic in the extended state. -/
theorem reciprocalSquareImCode_termsDegreeLE :
    PolynomialCode.TermsDegreeLE 2
      (reciprocalSquareImCode :
        PolynomialCode (dimension n)) := by
  have hproduct :
      PolynomialCode.TermsDegreeLE 2
        (PolynomialCode.mul
          (reciprocalReCode :
            PolynomialCode (dimension n))
          reciprocalImCode) := by
    simpa using
      PolynomialCode.termsDegreeLE_mul
        (reciprocalReCode_termsDegreeLE (n := n))
        (reciprocalImCode_termsDegreeLE (n := n))
  simpa [reciprocalSquareImCode] using
    PolynomialCode.termsDegreeLE_mul
      (twoCode_termsDegreeLE (n := n)) hproduct

/-- The real reciprocal-velocity equation has degree at most `E + 2`
when both real components of `wdot` have degree at most `E`. -/
theorem reciprocalVelocityReCode_termsDegreeLE
    (η : RationalCode) (wdot : ComplexObservableCode n)
    (hwdot : ComplexObservableTermsDegreeLE E wdot) :
    PolynomialCode.TermsDegreeLE (E + 2)
      (reciprocalVelocityReCode η wdot) := by
  have hre :
      PolynomialCode.TermsDegreeLE (E + 2)
        (PolynomialCode.mul (liftBase wdot.1)
          (reciprocalSquareReCode :
            PolynomialCode (dimension n))) :=
    PolynomialCode.termsDegreeLE_mul
      (liftBase_termsDegreeLE hwdot.1)
      (reciprocalSquareReCode_termsDegreeLE (n := n))
  have him :
      PolynomialCode.TermsDegreeLE (E + 2)
        (PolynomialCode.mul (liftBase wdot.2)
          (reciprocalSquareImCode :
            PolynomialCode (dimension n))) :=
    PolynomialCode.termsDegreeLE_mul
      (liftBase_termsDegreeLE hwdot.2)
      (reciprocalSquareImCode_termsDegreeLE (n := n))
  simpa [reciprocalVelocityReCode] using
    PolynomialCode.termsDegreeLE_mul
      (etaCode_termsDegreeLE (n := n) η)
      (PolynomialCode.termsDegreeLE_sub hre him)

/-- The imaginary reciprocal-velocity equation has degree at most
`E + 2` under the same componentwise hypothesis. -/
theorem reciprocalVelocityImCode_termsDegreeLE
    (η : RationalCode) (wdot : ComplexObservableCode n)
    (hwdot : ComplexObservableTermsDegreeLE E wdot) :
    PolynomialCode.TermsDegreeLE (E + 2)
      (reciprocalVelocityImCode η wdot) := by
  have hre :
      PolynomialCode.TermsDegreeLE (E + 2)
        (PolynomialCode.mul (liftBase wdot.1)
          (reciprocalSquareImCode :
            PolynomialCode (dimension n))) :=
    PolynomialCode.termsDegreeLE_mul
      (liftBase_termsDegreeLE hwdot.1)
      (reciprocalSquareImCode_termsDegreeLE (n := n))
  have him :
      PolynomialCode.TermsDegreeLE (E + 2)
        (PolynomialCode.mul (liftBase wdot.2)
          (reciprocalSquareReCode :
            PolynomialCode (dimension n))) :=
    PolynomialCode.termsDegreeLE_mul
      (liftBase_termsDegreeLE hwdot.2)
      (reciprocalSquareReCode_termsDegreeLE (n := n))
  simpa [reciprocalVelocityImCode] using
    PolynomialCode.termsDegreeLE_mul
      (etaCode_termsDegreeLE (n := n) η)
      (PolynomialCode.termsDegreeLE_add hre him)

/-- **Sharp parametric field ledger.**

If the base field has degree at most `D` and both real components of the
input velocity have degree at most `E`, every coordinate emitted by the
extended compiler has degree at most `max D (E + 2)`. -/
theorem fieldCode_termsDegreeLE
    (F : PolynomialFieldCode n)
    (η : RationalCode) (wdot : ComplexObservableCode n)
    (hF : ∀ i, PolynomialCode.TermsDegreeLE D (F i))
    (hwdot : ComplexObservableTermsDegreeLE E wdot) :
    ∀ k, PolynomialCode.TermsDegreeLE (max D (E + 2))
      (fieldCode F η wdot k) := by
  intro k
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective k
  · simpa [fieldCode] using
      (liftBase_termsDegreeLE (hF i)).promote
        (Nat.le_max_left D (E + 2))
  · fin_cases j
    · simpa [fieldCode] using
        (reciprocalVelocityReCode_termsDegreeLE η wdot hwdot).promote
          (Nat.le_max_right D (E + 2))
    · simpa [fieldCode] using
        (reciprocalVelocityImCode_termsDegreeLE η wdot hwdot).promote
          (Nat.le_max_right D (E + 2))

/-- The real denominator coordinate `1 - η Re(w)` has degree at most
the degree bound for `w`. -/
theorem denominatorReCode_termsDegreeLE
    (η : RationalCode) (w : ComplexObservableCode n)
    (hw : ComplexObservableTermsDegreeLE W w) :
    PolynomialCode.TermsDegreeLE W
      (denominatorReCode η w) := by
  have hηw :
      PolynomialCode.TermsDegreeLE W
        (PolynomialCode.mul (etaCode η) (liftBase w.1)) := by
    simpa using
      PolynomialCode.termsDegreeLE_mul
        (etaCode_termsDegreeLE (n := n) η)
        (liftBase_termsDegreeLE hw.1)
  exact
    PolynomialCode.termsDegreeLE_sub
      ((oneCode_termsDegreeLE (n := n)).promote (Nat.zero_le W))
      hηw

/-- The imaginary denominator coordinate `-η Im(w)` has degree at most
the degree bound for `w`. -/
theorem denominatorImCode_termsDegreeLE
    (η : RationalCode) (w : ComplexObservableCode n)
    (hw : ComplexObservableTermsDegreeLE W w) :
    PolynomialCode.TermsDegreeLE W
      (denominatorImCode η w) := by
  apply PolynomialCode.termsDegreeLE_neg
  simpa using
    PolynomialCode.termsDegreeLE_mul
      (etaCode_termsDegreeLE (n := n) η)
      (liftBase_termsDegreeLE hw.2)

/-- The real reciprocal graph residual has degree at most `W + 1`. -/
theorem residualReCode_termsDegreeLE
    (η : RationalCode) (w : ComplexObservableCode n)
    (hw : ComplexObservableTermsDegreeLE W w) :
    PolynomialCode.TermsDegreeLE (W + 1)
      (residualReCode η w) := by
  have hre :
      PolynomialCode.TermsDegreeLE (W + 1)
        (PolynomialCode.mul (denominatorReCode η w)
          (reciprocalReCode :
            PolynomialCode (dimension n))) :=
    PolynomialCode.termsDegreeLE_mul
      (denominatorReCode_termsDegreeLE η w hw)
      (reciprocalReCode_termsDegreeLE (n := n))
  have him :
      PolynomialCode.TermsDegreeLE (W + 1)
        (PolynomialCode.mul (denominatorImCode η w)
          (reciprocalImCode :
            PolynomialCode (dimension n))) :=
    PolynomialCode.termsDegreeLE_mul
      (denominatorImCode_termsDegreeLE η w hw)
      (reciprocalImCode_termsDegreeLE (n := n))
  exact
    PolynomialCode.termsDegreeLE_sub
      (PolynomialCode.termsDegreeLE_sub hre him)
      ((oneCode_termsDegreeLE (n := n)).promote
        (Nat.zero_le (W + 1)))

/-- The imaginary reciprocal graph residual has degree at most `W + 1`. -/
theorem residualImCode_termsDegreeLE
    (η : RationalCode) (w : ComplexObservableCode n)
    (hw : ComplexObservableTermsDegreeLE W w) :
    PolynomialCode.TermsDegreeLE (W + 1)
      (residualImCode η w) := by
  exact
    PolynomialCode.termsDegreeLE_add
      (PolynomialCode.termsDegreeLE_mul
        (denominatorReCode_termsDegreeLE η w hw)
        (reciprocalImCode_termsDegreeLE (n := n)))
      (PolynomialCode.termsDegreeLE_mul
        (denominatorImCode_termsDegreeLE η w hw)
        (reciprocalReCode_termsDegreeLE (n := n)))

/-- The two reciprocal graph residuals share the uniform degree bound
`W + 1`. -/
theorem residualCodes_termsDegreeLE
    (η : RationalCode) (w : ComplexObservableCode n)
    (hw : ComplexObservableTermsDegreeLE W w) :
    PolynomialCode.TermsDegreeLE (W + 1)
        (residualReCode η w) ∧
      PolynomialCode.TermsDegreeLE (W + 1)
        (residualImCode η w) :=
  ⟨residualReCode_termsDegreeLE η w hw,
    residualImCode_termsDegreeLE η w hw⟩

end HGAS.ComplexReciprocalPolynomialCode
