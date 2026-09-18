import HGAS.Compiler.ComplexReciprocalFamilyPolynomialCode
import HGAS.Compiler.ComplexReciprocalPolynomialDegrees
import Mathlib.Tactic

/-!
# Degree bounds for a finite family of complex reciprocal extensions

The family compiler is assembled by injective variable transport from the
one-reciprocal compiler.  Raw sparse monomial degree is therefore preserved
block by block.

If the common base field has degree at most `D` and every component of every
`wdotₐ` has degree at most `E`, the enlarged field has degree at most

```text
                         max D (E + 2).
```

If every component of every observable `wₐ` has degree at most `W`, all
`2b` reciprocal graph residual coordinates have degree at most `W + 1`.
The bounds are independent of the family size `b` and include `b = 0`.
-/

namespace HGAS.ComplexReciprocalFamilyPolynomialCode

variable {n b D E W : ℕ}

/-- Uniform componentwise degree bound for a finite observable family. -/
def ObservableFamilyTermsDegreeLE
    (d : ℕ) (p : ObservableFamily n b) : Prop :=
  ∀ a,
    ComplexReciprocalPolynomialCode.ComplexObservableTermsDegreeLE
      d (p a)

instance observableFamilyTermsDegreeLEDecidable
    (d : ℕ) (p : ObservableFamily n b) :
    Decidable (ObservableFamilyTermsDegreeLE d p) := by
  unfold ObservableFamilyTermsDegreeLE
  infer_instance

/-- Injecting a one-reciprocal code into a selected family block preserves
every raw total-degree bound. -/
theorem liftSingle_termsDegreeLE
    (a : Fin b)
    {p :
      PolynomialCode
        (ComplexReciprocalPolynomialCode.dimension n)}
    (hp : PolynomialCode.TermsDegreeLE D p) :
    PolynomialCode.TermsDegreeLE D (liftSingle a p) :=
  PolynomialCode.termsDegreeLE_injectVariables _ hp

/-- Inserting a common-base polynomial preserves raw total degree. -/
theorem liftBase_termsDegreeLE
    {p : PolynomialCode n}
    (hp : PolynomialCode.TermsDegreeLE D p) :
    PolynomialCode.TermsDegreeLE D
      (liftBase (b := b) p) :=
  PolynomialCode.termsDegreeLE_injectVariables _ hp

/-- Each real reciprocal velocity coordinate has degree at most `E + 2`. -/
theorem reciprocalVelocityReCode_termsDegreeLE
    (η : Fin b → RationalCode)
    (wdot : ObservableFamily n b)
    (hwdot : ObservableFamilyTermsDegreeLE E wdot)
    (a : Fin b) :
    PolynomialCode.TermsDegreeLE (E + 2)
      (reciprocalVelocityReCode η wdot a) := by
  exact
    liftSingle_termsDegreeLE a
      (ComplexReciprocalPolynomialCode.reciprocalVelocityReCode_termsDegreeLE
          (η a) (wdot a) (hwdot a))

/-- Each imaginary reciprocal velocity coordinate has degree at most
`E + 2`. -/
theorem reciprocalVelocityImCode_termsDegreeLE
    (η : Fin b → RationalCode)
    (wdot : ObservableFamily n b)
    (hwdot : ObservableFamilyTermsDegreeLE E wdot)
    (a : Fin b) :
    PolynomialCode.TermsDegreeLE (E + 2)
      (reciprocalVelocityImCode η wdot a) := by
  exact
    liftSingle_termsDegreeLE a
      (ComplexReciprocalPolynomialCode.reciprocalVelocityImCode_termsDegreeLE
          (η a) (wdot a) (hwdot a))

/-- Uniform field degree, independent of the number of reciprocal blocks. -/
theorem fieldCode_termsDegreeLE
    (F : PolynomialFieldCode n)
    (η : Fin b → RationalCode)
    (wdot : ObservableFamily n b)
    (hF : ∀ i, PolynomialCode.TermsDegreeLE D (F i))
    (hwdot : ObservableFamilyTermsDegreeLE E wdot) :
    ∀ k,
      PolynomialCode.TermsDegreeLE (max D (E + 2))
        (fieldCode F η wdot k) := by
  intro k
  obtain ⟨i | r, rfl⟩ := finSumFinEquiv.surjective k
  · simpa [fieldCode] using
      (liftBase_termsDegreeLE (b := b) (hF i)).promote
        (Nat.le_max_left D (E + 2))
  · obtain ⟨⟨a, j⟩, rfl⟩ :=
      finProdFinEquiv.surjective r
    fin_cases j
    · change
        PolynomialCode.TermsDegreeLE (max D (E + 2))
          (fieldCode F η wdot (reciprocalReIndex a))
      rw [fieldCode_reciprocalReIndex]
      exact
        (reciprocalVelocityReCode_termsDegreeLE
          η wdot hwdot a).promote
            (Nat.le_max_right D (E + 2))
    · change
        PolynomialCode.TermsDegreeLE (max D (E + 2))
          (fieldCode F η wdot (reciprocalImIndex a))
      rw [fieldCode_reciprocalImIndex]
      exact
        (reciprocalVelocityImCode_termsDegreeLE
          η wdot hwdot a).promote
            (Nat.le_max_right D (E + 2))

/-- Real graph residual of each block has degree at most `W + 1`. -/
theorem residualReCode_termsDegreeLE
    (η : Fin b → RationalCode)
    (w : ObservableFamily n b)
    (hw : ObservableFamilyTermsDegreeLE W w)
    (a : Fin b) :
    PolynomialCode.TermsDegreeLE (W + 1)
      (residualReCode η w a) := by
  exact
    liftSingle_termsDegreeLE a
      (ComplexReciprocalPolynomialCode.residualReCode_termsDegreeLE
          (η a) (w a) (hw a))

/-- Imaginary graph residual of each block has degree at most `W + 1`. -/
theorem residualImCode_termsDegreeLE
    (η : Fin b → RationalCode)
    (w : ObservableFamily n b)
    (hw : ObservableFamilyTermsDegreeLE W w)
    (a : Fin b) :
    PolynomialCode.TermsDegreeLE (W + 1)
      (residualImCode η w a) := by
  exact
    liftSingle_termsDegreeLE a
      (ComplexReciprocalPolynomialCode.residualImCode_termsDegreeLE
          (η a) (w a) (hw a))

/-- All `2b` flattened residual coordinates share the bound `W + 1`. -/
theorem residualCode_termsDegreeLE
    (η : Fin b → RationalCode)
    (w : ObservableFamily n b)
    (hw : ObservableFamilyTermsDegreeLE W w) :
    ∀ k,
      PolynomialCode.TermsDegreeLE (W + 1)
        (residualCode η w k) := by
  intro k
  obtain ⟨⟨a, j⟩, rfl⟩ :=
    finProdFinEquiv.surjective k
  change
    PolynomialCode.TermsDegreeLE (W + 1)
      (residualCode η w (reciprocalBlockEmbedding a j))
  rw [residualCode_reciprocalBlockEmbedding]
  fin_cases j
  · exact residualReCode_termsDegreeLE η w hw a
  · exact residualImCode_termsDegreeLE η w hw a

end HGAS.ComplexReciprocalFamilyPolynomialCode
