import HGAS.Accumulator.PolynomialDegrees
import HGAS.Clocks.RHSOscillatorPolynomialCode
import HGAS.Compiler.CompactAccumulatorPipelineDegrees
import Mathlib.Tactic

/-!
# Degree ledger for the right-hand-side oscillator compiler

If every supplied frequency polynomial has degree at most `E`, then the
weighted sum has degree at most `E` and each oscillator equation has degree
at most `E+1`.  In the manuscript application the literal frequencies
`pᵢrᵢ` are linear, so the added equations are quadratic independently of the
input-dependent integer coefficients.
-/

namespace HGAS.Clocks.RHSOscillatorPolynomialCode

open HGAS

variable {n q D E : ℕ}

theorem liftBase_termsDegreeLE
    {p : PolynomialCode n}
    (hp : PolynomialCode.TermsDegreeLE D p) :
    PolynomialCode.TermsDegreeLE D (liftBase (p := p)) :=
  PolynomialCode.termsDegreeLE_injectVariables _ hp

theorem weightedFrequencyCode_termsDegreeLE
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n)
    (hν : ∀ i, PolynomialCode.TermsDegreeLE E (ν i)) :
    PolynomialCode.TermsDegreeLE E
      (weightedFrequencyCode a ν) := by
  rw [weightedFrequencyCode]
  apply PolynomialCode.termsDegreeLE_sumCodes
  intro p hp
  rw [List.mem_ofFn] at hp
  obtain ⟨i, rfl⟩ := hp
  have ha :
      PolynomialCode.TermsDegreeLE 0
        (PolynomialCode.constant (a i) :
          PolynomialCode (dimension n)) :=
    PolynomialCode.termsDegreeLE_constant (a i)
  have hν' :
      PolynomialCode.TermsDegreeLE E (liftBase (ν i)) :=
    liftBase_termsDegreeLE (hν i)
  simpa using PolynomialCode.termsDegreeLE_mul ha hν'

theorem xFieldCode_termsDegreeLE
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n)
    (hν : ∀ i, PolynomialCode.TermsDegreeLE E (ν i)) :
    PolynomialCode.TermsDegreeLE (E + 1)
      (xFieldCode a ν) := by
  have hfour :
      PolynomialCode.TermsDegreeLE 0
        (fourCode : PolynomialCode (dimension n)) :=
    PolynomialCode.termsDegreeLE_constant _
  have hfrequency :=
    weightedFrequencyCode_termsDegreeLE a ν hν
  have hproduct :
      PolynomialCode.TermsDegreeLE E
        (PolynomialCode.mul fourCode
          (weightedFrequencyCode a ν)) := by
    simpa using
      PolynomialCode.termsDegreeLE_mul hfour hfrequency
  simpa [xFieldCode, yCode] using
    PolynomialCode.termsDegreeLE_mul hproduct
      (PolynomialCode.termsDegreeLE_varCode (yIndex n))

theorem yFieldCode_termsDegreeLE
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n)
    (hν : ∀ i, PolynomialCode.TermsDegreeLE E (ν i)) :
    PolynomialCode.TermsDegreeLE (E + 1)
      (yFieldCode a ν) := by
  have hfour :
      PolynomialCode.TermsDegreeLE 0
        (fourCode : PolynomialCode (dimension n)) :=
    PolynomialCode.termsDegreeLE_constant _
  have hfrequency :=
    weightedFrequencyCode_termsDegreeLE a ν hν
  have hproduct :
      PolynomialCode.TermsDegreeLE E
        (PolynomialCode.mul fourCode
          (weightedFrequencyCode a ν)) := by
    simpa using
      PolynomialCode.termsDegreeLE_mul hfour hfrequency
  apply PolynomialCode.termsDegreeLE_neg
  simpa [xCode] using
    PolynomialCode.termsDegreeLE_mul hproduct
      (PolynomialCode.termsDegreeLE_varCode (xIndex n))

/-- Complete degree ledger for adjoining the oscillator to a base field. -/
theorem fieldCode_termsDegreeLE
    (F : PolynomialFieldCode n)
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n)
    (hF : ∀ i, PolynomialCode.TermsDegreeLE D (F i))
    (hν : ∀ i, PolynomialCode.TermsDegreeLE E (ν i))
    (hED : E + 1 ≤ D) :
    ∀ k, PolynomialCode.TermsDegreeLE D
      (fieldCode F a ν k) := by
  intro k
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective k
  · change PolynomialCode.TermsDegreeLE D
      (fieldCode F a ν
        (PolynomialBlockCode.leftEmbedding (p := 2) i))
    rw [fieldCode_base]
    exact liftBase_termsDegreeLE (hF i)
  · fin_cases j
    · change PolynomialCode.TermsDegreeLE D
        (fieldCode F a ν (xIndex n))
      rw [fieldCode_x]
      exact (xFieldCode_termsDegreeLE a ν hν).promote hED
    · change PolynomialCode.TermsDegreeLE D
        (fieldCode F a ν (yIndex n))
      rw [fieldCode_y]
      exact (yFieldCode_termsDegreeLE a ν hν).promote hED

/-- The manuscript specialization: linear frequencies add only quadratic
oscillator equations. -/
theorem oscillatorComponents_termsDegreeLE_two
    (a : Fin q → RationalCode)
    (ν : Fin q → PolynomialCode n)
    (hν : ∀ i, PolynomialCode.TermsDegreeLE 1 (ν i)) :
    PolynomialCode.TermsDegreeLE 2 (xFieldCode a ν) ∧
      PolynomialCode.TermsDegreeLE 2 (yFieldCode a ν) := by
  exact ⟨xFieldCode_termsDegreeLE a ν hν,
    yFieldCode_termsDegreeLE a ν hν⟩

end HGAS.Clocks.RHSOscillatorPolynomialCode
