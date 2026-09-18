import HGAS.Algebra.ComplexPolynomialDegrees
import HGAS.Modular.UnaryPolynomialCode
import Mathlib.Tactic

/-!
# Raw degree bounds for the unary modular compiler

These bounds concern the *raw sparse syntax*, before normalization or
cancellation.  They are therefore robust compiler guarantees:

* the basic `(A,C,E,Y)` field is quadratic;
* the square-root extension has degree at most four (only the `H`
  equation reaches degree four);
* the fourth-root gauge field is linear;
* every validity residual has degree at most four.

The fixed-expression checks are discharged by evaluation of the finite
syntax.  The parameterized clock-rate statements then follow from the
general theorem that multiplication by a Gaussian-rational constant does
not increase degree.  Finally, the bounds pass unchanged through
realification.
-/

namespace HGAS.Modular

open HGAS

namespace UnaryPolynomialCode

private theorem rational_termsDegreeLE
    {n : ℕ} (q : ℚ) :
    ComplexPolynomialCode.TermsDegreeLE 0
      (rational q : ComplexPolynomialCode n) := by
  simpa [rational] using
    (ComplexPolynomialCode.termsDegreeLE_rationalConstant
      (n := n) (RationalCode.encode q))

private theorem scalarMul_termsDegreeLE
    {n D : ℕ} (q : ℚ) {p : ComplexPolynomialCode n}
    (hp : ComplexPolynomialCode.TermsDegreeLE D p) :
    ComplexPolynomialCode.TermsDegreeLE D
      (ComplexPolynomialCode.mul (rational q) p) := by
  have h :=
    ComplexPolynomialCode.termsDegreeLE_mul
      (rational_termsDegreeLE (n := n) q) hp
  simpa using h

private theorem modularAFieldCode_termsDegreeLE :
    ComplexPolynomialCode.TermsDegreeLE 2 modularAFieldCode := by
  have hA := ComplexPolynomialCode.termsDegreeLE_var AIndex
  have hC := ComplexPolynomialCode.termsDegreeLE_var CIndex
  have hE := ComplexPolynomialCode.termsDegreeLE_var EIndex
  have h2C :
      ComplexPolynomialCode.TermsDegreeLE 1
        (ComplexPolynomialCode.mul (rational 2) CCode) :=
    scalarMul_termsDegreeLE 2 hC
  have hsum :
      ComplexPolynomialCode.TermsDegreeLE 1
        (ComplexPolynomialCode.add
          (ComplexPolynomialCode.add ECode ACode)
          (ComplexPolynomialCode.mul (rational 2) CCode)) :=
    ComplexPolynomialCode.termsDegreeLE_add
      (ComplexPolynomialCode.termsDegreeLE_add hE hA) h2C
  have hqA :
      ComplexPolynomialCode.TermsDegreeLE 1
        (ComplexPolynomialCode.mul (rational (1 / 3)) ACode) :=
    scalarMul_termsDegreeLE (1 / 3) hA
  simpa [modularAFieldCode] using
    (ComplexPolynomialCode.termsDegreeLE_mul hqA hsum)

private theorem modularCFieldCode_termsDegreeLE :
    ComplexPolynomialCode.TermsDegreeLE 2 modularCFieldCode := by
  have hA := ComplexPolynomialCode.termsDegreeLE_var AIndex
  have hC := ComplexPolynomialCode.termsDegreeLE_var CIndex
  have hE := ComplexPolynomialCode.termsDegreeLE_var EIndex
  have h2A :
      ComplexPolynomialCode.TermsDegreeLE 1
        (ComplexPolynomialCode.mul (rational 2) ACode) :=
    scalarMul_termsDegreeLE 2 hA
  have hinner :
      ComplexPolynomialCode.TermsDegreeLE 1
        (ComplexPolynomialCode.sub
          (ComplexPolynomialCode.sub ECode
            (ComplexPolynomialCode.mul (rational 2) ACode))
          CCode) :=
    ComplexPolynomialCode.termsDegreeLE_sub
      (ComplexPolynomialCode.termsDegreeLE_sub hE h2A) hC
  have hqC :
      ComplexPolynomialCode.TermsDegreeLE 1
        (ComplexPolynomialCode.mul (rational (1 / 3)) CCode) :=
    scalarMul_termsDegreeLE (1 / 3) hC
  simpa [modularCFieldCode] using
    (ComplexPolynomialCode.termsDegreeLE_mul hqC hinner)

private theorem modularEFieldCode_termsDegreeLE :
    ComplexPolynomialCode.TermsDegreeLE 2 modularEFieldCode := by
  have hA := ComplexPolynomialCode.termsDegreeLE_var AIndex
  have hC := ComplexPolynomialCode.termsDegreeLE_var CIndex
  have hE := ComplexPolynomialCode.termsDegreeLE_var EIndex
  have hE2 :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.pow ECode 2) := by
    simpa using ComplexPolynomialCode.termsDegreeLE_pow hE 2
  have hA2 :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.pow ACode 2) := by
    simpa using ComplexPolynomialCode.termsDegreeLE_pow hA 2
  have hAC :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.mul ACode CCode) := by
    simpa using ComplexPolynomialCode.termsDegreeLE_mul hA hC
  have hC2 :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.pow CCode 2) := by
    simpa using ComplexPolynomialCode.termsDegreeLE_pow hC 2
  have hinner :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.sub
          (ComplexPolynomialCode.sub
            (ComplexPolynomialCode.sub
              (ComplexPolynomialCode.pow ECode 2)
              (ComplexPolynomialCode.pow ACode 2))
            (ComplexPolynomialCode.mul ACode CCode))
          (ComplexPolynomialCode.pow CCode 2)) :=
    ComplexPolynomialCode.termsDegreeLE_sub
      (ComplexPolynomialCode.termsDegreeLE_sub
        (ComplexPolynomialCode.termsDegreeLE_sub hE2 hA2) hAC) hC2
  simpa [modularEFieldCode] using
    scalarMul_termsDegreeLE (1 / 6) hinner

private theorem modularYFieldCode_termsDegreeLE :
    ComplexPolynomialCode.TermsDegreeLE 2 modularYFieldCode := by
  have hA := ComplexPolynomialCode.termsDegreeLE_var AIndex
  have hC := ComplexPolynomialCode.termsDegreeLE_var CIndex
  have hE := ComplexPolynomialCode.termsDegreeLE_var EIndex
  have hY := ComplexPolynomialCode.termsDegreeLE_var YIndex
  have hinner :
      ComplexPolynomialCode.TermsDegreeLE 1
        (ComplexPolynomialCode.sub
          (ComplexPolynomialCode.add ECode ACode) CCode) :=
    ComplexPolynomialCode.termsDegreeLE_sub
      (ComplexPolynomialCode.termsDegreeLE_add hE hA) hC
  have hqinner :
      ComplexPolynomialCode.TermsDegreeLE 1
        (ComplexPolynomialCode.mul (rational (1 / 12))
          (ComplexPolynomialCode.sub
            (ComplexPolynomialCode.add ECode ACode) CCode)) :=
    scalarMul_termsDegreeLE (1 / 12) hinner
  simpa [modularYFieldCode] using
    (ComplexPolynomialCode.termsDegreeLE_mul hqinner hY)

/-- Every raw monomial in the fixed unary field has degree at most two. -/
theorem modularFieldCode_termsDegreeLE :
    ComplexPolynomialFieldCode.TermsDegreeLE 2 modularFieldCode := by
  intro i
  fin_cases i
  · exact modularAFieldCode_termsDegreeLE
  · exact modularCFieldCode_termsDegreeLE
  · exact modularEFieldCode_termsDegreeLE
  · exact modularYFieldCode_termsDegreeLE

/-- A coded Gaussian-rational clock rate does not change the quadratic
degree bound. -/
theorem scaledModularFieldCode_termsDegreeLE
    (κ : GaussianRationalCode) :
    ComplexPolynomialFieldCode.TermsDegreeLE 2
      (scaledModularFieldCode κ) := by
  intro i
  exact
    ComplexPolynomialCode.termsDegreeLE_mulGaussian κ
      (modularFieldCode_termsDegreeLE i)

/-- The realified unary compiler is quadratic in all eight real
coordinates. -/
theorem compileModularFieldCode_termsDegreeLE
    (κ : GaussianRationalCode) :
    ∀ i, PolynomialCode.TermsDegreeLE 2
      (compileModularFieldCode κ i) := by
  exact
    ComplexPolynomialFieldCode.realify_termsDegreeLE
      (scaledModularFieldCode_termsDegreeLE κ)

/-- Jacobi's residual `Y⁴-A-C` has raw degree at most four. -/
theorem jacobiResidualCode_termsDegreeLE :
    ComplexPolynomialCode.TermsDegreeLE 4 jacobiResidualCode := by
  have hA :=
    (ComplexPolynomialCode.termsDegreeLE_var AIndex).promote
      (by omega : 1 ≤ 4)
  have hC :=
    (ComplexPolynomialCode.termsDegreeLE_var CIndex).promote
      (by omega : 1 ≤ 4)
  have hY4 :
      ComplexPolynomialCode.TermsDegreeLE 4
        (ComplexPolynomialCode.pow YCode 4) := by
    simpa using
      ComplexPolynomialCode.termsDegreeLE_pow
        (ComplexPolynomialCode.termsDegreeLE_var YIndex) 4
  exact
    ComplexPolynomialCode.termsDegreeLE_sub
      (ComplexPolynomialCode.termsDegreeLE_sub hY4 hA) hC

/-! ## Root extension -/

private theorem rootAFieldCode_termsDegreeLE :
    ComplexPolynomialCode.TermsDegreeLE 2 rootAFieldCode := by
  have hA := ComplexPolynomialCode.termsDegreeLE_var rootAIndex
  have hC := ComplexPolynomialCode.termsDegreeLE_var rootCIndex
  have hE := ComplexPolynomialCode.termsDegreeLE_var rootEIndex
  have h2C :
      ComplexPolynomialCode.TermsDegreeLE 1
        (ComplexPolynomialCode.mul (rational 2) rC) :=
    scalarMul_termsDegreeLE 2 hC
  have hsum :
      ComplexPolynomialCode.TermsDegreeLE 1
        (ComplexPolynomialCode.add
          (ComplexPolynomialCode.add rE rA)
          (ComplexPolynomialCode.mul (rational 2) rC)) :=
    ComplexPolynomialCode.termsDegreeLE_add
      (ComplexPolynomialCode.termsDegreeLE_add hE hA) h2C
  have hqA :
      ComplexPolynomialCode.TermsDegreeLE 1
        (ComplexPolynomialCode.mul (rational (1 / 3)) rA) :=
    scalarMul_termsDegreeLE (1 / 3) hA
  simpa [rootAFieldCode] using
    (ComplexPolynomialCode.termsDegreeLE_mul hqA hsum)

private theorem rootCFieldCode_termsDegreeLE :
    ComplexPolynomialCode.TermsDegreeLE 2 rootCFieldCode := by
  have hA := ComplexPolynomialCode.termsDegreeLE_var rootAIndex
  have hC := ComplexPolynomialCode.termsDegreeLE_var rootCIndex
  have hE := ComplexPolynomialCode.termsDegreeLE_var rootEIndex
  have h2A :
      ComplexPolynomialCode.TermsDegreeLE 1
        (ComplexPolynomialCode.mul (rational 2) rA) :=
    scalarMul_termsDegreeLE 2 hA
  have hinner :
      ComplexPolynomialCode.TermsDegreeLE 1
        (ComplexPolynomialCode.sub
          (ComplexPolynomialCode.sub rE
            (ComplexPolynomialCode.mul (rational 2) rA))
          rC) :=
    ComplexPolynomialCode.termsDegreeLE_sub
      (ComplexPolynomialCode.termsDegreeLE_sub hE h2A) hC
  have hqC :
      ComplexPolynomialCode.TermsDegreeLE 1
        (ComplexPolynomialCode.mul (rational (1 / 3)) rC) :=
    scalarMul_termsDegreeLE (1 / 3) hC
  simpa [rootCFieldCode] using
    (ComplexPolynomialCode.termsDegreeLE_mul hqC hinner)

private theorem rootEFieldCode_termsDegreeLE :
    ComplexPolynomialCode.TermsDegreeLE 2 rootEFieldCode := by
  have hA := ComplexPolynomialCode.termsDegreeLE_var rootAIndex
  have hC := ComplexPolynomialCode.termsDegreeLE_var rootCIndex
  have hE := ComplexPolynomialCode.termsDegreeLE_var rootEIndex
  have hE2 :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.pow rE 2) := by
    simpa using ComplexPolynomialCode.termsDegreeLE_pow hE 2
  have hA2 :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.pow rA 2) := by
    simpa using ComplexPolynomialCode.termsDegreeLE_pow hA 2
  have hAC :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.mul rA rC) := by
    simpa using ComplexPolynomialCode.termsDegreeLE_mul hA hC
  have hC2 :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.pow rC 2) := by
    simpa using ComplexPolynomialCode.termsDegreeLE_pow hC 2
  have hinner :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.sub
          (ComplexPolynomialCode.sub
            (ComplexPolynomialCode.sub
              (ComplexPolynomialCode.pow rE 2)
              (ComplexPolynomialCode.pow rA 2))
            (ComplexPolynomialCode.mul rA rC))
          (ComplexPolynomialCode.pow rC 2)) :=
    ComplexPolynomialCode.termsDegreeLE_sub
      (ComplexPolynomialCode.termsDegreeLE_sub
        (ComplexPolynomialCode.termsDegreeLE_sub hE2 hA2) hAC) hC2
  simpa [rootEFieldCode] using
    scalarMul_termsDegreeLE (1 / 6) hinner

private theorem rootYFieldCode_termsDegreeLE :
    ComplexPolynomialCode.TermsDegreeLE 2 rootYFieldCode := by
  have hA := ComplexPolynomialCode.termsDegreeLE_var rootAIndex
  have hC := ComplexPolynomialCode.termsDegreeLE_var rootCIndex
  have hE := ComplexPolynomialCode.termsDegreeLE_var rootEIndex
  have hY := ComplexPolynomialCode.termsDegreeLE_var rootYIndex
  have hinner :
      ComplexPolynomialCode.TermsDegreeLE 1
        (ComplexPolynomialCode.sub
          (ComplexPolynomialCode.add rE rA) rC) :=
    ComplexPolynomialCode.termsDegreeLE_sub
      (ComplexPolynomialCode.termsDegreeLE_add hE hA) hC
  have hqinner :
      ComplexPolynomialCode.TermsDegreeLE 1
        (ComplexPolynomialCode.mul (rational (1 / 12))
          (ComplexPolynomialCode.sub
            (ComplexPolynomialCode.add rE rA) rC)) :=
    scalarMul_termsDegreeLE (1 / 12) hinner
  simpa [rootYFieldCode] using
    (ComplexPolynomialCode.termsDegreeLE_mul hqinner hY)

private theorem p2FieldCode_termsDegreeLE :
    ComplexPolynomialCode.TermsDegreeLE 3 p2FieldCode := by
  have hp2 := ComplexPolynomialCode.termsDegreeLE_var p2Index
  have hp4 := ComplexPolynomialCode.termsDegreeLE_var p4Index
  have hH := ComplexPolynomialCode.termsDegreeLE_var HIndex
  have h12H :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.mul (rational 12) rH) :=
    (scalarMul_termsDegreeLE 12 hH).promote (by omega)
  have hp2sq :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.pow rp2 2) := by
    simpa using ComplexPolynomialCode.termsDegreeLE_pow hp2 2
  have hp4sq :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.pow rp4 2) := by
    simpa using ComplexPolynomialCode.termsDegreeLE_pow hp4 2
  have h2p4sq :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.mul (rational 2)
          (ComplexPolynomialCode.pow rp4 2)) :=
    scalarMul_termsDegreeLE 2 hp4sq
  have hinner :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.add
          (ComplexPolynomialCode.add
            (ComplexPolynomialCode.mul (rational 12) rH)
            (ComplexPolynomialCode.pow rp2 2))
          (ComplexPolynomialCode.mul (rational 2)
            (ComplexPolynomialCode.pow rp4 2))) :=
    ComplexPolynomialCode.termsDegreeLE_add
      (ComplexPolynomialCode.termsDegreeLE_add h12H hp2sq) h2p4sq
  have hscaled :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.mul (rational (1 / 6))
          (ComplexPolynomialCode.add
            (ComplexPolynomialCode.add
              (ComplexPolynomialCode.mul (rational 12) rH)
              (ComplexPolynomialCode.pow rp2 2))
            (ComplexPolynomialCode.mul (rational 2)
              (ComplexPolynomialCode.pow rp4 2)))) :=
    scalarMul_termsDegreeLE (1 / 6) hinner
  simpa [p2FieldCode] using
    (ComplexPolynomialCode.termsDegreeLE_mul hscaled hp2)

private theorem p3FieldCode_termsDegreeLE :
    ComplexPolynomialCode.TermsDegreeLE 3 p3FieldCode := by
  have hp2 := ComplexPolynomialCode.termsDegreeLE_var p2Index
  have hp3 := ComplexPolynomialCode.termsDegreeLE_var p3Index
  have hp4 := ComplexPolynomialCode.termsDegreeLE_var p4Index
  have hH := ComplexPolynomialCode.termsDegreeLE_var HIndex
  have h12H :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.mul (rational 12) rH) :=
    (scalarMul_termsDegreeLE 12 hH).promote (by omega)
  have hp2sq :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.pow rp2 2) := by
    simpa using ComplexPolynomialCode.termsDegreeLE_pow hp2 2
  have hp4sq :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.pow rp4 2) := by
    simpa using ComplexPolynomialCode.termsDegreeLE_pow hp4 2
  have hinner :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.sub
          (ComplexPolynomialCode.add
            (ComplexPolynomialCode.mul (rational 12) rH)
            (ComplexPolynomialCode.pow rp2 2))
          (ComplexPolynomialCode.pow rp4 2)) :=
    ComplexPolynomialCode.termsDegreeLE_sub
      (ComplexPolynomialCode.termsDegreeLE_add h12H hp2sq) hp4sq
  have hscaled :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.mul (rational (1 / 6))
          (ComplexPolynomialCode.sub
            (ComplexPolynomialCode.add
              (ComplexPolynomialCode.mul (rational 12) rH)
              (ComplexPolynomialCode.pow rp2 2))
            (ComplexPolynomialCode.pow rp4 2))) :=
    scalarMul_termsDegreeLE (1 / 6) hinner
  simpa [p3FieldCode] using
    (ComplexPolynomialCode.termsDegreeLE_mul hscaled hp3)

private theorem p4FieldCode_termsDegreeLE :
    ComplexPolynomialCode.TermsDegreeLE 3 p4FieldCode := by
  have hp2 := ComplexPolynomialCode.termsDegreeLE_var p2Index
  have hp4 := ComplexPolynomialCode.termsDegreeLE_var p4Index
  have hH := ComplexPolynomialCode.termsDegreeLE_var HIndex
  have h12H :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.mul (rational 12) rH) :=
    (scalarMul_termsDegreeLE 12 hH).promote (by omega)
  have hp2sq :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.pow rp2 2) := by
    simpa using ComplexPolynomialCode.termsDegreeLE_pow hp2 2
  have h2p2sq :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.mul (rational 2)
          (ComplexPolynomialCode.pow rp2 2)) :=
    scalarMul_termsDegreeLE 2 hp2sq
  have hp4sq :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.pow rp4 2) := by
    simpa using ComplexPolynomialCode.termsDegreeLE_pow hp4 2
  have hinner :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.sub
          (ComplexPolynomialCode.sub
            (ComplexPolynomialCode.mul (rational 12) rH)
            (ComplexPolynomialCode.mul (rational 2)
              (ComplexPolynomialCode.pow rp2 2)))
          (ComplexPolynomialCode.pow rp4 2)) :=
    ComplexPolynomialCode.termsDegreeLE_sub
      (ComplexPolynomialCode.termsDegreeLE_sub h12H h2p2sq) hp4sq
  have hscaled :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.mul (rational (1 / 6))
          (ComplexPolynomialCode.sub
            (ComplexPolynomialCode.sub
              (ComplexPolynomialCode.mul (rational 12) rH)
              (ComplexPolynomialCode.mul (rational 2)
                (ComplexPolynomialCode.pow rp2 2)))
            (ComplexPolynomialCode.pow rp4 2))) :=
    scalarMul_termsDegreeLE (1 / 6) hinner
  simpa [p4FieldCode] using
    (ComplexPolynomialCode.termsDegreeLE_mul hscaled hp4)

private theorem HFieldCode_termsDegreeLE :
    ComplexPolynomialCode.TermsDegreeLE 4 HFieldCode := by
  have hp2 := ComplexPolynomialCode.termsDegreeLE_var p2Index
  have hp4 := ComplexPolynomialCode.termsDegreeLE_var p4Index
  have hH := ComplexPolynomialCode.termsDegreeLE_var HIndex
  have h12H :
      ComplexPolynomialCode.TermsDegreeLE 1
        (ComplexPolynomialCode.mul (rational 12) rH) :=
    scalarMul_termsDegreeLE 12 hH
  have h12Hsq :
      ComplexPolynomialCode.TermsDegreeLE 4
        (ComplexPolynomialCode.pow
          (ComplexPolynomialCode.mul (rational 12) rH) 2) := by
    have hsq :
        ComplexPolynomialCode.TermsDegreeLE 2
          (ComplexPolynomialCode.pow
            (ComplexPolynomialCode.mul (rational 12) rH) 2) := by
      simpa using
        ComplexPolynomialCode.termsDegreeLE_pow h12H 2
    exact hsq.promote (by omega)
  have hp2four :
      ComplexPolynomialCode.TermsDegreeLE 4
        (ComplexPolynomialCode.pow rp2 4) := by
    simpa using ComplexPolynomialCode.termsDegreeLE_pow hp2 4
  have hp4four :
      ComplexPolynomialCode.TermsDegreeLE 4
        (ComplexPolynomialCode.pow rp4 4) := by
    simpa using ComplexPolynomialCode.termsDegreeLE_pow hp4 4
  have hp2sq :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.pow rp2 2) := by
    simpa using ComplexPolynomialCode.termsDegreeLE_pow hp2 2
  have hp4sq :
      ComplexPolynomialCode.TermsDegreeLE 2
        (ComplexPolynomialCode.pow rp4 2) := by
    simpa using ComplexPolynomialCode.termsDegreeLE_pow hp4 2
  have hcross :
      ComplexPolynomialCode.TermsDegreeLE 4
        (ComplexPolynomialCode.mul
          (ComplexPolynomialCode.pow rp2 2)
          (ComplexPolynomialCode.pow rp4 2)) := by
    simpa using ComplexPolynomialCode.termsDegreeLE_mul hp2sq hp4sq
  have hinner :
      ComplexPolynomialCode.TermsDegreeLE 4
        (ComplexPolynomialCode.sub
          (ComplexPolynomialCode.sub
            (ComplexPolynomialCode.sub
              (ComplexPolynomialCode.pow
                (ComplexPolynomialCode.mul (rational 12) rH) 2)
              (ComplexPolynomialCode.pow rp2 4))
            (ComplexPolynomialCode.mul
              (ComplexPolynomialCode.pow rp2 2)
              (ComplexPolynomialCode.pow rp4 2)))
          (ComplexPolynomialCode.pow rp4 4)) :=
    ComplexPolynomialCode.termsDegreeLE_sub
      (ComplexPolynomialCode.termsDegreeLE_sub
        (ComplexPolynomialCode.termsDegreeLE_sub h12Hsq hp2four)
        hcross) hp4four
  simpa [HFieldCode] using
    scalarMul_termsDegreeLE (1 / 72) hinner

/-- The full square-root extension has raw degree at most four. -/
theorem rootFieldCode_termsDegreeLE :
    ComplexPolynomialFieldCode.TermsDegreeLE 4 rootFieldCode := by
  intro i
  fin_cases i
  · exact rootAFieldCode_termsDegreeLE.promote (by omega)
  · exact rootCFieldCode_termsDegreeLE.promote (by omega)
  · exact rootEFieldCode_termsDegreeLE.promote (by omega)
  · exact rootYFieldCode_termsDegreeLE.promote (by omega)
  · exact p2FieldCode_termsDegreeLE.promote (by omega)
  · exact p3FieldCode_termsDegreeLE.promote (by omega)
  · exact p4FieldCode_termsDegreeLE.promote (by omega)
  · exact HFieldCode_termsDegreeLE

theorem scaledRootFieldCode_termsDegreeLE
    (κ : GaussianRationalCode) :
    ComplexPolynomialFieldCode.TermsDegreeLE 4
      (scaledRootFieldCode κ) := by
  intro i
  exact
    ComplexPolynomialCode.termsDegreeLE_mulGaussian κ
      (rootFieldCode_termsDegreeLE i)

/-- The realified root compiler has the same quartic bound on all sixteen
real components. -/
theorem compileRootFieldCode_termsDegreeLE
    (κ : GaussianRationalCode) :
    ∀ i, PolynomialCode.TermsDegreeLE 4
      (compileRootFieldCode κ i) := by
  exact
    ComplexPolynomialFieldCode.realify_termsDegreeLE
      (scaledRootFieldCode_termsDegreeLE κ)

/-- Uniform quartic raw bound for `R_J,L₂,L₄,L_H,S₃`. -/
theorem rootResidualCode_termsDegreeLE (i : Fin 5) :
    ComplexPolynomialCode.TermsDegreeLE 4
      (rootResidualCode i) := by
  have hA :=
    (ComplexPolynomialCode.termsDegreeLE_var rootAIndex).promote
      (by omega : 1 ≤ 4)
  have hC :=
    (ComplexPolynomialCode.termsDegreeLE_var rootCIndex).promote
      (by omega : 1 ≤ 4)
  have hE :=
    (ComplexPolynomialCode.termsDegreeLE_var rootEIndex).promote
      (by omega : 1 ≤ 4)
  have hY :=
    ComplexPolynomialCode.termsDegreeLE_var rootYIndex
  have hp2 :=
    ComplexPolynomialCode.termsDegreeLE_var p2Index
  have hp3 :=
    ComplexPolynomialCode.termsDegreeLE_var p3Index
  have hp4 :=
    ComplexPolynomialCode.termsDegreeLE_var p4Index
  have hH :=
    ComplexPolynomialCode.termsDegreeLE_var HIndex
  fin_cases i
  · have hY4 :
        ComplexPolynomialCode.TermsDegreeLE 4
          (ComplexPolynomialCode.pow rY 4) := by
      simpa using ComplexPolynomialCode.termsDegreeLE_pow hY 4
    exact
      ComplexPolynomialCode.termsDegreeLE_sub
        (ComplexPolynomialCode.termsDegreeLE_sub hY4 hA) hC
  · have hp2sq :
        ComplexPolynomialCode.TermsDegreeLE 2
          (ComplexPolynomialCode.pow rp2 2) := by
      simpa using ComplexPolynomialCode.termsDegreeLE_pow hp2 2
    exact
      (ComplexPolynomialCode.termsDegreeLE_sub hp2sq
        ((ComplexPolynomialCode.termsDegreeLE_var rootAIndex).promote
          (by omega : 1 ≤ 2))).promote
          (by omega)
  · have hp4sq :
        ComplexPolynomialCode.TermsDegreeLE 2
          (ComplexPolynomialCode.pow rp4 2) := by
      simpa using ComplexPolynomialCode.termsDegreeLE_pow hp4 2
    exact
      (ComplexPolynomialCode.termsDegreeLE_sub hp4sq
        ((ComplexPolynomialCode.termsDegreeLE_var rootCIndex).promote
          (by omega : 1 ≤ 2))).promote
          (by omega)
  · have h12H :
        ComplexPolynomialCode.TermsDegreeLE 1
          (ComplexPolynomialCode.mul (rational 12) rH) :=
      scalarMul_termsDegreeLE 12 hH
    exact
      (ComplexPolynomialCode.termsDegreeLE_sub h12H
        (ComplexPolynomialCode.termsDegreeLE_var rootEIndex)).promote
          (by omega)
  · have hY2 :
        ComplexPolynomialCode.TermsDegreeLE 2
          (ComplexPolynomialCode.pow rY 2) := by
      simpa using ComplexPolynomialCode.termsDegreeLE_pow hY 2
    exact
      (ComplexPolynomialCode.termsDegreeLE_sub
        ((ComplexPolynomialCode.termsDegreeLE_var p3Index).promote
          (by omega : 1 ≤ 2))
        hY2).promote (by omega)

end UnaryPolynomialCode

namespace GaugePolynomialCode

/-- The gauge vector field is linear for every coded logarithmic
coefficient. -/
theorem fieldCode_termsDegreeLE
    (a : GaussianRationalCode) :
    ComplexPolynomialFieldCode.TermsDegreeLE 1
      (fieldCode a) := by
  intro i
  fin_cases i
  · exact
      ComplexPolynomialCode.termsDegreeLE_mulGaussian a
        (ComplexPolynomialCode.termsDegreeLE_var GIndex)
  · have hclock :
        ComplexPolynomialCode.TermsDegreeLE 1
          (ComplexPolynomialCode.mulGaussian a clockCode) :=
      ComplexPolynomialCode.termsDegreeLE_mulGaussian a
        (ComplexPolynomialCode.termsDegreeLE_var clockIndex)
    have hfour :
        ComplexPolynomialCode.TermsDegreeLE 0
          (UnaryPolynomialCode.rational 4 :
            ComplexPolynomialCode dimension) := by
      simpa [UnaryPolynomialCode.rational] using
        (ComplexPolynomialCode.termsDegreeLE_rationalConstant
          (n := dimension) (RationalCode.encode 4))
    have hmul :=
      ComplexPolynomialCode.termsDegreeLE_mul hfour hclock
    simpa [fieldCode] using hmul

theorem realFieldCode_termsDegreeLE
    (a : GaussianRationalCode) :
    ∀ i, PolynomialCode.TermsDegreeLE 1
      (realFieldCode a i) := by
  exact
    ComplexPolynomialFieldCode.realify_termsDegreeLE
      (fieldCode_termsDegreeLE a)

/-- The gauge link `G⁴-C` has raw degree at most four. -/
theorem residualCode_termsDegreeLE :
    ComplexPolynomialCode.TermsDegreeLE 4 residualCode := by
  have hG :=
    ComplexPolynomialCode.termsDegreeLE_var GIndex
  have hG4 :
      ComplexPolynomialCode.TermsDegreeLE 4
        (ComplexPolynomialCode.pow GCode 4) := by
    simpa using ComplexPolynomialCode.termsDegreeLE_pow hG 4
  have hclock :=
    (ComplexPolynomialCode.termsDegreeLE_var clockIndex).promote
      (by omega : 1 ≤ 4)
  exact ComplexPolynomialCode.termsDegreeLE_sub hG4 hclock

end GaugePolynomialCode

end HGAS.Modular
