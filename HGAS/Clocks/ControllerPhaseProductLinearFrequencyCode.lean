import HGAS.Clocks.ControllerPhaseProductPolynomialCode
import Mathlib.Tactic

/-!
# Rational linear frequency readouts from finite clock products

A product of controller--phase clocks stores the effective signed frequency
of clock `i` in the polynomial coordinate

```
  parameterᵢ * rᵢ.
```

Here `parameterᵢ` is rational and `rᵢ` is the first controller coordinate.
On a locked controller branch, `rᵢ = ± 1 / √parameterᵢ`, so this coordinate
is exactly the signed radical frequency `±√parameterᵢ`.

Larger clocked blocks need rational linear combinations of these elementary
frequencies.  This file provides one reusable sparse-polynomial compiler:

```
  (weights, parameters) ↦ ∑ i, weightsᵢ * parametersᵢ * rᵢ.
```

The compiler works for an arbitrary fixed finite number of clocks, evaluates
correctly at every ambient real point (not only on the clock circles), has
raw degree at most one, and is primitive recursive in both rational input
tuples.  Each controller variable is inserted by the canonical block
embedding from `PolynomialFiniteProductCode`, so the coordinate convention
is shared with the finite-product vector-field compiler.
-/

namespace HGAS.Clocks.ControllerPhaseProductLinearFrequencyCode

open HGAS

variable {q : ℕ}

abbrev dimension (q : ℕ) : ℕ :=
  ControllerPhaseProductPolynomialCode.dimension q

abbrev StateFamily (q : ℕ) (R : Type*) :=
  ControllerPhaseProductPolynomialCode.StateFamily q R

/-- The ambient scalar-polynomial code for the first controller coordinate
`rᵢ` of block `i`. -/
def rCode (i : Fin q) : PolynomialCode (dimension q) :=
  PolynomialFiniteProductCode.lift i
    ControllerPolynomialCode.rCode

/-- One weighted controller contribution
`weightᵢ * parameterᵢ * rᵢ`. -/
def termCode
    (i : Fin q) (weight parameter : RationalCode) :
    PolynomialCode (dimension q) :=
  PolynomialCode.mul
    (PolynomialCode.constant weight)
    (PolynomialCode.mul
      (PolynomialCode.constant parameter)
      (rCode i))

/-- Compile the rational linear combination
`∑ i, weightᵢ * parameterᵢ * rᵢ`. -/
def code
    (weights parameters : Fin q → RationalCode) :
    PolynomialCode (dimension q) :=
  PolynomialCode.sumCodes
    (List.ofFn fun i : Fin q ↦
      termCode i (weights i) (parameters i))

/-- The real-valued structured semantics of the compiled readout. -/
def value
    (weights parameters : Fin q → ℝ)
    (z : StateFamily q ℝ) : ℝ :=
  ∑ i, weights i * parameters i * (z i).controller.r

/-! ## Exact semantics -/

/-- A lifted `rᵢ` code reads exactly the ambient coordinate selected by the
canonical block embedding. -/
@[simp]
theorem eval₂Hom_rCode
    (i : Fin q) (x : Fin (dimension q) → ℝ) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (rCode i)) =
      x
        (ControllerPhaseProductPolynomialCode.blockEmbedding i
          ControllerPolynomialCode.rIndex) := by
  simp [rCode, ControllerPolynomialCode.rCode,
    ControllerPhaseProductPolynomialCode.blockEmbedding]

/-- Exact arbitrary-point semantics of one weighted contribution. -/
@[simp]
theorem eval₂Hom_termCode
    (i : Fin q) (weight parameter : RationalCode)
    (x : Fin (dimension q) → ℝ) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode
          (termCode i weight parameter)) =
      (RationalCode.decode weight : ℝ) *
        (RationalCode.decode parameter : ℝ) *
        x
          (ControllerPhaseProductPolynomialCode.blockEmbedding i
            ControllerPolynomialCode.rIndex) := by
  simp only [termCode, PolynomialCode.decode_mul_code, map_mul,
    PolynomialCode.decode_constant, MvPolynomial.eval₂Hom_C]
  rw [eval₂Hom_rCode]
  have hweight :
      (algebraMap ℚ ℝ) (RationalCode.decode weight) =
        (RationalCode.decode weight : ℝ) := by
    rfl
  have hparameter :
      (algebraMap ℚ ℝ) (RationalCode.decode parameter) =
        (RationalCode.decode parameter : ℝ) := by
    rfl
  rw [hweight, hparameter]
  ring

/-- Exact semantics at an arbitrary flattened real point.  The right side
first reassembles that point into structured clock blocks. -/
@[simp]
theorem eval₂Hom_code_arbitrary
    (weights parameters : Fin q → RationalCode)
    (x : Fin (dimension q) → ℝ) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) x
        (PolynomialCode.decode (code weights parameters)) =
      value
        (fun i ↦ (RationalCode.decode (weights i) : ℝ))
        (fun i ↦ (RationalCode.decode (parameters i) : ℝ))
        (ControllerPhaseProductPolynomialCode.state x) := by
  rw [code, PolynomialCode.decode_sumCodes,
    List.map_ofFn, List.sum_ofFn, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply]
  rw [eval₂Hom_termCode]
  rfl

/-- Exact semantics on a structured family of controller--phase states. -/
@[simp]
theorem eval₂Hom_code
    (weights parameters : Fin q → RationalCode)
    (z : StateFamily q ℝ) :
    MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
        (ControllerPhaseProductPolynomialCode.point z)
        (PolynomialCode.decode (code weights parameters)) =
      value
        (fun i ↦ (RationalCode.decode (weights i) : ℝ))
        (fun i ↦ (RationalCode.decode (parameters i) : ℝ))
        z := by
  rw [eval₂Hom_code_arbitrary]
  simp

/-! ## Degree ledger -/

/-- Every lifted controller readout is linear. -/
theorem rCode_termsDegreeLE
    (i : Fin q) :
    PolynomialCode.TermsDegreeLE 1 (rCode i) := by
  exact
    PolynomialFiniteProductCode.termsDegreeLE_lift
      (PolynomialCode.termsDegreeLE_varCode
        ControllerPolynomialCode.rIndex)

/-- Multiplying `rᵢ` by two rational constants preserves degree one. -/
theorem termCode_termsDegreeLE
    (i : Fin q) (weight parameter : RationalCode) :
    PolynomialCode.TermsDegreeLE 1
      (termCode i weight parameter) := by
  have hweight :
      PolynomialCode.TermsDegreeLE 0
        (PolynomialCode.constant weight :
          PolynomialCode (dimension q)) :=
    PolynomialCode.termsDegreeLE_constant weight
  have hparameter :
      PolynomialCode.TermsDegreeLE 0
        (PolynomialCode.constant parameter :
          PolynomialCode (dimension q)) :=
    PolynomialCode.termsDegreeLE_constant parameter
  have hinner :
      PolynomialCode.TermsDegreeLE 1
        (PolynomialCode.mul
          (PolynomialCode.constant parameter)
          (rCode i)) := by
    simpa using
      PolynomialCode.termsDegreeLE_mul hparameter
        (rCode_termsDegreeLE i)
  simpa [termCode] using
    PolynomialCode.termsDegreeLE_mul hweight hinner

/-- A finite rational linear combination of controller readouts has raw
degree at most one, independently of the number of clocks. -/
theorem code_termsDegreeLE
    (weights parameters : Fin q → RationalCode) :
    PolynomialCode.TermsDegreeLE 1
      (code weights parameters) := by
  rw [code]
  apply PolynomialCode.termsDegreeLE_sumCodes
  intro p hp
  rw [List.mem_ofFn] at hp
  obtain ⟨i, rfl⟩ := hp
  exact termCode_termsDegreeLE i (weights i) (parameters i)

/-! ## Effective compilation -/

/-- Runtime input of the linear-frequency compiler. -/
abbrev CompilerInput (q : ℕ) :=
  (Fin q → RationalCode) × (Fin q → RationalCode)

/-- For every fixed number of blocks, compiling the two rational tuples is
primitive recursive. -/
theorem code_primrec :
    Primrec
      (fun input : CompilerInput q ↦
        code input.1 input.2) := by
  apply PolynomialCode.sumCodes_primrec.comp
  apply Primrec.list_ofFn
  intro i
  exact
    PolynomialCode.mul_primrec.comp
      (PolynomialCode.constant_primrec.comp
        (Primrec.fin_app.comp Primrec.fst
          (Primrec.const i)))
      (PolynomialCode.mul_primrec.comp
        (PolynomialCode.constant_primrec.comp
          (Primrec.fin_app.comp Primrec.snd
            (Primrec.const i)))
        (Primrec.const (rCode i)))

theorem code_computable :
    Computable
      (fun input : CompilerInput q ↦
        code input.1 input.2) :=
  code_primrec.to_comp

end HGAS.Clocks.ControllerPhaseProductLinearFrequencyCode
