import HGAS.Arithmetic.MathlibDiophBridge
import HGAS.Arithmetic.PolynomialGateCompiler
import Mathlib.Tactic

/-!
# Specializing finite Diophantine representations to DQL systems

A `FiniteDiophantineRepresentation m set` contains one fixed polynomial
whose first `m` variables are parameters and whose remaining variables are
existential witnesses.  For a concrete parameter tuple, this file
substitutes those parameter values into the sparse polynomial and compiles
the resulting witness-only equation to a literal
diagonal--quadratic--linear system.

The substitution is executable sparse syntax.  Each monomial is split into
its parameter factor and witness exponent vector; the parameter factor is
absorbed into the signed coefficient.  The main theorem states exactly
that the resulting DQL system is solvable iff the supplied tuple belongs
to the represented set.
-/

namespace HGAS

open scoped BigOperators

namespace IntegerPolynomialCode

/-- The factor contributed by the parameter coordinates of a monomial. -/
def parameterFactor {m k : ℕ}
    (parameters : Fin m → ℕ) (exponent : ExponentCode (m + k)) : ℕ :=
  (List.ofFn fun index =>
    parameters index ^
      exponent (Fin.castAdd k index)).prod

/-- Restrict an exponent vector to the witness coordinates. -/
def witnessExponent {m k : ℕ}
    (exponent : ExponentCode (m + k)) : ExponentCode k :=
  fun index => exponent (Fin.natAdd m index)

/-- Substitute the parameter tuple into one sparse term. -/
def specializeTerm {m k : ℕ}
    (parameters : Fin m → ℕ)
    (term : ExponentCode (m + k) × SignedMagnitudeCode) :
    ExponentCode k × SignedMagnitudeCode :=
  (witnessExponent term.1,
    SignedMagnitudeCode.mul term.2
      (SignedMagnitudeCode.encode
        (parameterFactor parameters term.1)))

/-- Substitute all parameter variables of a sparse integer polynomial.
The result is a polynomial only in the existential witness variables. -/
def specializeParameters {m k : ℕ}
    (polynomial : IntegerPolynomialCode (m + k))
    (parameters : Fin m → ℕ) :
    IntegerPolynomialCode k :=
  polynomial.map (specializeTerm parameters)

/-- A monomial on a concatenated assignment factors into its parameter and
witness parts. -/
theorem evalMonomial_addCases {m k : ℕ}
    (exponent : ExponentCode (m + k))
    (parameters : Fin m → ℕ) (witnesses : Fin k → ℕ) :
    NaturalPolynomialCode.evalMonomial exponent
        (Fin.addCases parameters witnesses) =
      parameterFactor parameters exponent *
        NaturalPolynomialCode.evalMonomial
          (witnessExponent exponent) witnesses := by
  simp only [NaturalPolynomialCode.evalMonomial,
    parameterFactor, witnessExponent, List.prod_ofFn]
  rw [Fin.prod_univ_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro index _
    simp
  · apply Finset.prod_congr rfl
    intro index _
    simp

/-- Sparse parameter substitution preserves evaluation exactly. -/
theorem eval_specializeParameters {m k : ℕ}
    (polynomial : IntegerPolynomialCode (m + k))
    (parameters : Fin m → ℕ) (witnesses : Fin k → ℕ) :
    eval (specializeParameters polynomial parameters) witnesses =
      eval polynomial (Fin.addCases parameters witnesses) := by
  induction polynomial with
  | nil =>
      rfl
  | cons term polynomial ih =>
      rw [show specializeParameters (term :: polynomial) parameters =
          specializeTerm parameters term ::
            specializeParameters polynomial parameters by rfl]
      rw [eval_cons, eval_cons, ih]
      simp only [specializeTerm, SignedMagnitudeCode.decode_mul,
        SignedMagnitudeCode.decode_encode]
      rw [evalMonomial_addCases]
      push_cast
      ring

end IntegerPolynomialCode

namespace FiniteDiophantineRepresentation

variable {m : ℕ} {set : Set (Fin m → ℕ)}

/-- Specialize a represented polynomial at one parameter tuple and compile
the remaining witness equation to DQL. -/
def specializedDQL
    (representation : FiniteDiophantineRepresentation m set)
    (parameters : Fin m → ℕ) :=
  PolynomialGateCompiler.integerPolynomialEquationDQL
    (IntegerPolynomialCode.specializeParameters
      representation.polynomial parameters)

/-- Exact semantic correctness of parameter specialization followed by
the polynomial-to-DQL compiler. -/
theorem specializedDQL_solvable_iff
    (representation : FiniteDiophantineRepresentation m set)
    (parameters : Fin m → ℕ) :
    (representation.specializedDQL parameters).Solvable ↔
      parameters ∈ set := by
  rw [specializedDQL,
    PolynomialGateCompiler.integerPolynomialEquationDQL_solvable_iff]
  simp only [IntegerPolynomialCode.eval_specializeParameters]
  exact (representation.represents parameters).symm

end FiniteDiophantineRepresentation

end HGAS
