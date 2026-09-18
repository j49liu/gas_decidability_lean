import HGAS.Arithmetic.DQL
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-!
# The positive constant-term selector

The analytic detector in Section 4 expands into terms indexed by two integer
vectors:

* `x` is the theta-series index;
* `s` is the Poisson-kernel index.

The private phase belonging to coordinate `j` has exponent
`x_j^2 - s_j`.  Thus its constant term forces `s_j = x_j^2`.  Once these
equalities are imposed, the equation-phase exponents vanish exactly when
the original diagonal-quadratic-linear system is satisfied.

This file formalizes that selection mechanism without yet invoking Haar
integration or convergence of the theta and Poisson series.  It also
packages the resulting nonnegative coefficient series in `ℝ≥0∞` and proves
the key no-cancellation statement: for nonzero positive parameters, that
series is positive exactly when the DQL instance has a solution.
-/

namespace HGAS

open scoped BigOperators ENNReal

noncomputable section

variable {eqs vars : ℕ}

/-- Exponent of the private phase for one arithmetic variable. -/
def privatePhaseExponent
    (x s : Fin vars → ℤ) (j : Fin vars) : ℤ :=
  x j ^ 2 - s j

/-- Exponent of one equation phase before private-phase selection. -/
def equationPhaseExponent
    (I : DQLSystem eqs vars) (x s : Fin vars → ℤ)
    (row : Fin eqs) : ℤ :=
  (∑ j, (I.quadratic row j * s j +
    I.linear row j * x j)) - I.rhs row

/-- All private phase exponents vanish exactly when the Poisson index is the
coordinatewise square of the theta index. -/
theorem privatePhaseExponent_eq_zero_iff
    (x s : Fin vars → ℤ) :
    (∀ j, privatePhaseExponent x s j = 0) ↔
      s = fun j ↦ x j ^ 2 := by
  constructor
  · intro h
    funext j
    have hj := h j
    simp only [privatePhaseExponent] at hj
    omega
  · rintro rfl
    intro j
    simp [privatePhaseExponent]

/-- With the private indices selected, vanishing of every equation-phase
exponent is precisely the DQL satisfaction predicate. -/
theorem equationPhaseExponent_square_eq_zero_iff
    (I : DQLSystem eqs vars) (x : Fin vars → ℤ) :
    (∀ row,
      equationPhaseExponent I x (fun j ↦ x j ^ 2) row = 0) ↔
        I.Satisfies x := by
  simp only [equationPhaseExponent, DQLSystem.Satisfies]
  constructor
  · intro h row
    have hrow := h row
    omega
  · intro h row
    have hrow := h row
    omega

/-- Complete constant-term support calculation: every private and equation
phase has exponent zero exactly for a genuine DQL witness, with the Poisson
index forced to be its coordinatewise square. -/
theorem allPhaseExponents_eq_zero_iff
    (I : DQLSystem eqs vars) (x s : Fin vars → ℤ) :
    ((∀ j, privatePhaseExponent x s j = 0) ∧
      (∀ row, equationPhaseExponent I x s row = 0)) ↔
        I.Satisfies x ∧ s = fun j ↦ x j ^ 2 := by
  constructor
  · rintro ⟨hprivate, hequation⟩
    have hs : s = fun j ↦ x j ^ 2 :=
      (privatePhaseExponent_eq_zero_iff x s).mp hprivate
    subst s
    exact
      ⟨(equationPhaseExponent_square_eq_zero_iff I x).mp hequation,
        rfl⟩
  · rintro ⟨hsatisfies, rfl⟩
    exact
      ⟨(privatePhaseExponent_eq_zero_iff x
          (fun j ↦ x j ^ 2)).mpr rfl,
        (equationPhaseExponent_square_eq_zero_iff I x).mpr
          hsatisfies⟩

/-- Natural energy `∑ j |x_j|²` appearing in every surviving coefficient. -/
def integerVectorEnergy (x : Fin vars → ℤ) : ℕ :=
  ∑ j, (x j).natAbs ^ 2

/-- Positive coefficient of a surviving witness after private-phase
selection. -/
def survivingCoefficient
    (lambda eta : ℝ≥0∞) (x : Fin vars → ℤ) : ℝ≥0∞ :=
  lambda ^ integerVectorEnergy x * eta ^ integerVectorEnergy x

/-- The formal nonnegative constant-term sum over all DQL witnesses. -/
def positiveConstantTerm
    (lambda eta : ℝ≥0∞) (I : DQLSystem eqs vars) : ℝ≥0∞ :=
  ∑' x : Fin vars → ℤ,
    if I.Satisfies x then survivingCoefficient lambda eta x else 0

/-- Nonzero parameters give a strictly positive coefficient to every
integer vector, including the zero-energy vector. -/
theorem survivingCoefficient_pos
    {lambda eta : ℝ≥0∞}
    (hlambda : lambda ≠ 0) (heta : eta ≠ 0)
    (x : Fin vars → ℤ) :
    0 < survivingCoefficient lambda eta x := by
  rw [pos_iff_ne_zero]
  exact mul_ne_zero (pow_ne_zero _ hlambda) (pow_ne_zero _ heta)

/-- A concrete DQL witness contributes a positive summand to the formal
constant term. -/
theorem positiveConstantTerm_pos_of_satisfies
    {lambda eta : ℝ≥0∞}
    (hlambda : lambda ≠ 0) (heta : eta ≠ 0)
    (I : DQLSystem eqs vars) (x : Fin vars → ℤ)
    (hx : I.Satisfies x) :
    0 < positiveConstantTerm lambda eta I := by
  let term : (Fin vars → ℤ) → ℝ≥0∞ :=
    fun y ↦ if I.Satisfies y then
      survivingCoefficient lambda eta y else 0
  have hxterm : 0 < term x := by
    simp only [term, if_pos hx]
    exact survivingCoefficient_pos hlambda heta x
  exact lt_of_lt_of_le hxterm (ENNReal.le_tsum x)

/-- If a DQL system has no witness, every candidate coefficient is removed
and the formal constant term is exactly zero. -/
theorem positiveConstantTerm_eq_zero_of_not_solvable
    (lambda eta : ℝ≥0∞) (I : DQLSystem eqs vars)
    (hI : ¬ I.Solvable) :
    positiveConstantTerm lambda eta I = 0 := by
  rw [positiveConstantTerm, ENNReal.tsum_eq_zero]
  intro x
  rw [if_neg]
  intro hx
  exact hI ⟨x, hx⟩

/-- No-cancellation theorem for the arithmetic detector.  This is the
positivity conclusion of equation (4.8), isolated from its later analytic
identification with a Haar integral. -/
theorem positiveConstantTerm_pos_iff_solvable
    {lambda eta : ℝ≥0∞}
    (hlambda : lambda ≠ 0) (heta : eta ≠ 0)
    (I : DQLSystem eqs vars) :
    0 < positiveConstantTerm lambda eta I ↔ I.Solvable := by
  constructor
  · intro hpositive
    by_contra hnotsolvable
    rw [positiveConstantTerm_eq_zero_of_not_solvable
      lambda eta I hnotsolvable] at hpositive
    exact lt_irrefl 0 hpositive
  · rintro ⟨x, hx⟩
    exact positiveConstantTerm_pos_of_satisfies
      hlambda heta I x hx

end

end HGAS
