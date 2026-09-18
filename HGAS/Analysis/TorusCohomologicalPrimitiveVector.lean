import HGAS.Analysis.TorusCohomologicalPrimitive
import HGAS.Algebra.FiniteEuclidean
import Mathlib.Tactic

/-!
# Finite real vectors of torus Fourier primitives

The compact accumulator consumes a finite real drift vector.  The analytic
Fourier calculation is most naturally complex and coordinatewise.  This
module is the small reusable bridge between those two presentations.

For each output coordinate `q : Fin m`, we permit a separate countable
Fourier index type, coefficient family, and exponent family.  The real
drift is the real part of the corresponding complex series.  The primitive
is obtained by the inverse-frequency construction in
`TorusCohomologicalPrimitive`.

The main results package:

* continuity of the complete finite primitive vector;
* the exact coordinatewise cohomological equation along torus translation;
* an explicit squared-norm bound by the sum of squared coefficient
  `ℓ¹`-norms.

The last estimate has exactly the algebraic `normSq` shape required by the
finite-graph certificate for the stereographically compactified vector
accumulator.
-/

noncomputable section

open scoped BigOperators

namespace HGAS.Analysis

variable {d : Type*} [Fintype d]
variable {m : ℕ}
variable (ι : Fin m → Type*)

/-- Real vector obtained by taking the real part of finitely many complex
Fourier series. -/
def realTorusFourierVector
    (coefficient : ∀ q, ι q → ℂ)
    (exponent : ∀ q, ι q → d → ℤ)
    (x : UnitAddTorus d) :
    HGAS.FinVector m ℝ :=
  fun q ↦
    (torusFourierSeries
      (coefficient q) (exponent q) x).re

/-- Coordinatewise centered primitive for `realTorusFourierVector`. -/
def realTorusCohomologicalPrimitive
    (coefficient : ∀ q, ι q → ℂ)
    (exponent : ∀ q, ι q → d → ℤ)
    (ω : d → ℝ)
    (x : UnitAddTorus d) :
    HGAS.FinVector m ℝ :=
  fun q ↦
    (torusCohomologicalPrimitive
      (coefficient q) (exponent q) ω x).re

/-- The inverse-frequency coefficient `ℓ¹` norm of one output
coordinate. -/
def primitiveCoordinateBound
    (coefficient : ∀ q, ι q → ℂ)
    (exponent : ∀ q, ι q → d → ℤ)
    (ω : d → ℝ)
    (q : Fin m) : ℝ :=
  ∑' i,
    ‖cohomologicalPrimitiveCoefficient
      (coefficient q) (exponent q) ω i‖

theorem primitiveCoordinateBound_nonneg
    (coefficient : ∀ q, ι q → ℂ)
    (exponent : ∀ q, ι q → d → ℤ)
    (ω : d → ℝ)
    (q : Fin m) :
    0 ≤ primitiveCoordinateBound ι coefficient exponent ω q := by
  exact tsum_nonneg fun i ↦ norm_nonneg _

/-- Coordinatewise inverse-frequency summability makes the finite real
primitive continuous. -/
theorem continuous_realTorusCohomologicalPrimitive
    (coefficient : ∀ q, ι q → ℂ)
    (exponent : ∀ q, ι q → d → ℤ)
    (ω : d → ℝ)
    (hprimitive :
      ∀ q,
        Summable fun i ↦
          ‖cohomologicalPrimitiveCoefficient
            (coefficient q) (exponent q) ω i‖) :
    Continuous
      (realTorusCohomologicalPrimitive
        ι coefficient exponent ω) := by
  apply continuous_pi
  intro q
  exact
    Complex.continuous_re.comp
      (continuous_torusCohomologicalPrimitive
        (coefficient q) (exponent q) ω (hprimitive q))

/-- Every real primitive coordinate is bounded in absolute value by the
`ℓ¹` norm of its inverse-frequency coefficients. -/
theorem abs_realTorusCohomologicalPrimitive_le
    (coefficient : ∀ q, ι q → ℂ)
    (exponent : ∀ q, ι q → d → ℤ)
    (ω : d → ℝ)
    (hprimitive :
      ∀ q,
        Summable fun i ↦
          ‖cohomologicalPrimitiveCoefficient
            (coefficient q) (exponent q) ω i‖)
    (x : UnitAddTorus d) (q : Fin m) :
    |realTorusCohomologicalPrimitive
        ι coefficient exponent ω x q| ≤
      primitiveCoordinateBound
        ι coefficient exponent ω q := by
  unfold realTorusCohomologicalPrimitive
  exact
    (Complex.abs_re_le_norm _).trans
      (norm_torusCohomologicalPrimitive_le
        (coefficient q) (exponent q) ω
        (hprimitive q) x)

/-- Squared norm of the complete real primitive vector is controlled by
the sum of the squared coordinate `ℓ¹` bounds. -/
theorem normSq_realTorusCohomologicalPrimitive_le
    (coefficient : ∀ q, ι q → ℂ)
    (exponent : ∀ q, ι q → d → ℤ)
    (ω : d → ℝ)
    (hprimitive :
      ∀ q,
        Summable fun i ↦
          ‖cohomologicalPrimitiveCoefficient
            (coefficient q) (exponent q) ω i‖)
    (x : UnitAddTorus d) :
    HGAS.normSq
        (realTorusCohomologicalPrimitive
          ι coefficient exponent ω x) ≤
      ∑ q : Fin m,
        (primitiveCoordinateBound
          ι coefficient exponent ω q) ^ 2 := by
  unfold HGAS.normSq HGAS.dot
  apply Finset.sum_le_sum
  intro q _
  let z :=
    realTorusCohomologicalPrimitive
      ι coefficient exponent ω x q
  let K :=
    primitiveCoordinateBound
      ι coefficient exponent ω q
  have habs : |z| ≤ K := by
    exact
      abs_realTorusCohomologicalPrimitive_le
        ι coefficient exponent ω hprimitive x q
  have hK : 0 ≤ K :=
    primitiveCoordinateBound_nonneg
      ι coefficient exponent ω q
  have hsquare : z ^ 2 ≤ K ^ 2 :=
    sq_le_sq.mpr (by simpa [abs_of_nonneg hK] using habs)
  simpa only [z, K, pow_two] using hsquare

/-- Coordinatewise cohomological equation for the finite real vector.
Nonresonance and vanishing zero modes identify its derivative with the
original real Fourier drift. -/
theorem realTorusCohomologicalPrimitive_hasDerivAt
    (coefficient : ∀ q, ι q → ℂ)
    (exponent : ∀ q, ι q → d → ℤ)
    (ω : d → ℝ)
    (hω :
      HGAS.Clocks.RadicalIndependence.HasNoNontrivialIntegerCharacter
        ω)
    (hzero :
      ∀ q i, exponent q i = 0 → coefficient q i = 0)
    (hcoefficient :
      ∀ q, Summable fun i ↦ ‖coefficient q i‖)
    (hprimitive :
      ∀ q,
        Summable fun i ↦
          ‖cohomologicalPrimitiveCoefficient
            (coefficient q) (exponent q) ω i‖)
    (x : UnitAddTorus d)
    (q : Fin m) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦
        realTorusCohomologicalPrimitive
          ι coefficient exponent ω
          (HGAS.Clocks.RadicalClock.torusTranslationFlow
            ω s x) q)
      (realTorusFourierVector
        ι coefficient exponent
        (HGAS.Clocks.RadicalClock.torusTranslationFlow
          ω t x) q)
      t := by
  exact
    torusCohomologicalPrimitive_re_hasDerivAt_of_zeroMode
      (coefficient q) (exponent q) ω hω
      (hzero q) (hcoefficient q) (hprimitive q) x t

end HGAS.Analysis
