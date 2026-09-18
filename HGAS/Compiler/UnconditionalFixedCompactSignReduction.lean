import HGAS.Compiler.UnconditionalFixedCompactSignSourceFamily
import HGAS.Propagation.CofinalSigmaOne
import Mathlib.Tactic

/-!
# Fixed-pair and cofinal completeness from a compact-sign source family

This module is the final recursion-theoretic composition layer.  It makes
the remaining burden completely explicit: construct one
`FixedUniversalCompactSignSourceFamily`.  From that object alone we obtain

1. `Σ⁰₁`-completeness at its fixed wrapper dimension and degree;
2. effective cubicization; and
3. `Σ⁰₁`-completeness at every sufficiently large fixed dimension and
   every fixed odd degree at least three.

No dynamical or analytic reasoning occurs here.
-/

namespace HGAS.Compiler

open HGAS

noncomputable section

namespace FixedUniversalCompactSignSourceFamily

variable {n k wrapperDegree : ℕ}
  {sourceBlock : Fin n → Fin k}
  [Nonempty
    (UnitSpherePolynomialWrapper.SourceProductSphere sourceBlock)]

/-- One completed compact-sign source family already yields fixed-pair
`Σ⁰₁`-completeness. -/
theorem fixedPair_sigmaOneComplete
    (family :
      FixedUniversalCompactSignSourceFamily
        sourceBlock wrapperDegree) :
    SigmaOneComplete
      (HGASQ (n + 1) (outputDegree k wrapperDegree)) :=
  sigmaOneComplete_of_universalHalts_reduction
    (hgasQ_re_of_oddDegree
      (n + 1) (outputDegree k wrapperDegree)
      (Nat.odd_iff.mpr family.outputDegree_odd))
    family.universalHalts_manyOneReducible_hgasQ

/-- The fixed output degree is at least three. -/
theorem three_le_outputDegree
    (family :
      FixedUniversalCompactSignSourceFamily
        sourceBlock wrapperDegree) :
    3 ≤ outputDegree k wrapperDegree := by
  have hdegree := family.wrapperDegree_ge_three
  unfold outputDegree
  unfold UnitSpherePolynomialWrapper.targetDegree
  omega

/-- A canonical half-degree parameter for cubicization. -/
def outputHalfDegree
    (k wrapperDegree : ℕ) : ℕ :=
  (outputDegree k wrapperDegree - 1) / 2

/-- The fixed odd output degree has the exact form expected by the
cubic-lift compiler. -/
theorem outputDegree_eq_two_mul_outputHalfDegree_add_one
    (family :
      FixedUniversalCompactSignSourceFamily
        sourceBlock wrapperDegree) :
    outputDegree k wrapperDegree =
      2 * outputHalfDegree k wrapperDegree + 1 := by
  have hodd :
      Odd (outputDegree k wrapperDegree) :=
    Nat.odd_iff.mpr family.outputDegree_odd
  obtain ⟨r, hr⟩ := hodd
  unfold outputHalfDegree
  omega

/-- The cubicization half-degree is nonzero. -/
theorem one_le_outputHalfDegree
    (family :
      FixedUniversalCompactSignSourceFamily
        sourceBlock wrapperDegree) :
    1 ≤ outputHalfDegree k wrapperDegree := by
  have hthree := family.three_le_outputDegree
  rw [family.outputDegree_eq_two_mul_outputHalfDegree_add_one]
    at hthree
  omega

/-- **Cofinal fixed-pair theorem, conditional only on construction of the
one faithful compact-sign source family.** -/
theorem cofinal_sigmaOneComplete
    (family :
      FixedUniversalCompactSignSourceFamily
        sourceBlock wrapperDegree)
    (N d : ℕ)
    (hN :
      Veronese.cubicLiftCodeDimension
          (n + 1) (outputHalfDegree k wrapperDegree) ≤ N)
    (hd : Odd d) (hthree : 3 ≤ d) :
    SigmaOneComplete (HGASQ N d) := by
  have hsource :
      UniversalHalts ≤₀
        HGASQ (n + 1)
          (2 * outputHalfDegree k wrapperDegree + 1) := by
    simpa only [
      ← family.outputDegree_eq_two_mul_outputHalfDegree_add_one] using
        family.universalHalts_manyOneReducible_hgasQ
  exact
    HGAS.Propagation.sigmaOneComplete_cofinalFixedPair_of_universalHalts_reduction
        (n + 1) (outputHalfDegree k wrapperDegree) N d
        (by omega)
        family.one_le_outputHalfDegree
        hsource hN hd hthree

end FixedUniversalCompactSignSourceFamily

end

end HGAS.Compiler
