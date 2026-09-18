import HGAS.Computability.CubicLiftEffectiveGain
import HGAS.Propagation.DegreePaddingCode
import Mathlib.Tactic

/-!
# Effective propagation to cofinally many fixed dimensions and degrees

This module composes the two finite-code compilers used in the paper:

1. the effective stabilized Veronese compiler, which sends a homogeneous
   field of odd degree `2k+1` to a cubic field in the fixed dimension
   `cubicLiftCodeDimension n k`; and
2. `DegreePaddingCode.degreeDimensionPadCode`, which adjoins any fixed
   number of cubic sinks and raises the common odd degree by any fixed even
   amount.

The resulting map is primitive recursive on raw sparse field codes and is
correct on *all* inputs.  No extra malformed-input guard is needed in the
second stage: `effectiveCubicReductionCode` produces a syntactically valid
cubic field even when its input is malformed (in that case it produces the
zero field).

The final theorems package the useful cofinal form.  Once a predicate has a
many-one reduction to one fixed odd-degree `HGASQ` language, it has a
many-one reduction to every larger target dimension and every odd target
degree at least three.
-/

namespace HGAS

noncomputable section

namespace Propagation

open Veronese

/-- The explicit two-stage raw-code compiler: odd degree to cubic, followed
by dimension and degree padding. -/
def oddToCofinalCode
    (n k p j : ℕ) (hk : 1 ≤ k)
    (F : PolynomialFieldCode n) :
    PolynomialFieldCode
      (cubicLiftCodeDimension n k + p) :=
  DegreePaddingCode.degreeDimensionPadCode
    (cubicLiftCodeDimension n k) p j
    (effectiveCubicReductionCode n k hk F)

/-- The two-stage compiler is primitive recursive for every fixed choice
of source and target parameters. -/
theorem oddToCofinalCode_primrec
    (n k p j : ℕ) (hk : 1 ≤ k) :
    Primrec (oddToCofinalCode n k p j hk) := by
  exact
    (DegreePaddingCode.degreeDimensionPadCode_primrec
      (cubicLiftCodeDimension n k) p j).comp
        (effectiveCubicReductionCode_primrec n k hk)

/-- Every output of the two-stage compiler is syntactically homogeneous of
the advertised target degree. -/
theorem oddToCofinalCode_homogeneous
    (n k p j : ℕ) (hk : 1 ≤ k)
    (F : PolynomialFieldCode n) :
    PolynomialFieldCode.homogeneous (3 + 2 * j)
      (oddToCofinalCode n k p j hk F) = true := by
  exact DegreePaddingCode.degreeDimensionPadCode_homogeneous
    (cubicLiftCodeDimension n k) p j
    (effectiveCubicReductionCode n k hk F)
    (effectiveCubicReductionCode_homogeneous n k hk F)

/-- Exact correctness of the explicit compiler on arbitrary raw codes. -/
theorem oddToCofinalCode_hgasQ_iff
    (n k p j : ℕ) (hn : 0 < n) (hk : 1 ≤ k)
    (F : PolynomialFieldCode n) :
    HGASQ n (2 * k + 1) F ↔
      HGASQ (cubicLiftCodeDimension n k + p) (3 + 2 * j)
        (oddToCofinalCode n k p j hk F) := by
  exact
    (effectiveCubicReductionCode_hgasQ_iff n k hn hk F).trans
      (DegreePaddingCode.degreeDimensionPadCode_hgasQ_iff_of_homogeneous
        (cubicLiftCodeDimension n k) p j
        (effectiveCubicReductionCode n k hk F)
        (effectiveCubicReductionCode_homogeneous n k hk F))

/-- Fixed-parameter many-one reduction to every target obtained by adding
`p` dimensions and `2j` degrees after the cubic lift. -/
theorem hgasQ_manyOneReducible_oddToCofinal
    (n k p j : ℕ) (hn : 0 < n) (hk : 1 ≤ k) :
    HGASQ n (2 * k + 1) ≤₀
      HGASQ (cubicLiftCodeDimension n k + p) (3 + 2 * j) := by
  exact ⟨oddToCofinalCode n k p j hk,
    (oddToCofinalCode_primrec n k p j hk).to_comp,
    oddToCofinalCode_hgasQ_iff n k p j hn hk⟩

/-- Arithmetic normalization of every odd degree at least three into the
form emitted by degree padding. -/
theorem odd_degree_eq_three_add_twice_half_sub_three
    {d : ℕ} (hd : Odd d) (hthree : 3 ≤ d) :
    3 + 2 * ((d - 3) / 2) = d := by
  rcases hd with ⟨a, rfl⟩
  omega

/-- **Cofinal fixed-pair propagation.**

For a fixed positive source dimension and fixed odd source degree, the
source `HGASQ` language reduces to every target pair `(N,d)` satisfying

* `N ≥ cubicLiftCodeDimension n k`, and
* `d ≥ 3` and `d` odd.

Thus both the target dimension and target degree are fixed constants in
each resulting decision problem; they do not depend on the input code.
-/
theorem hgasQ_manyOneReducible_cofinalFixedPair
    (n k N d : ℕ) (hn : 0 < n) (hk : 1 ≤ k)
    (hN : cubicLiftCodeDimension n k ≤ N)
    (hd : Odd d) (hthree : 3 ≤ d) :
    HGASQ n (2 * k + 1) ≤₀ HGASQ N d := by
  have hdimension :
      cubicLiftCodeDimension n k +
          (N - cubicLiftCodeDimension n k) =
        N :=
    Nat.add_sub_of_le hN
  have hdegree :
      3 + 2 * ((d - 3) / 2) = d :=
    odd_degree_eq_three_add_twice_half_sub_three hd hthree
  have hreduction :=
    hgasQ_manyOneReducible_oddToCofinal
      n k (N - cubicLiftCodeDimension n k)
        ((d - 3) / 2) hn hk
  rw [hdimension, hdegree] at hreduction
  exact hreduction

/-- A named existential form making the computable map and its exact
membership equivalence explicit at a normalized target pair. -/
theorem exists_computable_cofinalFixedPair_code
    (n k N d : ℕ) (hn : 0 < n) (hk : 1 ≤ k)
    (hN : cubicLiftCodeDimension n k ≤ N)
    (hd : Odd d) (hthree : 3 ≤ d) :
    ∃ f : PolynomialFieldCode n → PolynomialFieldCode N,
      Computable f ∧
        ∀ F,
          (HGASQ n (2 * k + 1) F ↔ HGASQ N d (f F)) := by
  rcases hgasQ_manyOneReducible_cofinalFixedPair
      n k N d hn hk hN hd hthree with
    ⟨f, hf, hcorrect⟩
  exact ⟨f, hf, hcorrect⟩

/-- Any pre-existing many-one reduction to the fixed odd-degree source
language propagates to every cofinal fixed target pair.  This is the
paper-facing composition theorem. -/
theorem manyOneReducible_cofinalFixedPair
    {α : Type*} [Primcodable α] (A : α → Prop)
    (n k N d : ℕ) (hn : 0 < n) (hk : 1 ≤ k)
    (hsource : A ≤₀ HGASQ n (2 * k + 1))
    (hN : cubicLiftCodeDimension n k ≤ N)
    (hd : Odd d) (hthree : 3 ≤ d) :
    A ≤₀ HGASQ N d :=
  hsource.trans
    (hgasQ_manyOneReducible_cofinalFixedPair
      n k N d hn hk hN hd hthree)

end Propagation

end

end HGAS
