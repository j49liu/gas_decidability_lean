import HGAS.Computability.CubicLiftEffectiveShadowGain
import HGAS.Veronese.CubicLiftLyapunovConjugacy
import HGAS.Stability.PaddingLyapunov
import HGAS.Propagation.CofinalFixedPairReduction
import HGAS.Computability.ManyOneHard
import Mathlib.Tactic

/-!
# Lyapunov stability: cubicization, padding and transfer of hardness

This module assembles the Lyapunov-stability half of Part I of the paper.

* `hlsQ_manyOneReducible_cubic`: for fixed `n ≥ 2` and `k ≥ 1`, the
  stabilized cubic Veronese lift is a computable many-one reduction from
  rational homogeneous Lyapunov stability in dimension `n` and degree
  `2k+1` to the cubic problem in dimension `cubicLiftCodeDimension n k`
  (Theorem 1.2 and Theorem 1.3(i) of the paper, for fixed `(n,k)`).  The
  same map is also a reduction for GAS.
* `hlsQ_manyOneReducible_cofinalFixedPair`: composed with degree raising
  and dimension padding, it reduces to every fixed target pair `(N,d)`
  with `N ≥ cubicLiftCodeDimension n k` and `d ≥ 3` odd (Corollary 6.5).
* `hlsQ_manyOneHard_cofinal_of_source` and
  `hlsQ_not_computable_cofinal_of_source`: transfer of many-one hardness
  and of undecidability.  Together with Korda's theorem, which is not
  formalized here and enters only as the hypothesis `hsource`, these give
  Corollary 1.4 and Remark 7.1 of the paper.
-/

namespace HGAS

noncomputable section

namespace Propagation

open Veronese

/-! ## The cubic reduction for Lyapunov stability -/

/-- Exact correctness of the Lyapunov-stability cubic compiler on raw
codes. -/
theorem effectiveCubicLSReductionCode_hlsQ_iff
    (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) (F : PolynomialFieldCode n) :
    HLSQ n (2 * k + 1) F ↔
      HLSQ (cubicLiftCodeDimension n k) 3
        (effectiveCubicLSReductionCode n k hk F) :=
  effectiveCubicLSReductionCode_hlsQ_iff_of_semantic n k hn hk
    (fun _ b hF ↦ sourceLS_iff_stabilizedCubicLS b hF hk) F

/-- **Cubicization for Lyapunov stability, fixed `(n,k)`.** -/
theorem hlsQ_manyOneReducible_cubic
    (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    HLSQ n (2 * k + 1) ≤₀ HLSQ (cubicLiftCodeDimension n k) 3 :=
  ⟨effectiveCubicLSReductionCode n k hk,
    (effectiveCubicLSReductionCode_primrec n k hk).to_comp,
    effectiveCubicLSReductionCode_hlsQ_iff n k hn hk⟩

/-- **Cubicization, both properties at once.**  One computable map sends
every code of degree `2k+1` to a cubic code with the same answer for GAS
and for Lyapunov stability. -/
theorem exists_computable_cubicization
    (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) :
    ∃ f : PolynomialFieldCode n →
        PolynomialFieldCode (cubicLiftCodeDimension n k),
      Computable f ∧
        ∀ F, (HGASQ n (2 * k + 1) F ↔
            HGASQ (cubicLiftCodeDimension n k) 3 (f F)) ∧
          (HLSQ n (2 * k + 1) F ↔
            HLSQ (cubicLiftCodeDimension n k) 3 (f F)) :=
  ⟨effectiveCubicLSReductionCode n k hk,
    (effectiveCubicLSReductionCode_primrec n k hk).to_comp,
    fun F ↦ ⟨effectiveCubicLSReductionCode_hgasQ_iff n k hn hk F,
      effectiveCubicLSReductionCode_hlsQ_iff n k hn hk F⟩⟩

/-! ## Padding -/

/-- The two-stage compiler for Lyapunov stability: odd degree to cubic,
followed by dimension and degree padding. -/
def oddToCofinalLSCode
    (n k p j : ℕ) (hk : 1 ≤ k) (F : PolynomialFieldCode n) :
    PolynomialFieldCode (cubicLiftCodeDimension n k + p) :=
  DegreePaddingCode.degreeDimensionPadCode
    (cubicLiftCodeDimension n k) p j
    (effectiveCubicLSReductionCode n k hk F)

theorem oddToCofinalLSCode_primrec
    (n k p j : ℕ) (hk : 1 ≤ k) :
    Primrec (oddToCofinalLSCode n k p j hk) :=
  (DegreePaddingCode.degreeDimensionPadCode_primrec
    (cubicLiftCodeDimension n k) p j).comp
      (effectiveCubicLSReductionCode_primrec n k hk)

theorem oddToCofinalLSCode_hlsQ_iff
    (n k p j : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) (F : PolynomialFieldCode n) :
    HLSQ n (2 * k + 1) F ↔
      HLSQ (cubicLiftCodeDimension n k + p) (3 + 2 * j)
        (oddToCofinalLSCode n k p j hk F) :=
  (effectiveCubicLSReductionCode_hlsQ_iff n k hn hk F).trans
    (DegreePaddingCode.degreeDimensionPadCode_hlsQ_iff_of_homogeneous
      (cubicLiftCodeDimension n k) p j
      (effectiveCubicLSReductionCode n k hk F)
      (effectiveCubicLSReductionCode_homogeneous n k hk F))

/-- **Transfer to every larger dimension and odd degree, for Lyapunov
stability.** -/
theorem hlsQ_manyOneReducible_cofinalFixedPair
    (n k N d : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hN : cubicLiftCodeDimension n k ≤ N)
    (hd : Odd d) (hthree : 3 ≤ d) :
    HLSQ n (2 * k + 1) ≤₀ HLSQ N d := by
  have hdimension :
      cubicLiftCodeDimension n k + (N - cubicLiftCodeDimension n k) = N :=
    Nat.add_sub_of_le hN
  have hdegree : 3 + 2 * ((d - 3) / 2) = d :=
    odd_degree_eq_three_add_twice_half_sub_three hd hthree
  have hreduction :
      HLSQ n (2 * k + 1) ≤₀
        HLSQ (cubicLiftCodeDimension n k + (N - cubicLiftCodeDimension n k))
          (3 + 2 * ((d - 3) / 2)) :=
    ⟨oddToCofinalLSCode n k (N - cubicLiftCodeDimension n k) ((d - 3) / 2) hk,
      (oddToCofinalLSCode_primrec n k _ _ hk).to_comp,
      oddToCofinalLSCode_hlsQ_iff n k _ _ hn hk⟩
  rw [hdimension, hdegree] at hreduction
  exact hreduction

/-! ## Hardness and undecidability -/

/-- **Transfer of many-one hardness for Lyapunov stability.**  If
`HLSQ n₀ (2k₀+1)` is many-one hard, then so is `HLSQ N d` for every
`N ≥ cubicLiftCodeDimension n₀ k₀` and every odd `d ≥ 3`; consequently it
is undecidable and its complement is not recursively enumerable.  With
Korda's theorem as the hypothesis `hsource`, this is Corollary 1.4 of the
paper. -/
theorem hlsQ_manyOneHard_cofinal_of_source
    (n₀ k₀ : ℕ) (hn₀ : 2 ≤ n₀) (hk₀ : 1 ≤ k₀)
    (hsource : ManyOneHard (HLSQ n₀ (2 * k₀ + 1)))
    (N d : ℕ) (hN : cubicLiftCodeDimension n₀ k₀ ≤ N)
    (hd : Odd d) (hthree : 3 ≤ d) :
    ManyOneHard (HLSQ N d) ∧ ¬ ComputablePred (HLSQ N d) ∧
      ¬ REPred (fun F ↦ ¬ HLSQ N d F) := by
  have h : ManyOneHard (HLSQ N d) :=
    hsource.of_manyOneReducible
      (hlsQ_manyOneReducible_cofinalFixedPair n₀ k₀ N d hn₀ hk₀ hN hd hthree)
  exact ⟨h, h.not_computable, h.complement_not_re⟩

/-- **Transfer of undecidability for Lyapunov stability** (Remark 7.1 of
the paper, with Korda's five-dimensional theorem as the hypothesis). -/
theorem hlsQ_not_computable_cofinal_of_source
    (n₀ k₀ : ℕ) (hn₀ : 2 ≤ n₀) (hk₀ : 1 ≤ k₀)
    (hsource : ¬ ComputablePred (HLSQ n₀ (2 * k₀ + 1)))
    (N d : ℕ) (hN : cubicLiftCodeDimension n₀ k₀ ≤ N)
    (hd : Odd d) (hthree : 3 ≤ d) :
    ¬ ComputablePred (HLSQ N d) := fun h ↦
  hsource (ComputablePred.computable_of_manyOneReducible
    (hlsQ_manyOneReducible_cofinalFixedPair n₀ k₀ N d hn₀ hk₀ hN hd hthree) h)

end Propagation

end

end HGAS
