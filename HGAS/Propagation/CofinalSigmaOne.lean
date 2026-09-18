import HGAS.Computability.SigmaOne
import HGAS.Lyapunov.RationalHomogeneousConverse
import HGAS.Propagation.CofinalFixedPairReduction

/-!
# Cofinal Sigma-one completeness from one fixed HGAS reduction

This file packages the short recursion-theoretic last step of the main
argument.  The substantial compiler construction has a clean endpoint:
one computable many-one reduction from universal halting to one fixed,
positive-dimensional, odd-degree rational HGAS language.

Once that endpoint is available, the results already proved in the
project give:

1. recursive enumerability at every fixed odd degree, from the rational
   homogeneous converse Lyapunov theorem;
2. an effective cubic Veronese lift;
3. effective dimension and odd-degree padding; and therefore
4. `Σ⁰₁`-completeness at every cofinal fixed pair.

No semantic construction, real number, or classical choice enters the
reduction proved here.
-/

namespace HGAS.Propagation

open HGAS

noncomputable section

/-- One fixed universal-halting reduction already makes the corresponding
fixed odd-degree HGAS language `Σ⁰₁`-complete. -/
theorem sigmaOneComplete_fixedPair_of_universalHalts_reduction
    (n k : ℕ)
    (hsource :
      UniversalHalts ≤₀ HGASQ n (2 * k + 1)) :
    SigmaOneComplete (HGASQ n (2 * k + 1)) := by
  apply sigmaOneComplete_of_universalHalts_reduction
  · exact
      hgasQ_re_of_oddDegree n (2 * k + 1)
        (by
          refine ⟨k, ?_⟩
          omega)
  · exact hsource

/-- **Cofinal fixed-pair completeness, reduced to one explicit compiler.**

If universal halting reduces to `HGASQ n (2*k+1)`, with `n>0` and
`k≥1`, then `HGASQ N d` is `Σ⁰₁`-complete for every fixed

```
N ≥ cubicLiftCodeDimension n k,   d ≥ 3,   Odd d.
```

The theorem is deliberately stated using the actual computable reduction
object, rather than a bare hardness proposition, so that the effectivity
firewall remains visible at the final composition step. -/
theorem sigmaOneComplete_cofinalFixedPair_of_universalHalts_reduction
    (n k N d : ℕ)
    (hn : 0 < n)
    (hk : 1 ≤ k)
    (hsource :
      UniversalHalts ≤₀ HGASQ n (2 * k + 1))
    (hN : Veronese.cubicLiftCodeDimension n k ≤ N)
    (hd : Odd d)
    (hthree : 3 ≤ d) :
    SigmaOneComplete (HGASQ N d) := by
  apply sigmaOneComplete_of_universalHalts_reduction
  · exact hgasQ_re_of_oddDegree N d hd
  · exact
      manyOneReducible_cofinalFixedPair
        UniversalHalts n k N d hn hk hsource
          hN hd hthree

end

end HGAS.Propagation
