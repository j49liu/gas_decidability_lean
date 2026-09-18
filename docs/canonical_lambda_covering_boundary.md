# Canonical modular lambda: the formalized local theorem and the global boundary

This note records exactly what is now proved in
`HGAS/Modular/CanonicalLambdaCovering.lean`, and exactly what remains before
one may use the modular-lambda universal covering theorem without a
hypothesis.

## 1. The target

The canonical function in the Lean development is

\[
  \Lambda(\tau)=\frac{H_2(\tau)}{H_3(\tau)}
  =\frac{\vartheta_2(\tau)^4}{\vartheta_3(\tau)^4}.
\]

`ThetaZeroFree.lean` proves pointwise nonvanishing of all three even theta
fourth powers.  Together with Jacobi's identity
\(H_2+H_4=H_3\), this gives

\[
  \Lambda(\tau)\ne0,\qquad
  1-\Lambda(\tau)=\frac{H_4(\tau)}{H_3(\tau)}\ne0.
\]

Consequently lambda has the honest codomain

\[
  X=\mathbb C\setminus\{0,1\}.
\]

In Lean this is `LambdaPuncturedPlane`, and the bundled map is
`canonicalLambdaPunctured : ℍ → LambdaPuncturedPlane`.

## 2. Why lambda is a local homeomorphism

`CanonicalLambdaLocal.lean` proves the exact normalized derivative identity

\[
  D\Lambda
  =\frac12 H_3\,\Lambda(1-\Lambda).
\]

Every factor on the right is nonzero.  Thus the ordinary complex derivative
of lambda is nonzero at every point of the upper half-plane.

There is one small formal subtlety.  Mathlib's Banach-space inverse function
theorem is stated for a function on an ambient normed vector space, whereas
lambda is defined on the upper half-plane.  The formal proof therefore uses

\[
  \Lambda_{\mathrm{raw}}(z)
  =\Lambda(\operatorname{ofComplex}(z)).
\]

At a point of the upper half-plane this ambient representative is analytic,
has the same germ as lambda, and has nonzero derivative.  Mathlib's complex
inverse function theorem produces an `OpenPartialHomeomorph ℂ ℂ`.  The proof
then:

1. composes its source with Mathlib's standard upper-half-plane chart;
2. restricts its target to the open subtype
   \(\mathbb C\setminus\{0,1\}\); and
3. checks that the resulting partial homeomorphism agrees with
   `canonicalLambdaPunctured` on its source.

This proves, without axioms,

```lean
canonicalLambdaPunctured_isLocalHomeomorph :
  IsLocalHomeomorph canonicalLambdaPunctured
```

and hence continuity and openness of the map.

## 3. What already follows for lifts

Two useful consequences require no global covering theorem.

First, two continuous lifts over a connected parameter space that agree at
one point agree everywhere:

```lean
canonicalLambdaPunctured_lift_unique
```

This follows because the upper half-plane is Hausdorff and a local
homeomorphism is locally injective.

Second, a continuous real lift is automatically differentiable whenever
the base curve is differentiable.  If

\[
  \Lambda(T(t))=\ell(t),
\]

then the real derivative of the lift is

\[
  T'(t)=
  \frac{\ell'(t)}
       {\Lambda_{\mathrm{raw}}'(T(t))}.
\]

The formal theorem is

```lean
canonicalLambdaPunctured_lift_hasDerivAt
```

and its proof uses the real restriction of the invertible complex
derivative.  Thus the differentiability hypothesis formerly carried by
`CanonicalLambdaLocal` is automatic once a continuous lift exists.

## 4. The isolated global input

The remaining proposition has been named

```lean
CanonicalLambdaIsCovering :=
  IsCoveringMap canonicalLambdaPunctured
```

From precisely this proposition, Mathlib's covering-space lifting theorem
gives a unique continuous lift of every continuous curve
\(\ell:\mathbb R\to X\) after one initial lift is fixed.  Combining it with
the preceding derivative theorem gives

```lean
canonicalLambdaPunctured_exists_lift_with_derivatives
```

in the exact form needed by the modular trajectory reconstruction.

This is a conditional theorem, not an axiom: the global covering proposition
is an explicit argument to the theorem.

## 5. Why the global proposition is not yet discharged

The standard mathematical proof identifies

\[
  \Gamma(2)\backslash\mathbb H
  \;\cong\;
  \mathbb C\setminus\{0,1\}
\]

by the modular lambda function.  Equivalently, lambda is the universal
cover and its deck group is
\(\Gamma(2)/\{\pm I\}\).

The present Mathlib version contains:

- the upper half-plane and its manifold/topological structure;
- congruence subgroups such as `Gamma 2`;
- general covering-space and path-lifting APIs; and
- the modular slash action.

It does **not** contain the required bridge between these packages:

1. a topological quotient of the upper half-plane by `Gamma 2` equipped
   with a usable fundamental domain;
2. proper discontinuity and the resulting quotient covering;
3. the theorem that lambda is invariant under all of `Gamma 2`;
4. the separation theorem saying equal lambda values differ by an element
   of `Gamma 2`; and
5. surjectivity onto the twice-punctured plane, including the three-cusp
   analysis.

The existing `S` and `T` theta transformation formulas are enough to begin
item 3, but not items 1, 2, 4, or 5.  In particular, nowhere-zero derivative
plus openness is not by itself a covering theorem: a surjective local
homeomorphism need not be a covering map without a global continuation or
evenly-covered-neighborhood argument.

Accordingly, the honest formal boundary is now very narrow and explicit:
all local analysis, uniqueness, and automatic differentiability are closed;
the missing theorem is exactly the classical global
\(\Gamma(2)\)-uniformization of modular lambda.

Classical references for that global theorem include Ahlfors,
*Complex Analysis*, 2nd edition, pp. 271–274; Chandrasekharan,
*Elliptic Functions*, Chapter VII; and DLMF §§20.7 and 23.18.
