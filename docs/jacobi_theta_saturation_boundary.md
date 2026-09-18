# Formal proof of projective Jacobi-theta saturation and local rank

## What is now unconditional

Fix \(\tau\in\mathbb H\), and use the conventions

\[
\theta_3(z|\tau)=\sum_{n\in\mathbb Z}
 e^{\pi i n^2\tau+2\pi i n z},\qquad
\theta_4(z|\tau)=\theta_3(z+\tfrac12|\tau),
\]
\[
\theta_2(z|\tau)=
 e^{\pi i(\tau/4+z)}
 \theta_3(z+\tfrac{\tau}{2}|\tau),\qquad
\theta_1(z|\tau)=-\theta_2(z+\tfrac12|\tau).
\]

Put

\[
 p_2=\theta_2(0|\tau)^2,\qquad
 p_3=\theta_3(0|\tau)^2,\qquad
 p_4=\theta_4(0|\tau)^2.
\]

The files `JacobiThetaDuplication.lean` and
`JacobiThetaResiduals.lean` now prove, without importing a Jacobi
addition theorem, that

\[
\begin{aligned}
p_2\theta_4(z)^2-p_4\theta_2(z)^2-p_3\theta_1(z)^2&=0,\\
p_2\theta_3(z)^2-p_3\theta_2(z)^2-p_4\theta_1(z)^2&=0.
\end{aligned}
\]

These are exactly \(Q_1=Q_2=0\) for the four-coordinate theta vector.
They are also connected definitionally to the coefficients of
`canonicalUnaryRoots`.

Together with the independently proved global no-common-zero theorem,
the explicit Jacobian calculation gives the following unconditional
conclusions at every theta value:

* the four homogeneous coordinates are not all zero;
* both residual quadrics vanish;
* the derivative of \((Q_1,Q_2)\) is surjective;
* the affine tangent kernel has complex dimension two;
* quotienting its radial line gives a one-dimensional projective tangent.

Thus the theta map lands in the smooth locus of the residual intersection,
with exactly the expected local target dimension.

The global set-theoretic statement is now unconditional as well.  The
files `ComplexProjectiveLine.lean`,
`JacobiThetaProjectiveLine.lean`, and
`JacobiThetaProjectiveSurjectivity.lean` prove

\[
 \operatorname{range}\!\left(
   z\longmapsto
   [\theta_1(z):\theta_2(z):\theta_3(z):\theta_4(z)]
 \right)
 =
 \{[X]\in\mathbb P^3(\mathbb C):Q_1(X)=Q_2(X)=0\}.
\]

In Lean, the final equality is
`range_projectiveJacobiTheta_eq_residualCurve`.  A stronger affine
representative statement,
`exists_smul_jacobiThetaVector_eq_of_residual`, says that for every
nonzero common zero \(X\) there are \(z,c\in\mathbb C\), with \(c\ne0\),
such that

\[
 c\,(\theta_1(z),\theta_2(z),\theta_3(z),\theta_4(z))=X.
\]

## The parity proof of the quadratic identities

The proof is elementary and useful beyond this application.  In the
square of a theta series, reindex \((m,n)\in\mathbb Z^2\) uniquely as

\[
(m,n)=(a+b,a-b)
\quad\hbox{or}\quad
(m,n)=(a+b+1,a-b),
\]

according as \(m+n\) is even or odd.  Absolute convergence justifies the
reindexing.  If

\[
A=\theta_3(2z|2\tau),\quad B=\theta_2(2z|2\tau),\quad
c=\theta_3(0|2\tau),\quad d=\theta_2(0|2\tau),
\]

the two parity classes give

\[
\begin{aligned}
\theta_3(z|\tau)^2&=cA+dB,\\
\theta_4(z|\tau)^2&=cA-dB,\\
\theta_2(z|\tau)^2&=dA+cB,\\
\theta_1(z|\tau)^2&=dA-cB.
\end{aligned}
\]

At \(z=0\), these say

\[
p_3=c^2+d^2,\qquad p_4=c^2-d^2,\qquad p_2=2cd.
\]

Substitution makes both residual quadrics cancel term by term.  The same
three constant formulas also give \(p_3^2=p_2^2+p_4^2\).

Lean formalizes the parity split as an explicit equivalence

```text
(ℤ × ℤ) ⊕ (ℤ × ℤ) ≃ ℤ × ℤ
```

and uses Mathlib's unconditional sums together with absolute summability
of the theta series.

## The global saturation proof

The proof deliberately avoids the difficult route through connectedness
or irreducibility of a projective complete intersection.  It has two
elementary stages.

### Stage 1: the ratio \([\theta_1:\theta_2]\) covers
\(\mathbb P^1(\mathbb C)\)

The projective line is modeled as the one-point compactification
\(\mathbb C\cup\{\infty\}\).  For two entire functions \(f,g\) with no
common zero, the ratio

\[
 z\longmapsto [f(z):g(z)]
\]

is continuous, including at zeros of \(f\), by changing to the reciprocal
chart.  If \(f\) and \(g\) are not globally proportional, this map is
open.  The proof uses the complex open-mapping theorem in whichever
affine chart is valid near a point; it does not assume that the
derivative is nonzero, so ramification causes no problem.

For \(f=\theta_1\) and \(g=\theta_2\), the already formalized
no-common-zero theorem supplies the first hypothesis.  The two functions
cannot be globally proportional because their translations by \(\tau\)
have opposite multipliers.  Their projective ratio is invariant under
the doubled lattice \(2\mathbb Z+2\tau\mathbb Z\).  Every
\(z\in\mathbb C\) can be reduced explicitly into a closed bounded
fundamental rectangle, so the image is compact.  Consequently the image
in \(\mathbb P^1(\mathbb C)\) is simultaneously nonempty, open, and
closed.  Connectedness of the projective line then gives

\[
 \{[\theta_1(z):\theta_2(z)]:z\in\mathbb C\}
 =\mathbb P^1(\mathbb C).
\]

This reusable topological argument is isolated in
`ComplexProjectiveLine.lean`; its specialization to theta functions is
`jacobiTheta12Projective_surjective`.

### Stage 2: the residual equations recover the other coordinates

Let \(X=(X_1,X_2,X_3,X_4)\ne0\) satisfy \(Q_1(X)=Q_2(X)=0\).
The pair \((X_1,X_2)\) cannot vanish: otherwise the two residual
equations, together with \(p_2\ne0\), force \(X_3=X_4=0\).
Surjectivity from Stage 1 therefore gives \(z\) and a nonzero scalar
\(c\) such that

\[
 c\theta_1(z)=X_1,\qquad c\theta_2(z)=X_2.
\]

Subtract the residual equations for \(X\) from those for the theta
vector.  Since \(p_2\ne0\), one obtains

\[
 X_3^2=(c\theta_3(z))^2,\qquad
 X_4^2=(c\theta_4(z))^2.
\]

Thus only two independent signs remain.  They are not an obstruction.
The transformations

\[
 z\longmapsto z+1,\qquad z\longmapsto\tau-z
\]

act projectively on the four coordinates by

\[
 (-,-,+,+),\qquad (+,+,+,-),
\]

respectively, after discarding a common nonzero multiplier.  Their four
combinations realize all four sign choices for \((X_3,X_4)\) while
preserving the already matched first two projective coordinates.  This
finishes the affine-up-to-scale theorem and hence projective
surjectivity.

The proof also formalizes the doubled-period identity

\[
 \Theta(z+2m+2n\tau)=\lambda_n(z,\tau)\Theta(z),
 \qquad \lambda_n(z,\tau)\ne0,
\]

and therefore proves that `projectiveJacobiTheta` is genuinely periodic
on the level-two lattice.

Finally, `JacobiPointwiseSaturationUnconditional.lean` connects the
global result to the earlier abstract downstream interface.  It proves
`canonicalJacobiProjectiveCoverage` and removes the coverage hypothesis
from the pointwise Jacobi--Bloch realization theorem.  Thus every
nonzero residual point with nonzero first coordinate, together with any
prescribed normalized first derivative, is realized by the explicit
Bloch-theta family.

## The Wronskians and local rank are now unconditional

`JacobiThetaInitialRank.lean` defines the actual elliptic derivatives of
all four theta coordinates from Mathlib's differentiated series and proves
their `HasDerivAt` statements.

The three Wronskian identities are

\[
\begin{aligned}
\theta_2'\theta_1-\theta_2\theta_1'
  &=-\pi p_2\theta_3\theta_4,\\
\theta_3'\theta_1-\theta_3\theta_1'
  &=-\pi p_3\theta_4\theta_2,\\
\theta_4'\theta_1-\theta_4\theta_1'
  &=-\pi p_4\theta_2\theta_3.
\end{aligned}
\]

`JacobiThetaWronskians.lean` now proves all three directly from the theta
series.  The central argument is as follows.

1. Expand
   \(\theta_2'\theta_1-\theta_2\theta_1'\) as an absolutely convergent
   double series and split the lattice into even and odd parity classes.
   The reindexing gives a doubled-modulus Wronskian formula involving
   \(\theta_1'(0|2\tau)\).
2. A second parity calculation supplies the required bilinear
   \(\theta_3\theta_4\) duplication formula.
3. Normalize \(\theta_1'(0|\tau)\) by
   \(\pi\theta_2(0|\tau)\theta_3(0|\tau)\theta_4(0|\tau)\).  The
   duplication formulas show that this ratio is unchanged by
   \(\tau\mapsto2\tau\).  Direct domination of the differentiated series
   shows that the ratio tends to \(1\) as
   \(\operatorname{Im}\tau\to\infty\).  Iterating doubling therefore
   proves Jacobi's derivative formula

   \[
   \theta_1'(0|\tau)=
   \pi\theta_2(0|\tau)\theta_3(0|\tau)\theta_4(0|\tau).
   \]

4. Substitute this formula into the doubled Wronskian identity to obtain
   the first displayed formula above.
5. Differentiate the two already proved residual quadrics.  After
   inserting the first Wronskian, the remaining errors are annihilated
   by \(\theta_3\) and \(\theta_4\), respectively.  Analyticity and the
   identity theorem eliminate those factors globally and give the other
   two Wronskians.

This yields `canonicalJacobiThetaWronskiansAt` with no hypothesis.  The
separate bridge `JacobiThetaInitialRankUnconditional.lean` then removes
the Wronskian argument from all downstream statements.  Lean proves
unconditionally:

1. the theta vector and its elliptic derivative are linearly independent;
2. the quotient-rule formulas in manuscript equation (8.5);
3. the linearization of the \((S,\xi,L)\) initial-value map is injective;
4. its complex rank is exactly three.

The rank proof mirrors the paper.  The first four coordinates force the
scale displacement and projective displacement to vanish, because
\(\theta\) and \(\theta'\) are independent.  The last coordinate then
forces the Bloch-slope displacement to vanish because
\(S\theta_1\ne0\).

The Wronskian proof and the global range proof are logically separate.
In particular, global set-theoretic saturation does not depend on
immersion, genus, irreducibility, or connectedness of the projective
residual curve.  At this boundary there is no remaining Wronskian or
global-surjectivity assumption and no missing analytic assertion is
introduced as an axiom.
