# The Jacobi residual curve: the formalized local regularity argument

This note explains the role of
`HGAS/Modular/JacobiResidualLocalRegularity.lean`.  It is deliberately
separate from the publication manuscript.  The Lean module proves the
analytic local statement and the projective tangent-dimension calculation,
but it does not claim the still-unformalized global assertions of
connectedness, irreducibility, or genus.

## 1. The two equations

Fix complex numbers \(p_2,p_3,p_4\) such that

\[
 p_2p_3p_4\ne0,\qquad p_3^2=p_2^2+p_4^2.
\]

On \(\mathbf C^4\), with coordinates
\((X_1,X_2,X_3,X_4)\), set

\[
\begin{aligned}
 Q_1(X)&=p_2X_4^2-p_4X_2^2-p_3X_1^2,\\
 Q_2(X)&=p_2X_3^2-p_3X_2^2-p_4X_1^2.
\end{aligned}
\]

The paired map is

\[
                 Q=(Q_1,Q_2):\mathbf C^4\longrightarrow\mathbf C^2.
\]

The preceding module
`JacobiResidualCurveSmoothness.lean` proves directly that, at every
nonzero common zero \(X\), the two covectors
\(dQ_1(X)\) and \(dQ_2(X)\) are linearly independent.  The new module
connects that algebraic calculation to Mathlib's complex analytic
implicit-function theorem.

## 2. Genuine Fréchet derivatives

The formal differentials from the algebraic module are converted into
continuous complex-linear maps.  This conversion is automatic because
the source \(\mathbf C^4\) is finite-dimensional.  Lean then proves

\[
\begin{aligned}
 \operatorname{D}Q_1(X)V
   &=2p_2X_4V_4-2p_4X_2V_2-2p_3X_1V_1,\\
 \operatorname{D}Q_2(X)V
   &=2p_2X_3V_3-2p_3X_2V_2-2p_4X_1V_1
\end{aligned}
\]

as both `HasStrictFDerivAt` and `HasFDerivAt` statements.  Thus the maps
called differentials in the algebraic calculation are now formally tied
to Mathlib's analytic derivative.

The quadrics and their paired map are also proved complex analytic.
In Mathlib's `ℕ∞ω` convention, the order `⊤` is \(\omega\), so the
`ContDiff ℂ ⊤` statements used in the module are analytic statements, not
merely finite-order smoothness statements.

## 3. Why independence gives a surjective derivative

The derivative

\[
                  \operatorname{D}Q(X):\mathbf C^4\to\mathbf C^2
\]

has \(dQ_1(X)\) and \(dQ_2(X)\) as its two rows.  The Lean proof of
surjectivity avoids choosing a nonzero \(2\times2\) minor.  Instead it
uses the dual map.

Suppose a functional \(\theta\in(\mathbf C^2)^*\) vanishes after
composition with \(\operatorname{D}Q(X)\).  Put

\[
 q=\theta(1,0),\qquad s=\theta(0,1).
\]

Linearity gives

\[
             \theta(a,b)=aq+bs,
\]

and therefore

\[
 q\,dQ_1(X)+s\,dQ_2(X)=0.
\]

The already formalized Jacobian-rank theorem forces \(q=s=0\), hence
\(\theta=0\).  The dual map is injective, and finite-dimensional linear
duality gives the desired surjectivity of \(\operatorname{D}Q(X)\).

Rank-nullity then proves

\[
                  \dim_{\mathbf C}\ker \operatorname{D}Q(X)=2.
\]

This proof is coordinate-free after the original explicit Jacobian
calculation and is reusable for other pairs of equations.

## 4. The local analytic normal form

Mathlib's finite-dimensional implicit-function theorem now supplies an
open partial homeomorphism

\[
 e:\mathbf C^4 \dashrightarrow
    \mathbf C^2\times\ker\operatorname{D}Q(X)
\]

such that

\[
 e(X)=((0,0),0),\qquad \operatorname{pr}_1(e(Y))=Q(Y).
\]

Consequently, throughout the source of this chart,

\[
 Q_1(Y)=Q_2(Y)=0
 \quad\Longleftrightarrow\quad
 \operatorname{pr}_1(e(Y))=(0,0).
\]

The module proves that both \(e\) at \(X\) and \(e^{-1}\) at
\(((0,0),0)\) are complex analytic.  It also separately exposes an
analytic parametrization

\[
 \psi:\ker\operatorname{D}Q(X)\longrightarrow\mathbf C^4
\]

with

\[
 \psi(0)=X,\qquad
 \operatorname{D}\psi(0)=
   \bigl(\ker\operatorname{D}Q(X)\hookrightarrow\mathbf C^4\bigr),
\]

and \(Q_1(\psi(y))=Q_2(\psi(y))=0\) for all sufficiently small \(y\).

This is the precise complex-analytic codimension-two local-submanifold
statement for the affine cone away from its vertex.

## 5. The projective tangent direction

Because each \(Q_i\) is homogeneous of degree two, Lean proves Euler's
identities

\[
       dQ_i(X)[X]=2Q_i(X).
\]

At a common zero, the radial vector \(X\) therefore belongs to
\(\ker\operatorname{D}Q(X)\).  Since \(X\ne0\), it spans a
one-dimensional line.  Quotienting the two-dimensional affine tangent
kernel by this radial line gives

\[
 \dim_{\mathbf C}
 \left(
   \ker\operatorname{D}Q(X)/\mathbf C X
 \right)=1.
\]

This quotient is the expected tangent space of the projective common-zero
locus at \([X]\).  The theorem
`jacobiResidual_projectiveTangent_finrank` is the fully formal
linear-algebraic content of that statement.

## 6. Exact remaining library boundary

Mathlib currently has algebraic files for `Projectivization`, but no
`ChartedSpace`/complex-manifold instance for projectivization and no
projective Jacobian criterion turning the preceding affine normal form
into a bundled global predicate such as “smooth projective curve.”
Accordingly, this module does **not** assert such a predicate.

It also does not prove:

1. connectedness of the projective complete intersection;
2. irreducibility;
3. the adjunction computation giving genus one.

Those are global algebraic-geometric statements.  The local analytic
regularity and the one-dimensional projective tangent calculation needed
before them are now unconditional Lean theorems with no project-specific
axioms.
