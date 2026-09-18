import HGAS.Modular.JacobiResidualCurveSmoothness
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Local analytic regularity of the Jacobi residual curve

This module turns the algebraic Jacobian calculation into an honest local
analytic statement on the affine cone.  It deliberately stops short of
projective irreducibility or genus.
-/

namespace HGAS.Modular

noncomputable section

open Filter
open scoped Topology

/-- The formal differential of `Q₁`, regarded as a continuous complex-linear
map.  Continuity is automatic because the source is finite-dimensional. -/
def jacobiResidualQ1FDeriv
    (p2 p3 p4 : ℂ) (X : Fin 4 → ℂ) :
    (Fin 4 → ℂ) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    (jacobiResidualQ1Differential p2 p3 p4 X)

/-- The formal differential of `Q₂`, regarded as a continuous complex-linear
map. -/
def jacobiResidualQ2FDeriv
    (p2 p3 p4 : ℂ) (X : Fin 4 → ℂ) :
    (Fin 4 → ℂ) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    (jacobiResidualQ2Differential p2 p3 p4 X)

@[simp] theorem jacobiResidualQ1FDeriv_apply
    (p2 p3 p4 : ℂ) (X V : Fin 4 → ℂ) :
    jacobiResidualQ1FDeriv p2 p3 p4 X V =
      jacobiResidualQ1Differential p2 p3 p4 X V := rfl

@[simp] theorem jacobiResidualQ2FDeriv_apply
    (p2 p3 p4 : ℂ) (X V : Fin 4 → ℂ) :
    jacobiResidualQ2FDeriv p2 p3 p4 X V =
      jacobiResidualQ2Differential p2 p3 p4 X V := rfl

/-- `Q₁` has the displayed complex Fréchet derivative. -/
theorem hasStrictFDerivAt_jacobiResidualQ1
    (p2 p3 p4 : ℂ) (X : Fin 4 → ℂ) :
    HasStrictFDerivAt (jacobiResidualQ1 p2 p3 p4)
      (jacobiResidualQ1FDeriv p2 p3 p4 X) X := by
  have h3 :=
    ((hasStrictFDerivAt_apply (𝕜 := ℂ) 3 X).pow 2).const_mul p2
  have h1 :=
    ((hasStrictFDerivAt_apply (𝕜 := ℂ) 1 X).pow 2).const_mul p4
  have h0 :=
    ((hasStrictFDerivAt_apply (𝕜 := ℂ) 0 X).pow 2).const_mul p3
  convert (h3.sub h1).sub h0 using 1
  ext V
  simp [jacobiResidualQ1FDeriv,
    jacobiResidualQ1Differential_apply]
  ring

/-- `Q₂` has the displayed complex Fréchet derivative. -/
theorem hasStrictFDerivAt_jacobiResidualQ2
    (p2 p3 p4 : ℂ) (X : Fin 4 → ℂ) :
    HasStrictFDerivAt (jacobiResidualQ2 p2 p3 p4)
      (jacobiResidualQ2FDeriv p2 p3 p4 X) X := by
  have h2 :=
    ((hasStrictFDerivAt_apply (𝕜 := ℂ) 2 X).pow 2).const_mul p2
  have h1 :=
    ((hasStrictFDerivAt_apply (𝕜 := ℂ) 1 X).pow 2).const_mul p3
  have h0 :=
    ((hasStrictFDerivAt_apply (𝕜 := ℂ) 0 X).pow 2).const_mul p4
  convert (h2.sub h1).sub h0 using 1
  ext V
  simp [jacobiResidualQ2FDeriv,
    jacobiResidualQ2Differential_apply]
  ring

/-- `Q₁` has the displayed (ordinary) complex Fréchet derivative. -/
theorem hasFDerivAt_jacobiResidualQ1
    (p2 p3 p4 : ℂ) (X : Fin 4 → ℂ) :
    HasFDerivAt (jacobiResidualQ1 p2 p3 p4)
      (jacobiResidualQ1FDeriv p2 p3 p4 X) X :=
  (hasStrictFDerivAt_jacobiResidualQ1 p2 p3 p4 X).hasFDerivAt

/-- `Q₂` has the displayed (ordinary) complex Fréchet derivative. -/
theorem hasFDerivAt_jacobiResidualQ2
    (p2 p3 p4 : ℂ) (X : Fin 4 → ℂ) :
    HasFDerivAt (jacobiResidualQ2 p2 p3 p4)
      (jacobiResidualQ2FDeriv p2 p3 p4 X) X :=
  (hasStrictFDerivAt_jacobiResidualQ2 p2 p3 p4 X).hasFDerivAt

/-- The first residual quadric is complex analytic (`Cω`, hence `C∞`). -/
theorem contDiff_jacobiResidualQ1
    (p2 p3 p4 : ℂ) :
    ContDiff ℂ ⊤ (jacobiResidualQ1 p2 p3 p4) := by
  unfold jacobiResidualQ1
  fun_prop

/-- The second residual quadric is complex analytic (`Cω`, hence `C∞`). -/
theorem contDiff_jacobiResidualQ2
    (p2 p3 p4 : ℂ) :
    ContDiff ℂ ⊤ (jacobiResidualQ2 p2 p3 p4) := by
  unfold jacobiResidualQ2
  fun_prop

/-- Pointwise analytic packaging for the first residual quadric. -/
theorem analyticAt_jacobiResidualQ1
    (p2 p3 p4 : ℂ) (X : Fin 4 → ℂ) :
    AnalyticAt ℂ (jacobiResidualQ1 p2 p3 p4) X :=
  (contDiff_jacobiResidualQ1 p2 p3 p4).contDiffAt.analyticAt

/-- Pointwise analytic packaging for the second residual quadric. -/
theorem analyticAt_jacobiResidualQ2
    (p2 p3 p4 : ℂ) (X : Fin 4 → ℂ) :
    AnalyticAt ℂ (jacobiResidualQ2 p2 p3 p4) X :=
  (contDiff_jacobiResidualQ2 p2 p3 p4).contDiffAt.analyticAt

/-- The coefficient residual is precisely the Jacobi square relation. -/
theorem residualR0_eq_zero_iff_jacobi_relation
    (z : JacobiState ℂ) :
    JacobiState.residualR0 z = 0 ↔
      z.p3 ^ 2 = z.p2 ^ 2 + z.p4 ^ 2 := by
  simp only [JacobiState.residualR0]
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

/-- The pair of equations whose zero fiber is the affine residual cone. -/
def jacobiResidualPair
    (p2 p3 p4 : ℂ) (X : Fin 4 → ℂ) : ℂ × ℂ :=
  (jacobiResidualQ1 p2 p3 p4 X,
    jacobiResidualQ2 p2 p3 p4 X)

/-- The derivative of the paired residual map. -/
def jacobiResidualPairFDeriv
    (p2 p3 p4 : ℂ) (X : Fin 4 → ℂ) :
    (Fin 4 → ℂ) →L[ℂ] ℂ × ℂ :=
  (jacobiResidualQ1FDeriv p2 p3 p4 X).prod
    (jacobiResidualQ2FDeriv p2 p3 p4 X)

@[simp] theorem jacobiResidualPairFDeriv_apply
    (p2 p3 p4 : ℂ) (X V : Fin 4 → ℂ) :
    jacobiResidualPairFDeriv p2 p3 p4 X V =
      (jacobiResidualQ1Differential p2 p3 p4 X V,
        jacobiResidualQ2Differential p2 p3 p4 X V) := rfl

/-- The paired residual map has the paired strict Fréchet derivative. -/
theorem hasStrictFDerivAt_jacobiResidualPair
    (p2 p3 p4 : ℂ) (X : Fin 4 → ℂ) :
    HasStrictFDerivAt (jacobiResidualPair p2 p3 p4)
      (jacobiResidualPairFDeriv p2 p3 p4 X) X :=
  (hasStrictFDerivAt_jacobiResidualQ1 p2 p3 p4 X).prodMk
    (hasStrictFDerivAt_jacobiResidualQ2 p2 p3 p4 X)

/-- The paired residual map has the paired Fréchet derivative. -/
theorem hasFDerivAt_jacobiResidualPair
    (p2 p3 p4 : ℂ) (X : Fin 4 → ℂ) :
    HasFDerivAt (jacobiResidualPair p2 p3 p4)
      (jacobiResidualPairFDeriv p2 p3 p4 X) X :=
  (hasStrictFDerivAt_jacobiResidualPair p2 p3 p4 X).hasFDerivAt

/-- The paired residual map is complex analytic (`Cω`, hence `C∞`). -/
theorem contDiff_jacobiResidualPair
    (p2 p3 p4 : ℂ) :
    ContDiff ℂ ⊤ (jacobiResidualPair p2 p3 p4) :=
  (contDiff_jacobiResidualQ1 p2 p3 p4).prodMk
    (contDiff_jacobiResidualQ2 p2 p3 p4)

/-- Pointwise analytic packaging for the paired residual map. -/
theorem analyticAt_jacobiResidualPair
    (p2 p3 p4 : ℂ) (X : Fin 4 → ℂ) :
    AnalyticAt ℂ (jacobiResidualPair p2 p3 p4) X :=
  (contDiff_jacobiResidualPair p2 p3 p4).contDiffAt.analyticAt

/-- Substitution of a Jacobi state into the paired equation recovers the
previously defined pair of affine residuals. -/
@[simp] theorem jacobiResidualPair_projectiveCoordinates
    (z : JacobiState ℂ) :
    jacobiResidualPair z.p2 z.p3 z.p4
        (jacobiResidualProjectiveCoordinates z) =
      (JacobiState.residualR1 z, JacobiState.residualR2 z) := by
  simp [jacobiResidualPair]

/-- Independence of `dQ₁,dQ₂` is equivalent here to surjectivity of the
derivative of `(Q₁,Q₂)`.  We prove this through the algebraic dual map, so
the statement remains reusable independently of a coordinate minor. -/
theorem jacobiResidualPairFDeriv_surjective
    {p2 p3 p4 : ℂ}
    (hp : p2 * p3 * p4 ≠ 0)
    (hJacobi : p3 ^ 2 = p2 ^ 2 + p4 ^ 2)
    {X : Fin 4 → ℂ}
    (hX : X ≠ 0)
    (hQ1 : jacobiResidualQ1 p2 p3 p4 X = 0)
    (hQ2 : jacobiResidualQ2 p2 p3 p4 X = 0) :
    Function.Surjective (jacobiResidualPairFDeriv p2 p3 p4 X) := by
  change Function.Surjective
    (jacobiResidualPairFDeriv p2 p3 p4 X).toLinearMap
  rw [← LinearMap.dualMap_injective_iff]
  intro φ ψ hφψ
  let θ : Module.Dual ℂ (ℂ × ℂ) := φ - ψ
  let q : ℂ := θ (1, 0)
  let s : ℂ := θ (0, 1)
  have hθdual :
      (jacobiResidualPairFDeriv p2 p3 p4 X).toLinearMap.dualMap θ = 0 := by
    dsimp only [θ]
    rw [map_sub, hφψ, sub_self]
  have hθ_apply (a b : ℂ) :
      θ (a, b) = a * q + b * s := by
    change (φ - ψ) (a, b) =
      a * (φ - ψ) (1, 0) + b * (φ - ψ) (0, 1)
    rw [show (a, b) = a • (1, 0) + b • (0, 1) by ext <;> simp]
    simp only [map_add, map_smul, smul_eq_mul]
  have hdependence :
      q • jacobiResidualQ1Differential p2 p3 p4 X +
          s • jacobiResidualQ2Differential p2 p3 p4 X =
        0 := by
    apply LinearMap.ext
    intro V
    have hz := congrArg
      (fun L : Module.Dual ℂ (Fin 4 → ℂ) => L V) hθdual
    change θ (jacobiResidualPairFDeriv p2 p3 p4 X V) = 0 at hz
    simp only [jacobiResidualPairFDeriv_apply] at hz
    rw [hθ_apply] at hz
    simp only [LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, LinearMap.zero_apply]
    linear_combination hz
  have hqs :=
    jacobiResidual_differentials_independent hp hJacobi hX hQ1 hQ2
      hdependence
  apply sub_eq_zero.mp
  apply LinearMap.ext
  rintro ⟨a, b⟩
  change θ (a, b) = 0
  rw [hθ_apply, hqs.1, hqs.2]
  ring

/-- The tangent kernel at a nonzero residual point has complex dimension
two.  Since the ambient affine cone has dimension four, this is the exact
complex codimension-two count. -/
theorem jacobiResidualPairFDeriv_ker_finrank
    {p2 p3 p4 : ℂ}
    (hp : p2 * p3 * p4 ≠ 0)
    (hJacobi : p3 ^ 2 = p2 ^ 2 + p4 ^ 2)
    {X : Fin 4 → ℂ}
    (hX : X ≠ 0)
    (hQ1 : jacobiResidualQ1 p2 p3 p4 X = 0)
    (hQ2 : jacobiResidualQ2 p2 p3 p4 X = 0) :
    Module.finrank ℂ
        (jacobiResidualPairFDeriv p2 p3 p4 X).ker = 2 := by
  let f' := jacobiResidualPairFDeriv p2 p3 p4 X
  have hsurj : Function.Surjective f' :=
    jacobiResidualPairFDeriv_surjective hp hJacobi hX hQ1 hQ2
  have hrange : LinearMap.range f'.toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hrank :=
    LinearMap.finrank_range_add_finrank_ker f'.toLinearMap
  rw [hrange] at hrank
  norm_num [f', Module.finrank_fin_fun, Module.finrank_prod] at hrank ⊢
  change Module.finrank ℂ f'.ker = 2
  omega

/-! ## The radial direction and the projective tangent dimension -/

/-- Euler's identity for the first homogeneous quadric. -/
theorem jacobiResidualQ1FDeriv_self
    (p2 p3 p4 : ℂ) (X : Fin 4 → ℂ) :
    jacobiResidualQ1FDeriv p2 p3 p4 X X =
      2 * jacobiResidualQ1 p2 p3 p4 X := by
  simp [jacobiResidualQ1FDeriv,
    jacobiResidualQ1Differential_apply, jacobiResidualQ1]
  ring

/-- Euler's identity for the second homogeneous quadric. -/
theorem jacobiResidualQ2FDeriv_self
    (p2 p3 p4 : ℂ) (X : Fin 4 → ℂ) :
    jacobiResidualQ2FDeriv p2 p3 p4 X X =
      2 * jacobiResidualQ2 p2 p3 p4 X := by
  simp [jacobiResidualQ2FDeriv,
    jacobiResidualQ2Differential_apply, jacobiResidualQ2]
  ring

/-- At a common zero, the radial vector belongs to the tangent kernel of
the affine cone. -/
theorem jacobiResidual_radial_mem_ker
    (p2 p3 p4 : ℂ) {X : Fin 4 → ℂ}
    (hQ1 : jacobiResidualQ1 p2 p3 p4 X = 0)
    (hQ2 : jacobiResidualQ2 p2 p3 p4 X = 0) :
    X ∈ (jacobiResidualPairFDeriv p2 p3 p4 X).ker := by
  change jacobiResidualPairFDeriv p2 p3 p4 X X = 0
  change
    (jacobiResidualQ1FDeriv p2 p3 p4 X X,
      jacobiResidualQ2FDeriv p2 p3 p4 X X) = 0
  rw [jacobiResidualQ1FDeriv_self,
    jacobiResidualQ2FDeriv_self, hQ1, hQ2]
  simp

/-- The radial vector, bundled in the tangent kernel. -/
def jacobiResidualRadialVector
    (p2 p3 p4 : ℂ) {X : Fin 4 → ℂ}
    (hQ1 : jacobiResidualQ1 p2 p3 p4 X = 0)
    (hQ2 : jacobiResidualQ2 p2 p3 p4 X = 0) :
    (jacobiResidualPairFDeriv p2 p3 p4 X).ker :=
  ⟨X, jacobiResidual_radial_mem_ker p2 p3 p4 hQ1 hQ2⟩

@[simp] theorem jacobiResidualRadialVector_coe
    (p2 p3 p4 : ℂ) {X : Fin 4 → ℂ}
    (hQ1 : jacobiResidualQ1 p2 p3 p4 X = 0)
    (hQ2 : jacobiResidualQ2 p2 p3 p4 X = 0) :
    (jacobiResidualRadialVector p2 p3 p4 hQ1 hQ2 :
      Fin 4 → ℂ) = X := rfl

/-- The projective tangent-space dimension count.

The affine tangent kernel has dimension two.  The nonzero radial vector
spans a one-dimensional subspace inside it, and the quotient by that line
has complex dimension one.  This is the precise linear-algebraic tangent
calculation behind the passage from the smooth affine cone to a smooth
projective curve. -/
theorem jacobiResidual_projectiveTangent_finrank
    {p2 p3 p4 : ℂ}
    (hp : p2 * p3 * p4 ≠ 0)
    (hJacobi : p3 ^ 2 = p2 ^ 2 + p4 ^ 2)
    {X : Fin 4 → ℂ}
    (hX : X ≠ 0)
    (hQ1 : jacobiResidualQ1 p2 p3 p4 X = 0)
    (hQ2 : jacobiResidualQ2 p2 p3 p4 X = 0) :
    Module.finrank ℂ
        ((jacobiResidualPairFDeriv p2 p3 p4 X).ker ⧸
          ℂ ∙ jacobiResidualRadialVector p2 p3 p4 hQ1 hQ2) = 1 := by
  let v :=
    jacobiResidualRadialVector p2 p3 p4 hQ1 hQ2
  have hv : v ≠ 0 := by
    intro hv
    apply hX
    have hcoe := congrArg
      (fun y :
        (jacobiResidualPairFDeriv p2 p3 p4 X).ker =>
          (y : Fin 4 → ℂ)) hv
    simpa [v] using hcoe
  have hspan :
      Module.finrank ℂ (ℂ ∙ v) = 1 :=
    finrank_span_singleton hv
  have hker :
      Module.finrank ℂ
          (jacobiResidualPairFDeriv p2 p3 p4 X).ker = 2 :=
    jacobiResidualPairFDeriv_ker_finrank hp hJacobi hX hQ1 hQ2
  have hquot :=
    (ℂ ∙ v).finrank_quotient_add_finrank
  rw [hspan, hker] at hquot
  change Module.finrank ℂ
      ((jacobiResidualPairFDeriv p2 p3 p4 X).ker ⧸ ℂ ∙ v) = 1
  omega

/-- **Local codimension-two normal form for the affine residual cone.**

At every nonzero common zero, an open neighborhood of `X` has coordinates
in `(ℂ × ℂ) × ker d(Q₁,Q₂)` in which the first coordinate is exactly
`(Q₁,Q₂)`.  Hence, inside the chart source, the common zero locus is the
vertical slice with first coordinate zero.  The kernel has complex
dimension two by `jacobiResidualPairFDeriv_ker_finrank`.

This is the local analytic/implicit-function content of smoothness on the
affine cone.  It makes no assertion about connectedness, irreducibility, or
genus of the projective quotient. -/
theorem exists_jacobiResidual_local_normal_form
    {p2 p3 p4 : ℂ}
    (hp : p2 * p3 * p4 ≠ 0)
    (hJacobi : p3 ^ 2 = p2 ^ 2 + p4 ^ 2)
    {X : Fin 4 → ℂ}
    (hX : X ≠ 0)
    (hQ1 : jacobiResidualQ1 p2 p3 p4 X = 0)
    (hQ2 : jacobiResidualQ2 p2 p3 p4 X = 0) :
    ∃ e : OpenPartialHomeomorph (Fin 4 → ℂ)
        ((ℂ × ℂ) ×
          (jacobiResidualPairFDeriv p2 p3 p4 X).ker),
      X ∈ e.source ∧
      e X = ((0, 0), 0) ∧
      (∀ Y, (e Y).1 = jacobiResidualPair p2 p3 p4 Y) ∧
      ∀ Y ∈ e.source,
        (jacobiResidualQ1 p2 p3 p4 Y = 0 ∧
            jacobiResidualQ2 p2 p3 p4 Y = 0 ↔
          (e Y).1 = (0, 0)) := by
  let f := jacobiResidualPair p2 p3 p4
  let f' := jacobiResidualPairFDeriv p2 p3 p4 X
  have hf : HasStrictFDerivAt f f' X :=
    hasStrictFDerivAt_jacobiResidualPair p2 p3 p4 X
  have hsurj : Function.Surjective f' :=
    jacobiResidualPairFDeriv_surjective hp hJacobi hX hQ1 hQ2
  have hrange : LinearMap.range f'.toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  let e : OpenPartialHomeomorph (Fin 4 → ℂ)
      ((ℂ × ℂ) × f'.ker) :=
    hf.implicitToOpenPartialHomeomorph f f' hrange
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · exact hf.mem_implicitToOpenPartialHomeomorph_source hrange
  · rw [hf.implicitToOpenPartialHomeomorph_self hrange]
    simp [f, jacobiResidualPair, hQ1, hQ2]
  · intro Y
    exact hf.implicitToOpenPartialHomeomorph_fst hrange Y
  · intro Y _
    rw [hf.implicitToOpenPartialHomeomorph_fst hrange]
    simp only [f, jacobiResidualPair, Prod.mk.injEq]

/-- A complex-analytic (`Cω`) local parametrization of the residual fiber.

The parameter space is the kernel of the paired derivative.  The
parametrization passes through `X`, has derivative the natural inclusion of
that kernel into the ambient four-dimensional space, and maps a
neighborhood of zero into the common zero locus.  Combined with
`exists_jacobiResidual_local_normal_form`, this records both directions of
the local submanifold description. -/
theorem exists_jacobiResidual_contDiff_parametrization
    {p2 p3 p4 : ℂ}
    (hp : p2 * p3 * p4 ≠ 0)
    (hJacobi : p3 ^ 2 = p2 ^ 2 + p4 ^ 2)
    {X : Fin 4 → ℂ}
    (hX : X ≠ 0)
    (hQ1 : jacobiResidualQ1 p2 p3 p4 X = 0)
    (hQ2 : jacobiResidualQ2 p2 p3 p4 X = 0) :
    ∃ ψ :
        (jacobiResidualPairFDeriv p2 p3 p4 X).ker →
          (Fin 4 → ℂ),
      ψ 0 = X ∧
      ContDiffAt ℂ ⊤ ψ 0 ∧
      HasFDerivAt ψ
        (jacobiResidualPairFDeriv p2 p3 p4 X).ker.subtypeL 0 ∧
      ∀ᶠ y in 𝓝 0,
        jacobiResidualQ1 p2 p3 p4 (ψ y) = 0 ∧
          jacobiResidualQ2 p2 p3 p4 (ψ y) = 0 := by
  let f := jacobiResidualPair p2 p3 p4
  let f' := jacobiResidualPairFDeriv p2 p3 p4 X
  have hf : HasStrictFDerivAt f f' X :=
    hasStrictFDerivAt_jacobiResidualPair p2 p3 p4 X
  have hsurj : Function.Surjective f' :=
    jacobiResidualPairFDeriv_surjective hp hJacobi hX hQ1 hQ2
  have hrange : LinearMap.range f'.toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  let hker : f'.ker.ClosedComplemented :=
    f'.ker_closedComplemented_of_finiteDimensional_range
  let φ : ImplicitFunctionData ℂ (Fin 4 → ℂ) (ℂ × ℂ) f'.ker :=
    hf.implicitFunctionDataOfComplemented f f' hrange hker
  let ψ : f'.ker → (Fin 4 → ℂ) :=
    hf.implicitFunctionOfComplemented f f' hrange hker (f X)
  have hleft : ContDiffAt ℂ ⊤ φ.leftFun φ.pt := by
    simpa [φ, f,
      HasStrictFDerivAt.implicitFunctionDataOfComplemented] using
      (contDiff_jacobiResidualPair p2 p3 p4).contDiffAt
  have hright : ContDiffAt ℂ ⊤ φ.rightFun φ.pt := by
    dsimp [φ, HasStrictFDerivAt.implicitFunctionDataOfComplemented]
    fun_prop
  have hprod :
      φ.prodFun φ.pt = (f X, (0 : f'.ker)) := by
    simp [φ, ImplicitFunctionData.prodFun,
      HasStrictFDerivAt.implicitFunctionDataOfComplemented]
  have hφsmooth :
      ContDiffAt ℂ ⊤ φ.implicitFunction.uncurry
        (f X, (0 : f'.ker)) := by
    rw [← hprod]
    exact φ.contDiffAt_implicitFunction hleft hright (by simp)
  have hin :
      ContDiffAt ℂ ⊤ (fun y : f'.ker => (f X, y)) 0 := by
    fun_prop
  have hψsmooth : ContDiffAt ℂ ⊤ ψ 0 := by
    have hcomp := hφsmooth.comp 0 hin
    simpa [ψ, φ,
      HasStrictFDerivAt.implicitFunctionOfComplemented,
      Function.uncurry] using hcomp
  have hψzero :
      ∀ᶠ y in 𝓝 0, f (ψ y) = f X := by
    have hpairs :=
      hf.map_implicitFunctionOfComplemented_eq hrange hker
    have htend :
        Tendsto (fun y : f'.ker => (f X, y)) (𝓝 0)
          (𝓝 (f X, (0 : f'.ker))) :=
      tendsto_const_nhds.prodMk_nhds tendsto_id
    simpa [ψ] using htend.eventually hpairs
  refine ⟨ψ, ?_, hψsmooth, ?_, ?_⟩
  · exact hf.implicitFunctionOfComplemented_apply_image hrange hker
  · exact
      (hf.to_implicitFunctionOfComplemented hrange hker).hasFDerivAt
  · filter_upwards [hψzero] with y hy
    have hpair :
        f (ψ y) = (0, 0) := by
      rw [hy]
      simp [f, jacobiResidualPair, hQ1, hQ2]
    simpa [f, jacobiResidualPair, Prod.ext_iff] using hpair

/-- The local normal form can be chosen complex analytic (`Cω`) in both
directions at the base point.  Thus the common zero locus is not merely locally
homeomorphic to a two-dimensional space: it has a genuine smooth complex
coordinate germ with normal coordinates `(Q₁,Q₂)`. -/
theorem exists_jacobiResidual_contDiff_local_normal_form
    {p2 p3 p4 : ℂ}
    (hp : p2 * p3 * p4 ≠ 0)
    (hJacobi : p3 ^ 2 = p2 ^ 2 + p4 ^ 2)
    {X : Fin 4 → ℂ}
    (hX : X ≠ 0)
    (hQ1 : jacobiResidualQ1 p2 p3 p4 X = 0)
    (hQ2 : jacobiResidualQ2 p2 p3 p4 X = 0) :
    ∃ e : OpenPartialHomeomorph (Fin 4 → ℂ)
        ((ℂ × ℂ) ×
          (jacobiResidualPairFDeriv p2 p3 p4 X).ker),
      X ∈ e.source ∧
      e X = ((0, 0), 0) ∧
      ContDiffAt ℂ ⊤ e X ∧
      ContDiffAt ℂ ⊤ e.symm ((0, 0), 0) ∧
      (∀ Y, (e Y).1 = jacobiResidualPair p2 p3 p4 Y) ∧
      ∀ Y ∈ e.source,
        (jacobiResidualQ1 p2 p3 p4 Y = 0 ∧
            jacobiResidualQ2 p2 p3 p4 Y = 0 ↔
          (e Y).1 = (0, 0)) := by
  let f := jacobiResidualPair p2 p3 p4
  let f' := jacobiResidualPairFDeriv p2 p3 p4 X
  have hf : HasStrictFDerivAt f f' X :=
    hasStrictFDerivAt_jacobiResidualPair p2 p3 p4 X
  have hsurj : Function.Surjective f' :=
    jacobiResidualPairFDeriv_surjective hp hJacobi hX hQ1 hQ2
  have hrange : LinearMap.range f'.toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  let hker : f'.ker.ClosedComplemented :=
    f'.ker_closedComplemented_of_finiteDimensional_range
  let φ : ImplicitFunctionData ℂ (Fin 4 → ℂ) (ℂ × ℂ) f'.ker :=
    hf.implicitFunctionDataOfComplemented f f' hrange hker
  let e : OpenPartialHomeomorph (Fin 4 → ℂ)
      ((ℂ × ℂ) × f'.ker) :=
    φ.toOpenPartialHomeomorph
  have hleft : ContDiffAt ℂ ⊤ φ.leftFun φ.pt := by
    simpa [φ, f,
      HasStrictFDerivAt.implicitFunctionDataOfComplemented] using
      (contDiff_jacobiResidualPair p2 p3 p4).contDiffAt
  have hright : ContDiffAt ℂ ⊤ φ.rightFun φ.pt := by
    dsimp [φ, HasStrictFDerivAt.implicitFunctionDataOfComplemented]
    fun_prop
  have hprod :
      φ.prodFun φ.pt = (f X, (0 : f'.ker)) := by
    simp [φ, ImplicitFunctionData.prodFun,
      HasStrictFDerivAt.implicitFunctionDataOfComplemented]
  have hzeroPair : f X = (0, 0) := by
    simp [f, jacobiResidualPair, hQ1, hQ2]
  have heX : e X = ((0, 0), 0) := by
    change φ.prodFun φ.pt = ((0, 0), 0)
    rw [hprod, hzeroPair]
  have hesmooth : ContDiffAt ℂ ⊤ e X := by
    change ContDiffAt ℂ ⊤ φ.prodFun φ.pt
    exact hleft.prodMk hright
  have heinvSmooth :
      ContDiffAt ℂ ⊤ e.symm ((0, 0), 0) := by
    have hi :=
      φ.contDiffAt_implicitFunction hleft hright (by simp)
    rw [hprod, hzeroPair] at hi
    simpa [e, ImplicitFunctionData.implicitFunction,
      Function.uncurry_curry] using hi
  refine ⟨e, ?_, heX, hesmooth, heinvSmooth, ?_, ?_⟩
  · exact φ.pt_mem_toOpenPartialHomeomorph_source
  · intro Y
    rfl
  · intro Y _
    change (jacobiResidualQ1 p2 p3 p4 Y = 0 ∧
        jacobiResidualQ2 p2 p3 p4 Y = 0 ↔
      f Y = (0, 0))
    simp only [f, jacobiResidualPair, Prod.mk.injEq]

/-- Explicit analytic formulation of the local normal-coordinate theorem.
The order `⊤ : ℕ∞ω` in
`exists_jacobiResidual_contDiff_local_normal_form` is `ω`; this corollary
exposes the corresponding `AnalyticAt` conclusions directly. -/
theorem exists_jacobiResidual_analytic_local_normal_form
    {p2 p3 p4 : ℂ}
    (hp : p2 * p3 * p4 ≠ 0)
    (hJacobi : p3 ^ 2 = p2 ^ 2 + p4 ^ 2)
    {X : Fin 4 → ℂ}
    (hX : X ≠ 0)
    (hQ1 : jacobiResidualQ1 p2 p3 p4 X = 0)
    (hQ2 : jacobiResidualQ2 p2 p3 p4 X = 0) :
    ∃ e : OpenPartialHomeomorph (Fin 4 → ℂ)
        ((ℂ × ℂ) ×
          (jacobiResidualPairFDeriv p2 p3 p4 X).ker),
      X ∈ e.source ∧
      e X = ((0, 0), 0) ∧
      AnalyticAt ℂ e X ∧
      AnalyticAt ℂ e.symm ((0, 0), 0) ∧
      (∀ Y, (e Y).1 = jacobiResidualPair p2 p3 p4 Y) ∧
      ∀ Y ∈ e.source,
        (jacobiResidualQ1 p2 p3 p4 Y = 0 ∧
            jacobiResidualQ2 p2 p3 p4 Y = 0 ↔
          (e Y).1 = (0, 0)) := by
  obtain ⟨e, hsource, heX, he, heinv, hfst, hfiber⟩ :=
    exists_jacobiResidual_contDiff_local_normal_form
      hp hJacobi hX hQ1 hQ2
  exact ⟨e, hsource, heX, he.analyticAt, heinv.analyticAt,
    hfst, hfiber⟩

end

end HGAS.Modular
