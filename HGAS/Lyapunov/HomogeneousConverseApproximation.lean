import HGAS.Lyapunov.GridRationalCertificateCompleteness
import HGAS.Lyapunov.TangentialHomogenization
import Mathlib.Tactic

/-!
# From a `C¹` spherical approximation to a homogeneous rational witness

This module assembles the algebraic pieces of the converse-Lyapunov
approximation argument.

Let `V` be a degree-two strict homogeneous `C¹` Lyapunov function and let
`E` be an even polynomial approximating `V` and its first differential on
the Euclidean unit sphere.  At a sphere point write

```
G(x) = T(x) + a(x)x,
T(x) = G(x) - a(x)x,
a(x) = x · G(x).
```

Euler's identity gives

```
DV(x)[G(x)] = DV(x)[T(x)] + 2 a(x)V(x).
```

Consequently the strict certificate expression for `E`,

```
-DE(x)[T(x)] - 2 a(x)E(x),
```

differs from `-DV(x)[G(x)]` by exactly

```
(DV-DE)(x)[T(x)] + 2a(x)(V(x)-E(x)).
```

The first theorem below records this open-error criterion without hiding
any compactness or approximation assumption.  The second theorem raises
`E` to a genuinely homogeneous polynomial using radial powers, and proves
that it is a `RealRationalLyapunovWitness`.  Positivity is propagated from
the Euclidean sphere to every nonzero ray before restricting to the
finite-product norm sphere used by the executable checker.
-/

namespace HGAS

open _root_.MvPolynomial Set

noncomputable section

variable {n : ℕ}

/-- The algebraic Euclidean unit sphere in coordinate space. -/
def euclideanUnitSphere (n : ℕ) : Set (Fin n → ℝ) :=
  {x | normSq x = 1}

@[simp]
theorem mem_euclideanUnitSphere_iff
    (x : Fin n → ℝ) :
    x ∈ euclideanUnitSphere n ↔ normSq x = 1 :=
  Iff.rfl

/-- The algebraic squared norm is continuous in the finite-product
topology. -/
theorem continuous_normSq :
    Continuous (normSq : (Fin n → ℝ) → ℝ) := by
  simpa only [eval_realRhoPolynomial] using
    continuous_mvPolynomial_eval
      (realRhoPolynomial (n := n))

/-- The Euclidean unit sphere is closed. -/
theorem isClosed_euclideanUnitSphere :
    IsClosed (euclideanUnitSphere n) := by
  exact isClosed_eq continuous_normSq continuous_const

/-- Every coordinate, hence the product sup norm, is at most one on the
Euclidean unit sphere. -/
theorem norm_le_one_of_normSq_eq_one
    (x : Fin n → ℝ) (hx : normSq x = 1) :
    ‖x‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  rw [Real.norm_eq_abs]
  have hterm : x i ^ 2 ≤ normSq x := by
    unfold normSq dot
    simpa only [pow_two] using
      Finset.single_le_sum
        (fun j _hj ↦ mul_self_nonneg (x j))
        (Finset.mem_univ i)
  rw [hx] at hterm
  exact (sq_le_one_iff_abs_le_one (x i)).mp hterm

/-- The Euclidean unit sphere is bounded in the ambient finite-product
norm. -/
theorem isBounded_euclideanUnitSphere :
    Bornology.IsBounded (euclideanUnitSphere n) := by
  rw [isBounded_iff_forall_norm_le]
  exact
    ⟨1, fun x hx ↦
      norm_le_one_of_normSq_eq_one x hx⟩

/-- Compactness of the algebraic Euclidean unit sphere. -/
theorem isCompact_euclideanUnitSphere :
    IsCompact (euclideanUnitSphere n) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact
    ⟨isClosed_euclideanUnitSphere,
      isBounded_euclideanUnitSphere⟩

/-- A continuous function strictly positive on the Euclidean unit sphere
has a uniform positive margin there. -/
theorem exists_pos_lower_bound_continuous_on_euclideanUnitSphere
    (f : (Fin n → ℝ) → ℝ) (hf : Continuous f)
    (hpos : ∀ x : Fin n → ℝ, normSq x = 1 → 0 < f x) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ x : Fin n → ℝ, normSq x = 1 → ε ≤ f x := by
  obtain ⟨ε, hε, hbound⟩ :=
    (isCompact_euclideanUnitSphere (n := n)).exists_forall_le'
      hf.continuousOn (a := 0) (by
        intro x hx
        exact hpos x hx)
  exact ⟨ε, hε, fun x hx ↦ hbound x hx⟩

/-! ## Coordinate geometry on the sphere -/

/-- Every continuous linear functional on a finite coordinate product is
the sum of its values on the standard coordinate vectors. -/
theorem continuousLinearMap_apply_eq_sum_piSingle
    (A : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    A v =
      ∑ i : Fin n, A (Pi.single i 1) * v i := by
  classical
  calc
    A v = A (∑ i : Fin n, Pi.single i (v i)) := by
      rw [LinearMap.sum_single_apply (v := v)]
    _ = ∑ i : Fin n, A (Pi.single i (v i)) := by
      rw [map_sum]
    _ = ∑ i : Fin n, A (Pi.single i 1) * v i := by
      apply Finset.sum_congr rfl
      intro i _hi
      have hsingle :
          Pi.single i (v i) = v i • Pi.single i (1 : ℝ) := by
        ext j
        by_cases hji : j = i
        · subst j
          simp
        · simp [hji]
      rw [hsingle, map_smul]
      simp only [smul_eq_mul]
      ring

/-- Coordinate `ℓ¹` size of the tangential field, plus the radial weight
that multiplies the value error. -/
def coordinateTangentialGeometryWeight
    (G : (Fin n → ℝ) → (Fin n → ℝ))
    (x : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n,
      |euclideanTangentComponent x (G x) i|) +
    2 * |dot x (G x)|

/-- The coordinate geometry weight of a continuous field is continuous. -/
theorem continuous_coordinateTangentialGeometryWeight
    {G : (Fin n → ℝ) → (Fin n → ℝ)}
    (hG : Continuous G) :
    Continuous (coordinateTangentialGeometryWeight G) := by
  have hT :=
    continuous_euclideanTangentComponent_field hG
  have ha := continuous_dot_field hG
  unfold coordinateTangentialGeometryWeight
  fun_prop

/-- A continuous field has a finite positive coordinate-geometry bound on
the Euclidean unit sphere. -/
theorem exists_pos_coordinateTangentialGeometryBound
    {G : (Fin n → ℝ) → (Fin n → ℝ)}
    (hG : Continuous G) :
    ∃ B : ℝ, 0 < B ∧
      ∀ x : Fin n → ℝ, normSq x = 1 →
        coordinateTangentialGeometryWeight G x ≤ B := by
  obtain ⟨A, hA⟩ :=
    (isCompact_euclideanUnitSphere (n := n)).bddAbove_image
      (continuous_coordinateTangentialGeometryWeight hG).continuousOn
  let B : ℝ := max A 0 + 1
  have hB : 0 < B := by
    dsimp only [B]
    have := le_max_right A 0
    linarith
  refine ⟨B, hB, ?_⟩
  intro x hx
  have hxA : coordinateTangentialGeometryWeight G x ≤ A := by
    apply hA
    exact ⟨x, hx, rfl⟩
  exact hxA.trans
    ((le_max_left A 0).trans (le_add_of_nonneg_right zero_le_one))

/-- The strict dissipation of a `C¹` Lyapunov function along a continuous
field is continuous. -/
theorem continuous_neg_fderiv_along
    {G : (Fin n → ℝ) → (Fin n → ℝ)}
    (L : StrictHomogeneousC1Lyapunov G 2)
    (hG : Continuous G) :
    Continuous (fun x ↦ -fderiv ℝ L.V x (G x)) := by
  exact
    ((L.contDiff.continuous_fderiv (by norm_num)).clm_apply hG).neg

/-! ## The open approximation criterion -/

/-- Exact pointwise criterion showing that an approximating polynomial has
positive value and positive tangential certificate expression.

The hypotheses are deliberately the two strict open inequalities that a
uniform `C¹` approximation must eventually satisfy. -/
theorem polynomial_tangential_lyapunov_of_open_errors
    {G : (Fin n → ℝ) → (Fin n → ℝ)}
    (L : StrictHomogeneousC1Lyapunov G 2)
    (E : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ) (hx : normSq x = 1)
    (hvalueError :
      |MvPolynomial.eval x E - L.V x| < L.V x)
    (hdecayError :
      |(fderiv ℝ L.V x
            (euclideanTangentComponent x (G x)) -
          mvPolynomialDifferential E x
            (euclideanTangentComponent x (G x))) +
        2 * dot x (G x) *
          (L.V x - MvPolynomial.eval x E)| <
        -fderiv ℝ L.V x (G x)) :
    0 < MvPolynomial.eval x E ∧
      0 <
        -mvPolynomialDifferential E x
            (euclideanTangentComponent x (G x)) -
          2 * MvPolynomial.eval x E * dot x (G x) := by
  have hxne : x ≠ 0 := by
    intro hzero
    rw [hzero, normSq_zero] at hx
    norm_num at hx
  have hVpos := L.positive x hxne
  have hVdec := L.decreases x hxne
  have hvalueLower := (abs_lt.mp hvalueError).1
  constructor
  · linarith
  · have hdecomp :
        fderiv ℝ L.V x (G x) =
          fderiv ℝ L.V x
              (euclideanTangentComponent x (G x)) +
            dot x (G x) * fderiv ℝ L.V x x := by
      conv_lhs =>
        rw [← euclideanTangentComponent_add_radial x (G x)]
      simp only [map_add, map_smul, smul_eq_mul]
    rw [L.euler_identity x] at hdecomp
    norm_num at hdecomp
    have herrorLower := (abs_lt.mp hdecayError).1
    rw [hdecomp] at herrorLower
    linarith

/-- Uniform value and operator-norm derivative errors imply the two open
pointwise errors once explicit value, dissipation, and spherical-geometry
bounds are available.  This quantitative lemma is the interface used by a
`C¹` polynomial approximation theorem. -/
theorem open_polynomial_errors_of_uniform_C1_bounds
    {G : (Fin n → ℝ) → (Fin n → ℝ)}
    (L : StrictHomogeneousC1Lyapunov G 2)
    (E : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ)
    {ε mV mD B : ℝ}
    (hvalueMargin : mV ≤ L.V x)
    (hdecayMargin : mD ≤ -fderiv ℝ L.V x (G x))
    (hgeometry :
      ‖euclideanTangentComponent x (G x)‖ +
          2 * |dot x (G x)| ≤ B)
    (hεV : ε < mV)
    (hεD : ε * B < mD)
    (hvalueApprox :
      |MvPolynomial.eval x E - L.V x| < ε)
    (hderivApprox :
      ‖mvPolynomialDifferential E x - fderiv ℝ L.V x‖ < ε) :
    |MvPolynomial.eval x E - L.V x| < L.V x ∧
      |(fderiv ℝ L.V x
            (euclideanTangentComponent x (G x)) -
          mvPolynomialDifferential E x
            (euclideanTangentComponent x (G x))) +
        2 * dot x (G x) *
          (L.V x - MvPolynomial.eval x E)| <
        -fderiv ℝ L.V x (G x) := by
  constructor
  · exact hvalueApprox.trans_le (hεV.le.trans hvalueMargin)
  · let T : Fin n → ℝ :=
      euclideanTangentComponent x (G x)
    let A : (Fin n → ℝ) →L[ℝ] ℝ :=
      mvPolynomialDifferential E x - fderiv ℝ L.V x
    have hdir :
        |fderiv ℝ L.V x T -
            mvPolynomialDifferential E x T| ≤
          ε * ‖T‖ := by
      calc
        |fderiv ℝ L.V x T -
            mvPolynomialDifferential E x T| =
            ‖A T‖ := by
          simp only [A, ContinuousLinearMap.sub_apply,
            Real.norm_eq_abs]
          rw [abs_sub_comm]
        _ ≤ ‖A‖ * ‖T‖ :=
          A.le_opNorm T
        _ ≤ ε * ‖T‖ := by
          exact mul_le_mul_of_nonneg_right
            hderivApprox.le (norm_nonneg T)
    have hvalueTerm :
        |2 * dot x (G x) *
            (L.V x - MvPolynomial.eval x E)| ≤
          2 * |dot x (G x)| * ε := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_sub_comm]
      exact mul_le_mul_of_nonneg_left hvalueApprox.le
        (mul_nonneg (by norm_num) (abs_nonneg _))
    calc
      |(fderiv ℝ L.V x
              (euclideanTangentComponent x (G x)) -
            mvPolynomialDifferential E x
              (euclideanTangentComponent x (G x))) +
          2 * dot x (G x) *
            (L.V x - MvPolynomial.eval x E)| ≤
          ε * ‖T‖ + 2 * |dot x (G x)| * ε := by
        exact (abs_add_le _ _).trans
          (add_le_add hdir hvalueTerm)
      _ = ε *
          (‖euclideanTangentComponent x (G x)‖ +
            2 * |dot x (G x)|) := by
        dsimp only [T]
        ring
      _ ≤ ε * B := by
        have hεnonneg : 0 ≤ ε := by
          by_contra hε
          have hεneg : ε < 0 := lt_of_not_ge hε
          have hnormNonneg :
              0 ≤ ‖mvPolynomialDifferential E x -
                fderiv ℝ L.V x‖ := norm_nonneg _
          linarith
        exact mul_le_mul_of_nonneg_left hgeometry hεnonneg
      _ < mD := hεD
      _ ≤ -fderiv ℝ L.V x (G x) := hdecayMargin

/-- Coordinatewise partial-derivative approximation implies the same open
errors with the coordinate `ℓ¹` geometry weight.  This is the version that
matches `HasC1MvPolynomialApproximationOn` exactly. -/
theorem open_polynomial_errors_of_uniform_coordinate_C1_bounds
    {G : (Fin n → ℝ) → (Fin n → ℝ)}
    (L : StrictHomogeneousC1Lyapunov G 2)
    (E : MvPolynomial (Fin n) ℝ)
    (x : Fin n → ℝ)
    {ε mV mD B : ℝ}
    (hvalueMargin : mV ≤ L.V x)
    (hdecayMargin : mD ≤ -fderiv ℝ L.V x (G x))
    (hgeometry :
      coordinateTangentialGeometryWeight G x ≤ B)
    (hεV : ε < mV)
    (hεD : ε * B < mD)
    (hvalueApprox :
      |MvPolynomial.eval x E - L.V x| < ε)
    (hpartialApprox :
      ∀ i : Fin n,
        |MvPolynomial.eval x (pderiv i E) -
          fderiv ℝ L.V x (Pi.single i 1)| < ε) :
    |MvPolynomial.eval x E - L.V x| < L.V x ∧
      |(fderiv ℝ L.V x
            (euclideanTangentComponent x (G x)) -
          mvPolynomialDifferential E x
            (euclideanTangentComponent x (G x))) +
        2 * dot x (G x) *
          (L.V x - MvPolynomial.eval x E)| <
        -fderiv ℝ L.V x (G x) := by
  constructor
  · exact hvalueApprox.trans_le (hεV.le.trans hvalueMargin)
  · let T : Fin n → ℝ :=
      euclideanTangentComponent x (G x)
    have hdirIdentity :
        fderiv ℝ L.V x T -
            mvPolynomialDifferential E x T =
          ∑ i : Fin n,
            (fderiv ℝ L.V x (Pi.single i 1) -
              MvPolynomial.eval x (pderiv i E)) * T i := by
      rw [continuousLinearMap_apply_eq_sum_piSingle
        (fderiv ℝ L.V x) T,
        mvPolynomialDifferential_apply,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    have hdir :
        |fderiv ℝ L.V x T -
            mvPolynomialDifferential E x T| ≤
          ε * ∑ i : Fin n, |T i| := by
      rw [hdirIdentity]
      calc
        |∑ i : Fin n,
            (fderiv ℝ L.V x (Pi.single i 1) -
              MvPolynomial.eval x (pderiv i E)) * T i| ≤
            ∑ i : Fin n,
              |(fderiv ℝ L.V x (Pi.single i 1) -
                MvPolynomial.eval x (pderiv i E)) * T i| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin n, ε * |T i| := by
          apply Finset.sum_le_sum
          intro i _hi
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right
            (by
              rw [abs_sub_comm]
              exact (hpartialApprox i).le)
            (abs_nonneg _)
        _ = ε * ∑ i : Fin n, |T i| := by
          rw [Finset.mul_sum]
    have hvalueTerm :
        |2 * dot x (G x) *
            (L.V x - MvPolynomial.eval x E)| ≤
          2 * |dot x (G x)| * ε := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_sub_comm]
      exact mul_le_mul_of_nonneg_left hvalueApprox.le
        (mul_nonneg (by norm_num) (abs_nonneg _))
    calc
      |(fderiv ℝ L.V x
              (euclideanTangentComponent x (G x)) -
            mvPolynomialDifferential E x
              (euclideanTangentComponent x (G x))) +
          2 * dot x (G x) *
            (L.V x - MvPolynomial.eval x E)| ≤
          ε * (∑ i : Fin n, |T i|) +
            2 * |dot x (G x)| * ε := by
        exact (abs_add_le _ _).trans
          (add_le_add hdir hvalueTerm)
      _ = ε * coordinateTangentialGeometryWeight G x := by
        dsimp only [T]
        unfold coordinateTangentialGeometryWeight
        ring
      _ ≤ ε * B := by
        have hεnonneg : 0 ≤ ε := by
          by_contra hε
          have hεneg : ε < 0 := lt_of_not_ge hε
          have habsNonneg :
              0 ≤
                |MvPolynomial.eval x E - L.V x| :=
            abs_nonneg _
          linarith
        exact mul_le_mul_of_nonneg_left hgeometry hεnonneg
      _ < mD := hεD
      _ ≤ -fderiv ℝ L.V x (G x) := hdecayMargin

/-- Compactness supplies one uniform coordinatewise `C¹` tolerance for
which every approximating polynomial satisfies the open Lyapunov errors on
the whole Euclidean unit sphere. -/
theorem exists_uniform_coordinate_C1_tolerance_for_open_errors
    {G : (Fin n → ℝ) → (Fin n → ℝ)}
    (L : StrictHomogeneousC1Lyapunov G 2)
    (hG : Continuous G) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ E : MvPolynomial (Fin n) ℝ,
        (∀ x : Fin n → ℝ, normSq x = 1 →
          |MvPolynomial.eval x E - L.V x| < ε) →
        (∀ x : Fin n → ℝ, normSq x = 1 → ∀ i : Fin n,
          |MvPolynomial.eval x (pderiv i E) -
            fderiv ℝ L.V x (Pi.single i 1)| < ε) →
        ∀ x : Fin n → ℝ, normSq x = 1 →
          |MvPolynomial.eval x E - L.V x| < L.V x ∧
          |(fderiv ℝ L.V x
                (euclideanTangentComponent x (G x)) -
              mvPolynomialDifferential E x
                (euclideanTangentComponent x (G x))) +
            2 * dot x (G x) *
              (L.V x - MvPolynomial.eval x E)| <
            -fderiv ℝ L.V x (G x) := by
  have hsphereNonzero :
      ∀ x : Fin n → ℝ, normSq x = 1 → x ≠ 0 := by
    intro x hx hzero
    rw [hzero, normSq_zero] at hx
    norm_num at hx
  obtain ⟨mV, hmVpos, hmV⟩ :=
    exists_pos_lower_bound_continuous_on_euclideanUnitSphere
      L.V L.contDiff.continuous (fun x hx ↦
        L.positive x (hsphereNonzero x hx))
  obtain ⟨mD, hmDpos, hmD⟩ :=
    exists_pos_lower_bound_continuous_on_euclideanUnitSphere
      (fun x ↦ -fderiv ℝ L.V x (G x))
      (continuous_neg_fderiv_along L hG)
      (fun x hx ↦ by
        have := L.decreases x (hsphereNonzero x hx)
        linarith)
  obtain ⟨B, hBpos, hB⟩ :=
    exists_pos_coordinateTangentialGeometryBound hG
  let η : ℝ := min mV mD
  let ε : ℝ := η / (B + 1)
  have hηpos : 0 < η := lt_min hmVpos hmDpos
  have hden : 1 < B + 1 := by linarith
  have hεpos : 0 < ε := by
    exact div_pos hηpos (by linarith)
  have hεV : ε < mV := by
    have hεη : ε < η :=
      div_lt_self hηpos hden
    exact hεη.trans_le (min_le_left _ _)
  have hεD : ε * B < mD := by
    have hBnonneg : 0 ≤ B := hBpos.le
    have hratio : B / (B + 1) < 1 := by
      exact (div_lt_one (by linarith)).2 (by linarith)
    have hεη : ε * B < η := by
      dsimp only [ε]
      calc
        η / (B + 1) * B =
            η * (B / (B + 1)) := by ring
        _ < η * 1 :=
          mul_lt_mul_of_pos_left hratio hηpos
        _ = η := mul_one η
    exact hεη.trans_le (min_le_right _ _)
  refine ⟨ε, hεpos, ?_⟩
  intro E hvalueApprox hpartialApprox x hx
  exact open_polynomial_errors_of_uniform_coordinate_C1_bounds
    L E x (hmV x hx) (hmD x hx) (hB x hx)
    hεV hεD (hvalueApprox x hx) (hpartialApprox x hx)

/-! ## Radial homogenization and the checker-facing witness -/

/-- An even polynomial satisfying the strict tangential inequalities on
the Euclidean unit sphere yields the exact homogeneous real witness used
by the rational certificate search.

The target degree is chosen canonically as
`2 * (C.totalDegree + 1)`, so no effective degree-selection issue remains. -/
theorem realRationalLyapunovWitness_of_evenPolynomial_tangential
    {d : ℕ} (F : PolynomialField n)
    (hF : IsHomogeneousOfDegree d F)
    (C : MvPolynomial (Fin n) ℝ)
    (hvalue :
      ∀ x : Fin n → ℝ, normSq x = 1 →
        0 < MvPolynomial.eval x (evenPolynomialPart C))
    (hdecay :
      ∀ x : Fin n → ℝ, normSq x = 1 →
        0 <
          -mvPolynomialDifferential (evenPolynomialPart C) x
              (euclideanTangentComponent x
                (realPolynomialFieldEval
                  (realPolynomialFieldOfRational F) x)) -
            2 * MvPolynomial.eval x (evenPolynomialPart C) *
              dot x
                (realPolynomialFieldEval
                  (realPolynomialFieldOfRational F) x)) :
    Nonempty (RealRationalLyapunovWitness F) := by
  let r : ℕ := C.totalDegree
  let M : ℕ := 2 * (r + 1)
  let E : MvPolynomial (Fin n) ℝ := evenPolynomialPart C
  let p : MvPolynomial (Fin n) ℝ :=
    radialHomogenization M E
  have hM_even : Even M := by
    refine ⟨r + 1, ?_⟩
    dsimp only [M]
    omega
  have hdegree :
      ∀ e ∈ C.support, e.degree ≤ M := by
    intro e he
    exact (MvPolynomial.le_totalDegree he).trans (by
      dsimp only [M, r]
      omega)
  have hparity : HasRadialHomogenizationParity M E := by
    exact
      evenPolynomialPart_hasRadialHomogenizationParity
        C M hM_even hdegree
  have hp : p.IsHomogeneous M :=
    radialHomogenization_isHomogeneous M E hparity
  have hpDegree :
      p.IsHomogeneous (2 * (r + 1)) := by
    exact hp
  have hFreal :
      IsRealHomogeneousOfDegree d
        (realPolynomialFieldOfRational F) :=
    realPolynomialFieldOfRational_isHomogeneous F hF
  have hqHom :
      (realRationalLyapunovNumerator
          (realPolynomialFieldOfRational F) p r).IsHomogeneous
        (2 * r + d + 3) := by
    apply realRationalLyapunovNumerator_isHomogeneous
      (realPolynomialFieldOfRational F) p r hFreal
    simpa [mul_add] using hpDegree
  have hpEuclidean :
      ∀ x : Fin n → ℝ, normSq x = 1 →
        0 < MvPolynomial.eval x p := by
    intro x hx
    change
      0 < MvPolynomial.eval x (radialHomogenization M E)
    rw [eval_radialHomogenization_of_normSq_eq_one M E x hx]
    exact hvalue x hx
  have hqEuclidean :
      ∀ x : Fin n → ℝ, normSq x = 1 →
        0 < MvPolynomial.eval x
          (realRationalLyapunovNumerator
            (realPolynomialFieldOfRational F) p r) := by
    intro x hx
    rw [
      eval_realRationalLyapunovNumerator_of_normSq_eq_one
        (realPolynomialFieldOfRational F) p r hpDegree x hx,
      show p = radialHomogenization M E by rfl,
      mvPolynomialDifferential_radialHomogenization_apply_of_tangent
        M E x
          (euclideanTangentComponent x
            (realPolynomialFieldEval
              (realPolynomialFieldOfRational F) x))
        hx
        (dot_euclideanTangentComponent_eq_zero x
          (realPolynomialFieldEval
            (realPolynomialFieldOfRational F) x) hx),
      eval_radialHomogenization_of_normSq_eq_one M E x hx]
    exact hdecay x hx
  refine ⟨{
    denominatorExponent := r
    numerator := p
    numerator_isHomogeneous := hpDegree
    value_positive_on_unitSphere := ?_
    decay_positive_on_unitSphere := ?_ }⟩
  · intro x hx
    apply eval_pos_of_isHomogeneous_of_normSq_one_pos
      hpDegree hpEuclidean x
    exact norm_ne_zero_iff.mp (by norm_num [hx])
  · intro x hx
    apply eval_pos_of_isHomogeneous_of_normSq_one_pos
      hqHom hqEuclidean x
    exact norm_ne_zero_iff.mp (by norm_num [hx])

/-- A degree-two strict homogeneous `C¹` Lyapunov function and one
polynomial satisfying the explicit open approximation errors produce the
checker-facing homogeneous witness. -/
theorem realRationalLyapunovWitness_of_open_polynomial_approximation
    {d : ℕ} (F : PolynomialField n)
    (hF : IsHomogeneousOfDegree d F)
    (L : StrictHomogeneousC1Lyapunov
      (realPolynomialFieldEval
        (realPolynomialFieldOfRational F)) 2)
    (C : MvPolynomial (Fin n) ℝ)
    (hvalueError :
      ∀ x : Fin n → ℝ, normSq x = 1 →
        |MvPolynomial.eval x (evenPolynomialPart C) - L.V x| <
          L.V x)
    (hdecayError :
      ∀ x : Fin n → ℝ, normSq x = 1 →
        |(fderiv ℝ L.V x
              (euclideanTangentComponent x
                (realPolynomialFieldEval
                  (realPolynomialFieldOfRational F) x)) -
            mvPolynomialDifferential (evenPolynomialPart C) x
              (euclideanTangentComponent x
                (realPolynomialFieldEval
                  (realPolynomialFieldOfRational F) x))) +
          2 * dot x
              (realPolynomialFieldEval
                (realPolynomialFieldOfRational F) x) *
            (L.V x -
              MvPolynomial.eval x (evenPolynomialPart C))| <
          -fderiv ℝ L.V x
            (realPolynomialFieldEval
              (realPolynomialFieldOfRational F) x)) :
    Nonempty (RealRationalLyapunovWitness F) := by
  apply realRationalLyapunovWitness_of_evenPolynomial_tangential
    F hF C
  · intro x hx
    exact
      (polynomial_tangential_lyapunov_of_open_errors
        L (evenPolynomialPart C) x hx
        (hvalueError x hx) (hdecayError x hx)).1
  · intro x hx
    exact
      (polynomial_tangential_lyapunov_of_open_errors
        L (evenPolynomialPart C) x hx
        (hvalueError x hx) (hdecayError x hx)).2

end

end HGAS
