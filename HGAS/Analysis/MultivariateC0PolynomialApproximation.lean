import HGAS.Analysis.MvPolynomialCalculus
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Tactic

/-!
# Uniform polynomial approximation on compact sets in finite dimension

This file packages the ordinary multivariate Stone--Weierstrass theorem
directly in terms of `MvPolynomial`.  It is a useful companion to the
Bernstein `C¹` argument: the only extra ingredient needed for the latter is
control of the first derivatives.

The construction is reusable beyond cubes.  On any compact subset of
`Fin n → ℝ`, evaluations of multivariate polynomials form a subalgebra of
the continuous functions and separate points because the coordinate
polynomials do.
-/

namespace HGAS

open Set

noncomputable section

variable {n : ℕ}

/-- Restriction of multivariate-polynomial evaluation to a set, bundled as
a continuous function. -/
def mvPolynomialToContinuousMapOn
    (s : Set (Fin n → ℝ)) (p : MvPolynomial (Fin n) ℝ) :
    C(s, ℝ) where
  toFun x := MvPolynomial.eval x.1 p
  continuous_toFun :=
    (continuous_mvPolynomial_eval p).comp continuous_subtype_val

@[simp]
theorem mvPolynomialToContinuousMapOn_apply
    (s : Set (Fin n → ℝ)) (p : MvPolynomial (Fin n) ℝ) (x : s) :
    mvPolynomialToContinuousMapOn s p x =
      MvPolynomial.eval x.1 p :=
  rfl

/-- Polynomial restriction is an algebra homomorphism into the continuous
functions on the set. -/
def mvPolynomialToContinuousMapOnAlgHom
    (s : Set (Fin n → ℝ)) :
    MvPolynomial (Fin n) ℝ →ₐ[ℝ] C(s, ℝ) where
  toFun := mvPolynomialToContinuousMapOn s
  map_one' := by
    ext x
    simp [mvPolynomialToContinuousMapOn]
  map_mul' p q := by
    ext x
    simp [mvPolynomialToContinuousMapOn]
  map_zero' := by
    ext x
    simp [mvPolynomialToContinuousMapOn]
  map_add' p q := by
    ext x
    simp [mvPolynomialToContinuousMapOn]
  commutes' c := by
    ext x
    simp [mvPolynomialToContinuousMapOn]

@[simp]
theorem mvPolynomialToContinuousMapOnAlgHom_apply
    (s : Set (Fin n → ℝ)) (p : MvPolynomial (Fin n) ℝ) :
    mvPolynomialToContinuousMapOnAlgHom s p =
      mvPolynomialToContinuousMapOn s p :=
  rfl

/-- The polynomial functions on a subset of finite-dimensional coordinate
space separate its points. -/
theorem mvPolynomialFunctions_separatesPoints
    (s : Set (Fin n → ℝ)) :
    (mvPolynomialToContinuousMapOnAlgHom s).range.SeparatesPoints := by
  intro x y hxy
  have hcoordinate : ∃ i : Fin n, x.1 i ≠ y.1 i := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hxy
    apply Subtype.ext
    exact funext h
  obtain ⟨i, hi⟩ := hcoordinate
  let coordinate :
      C(s, ℝ) :=
    mvPolynomialToContinuousMapOn s (MvPolynomial.X i)
  have hcoordinate_mem :
      coordinate ∈
        (mvPolynomialToContinuousMapOnAlgHom s).range :=
    ⟨MvPolynomial.X i, rfl⟩
  have hcoordinate_image :
      (coordinate : s → ℝ) ∈
        (fun u : C(s, ℝ) ↦ (u : s → ℝ)) ''
          ((mvPolynomialToContinuousMapOnAlgHom s).range :
            Set C(s, ℝ)) :=
    ⟨coordinate, hcoordinate_mem, rfl⟩
  refine ⟨(coordinate : s → ℝ), hcoordinate_image, ?_⟩
  simpa only [coordinate, mvPolynomialToContinuousMapOn_apply,
    MvPolynomial.eval_X] using hi

/-- Multivariate real polynomials are uniformly dense in the continuous
functions on every compact subset of `Fin n → ℝ`.

The approximation is stated pointwise with an absolute-value bound, which
is the form used by the later Lyapunov estimates. -/
theorem exists_mvPolynomial_near_of_isCompact
    (s : Set (Fin n → ℝ)) (hs : IsCompact s)
    (f : (Fin n → ℝ) → ℝ) (hf : ContinuousOn f s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin n) ℝ,
      ∀ x ∈ s, |MvPolynomial.eval x p - f x| < ε := by
  letI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  let A : Subalgebra ℝ C(s, ℝ) :=
    (mvPolynomialToContinuousMapOnAlgHom s).range
  have hsep : A.SeparatesPoints :=
    mvPolynomialFunctions_separatesPoints s
  have hcontinuous :
      Continuous (fun x : s ↦ f x.1) :=
    continuousOn_iff_continuous_restrict.mp hf
  obtain ⟨g, hg⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
      A hsep (fun x : s ↦ f x.1) hcontinuous ε hε
  obtain ⟨p, hp⟩ := g.property
  refine ⟨p, ?_⟩
  intro x hx
  have hpoint := hg ⟨x, hx⟩
  rw [← hp] at hpoint
  simpa only [mvPolynomialToContinuousMapOnAlgHom_apply,
    mvPolynomialToContinuousMapOn_apply, Real.norm_eq_abs] using hpoint

end

end HGAS
