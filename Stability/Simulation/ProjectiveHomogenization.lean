import HGAS.Compactification.AllAffinePolynomialCode
import HGAS.Compactification.MixedCentralPolynomialComputability

/-!
# Sparse homogenization with one final coordinate

The existing one-block sparse compiler places the affine coordinates at
`Fin.castSucc` and its new coordinate at `Fin.last`. The results here expose
ordinary homogeneity, chart evaluation, and vanishing on the equator.
-/

namespace Stability.ProjectivePolynomialCode

open HGAS MvPolynomial
open scoped BigOperators

variable {n : ℕ}

theorem xIndex_eq_castSucc (i : Fin n) :
    MixedCentralPolynomialCode.xIndex (k := 1) i = i.castSucc := rfl

theorem wIndex_eq_last :
    MixedCentralPolynomialCode.wIndex (n := n) (0 : Fin 1) = Fin.last n := by
  apply Fin.ext
  simp [MixedCentralPolynomialCode.wIndex, MultiCentralPolynomialCode.wIndex]

/-- Executable ordinary homogenization using one additional last coordinate. -/
def homogenize (d : ℕ) (p : PolynomialCode n) : PolynomialCode (n + 1) :=
  MixedCentralPolynomialCode.homogenize
    (MixedCentralPolynomialCode.oneBlockAllAffineLayout n) d p

theorem homogenize_primrec (d : ℕ) :
    Primrec (homogenize d : PolynomialCode n → PolynomialCode (n + 1)) :=
  MixedCentralPolynomialCode.homogenize_primrec _ d

theorem liftExponent_castSucc (d : ℕ) (e : ExponentCode n) (i : Fin n) :
    MixedCentralPolynomialCode.liftExponent
      (MixedCentralPolynomialCode.oneBlockAllAffineLayout n) d e i.castSucc = e i := by
  rw [← xIndex_eq_castSucc]
  exact MixedCentralPolynomialCode.liftExponent_xIndex _ _ _ _

theorem liftExponent_last (d : ℕ) (e : ExponentCode n) :
    MixedCentralPolynomialCode.liftExponent
      (MixedCentralPolynomialCode.oneBlockAllAffineLayout n) d e (Fin.last n) =
        d - ExponentCode.totalDegree e := by
  rw [← wIndex_eq_last, MixedCentralPolynomialCode.liftExponent_wIndex,
    MixedCentralPolynomialCode.affineBlockDegree_oneBlockAllAffineLayout]

theorem totalDegree_liftExponent (d : ℕ) (e : ExponentCode n)
    (he : ExponentCode.totalDegree e ≤ d) :
    ExponentCode.totalDegree (MixedCentralPolynomialCode.liftExponent
      (MixedCentralPolynomialCode.oneBlockAllAffineLayout n) d e) = d := by
  rw [ExponentCode.totalDegree, List.sum_ofFn, Fin.sum_univ_castSucc]
  simp only [liftExponent_castSucc, liftExponent_last]
  simpa only [ExponentCode.totalDegree, List.sum_ofFn] using Nat.add_sub_of_le he

/-- The raw homogenized list obeys the same degree bound before decoding. -/
theorem termsDegreeLE_homogenize (d : ℕ) (p : PolynomialCode n)
    (hp : PolynomialCode.TermsDegreeLE d p) :
    PolynomialCode.TermsDegreeLE d (homogenize d p) := by
  intro t ht
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  change ExponentCode.totalDegree (MixedCentralPolynomialCode.liftExponent
    (MixedCentralPolynomialCode.oneBlockAllAffineLayout n) d u.1) ≤ d
  rw [totalDegree_liftExponent d u.1 (hp u hu)]

/-- Every decoded homogenization is genuinely homogeneous, under the
raw term-degree bound required for natural subtraction to clear powers. -/
theorem isHomogeneous_homogenize (d : ℕ) (p : PolynomialCode n)
    (hp : PolynomialCode.TermsDegreeLE d p) :
    (PolynomialCode.decode (homogenize d p)).IsHomogeneous d := by
  induction p with
  | nil => exact isHomogeneous_zero _ _ d
  | cons t p ih =>
      have ht : ExponentCode.totalDegree t.1 ≤ d := hp t (by simp)
      have hp' : PolynomialCode.TermsDegreeLE d p := fun u hu ↦ hp u (by simp [hu])
      change (PolynomialCode.decodeTerm
        (MixedCentralPolynomialCode.liftTerm
          (MixedCentralPolynomialCode.oneBlockAllAffineLayout n) d t) +
          PolynomialCode.decode (homogenize d p)).IsHomogeneous d
      apply IsHomogeneous.add _ (ih hp')
      apply isHomogeneous_monomial
      rw [ExponentCode.degree_decode]
      exact totalDegree_liftExponent d t.1 ht

/-- Evaluation in the scaled affine chart, including a zero chart scale. -/
theorem eval_homogenize_scaled (d : ℕ) (p : PolynomialCode n)
    (hp : PolynomialCode.TermsDegreeLE d p) (x : Fin n → ℝ) (z : ℝ) :
    eval₂Hom (algebraMap ℚ ℝ) (Fin.lastCases z (fun i ↦ z * x i))
      (PolynomialCode.decode (homogenize d p)) =
        z ^ d * eval₂Hom (algebraMap ℚ ℝ) x (PolynomialCode.decode p) := by
  have h := MixedCentralPolynomialCode.eval₂Hom_homogenize_scaledChart
    (MixedCentralPolynomialCode.oneBlockAllAffineLayout n) d p
    (MixedCentralPolynomialCode.termsAffineBlockDegreeLE_oneBlockAllAffineLayout hp)
    (fun _ ↦ z) x
  have hpoint : MixedCentralPolynomialCode.scaledChartPoint
      (MixedCentralPolynomialCode.oneBlockAllAffineLayout n) (fun _ ↦ z) x =
        Fin.lastCases z (fun i ↦ z * x i) := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [← wIndex_eq_last, MixedCentralPolynomialCode.scaledChartPoint_wIndex,
        wIndex_eq_last]
      simp
    · rw [← xIndex_eq_castSucc, MixedCentralPolynomialCode.scaledChartPoint_xIndex,
        xIndex_eq_castSucc]
      simp
  rw [hpoint] at h
  simpa only [homogenize, MixedCentralPolynomialCode.slowdown, Fin.prod_univ_one] using h

/-- Away from the equator the homogeneous polynomial evaluates to the
usual denominator-cleared affine expression. -/
theorem eval_homogenize_quotient (d : ℕ) (p : PolynomialCode n)
    (hp : PolynomialCode.TermsDegreeLE d p) (y : Fin (n + 1) → ℝ)
    (hy : y (Fin.last n) ≠ 0) :
    eval₂Hom (algebraMap ℚ ℝ) y (PolynomialCode.decode (homogenize d p)) =
      y (Fin.last n) ^ d * eval₂Hom (algebraMap ℚ ℝ)
        (fun i ↦ y i.castSucc / y (Fin.last n)) (PolynomialCode.decode p) := by
  have hpoint : Fin.lastCases (y (Fin.last n))
      (fun i ↦ y (Fin.last n) * (y i.castSucc / y (Fin.last n))) = y := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp
    · simp only [Fin.lastCases_castSucc]
      field_simp
  simpa only [hpoint] using eval_homogenize_scaled d p hp
    (fun i ↦ y i.castSucc / y (Fin.last n)) (y (Fin.last n))

/-- A strict raw source degree bound forces the homogenization to vanish
on the entire equator, not just on a chosen affine chart. -/
theorem eval_homogenize_equator (d : ℕ) (p : PolynomialCode n)
    (hp : ∀ t ∈ p, ExponentCode.totalDegree t.1 < d)
    (y : Fin (n + 1) → ℝ) (hy : y (Fin.last n) = 0) :
    eval₂Hom (algebraMap ℚ ℝ) y (PolynomialCode.decode (homogenize d p)) = 0 := by
  induction p with
  | nil => simp [homogenize, MixedCentralPolynomialCode.homogenize]
  | cons t p ih =>
      have ht : ExponentCode.totalDegree t.1 < d := hp t (by simp)
      have hp' : ∀ u ∈ p, ExponentCode.totalDegree u.1 < d := fun u hu ↦ hp u (by simp [hu])
      change eval₂Hom (algebraMap ℚ ℝ) y
        (PolynomialCode.decodeTerm (MixedCentralPolynomialCode.liftTerm
          (MixedCentralPolynomialCode.oneBlockAllAffineLayout n) d t) +
          PolynomialCode.decode (homogenize d p)) = 0
      rw [map_add, ih hp', add_zero]
      simp only [PolynomialCode.decodeTerm, MixedCentralPolynomialCode.liftTerm,
        eval₂Hom_monomial]
      rw [Finsupp.prod_of_support_subset _ (Finset.subset_univ _) _ (by simp)]
      change _ * (∏ i, y i ^
        MixedCentralPolynomialCode.liftExponent
          (MixedCentralPolynomialCode.oneBlockAllAffineLayout n) d t.1 i) = 0
      rw [Fin.prod_univ_castSucc, liftExponent_last, hy,
        zero_pow (Nat.sub_ne_zero_of_lt ht), mul_zero, mul_zero]

end Stability.ProjectivePolynomialCode
